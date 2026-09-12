//! Minimal OCI distribution-spec client (push/pull) over `ureq`.
//!
//! Protocol per https://github.com/opencontainers/distribution-spec:
//! - blob upload:  POST /v2/<repo>/blobs/uploads/  → 202 + Location
//!                 PUT  <location>?digest=sha256:<hex> (blob bytes)
//! - manifest:     PUT  /v2/<repo>/manifests/<tag>  (OCI manifest JSON)
//! - manifest:     GET  /v2/<repo>/manifests/<tag>  (Accept: manifest type)
//! - blob:         GET  /v2/<repo>/blobs/sha256:<hex>
//!
//! Plain HTTP for local/test registries; https works via ureq's bundled
//! rustls. Auth: OPTIONAL bearer token — when set, `Authorization:
//! Bearer <token>` rides on EVERY request (blob POST/PUT/GET, manifest
//! PUT/GET). No OAuth/OIDC dance here: the token flow's token-exchange
//! endpoint (WWW-Authenticate → challenge → token fetch) is out of
//! scope; callers obtain the token however they do and we present it.

use std::fs;
use std::io::{self, Read};
use std::path::{Path, PathBuf};


use crate::manifest::{Manifest, MANIFEST_MEDIA_TYPE};
use crate::oci::{Digest, OciStore, sha256_hex};

/// A parsed registry target: `<base>/<repo>` with an optional
/// `http://`/`https://` scheme (default http).
pub struct Registry {
    /// e.g. `http://127.0.0.1:5000`
    pub base: String,
    /// e.g. `guestlang/demo`
    pub repo: String,
    /// Optional bearer token: sent as `Authorization: Bearer <token>`
    /// on all requests when present.
    pub token: Option<String>,
}

/// What a pull landed, for reporting.
pub struct Pulled {
    pub manifest: Manifest,
    /// (label, bare hex digest, bytes) per materialized artifact.
    pub artifacts: Vec<(String, Digest, Vec<u8>)>,
}

impl Registry {
    /// Parse `registry/repo:tag` (or `scheme://registry/repo:tag`) into
    /// the client + tag. Tag defaults to `latest`.
    pub fn parse(target: &str) -> Result<(Registry, String), String> {
        let (scheme, rest) = if let Some(r) = target.strip_prefix("http://") {
            ("http", r)
        } else if let Some(r) = target.strip_prefix("https://") {
            ("https", r)
        } else {
            ("http", target)
        };
        let (host, repo_tag) = rest
            .split_once('/')
            .ok_or_else(|| format!("registry target `{target}`: missing repo (want registry/repo:tag)"))?;
        if host.is_empty() || repo_tag.is_empty() {
            return Err(format!("registry target `{target}`: empty host or repo"));
        }
        let (repo, tag) = match repo_tag.rsplit_once(':') {
            Some((r, t)) if !t.contains('/') => (r, t),
            _ => (repo_tag, "latest"),
        };
        Ok((
            Registry {
                base: format!("{scheme}://{host}"),
                repo: repo.to_string(),
                token: None,
            },
            tag.to_string(),
        ))
    }

    /// Client with bearer auth: same shape as `parse`'s output but with
    /// a token attached (sent on every request).
    pub fn with_token(base: String, repo: String, token: String) -> Registry {
        Registry {
            base,
            repo,
            token: Some(token),
        }
    }

    /// Attach the Authorization header when a token is set.
    fn auth(&self, req: ureq::Request) -> ureq::Request {
        match &self.token {
            Some(t) => req.set("Authorization", &format!("Bearer {t}")),
            None => req,
        }
    }

    /// Push blobs (by path; digests are computed from the bytes) then
    /// the manifest, tagged `tag`.
    pub fn push(&self, tag: &str, manifest: &Manifest, blobs: &[PathBuf]) -> Result<(), String> {
        let agent = agent();
        let mut uploaded: Vec<Digest> = Vec::new();
        for path in blobs {
            let data = fs::read(path)
                .map_err(|e| format!("read blob {}: {e}", path.display()))?;
            let digest = sha256_hex(&data);
            if uploaded.contains(&digest) {
                continue;
            }
            self.upload_blob(&agent, &digest, &data)?;
            uploaded.push(digest);
        }
        self.put_manifest(&agent, tag, manifest)
    }

    /// Pull the tagged manifest, fetch + verify every blob, store all of
    /// them into `dst`, and materialize the layer artifact at
    /// `<artifacts_root>/<label>`.
    pub fn pull(
        &self,
        tag: &str,
        dst: &mut OciStore,
        artifacts_root: &Path,
    ) -> Result<Pulled, String> {
        let agent = agent();
        let raw = self.fetch_manifest(&agent, tag)?;
        let manifest = Manifest::from_bytes(&raw)?;

        let mut fetched: Vec<(Digest, Vec<u8>)> = Vec::new();
        for desc in manifest.blobs() {
            let data = self.fetch_blob(&agent, &desc.digest)?;
            let actual = sha256_hex(&data);
            if actual != desc.digest {
                let claimed = desc.digest.clone();
                return Err(format!(
                    "pull {}/{}: blob digest mismatch: manifest {claimed}, got {actual}",
                    self.repo, tag
                ));
            }
            // Non-layer blobs (the config) keep their digest as the
            // store label — content-addressed either way.
            dst.put(&desc.digest, &data)
                .map_err(|e| format!("store blob {}: {e}", desc.digest))?;
            fetched.push((desc.digest.clone(), data));
        }

        // Materialize the layer artifact where the manifest's label
        // annotation says. Single-layer manifests only: one artifact
        // per image is the forge's model.
        // TODO(registry): multi-layer artifacts if component + assets
        // ever share one manifest.
        let layer = manifest
            .layers
            .first()
            .ok_or("manifest: zero layers")?;
        let bytes = fetched
            .iter()
            .find(|(d, _)| d == &layer.digest)
            .map(|(_, b)| b.clone())
            .ok_or("manifest: layer blob not fetched")?;
        if manifest.label.contains("..") || manifest.label.starts_with('/') {
            return Err(format!("manifest label `{}` escapes the root", manifest.label));
        }
        let artifact_path = artifacts_root.join(&manifest.label);
        if let Some(parent) = artifact_path.parent() {
            fs::create_dir_all(parent)
                .map_err(|e| format!("mkdir {}: {e}", parent.display()))?;
        }
        fs::write(&artifact_path, &bytes)
            .map_err(|e| format!("write {}: {e}", artifact_path.display()))?;
        // Relabel in the local store so `verify`/index.json see it.
        dst.put(&manifest.label, &bytes)
            .map_err(|e| format!("relabel {}: {e}", manifest.label))?;

        Ok(Pulled {
            artifacts: vec![(manifest.label.clone(), layer.digest.clone(), bytes)],
            manifest,
        })
    }

    fn upload_blob(&self, agent: &ureq::Agent, digest: &str, data: &[u8]) -> Result<(), String> {
        // POST /v2/<repo>/blobs/uploads/ → 202 + Location.
        let init_url = format!("{}/v2/{}/blobs/uploads/", self.base, self.repo);
        let resp = self
            .auth(agent.post(&init_url))
            .set("Content-Type", "application/octet-stream")
            .send_bytes(&[])
            .map_err(|e| http_err(&format!("POST {init_url}"), e))?;
        if resp.status() != 202 {
            return Err(format!("POST {init_url}: expected 202, got {}", resp.status()));
        }
        let location = resp
            .header("Location")
            .ok_or_else(|| format!("POST {init_url}: 202 without Location header"))?;
        let upload_url = self.resolve_location(location);
        // PUT <location>?digest=sha256:<hex> with the blob bytes.
        let sep = if upload_url.contains('?') { '&' } else { '?' };
        let put_url = format!("{upload_url}{sep}digest=sha256:{digest}");
        let resp = self
            .auth(agent.put(&put_url))
            .set("Content-Type", "application/octet-stream")
            .send_bytes(data)
            .map_err(|e| http_err(&format!("PUT {put_url}"), e))?;
        if !(200..300).contains(&resp.status()) {
            return Err(format!("PUT {put_url}: expected 2xx, got {}", resp.status()));
        }
        Ok(())
    }

    fn put_manifest(&self, agent: &ureq::Agent, tag: &str, manifest: &Manifest) -> Result<(), String> {
        let url = format!("{}/v2/{}/manifests/{}", self.base, self.repo, tag);
        let resp = self
            .auth(agent.put(&url))
            .set("Content-Type", MANIFEST_MEDIA_TYPE)
            .send_bytes(&manifest.to_bytes())
            .map_err(|e| http_err(&format!("PUT {url}"), e))?;
        if !(200..300).contains(&resp.status()) {
            return Err(format!("PUT {url}: expected 2xx, got {}", resp.status()));
        }
        Ok(())
    }

    fn fetch_manifest(&self, agent: &ureq::Agent, tag: &str) -> Result<Vec<u8>, String> {
        let url = format!("{}/v2/{}/manifests/{}", self.base, self.repo, tag);
        let resp = self
            .auth(agent.get(&url))
            .set("Accept", MANIFEST_MEDIA_TYPE)
            .call()
            .map_err(|e| http_err(&format!("GET {url}"), e))?;
        let mut buf = Vec::new();
        resp.into_reader()
            .take(64 * 1024 * 1024)
            .read_to_end(&mut buf)
            .map_err(|e| format!("GET {url}: read body: {e}"))?;
        Ok(buf)
    }

    fn fetch_blob(&self, agent: &ureq::Agent, digest: &str) -> Result<Vec<u8>, String> {
        let url = format!("{}/v2/{}/blobs/sha256:{digest}", self.base, self.repo);
        let resp = self
            .auth(agent.get(&url))
            .call()
            .map_err(|e| http_err(&format!("GET {url}"), e))?;
        let mut buf = Vec::new();
        resp.into_reader()
            .take(1024 * 1024 * 1024)
            .read_to_end(&mut buf)
            .map_err(|e| format!("GET {url}: read body: {e}"))?;
        Ok(buf)
    }

    /// Registries may return an absolute URL or an absolute path in
    /// `Location`. Paths resolve against our own base.
    fn resolve_location(&self, location: &str) -> String {
        if location.starts_with("http://") || location.starts_with("https://") {
            location.to_string()
        } else {
            format!("{}{}", self.base, location)
        }
    }
}

fn agent() -> ureq::Agent {
    ureq::AgentBuilder::new().build()
}

/// Render a ureq error with the HTTP status + body when it's a status error.
fn http_err(what: &str, e: ureq::Error) -> String {
    match e {
        ureq::Error::Status(code, resp) => {
            let body = resp.into_string().unwrap_or_default();
            format!("{what}: HTTP {code} {body}")
        }
        e => format!("{what}: {e}"),
    }
}

