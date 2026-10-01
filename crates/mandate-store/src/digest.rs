//! The digest face: sha256 content addresses (64 lowercase hex chars).
//!
//! OCI registries require sha256 digests; the digest is both the
//! content address and the security boundary, so it must be
//! cryptographic (`sha2` — hand-rolling sha256 is not acceptable).

use sha2::{Digest as _, Sha256};

/// sha256 digest as a lowercase hex string (64 chars).
pub type Digest = String;

/// sha256 hex digest (64 lowercase hex chars, 256 bits).
pub fn sha256_hex(data: &[u8]) -> Digest {
    let hash = Sha256::digest(data);
    let mut out = String::with_capacity(64);
    for b in hash {
        out.push(char::from_digit((b >> 4) as u32, 16).unwrap_or('0'));
        out.push(char::from_digit((b & 0xf) as u32, 16).unwrap_or('0'));
    }
    out
}

/// Is `s` a well-formed digest (64 lowercase hex chars)? The path-safety
/// face too: only a well-formed digest names a blob path, so traversal
/// (`..`, `/`) is refused before the filesystem is touched.
pub fn is_valid_digest(s: &str) -> bool {
    s.len() == 64 && s.bytes().all(|b| matches!(b, b'0'..=b'9' | b'a'..=b'f'))
}

/// The OCI digest spelling: `sha256:<hex>`.
pub fn oci_digest(hex: &str) -> String {
    format!("sha256:{hex}")
}

/// Strip the `sha256:` prefix, refusing anything else.
pub fn parse_oci_digest(s: &str) -> Option<&str> {
    s.strip_prefix("sha256:").filter(|h| is_valid_digest(h))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn sha256_known_vectors() {
        assert_eq!(
            sha256_hex(b""),
            "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
        );
        assert_eq!(
            sha256_hex(b"abc"),
            "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
        );
    }

    #[test]
    fn digest_validation() {
        assert!(is_valid_digest(&"a".repeat(64)));
        assert!(!is_valid_digest(&"A".repeat(64))); // uppercase refused
        assert!(!is_valid_digest(&"a".repeat(63)));
        assert!(!is_valid_digest("../etc/passwd"));
        assert_eq!(parse_oci_digest("sha256:"), None); // empty hex
        assert_eq!(
            parse_oci_digest(&oci_digest(&"a".repeat(64))),
            Some("a".repeat(64).as_str())
        );
    }
}
