//! mandate-store — the OCI artifact store with the provenance badges
//! (design-wave-30 D5; legacy's forge `oci.rs` mined, local layout
//! lane).
//!
//! THE STORE'S SHAPE: the OCI image-layout on disk — content-addressed
//! sha256 blobs + manifests, the image spec's honest subset, no
//! network. The artifacts stored: the wasm components, the WIT worlds,
//! the duel manifests (the tree's gen/ artifacts).
//!
//! THE PROVENANCE ANNOTATIONS: the manifest's annotations ARE the
//! gates' outputs — the axiom-report badge (the artifact's axiom
//! surface, by content), the gates-green stamp, the ledger's content
//! hash. The ledger's row → the manifest's annotations, ONE writer
//! ([`store::Store::put`]); readers elsewhere ([`store::Store::read`],
//! [`prov::check`]).
//!
//! THE VERIFY DISCIPLINE: every read re-hashes every blob; a tampered
//! blob refuses. A manifest whose provenance is incomplete or not
//! green refuses. A stale axiom badge refuses
//! ([`store::Store::read_fresh`]). Refuse-with-report, never silent.
//!
//! THE OCI-REMOTE face (push/pull over oci-distribution — the oci-wasm
//! discipline, a thin wrapper over oci-distribution with the OCI-Wasm
//! config types) is the NAMED NEXT STEP, not this crate: the local
//! store + the annotations + the verify are the content; the layout is
//! deliberately image-spec-shaped so the remote lane uploads from
//! [`store::Store::blob_path`] + manifest digests without re-packing.

pub mod digest;
pub mod prov;
pub mod store;

pub use digest::Digest;
pub use prov::{ProvRefusal, Provenance};
pub use store::{Artifact, Refusal, Store, StoreError, StoredRow, Verify};
