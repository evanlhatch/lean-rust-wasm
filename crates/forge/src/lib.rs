//! forge library surface: the OCI image-layout store, OCI image-manifest
//! packing, and the OCI distribution registry client.
//!
//! Split from main.rs so integration tests (tests/) can drive push/pull
//! against an in-process minimal registry. The binary keeps the pipeline
//! driver + generated stage machine.

pub mod manifest;
pub mod oci;
pub mod registry;
