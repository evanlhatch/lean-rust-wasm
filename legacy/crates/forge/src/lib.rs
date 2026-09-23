//! forge library surface: the OCI image-layout store (content-addressed
//! artifact caching for the gen pipeline's byte-tie + drift checks).
//!
//! Split from main.rs so integration tests (tests/) can drive the store.
//! The binary keeps the pipeline driver + generated stage machine.

pub mod oci;
