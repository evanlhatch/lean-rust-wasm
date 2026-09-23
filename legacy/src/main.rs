//! Binary — fast-observe base wiring.
//!
//! `init()` is zero-config: stdout logs + fastrace console reporter.
//! Run with no args to see the deterministic fault report.

#![feature(error_generic_member_access)] // error! emits Error::provide

use fast_observe::prelude::*;

error! {
    /// Errors the application can fail with.
    pub enum AppError {
        /// check the path exists and is readable
        #[error("config unreadable: {path}")]
        #[code = "E100", category = Content]
        ConfigUnreadable {
            /// The path we tried to read.
            path: String,
        },
        /// The underlying I/O failure.
        #[error("io: {0}")]
        #[code = "E101", category = Transient, advice = "retry; if persistent, check the disk"]
        #[from]
        Io(std::io::Error),
    }
}

/// Load a config file, failing with a typed `Content` fault on an empty
/// path and a `Transient` fault on I/O errors.
fn load_config(path: &str) -> Result<String, AppError> {
    let _span = scope!("app.load_config");
    ensure!(
        !path.is_empty(),
        ConfigUnreadable {
            path: path.to_owned()
        }
    );
    // `#[from]` wires io::Error → AppError; `?` lifts it into the fault.
    std::fs::read_to_string(path)
        .map_err(AppError::from)
        .map_err(|e| Fault::from(e).attach_key("path", path.to_owned()))
}

fn main() {
    init();

    let path = std::env::args().nth(1).unwrap_or_default();
    match load_config(&path) {
        Ok(contents) => log::info!(bytes = contents.len(); "config loaded"),
        Err(fault) => print!("{}", render_report(&fault)),
    }
}
