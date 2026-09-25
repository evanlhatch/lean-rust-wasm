//! The typed error surface. Data, not strings (rendering is `Display`'s
//! job): every failure the log surfaces maps to a ctor — no bare panics,
//! no silent truncation, no silent misparse.

use std::fmt;

/// Every error the delta log surfaces.
#[derive(Debug)]
pub enum DeltaError {
    /// The durable backend failed.
    Io(std::io::Error),
    /// A delta's payload doesn't match the log's schema (row arity,
    /// field types, key type, or a key name that names no field).
    SchemaMismatch {
        /// What mismatched.
        reason: &'static str,
    },
    /// A COMPLETE frame that fails to decode. Mid-log corruption (or a
    /// corrupt non-tail byte shape) — a torn write cannot produce this
    /// (see the crate doc's prefix argument). The log REFUSES: never a
    /// silent truncation of data away.
    Corrupt {
        /// Byte offset of the offending frame.
        offset: u64,
        /// What failed.
        reason: &'static str,
    },
    /// A TRUNCATED tail, refused by the strict open (`DeltaLog::
    /// open_strict`). The recovering open treats the same shape as
    /// last-good-frame recovery + a REPORTED truncation instead.
    TornTail {
        /// Byte offset where the good prefix ends (the tail's start).
        offset: u64,
    },
    /// The whole-journal wire (`journal_bytes`) didn't fully consume its
    /// input — trailing bytes after the declared frame count.
    JournalTrailing {
        /// Byte offset of the first trailing byte.
        offset: u64,
    },
}

impl fmt::Display for DeltaError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Io(e) => write!(f, "io: {e}"),
            Self::SchemaMismatch { reason } => write!(f, "schema mismatch: {reason}"),
            Self::Corrupt { offset, reason } => {
                write!(f, "journal frame at {offset}: corrupt ({reason})")
            }
            Self::TornTail { offset } => {
                write!(f, "journal torn tail at {offset} (strict open refuses)")
            }
            Self::JournalTrailing { offset } => {
                write!(f, "journal wire: trailing bytes at {offset}")
            }
        }
    }
}

impl std::error::Error for DeltaError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::Io(e) => Some(e),
            _ => None,
        }
    }
}

impl From<std::io::Error> for DeltaError {
    fn from(e: std::io::Error) -> Self {
        Self::Io(e)
    }
}

/// The frame decoder's failure classes (the port of `decDelta?`'s
/// `none` — but CLASSIFIED: the log's recovery discipline dispatches on
/// exactly this distinction).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DecodeFail {
    /// The input ran out mid-frame — the torn-write shape at the tail.
    Truncated,
    /// Complete input, invalid bytes (unknown tag, invalid atom,
    /// non-canonical varint, ill-typed payload).
    Corrupt(&'static str),
}

impl DecodeFail {
    /// The typed-error face (the corrupt-frame refusal names its offset).
    pub fn corrupt_error(self, offset: u64) -> DeltaError {
        match self {
            Self::Truncated => DeltaError::TornTail { offset },
            Self::Corrupt(reason) => DeltaError::Corrupt { offset, reason },
        }
    }
}

/// The REPORTED truncation a recovering open performed (never silent:
/// every recovery names where the cut happened and what survived).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Recovery {
    /// Byte offset where the torn tail began — the good prefix's length
    /// (the backend was truncated to exactly this).
    pub offset: u64,
    /// The number of frames the good prefix carries.
    pub frames: u64,
}
