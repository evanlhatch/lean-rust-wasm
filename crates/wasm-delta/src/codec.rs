//! The wire codec — a byte-exact Rust mirror of `SchemaLang.Codec`
//! (lean/schema-lang/SchemaLang/Codec.lean): LEB128 varint base, bool/u8
//! atoms, the option/sum/list/bytes combinators, and the versioned
//! envelope. The Lean module carries the kernel-checked append-form
//! round-trip theorems; this port is pinned to it by golden vectors
//! generated FROM the Lean definitions (tests/codec_golden.rs).
//!
//! Deliberate strictness divergence (decode side only): Lean's
//! `decVarNat` is TOTAL (empty input decodes to `(0, [])`, a dangling
//! continuation byte pads with zero). The host decoder REJECTS empty and
//! truncated varints — the accept sets agree on every well-formed byte
//! string (the only lane the round-trip theorems quantify over), and the
//! strictness is what makes torn-tail detection in the log possible.

/// A decode failure. The log's recovery scan distinguishes TORN (the
/// input ended mid-item — the crash-recovery lane) from CORRUPT (bytes
/// present but invalid).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum DecFail {
    /// The input ended before the item was complete.
    Torn,
    /// The bytes are present but invalid (bad tag, overflow, bad
    /// codepoint, out-of-range value).
    Corrupt,
}

pub(crate) type Dec<T> = Result<(T, usize), DecFail>;

/// The varint's byte ceiling: 64 bits need at most ceil(64/7) = 10
/// digits. An 11th digit (or value overflow) is corrupt, never torn.
const VARNAT_MAX_BYTES: usize = 10;

/// `Codec.encVarNat`: LEB128, little-endian base-128 digits, high bit =
/// continuation. Self-delimiting.
pub(crate) fn enc_varnat(n: u64, out: &mut Vec<u8>) {
    if n < 128 {
        // n < 128: the truncation is exact.
        #[allow(clippy::cast_possible_truncation, reason = "n < 128")]
        out.push(n as u8);
    } else {
        // 128 + n % 128 < 256: the truncation is exact.
        #[allow(clippy::cast_possible_truncation, reason = "128 + n % 128 < 256")]
        out.push((128 + n % 128) as u8);
        enc_varnat(n / 128, out);
    }
}

/// Strict `Codec.decVarNat`: returns (value, bytes consumed). `Torn`
/// when the input ends before the terminating digit; `Corrupt` on
/// overflow past u64.
pub(crate) fn dec_varnat(bs: &[u8]) -> Dec<u64> {
    let mut acc: u64 = 0;
    let mut shift: u32 = 0;
    for (i, &b) in bs.iter().enumerate() {
        if i == VARNAT_MAX_BYTES {
            return Err(DecFail::Corrupt);
        }
        let digit = u64::from(b & 0x7f);
        let shifted = digit.checked_shl(shift).ok_or(DecFail::Corrupt)?;
        acc = acc.checked_add(shifted).ok_or(DecFail::Corrupt)?;
        if b < 128 {
            return Ok((acc, i + 1));
        }
        shift += 7;
    }
    Err(DecFail::Torn)
}

/// `Codec.encodeBool`: one byte, 0 = false, 1 = true.
pub(crate) fn enc_bool(b: bool, out: &mut Vec<u8>) {
    out.push(u8::from(b));
}

/// Strict `Codec.decBool?`: any byte other than 0/1 is corrupt.
pub(crate) fn dec_bool(bs: &[u8]) -> Dec<bool> {
    match bs.first() {
        None => Err(DecFail::Torn),
        Some(0) => Ok((false, 1)),
        Some(1) => Ok((true, 1)),
        Some(_) => Err(DecFail::Corrupt),
    }
}

/// `Codec.encBytes`: varint length prefix + raw bytes.
pub(crate) fn enc_bytes(payload: &[u8], out: &mut Vec<u8>) {
    enc_varnat(payload.len() as u64, out);
    out.extend_from_slice(payload);
}

/// Strict `Codec.decBytes?`: fewer than `n` bytes available is TORN
/// (Lean's `decBytes?` rejects with `none` — the same rejection,
/// classified).
pub(crate) fn dec_bytes(bs: &[u8]) -> Dec<&[u8]> {
    let (n, used) = dec_varnat(bs)?;
    let n = usize::try_from(n).map_err(|_| DecFail::Corrupt)?;
    let rest = &bs[used..];
    if rest.len() < n {
        return Err(DecFail::Torn);
    }
    Ok((&rest[..n], used + n))
}

/// The versioned envelope (`Codec.encEnvelope`): version varint,
/// fingerprint varint, length-prefixed payload.
pub(crate) fn enc_envelope(version: u64, fingerprint: u64, payload: &[u8], out: &mut Vec<u8>) {
    enc_varnat(version, out);
    enc_varnat(fingerprint, out);
    enc_bytes(payload, out);
}

/// A decoded envelope prefix: version, fingerprint, payload slice, and
/// total byte length of the whole envelope (so a log scan can advance).
pub(crate) struct EnvelopeRef<'a> {
    /// The envelope version field.
    pub(crate) version: u64,
    /// The schema fingerprint field.
    pub(crate) fingerprint: u64,
    /// The payload bytes.
    pub(crate) payload: &'a [u8],
    /// Total bytes consumed by the envelope (header + payload).
    pub(crate) len: usize,
}

/// Envelope scan: trailing bytes belong to the caller (the log's next
/// record); the total byte length rides in the result. Version and
/// fingerprint varints and the payload length classify truncation as
/// Torn; the payload-overrun check is `dec_bytes`'s.
pub(crate) fn dec_envelope_prefix(bs: &[u8]) -> Result<EnvelopeRef<'_>, DecFail> {
    let (version, u1) = dec_varnat(bs)?;
    let (fingerprint, u2) = dec_varnat(&bs[u1..])?;
    let (payload, u3) = dec_bytes(&bs[u1 + u2..])?;
    Ok(EnvelopeRef {
        version,
        fingerprint,
        payload,
        len: u1 + u2 + u3,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn varnat_boundaries() {
        let mut out = Vec::new();
        enc_varnat(0, &mut out);
        enc_varnat(127, &mut out);
        enc_varnat(128, &mut out);
        assert_eq!(out, [0x00, 0x7f, 0x80, 0x01]);
        assert_eq!(dec_varnat(&out), Ok((0, 1)));
        assert_eq!(dec_varnat(&out[1..]), Ok((127, 1)));
        assert_eq!(dec_varnat(&out[2..]), Ok((128, 2)));
    }

    #[test]
    fn varnat_strictness() {
        assert_eq!(dec_varnat(&[]), Err(DecFail::Torn));
        assert_eq!(dec_varnat(&[0x80]), Err(DecFail::Torn));
        // 11 continuation bytes: corrupt, not torn.
        assert_eq!(dec_varnat(&[0xff; 11]), Err(DecFail::Corrupt));
    }

    /// The Lean-oracle envelope golden: `encEnvelope 1 42 [9,9]`.
    #[test]
    fn envelope_golden() {
        let mut out = Vec::new();
        enc_envelope(1, 42, &[9, 9], &mut out);
        assert_eq!(out, [0x01, 0x2a, 0x02, 0x09, 0x09]);
    }

    #[test]
    fn envelope_roundtrip() {
        let mut out = Vec::new();
        enc_envelope(1, 42, &[9, 9], &mut out);
        let env = dec_envelope_prefix(&out);
        assert!(env.is_ok());
        let Ok(env) = env else { return };
        assert_eq!((env.version, env.fingerprint, env.payload, env.len), (1, 42, &[9, 9][..], out.len()));
    }
}
