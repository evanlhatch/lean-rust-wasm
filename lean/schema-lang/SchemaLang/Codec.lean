/-
# SchemaLang.Codec — kernel-checked round-trip laws (the linen pattern)

Linen's JSON module proves `decode ∘ encode = id` instead of asserting
it; flatland's `ExtMetadata` applies the same law to its metadata
shapes. This module starts OUR codec layer with the trivially-provable
subset (Bool, UInt8): the law shape is the deliverable — string
codecs (UTF-8) hit the core-lemma gap flatland documented and get
executable witnesses in Tests instead.

Encoding: one byte per value, little alphabet. Decoding rejects
everything else (wrong length, out of domain) — the failure cases are
exactly the Rust-side checks when the schema compiler emits codecs.
-/

import SchemaLang.Ty

namespace SchemaLang.Codec

/-! ## Bool -/

def encodeBool : Bool → List UInt8
  | .false => [0]
  | .true => [1]

def decodeBool : List UInt8 → Option Bool
  | [0] => some false
  | [1] => some true
  | _ => none

theorem decode_encodeBool (b : Bool) : decodeBool (encodeBool b) = some b := by
  cases b <;> rfl

/-! ## UInt8 -/

def encodeU8 : UInt8 → List UInt8
  | v => [v]

def decodeU8 : List UInt8 → Option UInt8
  | [v] => some v
  | _ => none

/-- Round-trip by exhaustive enumeration — 256 cases, closed domain
    (the flatland exhaustive-byte-sweep doctrine, as a theorem). -/
theorem decode_encodeU8 (v : UInt8) : decodeU8 (encodeU8 v) = some v := by
  cases v <;> rfl

end SchemaLang.Codec
