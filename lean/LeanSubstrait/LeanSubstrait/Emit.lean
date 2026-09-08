/-
# LeanSubstrait.Emit

Emitters from the `Proto.Plan` wire model.

- `LeanSubstrait.Emit.Text`: the canonical substrait-explain text format
  (byte-for-byte compatible; the v0 wire).

(An earlier debug JSON emitter, `LeanSubstrait.Emit.Json`, was removed: it
was not buildable against the Lean 4.33 JSON module surface and sat outside
the v0 wire path, so it carried nonzero maintenance for zero wire value.)

`Emit.Text.emit : Proto.Plan → Except String String` is the primary public
function; it hard-fails on plans the text grammar cannot express (Write,
Extension* rels).
-/
import LeanSubstrait.Emit.Text
