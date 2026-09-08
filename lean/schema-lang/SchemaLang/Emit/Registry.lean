/-
# SchemaLang.Emit.Registry — the emitter registry (the buf plugin model)

buf's architecture: ONE parsed schema, MANY emitters, each a plugin
that consumes the descriptor and produces files. Here: the universe
(`List Item`, kernel-checked) is the descriptor; an `Emitter` is a
plugin with a name, a comment style, DECLARED output paths (the
one-writer audit surface), and a pure `run` from items to files.

Adding a language = one module defining an `Emitter` + one line in
`emitters`. No driver changes, no GenMain changes (the driver iterates
the registry). Outputs must be unique across the registry — the audit
test fails the build on a collision, and `forge gen --check` byte-ties
every declared path.
-/

import CodegenCore
import SchemaLang.Item
import SchemaLang.Emit.Wit
import SchemaLang.Emit.Rust

namespace SchemaLang.Emit

/-- The registry. Order = write order. -/
def emitters : List (CodegenCore.Emit.Emitter (List SchemaLang.Item)) :=
  [ witEmitter
  , rustEmitter
  ]

/-- Audit: no two emitters claim the same output path. -/
def pathsUnique : Bool :=
  (emitters.flatMap (·.outputs)).Nodup

end SchemaLang.Emit
