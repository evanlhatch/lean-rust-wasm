/-
# SchemaLang.GenMain — the artifact writer (one-writer-per-artifact)

Regenerates the committed artifacts from the demo spec: the WIT world
and the rich Rust domain module. Byte-tie CI: `forge gen --check`
re-runs this in memory and diffs — never edit the artifacts, regenerate.
-/
import SchemaLang

def witOut : System.FilePath := "../../wit/gateway.wit"
def rustOut : System.FilePath := "../../src/schema_generated.rs"

def main : IO Unit := do
  -- WIT world (comments are //, the header template is Lean/-- — rewrite)
  let hdr := (CodegenCore.Emit.header "schema-lang" "SchemaLang/Spec/Demo.lean")
    |>.replace "--" "//"
  IO.FS.createDirAll "../../wit"
  let wit := hdr ++ SchemaLang.Emit.Wit.worldOf "demo:gateway" "gateway" SchemaLang.Spec.demo
  IO.FS.writeFile witOut wit
  IO.println s!"wrote {witOut}"

  -- Rich Rust types (comments are // for .rs)
  let items := SchemaLang.Emit.Rust.schemaItems
    SchemaLang.Emit.Rust.defaultDerives SchemaLang.Spec.demo
  let hdr := (CodegenCore.Emit.header "schema-lang" "SchemaLang/Spec/Demo.lean")
    |>.replace "--" "//"
  let body := CodegenCore.Emit.Rust.renderModule items
  let rust := hdr ++ body
  IO.FS.writeFile rustOut rust
  IO.println s!"wrote {rustOut}"
