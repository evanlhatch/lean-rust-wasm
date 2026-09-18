/-
# SchemaLang.Snapshot — the committed universe snapshot (the `breaking` baseline)

The buf-breaking storage layer: a STABLE TEXT encoding of a universe
(`List Item`), committed at `goldens/universe.snapshot`, that the
`schema-breaking` exe diffs the current registry against
(`SchemaLang.Diff.diff`). Line-based, one line per item member:

    record <name>
    field <name> <ty>
    variant <name>
    case <name> [<ty>]
    func <name>
    param <name> <ty>
    ret <ty>
    sem <nullsem> <determinism>   -- OPTIONAL, last; written only when
                                  -- non-default (6.5.1). Absent = the
                                  -- `FuncSem` defaults, so pre-6.5.1
                                  -- baselines parse unchanged.
    resource <name>

`<ty>` is `Ty.toSnapshot`'s paren encoding (`option(u64)`,
`result(string,ty(User))`, …); `<nullsem>` is `strict | propagate |
custom`, `<determinism>` is `pure | stable | volatile`. The format
carries NO spaces inside a `<ty>` and forbids whitespace/separators in
names — the write side VALIDATES (`namesEncodable`) and the exe
refuses to write otherwise, so parse failures are always corruption,
never writer drift.

Deliberately omitted: ordering normalization (the snapshot preserves
registry order; `diff` is order-insensitive over names), item-kind
migrations (a kind change parses as a different shape → `changed`,
which is the honest breaking verdict).

Ownership: the ONLY encoder/decoder of the snapshot format. The
`schema-breaking` exe and the Tests negative controls consume this;
nothing else writes `goldens/universe.snapshot`.
-/

module

public import SchemaLang.Diff

@[expose] public section

namespace SchemaLang

/-- The key's snapshot spelling, DIRECT (the `toTy` indirection breaks
    `Ty.toSnapshot`'s structural recursion). Agrees with the injected
    spelling by `toSnapshot_toTy`. -/
def KeyTy.toSnapshot : KeyTy → String
  | .bool => "bool"
  | .u8 => "u8" | .u16 => "u16" | .u32 => "u32" | .u64 => "u64"
  | .i8 => "i8" | .i16 => "i16" | .i32 => "i32" | .i64 => "i64"
  | .string => "string"

/-- Paren encoding of a type: scalars as atoms, constructors as
    `head(arg,…)`, named refs as `ty(<name>)`. No spaces. -/
def Ty.toSnapshot : Ty → String
  | .bool => "bool"
  | .u8 => "u8" | .u16 => "u16" | .u32 => "u32" | .u64 => "u64"
  | .i8 => "i8" | .i16 => "i16" | .i32 => "i32" | .i64 => "i64"
  | .f32 => "f32" | .f64 => "f64"
  | .string => "string" | .bytes => "bytes"
  | .option a => s!"option({a.toSnapshot})"
  | .result ok err => s!"result({ok.toSnapshot},{err.toSnapshot})"
  | .list a => s!"list({a.toSnapshot})"
  -- the key rides in its scalar spelling (`KeyTy.toSnapshot`); the
  -- parse side GATES it through `Ty.toKeyTy?` (`map(f32,u64)` is a
  -- parse error — the type-level negative control)
  | .map k v => s!"map({k.toSnapshot},{v.toSnapshot})"
  | .set k => s!"set({k.toSnapshot})"
  | .future a => s!"future({a.toSnapshot})"
  | .stream a => s!"stream({a.toSnapshot})"
  | .tensor dims a =>
      -- the dims ride as ';'-separated nat atoms BEFORE the element:
      -- `tensor(2;3;u64)` (a 2×3 u64 tensor); zero dims = `tensor(;elem)`
      s!"tensor({String.intercalate "" (dims.map (fun d => s!"{d};"))}{a.toSnapshot})"
  | .ty n => s!"ty({n})"

/-- The two key spellings agree (the direct one is the structural
    recursion's; the injected one is what the parser's key gate
    consumes). -/
theorem KeyTy.toSnapshot_toTy (k : KeyTy) :
    Ty.toSnapshot k.toTy = k.toSnapshot := by
  cases k <;> rfl

-- the `<nullsem>`/`<determinism>` tokens are `NullSem.toToken` /
-- `Determinism.toToken` (Item.lean — the one spelling, shared with the
-- `@[schema_fn]` attr args); the parse side (`ofToken?`) is loud on
-- anything outside the closed sets.

namespace Snapshot

/-! ## Name validation (the write-side gate) -/

/-- Characters the line format round-trips: alphanumeric plus the
    identifier punctuation the registry actually produces (`-` kebab,
    `_` silenced binders, `.` qualified). Anything else (whitespace,
    `()`,`,`) collides with the format's separators. -/
def nameOk (s : String) : Bool :=
  !s.isEmpty && s.all fun c => c.isAlphanum || c == '-' || c == '_' || c == '.'

/-! ## The Ty parser -/

/-- Fuel-bounded total parser (fuel = input length + 1 at the top;
    each recursive call consumes at least one character, so the zero
    arm is unreachable from `parseTyText`). Returns the type and the
    unconsumed rest. Errors are LOUD — a snapshot that doesn't parse is
    a gate failure, not a skip. -/
def parseTy : Nat → List Char → Except String (Ty × List Char)
  | 0, _ => .error "snapshot: parse fuel exhausted (malformed nesting)"
  | fuel + 1, cs =>
      let (kw, rest) := cs.span Char.isAlphanum
      let arg1 (k : Ty → Ty) : Except String (Ty × List Char) :=
        match rest with
        | '(' :: r => do
            let (t, r) ← parseTy fuel r
            match r with
            | ')' :: r => .ok (k t, r)
            | _ => .error s!"snapshot: expected ')' after `{String.ofList kw}(`"
        | _ => .error s!"snapshot: expected '(' after `{String.ofList kw}`"
      match String.ofList kw with
      | "bool" => .ok (.bool, rest)
      | "u8" => .ok (.u8, rest) | "u16" => .ok (.u16, rest)
      | "u32" => .ok (.u32, rest) | "u64" => .ok (.u64, rest)
      | "i8" => .ok (.i8, rest) | "i16" => .ok (.i16, rest)
      | "i32" => .ok (.i32, rest) | "i64" => .ok (.i64, rest)
      | "f32" => .ok (.f32, rest) | "f64" => .ok (.f64, rest)
      | "string" => .ok (.string, rest) | "bytes" => .ok (.bytes, rest)
      | "option" => arg1 .option
      | "list" => arg1 .list
      | "set" =>
          -- the key GATE: the element type must parse, then BE a
          -- scalar key (`Ty.toKeyTy?` — the type-level discipline,
          -- enforced at the format boundary)
          match rest with
          | '(' :: r => do
              let (t, r) ← parseTy fuel r
              match Ty.toKeyTy? t with
              | none => .error s!"snapshot: set element `{t.toSnapshot}` is not a scalar key type"
              | some k =>
                  match r with
                  | ')' :: r => .ok (.set k, r)
                  | _ => .error "snapshot: expected ')' after `set(…`"
          | _ => .error "snapshot: expected '(' after `set`"
      | "map" =>
          match rest with
          | '(' :: r => do
              let (kt, r) ← parseTy fuel r
              match Ty.toKeyTy? kt with
              | none => .error s!"snapshot: map key `{kt.toSnapshot}` is not a scalar key type"
              | some k =>
                  match r with
                  | ',' :: r => do
                      let (v, r) ← parseTy fuel r
                      match r with
                      | ')' :: r => .ok (.map k v, r)
                      | _ => .error "snapshot: expected ')' after map's value type"
                  | _ => .error "snapshot: expected ',' between map's key and value types"
          | _ => .error "snapshot: expected '(' after `map`"
      | "future" => arg1 .future
      | "stream" => arg1 .stream
      | "result" =>
          match rest with
          | '(' :: r => do
              let (ok, r) ← parseTy fuel r
              match r with
              | ',' :: r => do
                  let (err, r) ← parseTy fuel r
                  match r with
                  | ')' :: r => .ok (.result ok err, r)
                  | _ => .error "snapshot: expected ')' after result's err type"
              | _ => .error "snapshot: expected ',' between result's types"
          | _ => .error "snapshot: expected '(' after `result`"
      | "ty" =>
          match rest with
          | '(' :: r =>
              let (nm, r) := r.span (· != ')')
              match r with
              | ')' :: r =>
                  -- the EMPTY-REF gate: the writer never emits `ty()`
                  -- (`namesEncodable` forbids empty names), so accepting
                  -- one would parse a corruption hole as a ref
                  if nm.isEmpty then .error "snapshot: empty ty ref"
                  else .ok (.ty (String.ofList nm), r)
              | _ => .error "snapshot: expected ')' after ty ref"
          | _ => .error "snapshot: expected '(' after `ty`"
      | "tensor" =>
          -- `tensor(` (dim ';')* elem ')` — the nat atoms first (each
          -- consumed WITH its ';'), then the element type, then ')'.
          -- Zero dims = the empty prefix: `tensor(;elem)`.
          -- parseDims is fuel-bounded (each recursive call consumed a
          -- digit-run + ';' — ≥ 2 chars — so fuel = input length is
          -- strictly sufficient, the parseTy fuel discipline).
          match rest with
          | '(' :: r =>
              let rec parseDims (f : Nat) (cs : List Char) (acc : List Nat) :
                  Except String (List Nat × List Char) :=
                  match f with
                  | 0 => .error "snapshot: parse fuel exhausted (tensor dims)"
                  | f + 1 =>
                      let (ds, r) := cs.span Char.isDigit
                      if ds.isEmpty then .ok (acc.reverse, r)
                      else match r with
                        | ';' :: r => parseDims f r ((String.ofList ds).toNat! :: acc)
                        | _ => .error "snapshot: expected ';' after tensor dim"
              match parseDims (r.length + 1) r [] with
              | .error e => .error e
              | .ok (dims, r) =>
                  match parseTy fuel r with
                  | .error e => .error e
                  | .ok (elem, r) =>
                      match r with
                      | ')' :: r => .ok (.tensor dims elem, r)
                      | _ => .error "snapshot: expected ')' after tensor"
          | _ => .error "snapshot: expected '(' after `tensor`"
      | other => .error s!"snapshot: unknown type token `{other}`"

/-- Parse a whole type token; trailing garbage is an error. -/
def parseTyText (s : String) : Except String Ty :=
  match parseTy (s.length + 1) s.toList with
  | .ok (t, []) => .ok t
  | .ok (_, rest) => .error s!"snapshot: trailing garbage `{String.ofList rest}`"
  | .error e => .error e

/-! ## The item codec -/

/-- One item → its snapshot lines (header line first, members after). -/
def itemLines : Item → List String
  | .record n fields =>
      s!"record {n}" :: fields.map fun f => s!"field {f.name} {f.ty.toSnapshot}"
  | .variant n cases =>
      s!"variant {n}" :: cases.map fun (c, payload) =>
        match payload with
        | some t => s!"case {c} {t.toSnapshot}"
        | none => s!"case {c}"
  | .func s =>
      s!"func {s.name}"
        :: s.params.map (fun (n, t) => s!"param {n} {t.toSnapshot}")
          ++ [s!"ret {s.ret.toSnapshot}"]
          -- the sem line is written ONLY when non-default: pre-6.5.1
          -- baselines (and all-default universes) render byte-identically
          ++ if s.sem == ({} : FuncSem) then []
             else [s!"sem {s.sem.nullSem.toToken} {s.sem.determinism.toToken}"
               ++ (if s.sem.delivery == (.stream : Delivery) then " stream" else "")]
  | .resource n => [s!"resource {n}"]

/-- The whole universe as snapshot text (registry order, trailing
    newline on every line). -/
def render (items : List Item) : String :=
  String.join ((items.flatMap itemLines).map (· ++ "\n"))

/-- The partially-accumulated open item during a parse fold
    (member lists reversed until `close`). -/
inductive Open where
  | record (n : String) (fields : List Field)
  | variant (n : String) (cases : List VariantCase)
  | func (n : String) (params : List (String × Ty)) (ret : Option Ty)
    (sem : Option FuncSem)
  | resource (n : String)

/-- Close the open item (member order restored). A func without `ret`
    is malformed — the writer always emits one. -/
def Open.close : Open → Except String Item
  | .record n fs => .ok (.record n fs.reverse)
  | .variant n cs => .ok (.variant n cs.reverse)
  | .func n ps (some r) sem =>
      -- `body` is registry metadata, NOT wire data: the snapshot round-trip
      -- reconstructs it anonymous (the declaring constant is re-attached by
      -- the attribute on the Lean side)
      .ok (.func ⟨n, ps.reverse, r, sem.getD {}, .anonymous⟩)
  | .func n _ none _ => .error s!"snapshot: func `{n}` has no `ret` line"
  | .resource n => .ok (.resource n)

/-- The fold state: closed items (reversed) plus the currently open
    item, if any. -/
abbrev State := Except String (List Item × Option Open)

/-- One line onto the fold state; the first error sticks. -/
def parseLine (st : State) (line : String) : State := do
  let (done, cur?) ← st
  -- close the open item (if any) and start `o`
  let restart (o : Open) : State := do
    match cur? with
    | some cur => pure ((← cur.close) :: done, some o)
    | none => pure (done, some o)
  match line.splitOn " " with
  | ["record", n] => restart (.record n [])
  | ["variant", n] => restart (.variant n [])
  | ["func", n] => restart (.func n [] none none)
  | ["resource", n] => restart (.resource n)
  | ["field", n, tyText] =>
      match cur? with
      | some (.record rn fs) => do
          let t ← parseTyText tyText
          pure (done, some (.record rn (⟨n, t⟩ :: fs)))
      | _ => throw s!"snapshot: `field` outside a record (line `{line}`)"
  | ["case", n] =>
      match cur? with
      | some (.variant vn cs) => pure (done, some (.variant vn ((n, none) :: cs)))
      | _ => throw s!"snapshot: `case` outside a variant (line `{line}`)"
  | ["case", n, tyText] =>
      match cur? with
      | some (.variant vn cs) => do
          let t ← parseTyText tyText
          pure (done, some (.variant vn ((n, some t) :: cs)))
      | _ => throw s!"snapshot: `case` outside a variant (line `{line}`)"
  | ["param", n, tyText] =>
      match cur? with
      | some (.func fn ps none sem?) => do
          let t ← parseTyText tyText
          pure (done, some (.func fn ((n, t) :: ps) none sem?))
      | some (.func _ _ (some _) _) =>
          throw s!"snapshot: `param` after `ret` (line `{line}`)"
      | _ => throw s!"snapshot: `param` outside a func (line `{line}`)"
  | ["ret", tyText] =>
      match cur? with
      | some (.func fn ps none sem?) => do
          let t ← parseTyText tyText
          pure (done, some (.func fn ps (some t) sem?))
      | some (.func _ _ (some _) _) =>
          throw s!"snapshot: duplicate `ret` (line `{line}`)"
      | _ => throw s!"snapshot: `ret` outside a func (line `{line}`)"
  | ["sem", nsTok, dsTok] | ["sem", nsTok, dsTok, "stream"] =>
      match cur? with
      | some (.func fn ps (some r) none) => do
          let ns ← match NullSem.ofToken? nsTok with
            | some v => pure v
            | none => throw s!"snapshot: unknown nullSem token `{nsTok}` — valid: strict, propagate, custom"
          let ds ← match Determinism.ofToken? dsTok with
            | some v => pure v
            | none => throw s!"snapshot: unknown determinism token `{dsTok}` — valid: pure, stable, volatile"
          -- the OPTIONAL 4th token: the delivery (`stream`; its absence =
          -- `once` — the default, keeping old baselines parsable)
          let del : Delivery := if (line.splitOn " ").getLast! == "stream" then .stream else .once
          pure (done, some (.func fn ps (some r) (some ⟨ns, ds, del⟩)))
      | some (.func _ _ (some _) (some _)) =>
          throw s!"snapshot: duplicate `sem` (line `{line}`)"
      | some (.func _ _ none _) =>
          throw s!"snapshot: `sem` before `ret` (line `{line}`)"
      | _ => throw s!"snapshot: `sem` outside a func (line `{line}`)"
  | _ => throw s!"snapshot: unrecognized line `{line}`"

/-- Parse snapshot text back to a universe. The empty snapshot is the
    empty universe (a brand-new project has no baseline).

    LF-ONLY: the writer emits `\n` line endings and NEVER `\r` (render
    below joins on `"\n"` alone), so a `\r` is corruption: it sticks to
    the last token of its line and fails loud (unrecognized line or
    trailing garbage). The Rust twin parses the same law — both parsers
    REJECT CRLF (the snapshot-codec differential's pin). -/
def parse (text : String) : Except String (List Item) := do
  let lines := text.splitOn "\n" |>.filter (!·.isEmpty)
  let (done, cur?) ← lines.foldl parseLine (.ok ([], none))
  match cur? with
  | some cur => pure ((← cur.close) :: done).reverse
  | none => pure done.reverse

/-! ## Write-side validation -/

/-- Every name the snapshot must encode: item names, member names
    (fields/cases/params), and `.ty` reference names (they land inside
    `ty(…)`). -/
def allNames (items : List Item) : List String :=
  items.flatMap fun it =>
    it.name :: Item.tyRefs it ++
      match it with
      | .record _ fs => fs.map (·.name)
      | .variant _ cs => cs.map (·.1)
      | .func s => s.params.map (·.1)
      | .resource _ => []

/-- The write-side gate: every encodable name survives the format.
    `schema-breaking --update` REFUSES to write when this is false. -/
def namesEncodable (items : List Item) : Bool :=
  (allNames items).all nameOk

end Snapshot

end SchemaLang
