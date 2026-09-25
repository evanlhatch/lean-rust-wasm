/-
Gates.Impact — the impact-aware gating core (notes/v3/09-gates-ops.md §6)

The doctrine's dev loop: "The full run is the release gate. The dev loop
runs the affected set: the change set (the VCS diff) → affected modules
(the import-closure walk) → affected artifacts (the ledger's forward
query) → only their gates. The affected-set correctness is the
invariant: CONSERVATIVE, never under-reports."

The three faces, as data + pure functions over them:

1. THE MODULES — the changed `.lean` paths → their module names (the
   srcDir-strip convention, BOTH spellings registered — over-reporting
   only) → the REVERSE import closure (the module importing a changed
   module is affected). The closure rides ZSet.Graph's landed
   Reach discipline: the reverse graph is a Bool-weighted relation over
   table indices, the affected set is the bounded reachability sweep
   (`reachFrom`) from every changed index, and the conservatism theorem
   `closureIdxs_covers` proves the sweep covers every walk of at most
   `N` edges out of a changed module. The fuel-honest boundary: `N =
   |modules|` and the simple-path shortcut (any `Reach` path needs no
   more) is Graph.lean's named follow-up — the theorem states the walk
   face, never the unbounded one.
2. THE ARTIFACTS — the ledger's forward query over the AFFECTED
   modules' names (not just the changed ones: a moved module moves what
   demands it). The conservatism is Kit.Ledger's PROVED face
   (`forward_covers_row`, `forward_growthInvalidates`), composed here
   (`affectedArtifacts_covers` / `affectedArtifacts_growth`).
3. THE GATES — the coverage data: which registered gate rows each
   affected face runs (the env-replay gates over gated modules —
   Gates.Packages' table consumed, never a parallel copy; the byte-tie
   + audit gates over artifacts; docs-check over notes). The names are
   pinned against `Gates.gateNames` in the test battery (drift fails
   it).

THE CONSERVATIVE-HONESTY DISCIPLINE: the affected set never
under-reports, so every gap in the graph's knowledge WIDENS — the
verdict is `.full why` (the safe set: the whole release gate) whenever

- the import scan failed (a source file unreadable — the graph is
  incomplete, its closure proves nothing);
- a changed source is not a scanned module vertex (the convention
  cannot see its importers);
- a scanned import names a project namespace but no scanned module
  (the graph's naming gap — an importer may be invisible);
- the ledger is absent or refused (the artifact face is blind);
- a changed path has no handler's face and no ledger row.

Over-reporting is the honest face of conservatism; under-reporting is
the failure the widening exists to prevent. The untracked-everything
world of today (no committed ledger) means `just impacted` widens to
the full run — the DORMANT state rendered loudly, never a fabricated
narrow answer.

The IO face (`run`) reads the change set honestly and minimally: a
manual `--paths` argument, else `jj diff --name-only` (fallback `git`);
nothing else shells out. The gates run as child `lake exe gates <row>`
processes (Gates.lean's per-gate RSS discipline).

The five questions (notes/v3/01-core.md):
- root: Universe × Change crossing — the change set's three faces
  (modules, artifacts, gates) as closed data + total functions.
- carrier grade: the conservatism theorems — the module face's
  walk-covers law (`closureIdxs_covers`) and the artifact face's
  composed forward laws.
- spine reading: the artifact stage's impact face (09 §4's FORWARD
  direction) driven by §6's dev loop.
- ladder rung: rung 1-6 — total folds + the covers theorem (one
  `List.mem_flatMap` composition off Graph.lean's landed sweep).
- gate row: none — `impacted` is a DRIVER (the dev-loop mode over the
  registry's rows), not a row; its coverage data is pinned by the
  GatesTests battery.
-/
import Kit.Ledger
import Inspector.LedgerView
import ZSet.Graph
import Gates.Packages

namespace Gates.Impact

/-! ## The change set — the paths' classification -/

/-- The module-name faces of one source path: the FULL dotted path
    (`zset.ZSet.Graph`) AND the srcDir-stripped name (`ZSet.Graph`) —
    the tree's dominant layout strips the leading source directory;
    registering both spellings can only OVER-report. -/
def moduleNamesOfPath (path : String) : List String :=
  let stem := if path.endsWith ".lean" then (path.take (path.length - 5)).toString else path
  let comps := stem.splitOn "/"
  match comps with
  | [] => []
  | [_] => [stem]
  | _ => [String.intercalate "." comps, String.intercalate "." (comps.drop 1)]

/-- One changed path's handler face (ctors, never strings — 04 §6). -/
inductive PathKind where
  /-- A Lean source file — the module face (the import closure). -/
  | moduleFile
  /-- A note — docs-check's face. -/
  | notes
  /-- No handler's face: the ledger row decides (tracked = artifact,
      untracked = the SAFE widening). -/
  | unhandled
deriving BEq, DecidableEq, Repr, Inhabited

/-- The classification: `.lean` → the module face, `notes/…` → the
    notes face, anything else → the ledger's row decides. -/
def classifyPath (path : String) : PathKind :=
  if path.endsWith ".lean" then .moduleFile
  else if path.startsWith "notes/" then .notes
  else .unhandled

/-! ## The import graph — the scan's shape + the reverse closure -/

/-- The scanned import graph: one (module, direct imports) row per
    source file, plus the DANGLING imports — targets rooted at a
    scanned namespace that name no scanned module (the graph's naming
    gap; the widen face). -/
structure ImportScan where
  graph : List (String × List String)
  dangling : List String
deriving BEq, Repr, Inhabited

/-- The first dotted component (the namespace root). -/
def rootOf (mod : String) : String :=
  match mod.splitOn "." with
  | h :: _ => h
  | [] => ""

/-- The scanned module names (deduplicated, drop-empty). -/
def vertTable (scan : ImportScan) : List String :=
  Inspector.LedgerView.dedupStr ((scan.graph.map (·.1)).filter (· != ""))

/-- The table lookup (the hand-rolled index — no core-`idxOf?` gamble). -/
def indexOf? : List String → String → Option Nat
  | [], _ => none
  | x :: r, s => if x == s then some 0 else (indexOf? r s).map (· + 1)

/-- The table indexing (total — `""` never names a vertex). -/
def at? : List String → Nat → Option String
  | [], _ => none
  | x :: _, 0 => some x
  | _ :: r, i + 1 => at? r i

/-- THE REVERSE IMPORT GRAPH over the table's indices: an edge `d → m`
    when module `m` directly imports `d` — the direction the
    affected-closure walks (the module importing a changed module is
    affected). A `Graph Bool Nat`: membership weights (the canonical
    instance), `CanonKey Nat` vertices (ZSet.Graph's reading). -/
def revGraphOf (scan : ImportScan) : ZSet.Graph Bool Nat :=
  let verts := vertTable scan
  let edges : List (Nat × Nat) :=
    scan.graph.flatMap fun (m, imports) =>
      match indexOf? verts m with
      | none => []
      | some im =>
          imports.filterMap fun d =>
            match indexOf? verts d with
            | none => none
            | some id => some (id, im)
  ZSet.fromListW (edges.map fun e => (e, true))

/-! ## The closure's small laws (the module face's proof kit) -/

/-- Nat-list dedup, order-preserving. -/
def dedupNat : List Nat → List Nat
  | [] => []
  | x :: xs => if xs.contains x then dedupNat xs else x :: dedupNat xs

theorem mem_dedupNat (x : Nat) (l : List Nat) : x ∈ dedupNat l ↔ x ∈ l := by
  induction l with
  | nil => simp [dedupNat]
  | cons y r ih =>
    by_cases h : r.contains y = true
    · have hy : y ∈ r := List.contains_iff_mem.1 h
      simp only [dedupNat, if_pos h, ih]
      constructor
      · exact fun hx => List.mem_cons.2 (Or.inr hx)
      · intro hx
        rcases List.mem_cons.1 hx with rfl | hx
        · exact hy
        · exact hx
    · simp only [dedupNat, if_neg h, ih, List.mem_cons]

/-- The reverse-addAll law (Graph.lean's `mem_addAll` is the forward
    direction; the closure's construction needs the converse). -/
theorem mem_addAll_of {V : Type} [DecidableEq V] :
    ∀ (l acc : List V) (x : V), x ∈ l ∨ x ∈ acc → x ∈ ZSet.addAll l acc := by
  intro l
  induction l with
  | nil => intro acc x h; rcases h with h | h; cases h; exact h
  | cons v r ih =>
    intro acc x h
    rcases h with hmem | h
    · rcases List.mem_cons.1 hmem with rfl | hmem
      · exact ih (ZSet.vertIns _ acc) x
          (Or.inr (ZSet.vertIns_mem x _ acc |>.2 (Or.inl rfl)))
      · exact ih (ZSet.vertIns _ acc) x (Or.inl hmem)
    · exact ih (ZSet.vertIns v acc) x
        (Or.inr (ZSet.vertIns_mem x v acc |>.2 (Or.inr h)))

/-- Constructing one expansion step's membership: a frontier member's
    successor joins the expansion. -/
theorem mem_expand_of {g : ZSet.Graph Bool Nat} {frontier : List Nat} {m u : Nat}
    (hm : m ∈ frontier) (hu : u ∈ ZSet.succs g m) :
    u ∈ ZSet.expand g frontier :=
  mem_addAll_of _ _ u (Or.inl (List.mem_flatMap.2 ⟨m, hm, hu⟩))

/-- The reachability sweep is FUEL-MONOTONE (one step). -/
theorem reachFrom_mono (g : ZSet.Graph Bool Nat) (k v x : Nat)
    (h : x ∈ ZSet.reachFrom g k v) : x ∈ ZSet.reachFrom g (k + 1) v :=
  mem_addAll_of _ _ x (Or.inr h)

/-- The reachability sweep is FUEL-MONOTONE (to any larger fuel). -/
theorem reachFrom_mono_le (g : ZSet.Graph Bool Nat) :
    ∀ (n k v x : Nat), k ≤ n → x ∈ ZSet.reachFrom g k v → x ∈ ZSet.reachFrom g n v := by
  intro n
  induction n with
  | zero =>
    intro k v x hk h
    have h0 : k = 0 := Nat.le_zero.mp hk
    subst h0
    exact h
  | succ n ih =>
    intro k v x hk h
    rcases Nat.eq_or_lt_of_le hk with rfl | hlt
    · exact h
    · exact reachFrom_mono g n v x (ih k v x (Nat.le_of_lt_succ hlt) h)

/-- The appended singleton is a walk's last vertex. -/
theorem lastOf?_append_singleton : ∀ (p : List Nat) (u : Nat),
    ZSet.lastOf? (p ++ [u]) = some u
  | [], _ => rfl
  | [_], _ => rfl
  | _ :: b :: r, u => lastOf?_append_singleton (b :: r) u

/-- THE WALK LAW: a walk's endpoint is in the fuel-exact sweep (the
    composed shape `closureIdxs_covers` consumes). -/
theorem walkTo_reachFrom (g : ZSet.Graph Bool Nat) :
    ∀ (k : Nat) (p : List Nat) (c m : Nat),
      p ∈ ZSet.walksFrom g k c → ZSet.lastOf? p = some m →
      m ∈ ZSet.reachFrom g k c := by
  intro k
  induction k with
  | zero =>
    intro p c m hp hlast
    have hpc : p = [c] := by
      have hred : ZSet.walksFrom g 0 c = [[c]] := rfl
      rw [hred] at hp
      exact List.mem_singleton.1 hp
    subst hpc
    have hred : ZSet.lastOf? [c] = some c := rfl
    have hmc : m = c := Option.some.inj (hlast.symm.trans hred.symm)
    subst hmc
    exact List.mem_singleton.2 rfl
  | succ k ih =>
    intro p c m hp hlast
    simp only [ZSet.walksFrom, List.mem_flatMap] at hp
    obtain ⟨p', hp'mem, hp'ext⟩ := hp
    cases hlastp' : ZSet.lastOf? p' with
    | none => rw [hlastp'] at hp'ext; simp at hp'ext
    | some l =>
      rw [hlastp'] at hp'ext
      simp only at hp'ext
      obtain ⟨u, hu, hpEq⟩ := List.mem_map.1 hp'ext
      have hp'' : p = p' ++ [u] := hpEq.symm
      subst hp''
      rw [lastOf?_append_singleton] at hlast
      have hmu : u = m := Option.some.inj hlast
      subst hmu
      exact mem_expand_of (ih p' c l hp'mem hlastp') hu

/-! ## THE MODULE FACE's conservatism theorem -/

/-- The affected-index closure: every changed index plus everything
    reverse-reachable within the fuel `N` (the caller pins `N =
    |modules|` — the simple-path bound is Graph.lean's named
    follow-up, so the fuel is a premise, never a verdict). -/
def closureIdxs (rev : ZSet.Graph Bool Nat) (N : Nat) (changed : List Nat) : List Nat :=
  dedupNat (changed.flatMap (ZSet.reachFrom rev N))

/-- THE CONSERVATISM THEOREM (the module face, the walk reading): a
    module at the end of a walk of at most `N` edges OUT of a changed
    module IS in the affected closure — the affected set never
    under-reports the walk-reachable modules. The unbounded `Reach`
    face composes with Graph.lean's named fuel follow-up; the fuel is
    pinned at the module count by the caller (over-provisioned for
    simple paths, never a verdict of completeness). -/
theorem closureIdxs_covers (rev : ZSet.Graph Bool Nat) (N : Nat) (changed : List Nat)
    (c k m : Nat) (p : List Nat) (hc : c ∈ changed)
    (hp : p ∈ ZSet.walksFrom rev k c) (hlast : ZSet.lastOf? p = some m)
    (hfuel : k ≤ N) :
    m ∈ closureIdxs rev N changed := by
  have h1 : m ∈ ZSet.reachFrom rev k c := walkTo_reachFrom rev k p c m hp hlast
  have h2 : m ∈ ZSet.reachFrom rev N c := reachFrom_mono_le rev N k c m hfuel h1
  exact (mem_dedupNat m _).2 (List.mem_flatMap.2 ⟨c, hc, h2⟩)

/-- The one-step importer closure (the doctrine's reading: the module
    importing an affected module is affected) — at the next fuel level;
    the caller's fixed fuel over-provisions, `reachFrom_mono_le` lifts. -/
theorem closureIdxs_importer (rev : ZSet.Graph Bool Nat) (N : Nat) (changed : List Nat)
    (c m u : Nat) (hc : c ∈ changed) (hm : m ∈ ZSet.reachFrom rev N c)
    (hu : u ∈ ZSet.succs rev m) :
    u ∈ closureIdxs rev (N + 1) changed :=
  (mem_dedupNat u _).2 (List.mem_flatMap.2 ⟨c, hc, mem_expand_of hm hu⟩)

/-! ## THE ARTIFACT FACE — the ledger's forward query, composed -/

/-- The affected ARTIFACTS: the ledger's forward query over the changed
    spec names, with the changed collection set (the caller passes the
    changed names as BOTH — a changed name is its row or its
    collection's contents, Inspector.LedgerView's forward-table face). -/
def affectedArtifacts (ledger : List Kit.Ledger.LedgerRow)
    (names : List Lean.Name) (cols : List Lean.Name) : List Kit.Ledger.LedgerRow :=
  names.flatMap fun n => Kit.Ledger.forward n cols ledger

/-- THE COMPOSED CONSERVATISM (the rows face): an artifact whose demand
    read a changed spec name IS in the affected set —
    Kit.Ledger.forward_covers_row, lifted over the name fold. -/
theorem affectedArtifacts_covers (ledger : List Kit.Ledger.LedgerRow)
    (names cols : List Lean.Name) (a : Kit.Ledger.LedgerRow) (ha : a ∈ ledger)
    (n : Lean.Name) (hn : n ∈ names) (hr : n ∈ a.demand.rows) :
    a ∈ affectedArtifacts ledger names cols :=
  List.mem_flatMap.2 ⟨n, hn, Kit.Ledger.forward_covers_row n cols ledger a ha hr⟩

/-- THE COMPOSED CONSERVATISM (the collection-growth face): an artifact
    that merely ENUMERATED a changed collection IS in the affected set —
    Kit.Ledger.forward_growthInvalidates, lifted over the name fold. -/
theorem affectedArtifacts_growth (ledger : List Kit.Ledger.LedgerRow)
    (names cols : List Lean.Name) (a : Kit.Ledger.LedgerRow) (ha : a ∈ ledger)
    (c : Lean.Name) (hc : c ∈ a.demand.collections) (hcs : c ∈ cols)
    (n : Lean.Name) (hn : n ∈ names) :
    a ∈ affectedArtifacts ledger names cols :=
  List.mem_flatMap.2 ⟨n, hn, Kit.Ledger.forward_growthInvalidates n c cols ledger a ha hc hcs⟩

/-! ## THE GATE FACE — the coverage data (pinned against the registry) -/

/-- The env-replay gates over gated modules (the axiom sweep, the
    native-policy ratchet, the lean4lean replay — each replays the
    gated packages' environments). -/
def moduleGates : List String := ["axioms", "native-policy", "kernel-check"]

/-- The byte-tie + audit gates over artifacts (the committed bytes'
    faces). -/
def artifactGates : List String :=
  ["gen-check", "snapshot-check", "audit", "artifact-headers", "ownership"]

/-- The notes gate. -/
def notesGates : List String := ["docs-check"]

/-- The gated roots' names (Gates.Packages' table consumed — never a
    parallel copy). -/
def gatedRoots : List String :=
  Gates.gatedPackages.toList.flatMap fun p => p.roots.toList.map (·.toString)

/-- A module under a gated root (prefix match: the root itself or a
    dotted descendant). -/
def moduleIsGated (mod : String) : Bool :=
  gatedRoots.any fun r => mod == r || mod.startsWith (r ++ ".")

/-! ## THE VERDICT -/

/-- The verdict (ctors, never strings — 04 §6): the SAFE full run with
    its reason, or the affected sets. -/
inductive Verdict where
  /-- The full release gate — the safe set (an unknown zone widens). -/
  | full (why : String)
  /-- The affected sets: modules, artifacts, gates. -/
  | affected (mods : List String) (artifacts : List String) (gates : List String)
deriving BEq, Repr, Inhabited

/-- Render one verdict (the human surface; the ctors are the evidence). -/
def Verdict.render : Verdict → String
  | .full why =>
      "impacted: FULL RUN — " ++ why ++
      "\n  (the affected set never under-reports: an unknown zone widens to the safe set)"
  | .affected mods arts gates =>
      s!"impacted: {mods.length} affected module(s), {arts.length} artifact(s), \
{gates.length} gate(s)" ++
      (if mods.isEmpty then "" else "\n  modules: " ++ String.intercalate ", " mods) ++
      (if arts.isEmpty then "" else "\n  artifacts: " ++ String.intercalate ", " arts) ++
      (if gates.isEmpty then "" else "\n  gates: " ++ String.intercalate ", " gates)

/-- THE IMPACT ANALYSIS (the pure core; the IO faces feed it):
    `scan` = the import scan (`none` = the scan failed), `ledger` =
    the parsed ledger (`none` = absent or refused), `changed` = the
    change set. Every gap widens to `.full` — see the module header's
    discipline list. -/
def analyze (scan : Option ImportScan)
    (ledger : Option (List Kit.Ledger.LedgerRow)) (changed : List String) : Verdict :=
  if changed.isEmpty then
    -- the honest vacuity: an empty change set moves nothing
    .affected [] [] []
  else match scan with
  | none => .full "the import scan failed — a source file was unreadable, \
the graph is incomplete"
  | some sc =>
    match ledger with
    | none => .full "the artifact ledger is unknown (absent or refused) — \
the artifact face cannot be selected safely"
    | some rows =>
      let verts := vertTable sc
      let modNames :=
        Inspector.LedgerView.dedupStr
          ((changed.filter (fun p => classifyPath p == .moduleFile)).flatMap
            moduleNamesOfPath)
      let others := changed.filter fun p => !p.endsWith ".lean"
      let notesChanged := others.filter (·.startsWith "notes/")
      let unhandled := others.filter fun p =>
        !p.startsWith "notes/" && !(rows.any fun a => a.path == p)
      if modNames.any (fun m => !(verts.contains m)) then
        .full "a changed source is not a scanned module vertex — the import \
graph cannot see its importers"
      else if !unhandled.isEmpty then
        .full s!"changed path(s) outside the graph's knowledge: \
{String.intercalate ", " unhandled} — no ledger row, no handler face"
      else
        -- the dangling face: import targets rooted at a scanned
        -- namespace but naming no scanned module
        let roots := Inspector.LedgerView.dedupStr (verts.map rootOf)
        let danglingProj := sc.dangling.filter fun d => roots.contains (rootOf d)
        if !danglingProj.isEmpty then
          .full s!"unresolved project import(s): {String.intercalate ", " danglingProj} — \
the import graph has a naming gap"
        else
          -- the module closure over the table's indices
          let rev := revGraphOf sc
          let chIdx := modNames.filterMap (indexOf? verts)
          let affIdx := closureIdxs rev verts.length chIdx
          let affMods := Inspector.LedgerView.dedupStr (affIdx.filterMap (at? verts))
          -- the artifact face: forward over the AFFECTED names
          let affNames := affMods.map (fun m => Kit.Ledger.namesOf m)
          let fwd := affectedArtifacts rows affNames affNames
          let changedArts := others.filter fun p => rows.any fun a => a.path == p
          let artPaths := Inspector.LedgerView.dedupStr (changedArts ++ fwd.map (·.path))
          -- the gate face: the coverage data over the affected faces
          let gates :=
            (if affMods.any moduleIsGated then moduleGates else []) ++
            (if !artPaths.isEmpty then artifactGates else []) ++
            (if !notesChanged.isEmpty then notesGates else [])
          .affected affMods artPaths (Inspector.LedgerView.dedupStr gates)

/-! ## The IO faces (the scan, the change set, the driver) -/

/-- Run an IO action, catching ANY failure as `none` (the loud widen
    face — a read failure is a graph gap, never a crash). -/
def tryCatch (a : IO α) : IO (Option α) := do
  try
    return some (← a)
  catch _ =>
    return none

/-- The skipped top-level names: hidden dirs, the read-only pre-v3 tree
    (`legacy/` is not part of the build), foreign build dirs. -/
def skipDir (name : String) : Bool :=
  name.startsWith "." || name == "legacy" || name == "node_modules"

/-- The tree's `.lean` sources, root-relative, sorted. ANY read failure
    at the top level → `none` (the caller widens). -/
def leanSources : IO (Option (List String)) := do
  let top ← tryCatch (("." : System.FilePath).readDir)
  match top with
  | none => return none
  | some entries => do
    let mut files : List String := []
    for e in entries do
      let p := e.path.toString
      unless skipDir p do
        if ← e.path.isDir then
          let all ← Inspector.LedgerView.walk p
          files := files ++ all.filter (·.endsWith ".lean")
    return some ((files.toArray.qsort (fun a b => a <= b)).toList)

/-- One import line's module name (`import Foo.Bar`, the qualifiers
    stripped); `none` = not an import. A malformed remainder (an empty
    target) is reported as the empty name — the scan's dangling face. -/
def importLine? (line : String) : Option String :=
  let toks := (line.trimAscii.toString.splitOn " ").filter (· != "")
  let toks := stripQualifiers toks
  match toks with
  | "import" :: name :: _ => some name
  | _ => none
where
  /-- Strip the import-statement qualifiers. -/
  stripQualifiers : List String → List String
    | [] => []
    | x :: r =>
        if x == "public" || x == "private" || x == "protected"
            || x == "meta" || x == "unsafe" || x == "scoped" then
          stripQualifiers r
        else
          x :: r

/-- THE IMPORT SCAN: every source file's direct imports, as names.
    ANY read failure makes the whole scan `none` — a graph gap must
    never silently shrink the affected set. -/
def scanImports (files : List String) : IO (Option ImportScan) := do
  let mut graph : List (String × List String) := []
  for f in files do
    let txtOpt ← tryCatch (IO.FS.readFile f)
    match txtOpt with
    | none => return none
    | some s =>
      let imports := (s.splitOn "\n").filterMap importLine?
      graph := (moduleNamesOfPath f).map (fun m => (m, imports)) ++ graph
  let verts := Inspector.LedgerView.dedupStr (graph.map (·.1))
  let roots := Inspector.LedgerView.dedupStr (verts.map rootOf)
  let dangling :=
    Inspector.LedgerView.dedupStr
      ((graph.flatMap (·.2)).filter fun d =>
        !(verts.contains d) && roots.contains (rootOf d))
  return some { graph := graph.reverse, dangling }

/-- The change set from the VCS: `jj diff --name-only`, fallback
    `git diff --name-only`; `none` = no VCS answer (the caller widens). -/
def vcsChanged : IO (Option (List String)) := do
  let attempts : List (List String) :=
    [["jj", "diff", "--name-only"], ["git", "diff", "--name-only"]]
  for args in attempts do
    match args with
    | cmd :: rest =>
      let r ← tryCatch (IO.Process.output { cmd := cmd, args := rest.toArray })
      match r with
      | some out =>
        if out.exitCode == 0 then
          return some ((out.stdout.splitOn "\n").map (·.trimAscii.toString)
            |>.filter (· != ""))
      | none => pure ()
    | [] => pure ()
  return none

/-- One affected gate as a child `lake exe gates <row>` process (the
    per-gate RSS discipline — Gates.lean's driver shape). -/
def runGate (name : String) : IO UInt32 := do
  IO.println s!"══ gates impacted: {name} ══"
  let child ← IO.Process.spawn
    { cmd := "lake", args := #["exe", "gates", name]
    , stdout := .inherit, stderr := .inherit }
  let code ← child.wait
  if code != 0 then
    IO.eprintln s!"gates impacted: {name} FAILED (exit {code})"
  return code

/-- The full run, delegated to the registry's own driver (ONE name —
    the gate set is never duplicated here). -/
def runFull : IO UInt32 := do
  IO.println "══ gates impacted: the full run (the release gate) ══"
  let child ← IO.Process.spawn
    { cmd := "lake", args := #["exe", "gates", "all"]
    , stdout := .inherit, stderr := .inherit }
  child.wait

/-- `gates impacted` — 09 §6's dev loop: the change set → affected
    modules → affected artifacts → ONLY their gates. Any gap in the
    graph's knowledge widens to the full run (the conservatism
    invariant: never under-reports). -/
def run (printOnly : Bool) (paths : Option (List String)) : IO UInt32 := do
  let changedOpt ←
    match paths with
    | some ps => pure (some ps)
    | none => vcsChanged
  let changed := changedOpt.getD []
  let filesOpt ← leanSources
  let scanOpt ←
    match filesOpt with
    | none => pure none
    | some files => scanImports files
  let st ← Inspector.LedgerView.readLedger
  let ledgerOpt : Option (List Kit.Ledger.LedgerRow) :=
    match st with
    | .loaded rows => some rows
    | _ => none
  let v := analyze scanOpt ledgerOpt changed
  IO.println (v.render)
  match v with
  | .full _ =>
      if printOnly then return 0 else runFull
  | .affected _ _ gates =>
      if gates.isEmpty then
        IO.println "impacted: nothing affected — clean"
        return 0
      if printOnly then return 0
      for g in gates do
        let code ← runGate g
        if code != 0 then return code
      IO.println "impacted: affected gates clean"
      return 0

end Gates.Impact
