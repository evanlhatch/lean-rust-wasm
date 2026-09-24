/-
# TextKit.Grammar.Parse — the derived total parser + printer + run

The design of record: `notes/design-grammar-layer.md` §3 (the folds)
+ §1.3 (print totality) + §4 (the error discipline). ONE `Grammar`
value drives both directions.

THE SCHEME (the reformulation's payoff): with the body of a `fix`
living in the open family `GrammarE R R` (Grammar.lean's header), the
parser needs NO environment at all —

- `GrammarE.parseE sb g fuel cur` walks the open grammar `g` with the
  enclosing body `sb` as a plain parameter; the `selfE` arm re-enters
  `sb` at one less fuel (`parseE sb sb (fuel-1)`; the fuel-0 arm is
  the dead "recursion limit" error — the laws' guardedness accounting
  proves it unreachable under the certificate, Laws.lean). Parse
  recursion stays INPUT+FUEL-driven (the tyP precedent): termination
  is the lexicographic `(fuel, sizeOf g, phase)` measure — each
  `selfE` crossing decrements the fuel, each structural step shrinks
  the node, and the repetition engine's body call is at the same fuel
  one phase down (06 §6's explicit-measure pattern; the compiled code
  is what the tests run, the equation lemmas are what the proofs
  consume).
- `Grammar.print` is total with NO premises: print recursion is
  VALUE-driven and crosses `rel` (an arbitrary `encode`), so the
  `selfE` re-entry rides the `AccD` certificate over the fix's carried
  measure — CONSTRUCTED at the fix arm from the measure itself
  (`AccD.ofFuel m x (m x + 1)`, always constructible). The walk
  (`printWalk`) threads `SelfPathE` derivations to the `selfE` leaves
  so the handler can pay the decrease proof — the design's
  "self-handler with its selfVals membership proof" (§1.3), which the
  open family makes type-check directly. The walk carries TWO
  handlers: the value-side `Hb` (the altE branch discriminator — it
  must be the SAME closure the laws quantify over; a const-true
  discriminator could pick a branch whose closure discipline fails)
  and the string-side `H`.
- `Grammar.run` — the run entry: fuel = length + 1, offset 0, full
  consumption or the trailing-garbage error at the final offset.

ERRORS (design §4): parse failures are the converged
`TextKit.ParseError` BY CONSTRUCTION — `alt` merges via
`ParseError.farther`, `label` pushes the context + sets the valid
surface, `rel` decode failure is the curated error at the node's
START offset (message + got + valid + the ONE engine's suggestion).

Core-only. Five questions:
- root: Universe — total functions over the grammar value + the cursor.
- carrier grade: none — the laws (TextKit/Grammar/Laws.lean) name the
  crossings; parse/print are the mechanism.
- spine reading: none — the derived machinery the formats consume.
- ladder rung: rung 1-2 — structural matches + the AccD certificate +
  one explicit lex measure for the fuel crossing; no `partial`.
- gate row: none yet — TextKitTests pins the fixture round trips.
-/

import TextKit.Grammar

namespace TextKit

/-! ## the derived parser (the open family) -/

mutual
/-- The parser fold for the open family: `sb` is the enclosing fix's
    body (the `selfE` re-entry target). Fuel discipline: `selfE`
    decrements (the crossing), `repE`'s engine decrements per
    iteration; everything else threads. -/
def GrammarE.parseE {R A : Type} (sb : GrammarE R R) : GrammarE R A → Nat → GParser A :=
  fun g fuel => match g, fuel with
  | .atomE L, _ => fun cur => L.scan cur
  | .seqE a b, fuel => fun cur =>
      match parseE sb a fuel cur with
      | .error e => .error e
      | .ok (x, cur1) =>
          match parseE sb b fuel cur1 with
          | .error e => .error e
          | .ok (y, cur2) => .ok ((x, y), cur2)
  | .altE a b, fuel => fun cur =>
      match parseE sb a fuel cur with
      | .ok r => .ok r
      | .error e =>
          match parseE sb b fuel cur with
          | .ok r => .ok r
          | .error e' => .error (ParseError.farther e e')
  | .repE a, fuel => fun cur => parseManyE sb a fuel cur
  | .optE a, fuel => fun cur =>
      match parseE sb a fuel cur with
      | .error _ => .ok (Option.none, cur)
      | .ok (x, cur') => .ok (Option.some x, cur')
  | .labelE n a, fuel => fun cur =>
      match parseE sb a fuel cur with
      | .error e =>
          .error { e with valid := [n], message := s!"expected {n}",
                          context := TextKit.Label.at n :: e.context }
      | .ok r => .ok r
  | .relE m _ _ _ nm vld sub, fuel => fun cur =>
      match parseE sb sub fuel cur with
      | .error e => .error e
      | .ok (raw, cur') =>
          match m.decode raw with
          | .some r => .ok (r, cur')
          | .none =>
              let got := String.ofList (cur.cs.take (cur.cs.length - cur'.cs.length))
              .error ({ Diag.closedWorld parseCode s!"invalid {nm}" .error got vld
                        with pos := cur.off })
  | .selfE, 0 => fun cur => .error (ParseError.base cur.off ["<recursion limit>"])
  | .selfE, fuel + 1 => fun cur => parseE sb sb fuel cur
termination_by g fuel => (fuel, sizeOf g, 0)

/-- The repetition engine: the body's failure stops the loop with what
    it has; the zero-progress body's final attempt stops too (the
    progress rule — WF-REP-1 makes the stop exact for checked
    grammars). -/
def GrammarE.parseManyE {R A : Type} (sb : GrammarE R R) (a : GrammarE R A) :
    Nat → GParser (List A) :=
  fun fuel cur =>
    match fuel, cur with
    | 0, cur => .ok ([], cur)
    | fuel + 1, cur =>
        match parseE sb a (fuel + 1) cur with
        | .error _ => .ok ([], cur)
        | .ok (x, cur') =>
            if cur'.cs.length < cur.cs.length then
              match parseManyE sb a fuel cur' with
              | .ok (xs, cur'') => .ok (x :: xs, cur'')
              | .error e => .error e
            else .ok ([x], cur')
termination_by fuel => (fuel, sizeOf a, 1)
end

/-! ## the derived parser (the closed level) -/

mutual
/-- The closed parser fold; the fix arm enters the body. -/
def Grammar.parseG {A : Type} : Grammar A → Nat → GParser A :=
  fun g fuel => match g, fuel with
  | .atom L, _ => fun cur => L.scan cur
  | .seq a b, fuel => fun cur =>
      match parseG a fuel cur with
      | .error e => .error e
      | .ok (x, cur1) =>
          match parseG b fuel cur1 with
          | .error e => .error e
          | .ok (y, cur2) => .ok ((x, y), cur2)
  | .alt a b, fuel => fun cur =>
      match parseG a fuel cur with
      | .ok r => .ok r
      | .error e =>
          match parseG b fuel cur with
          | .ok r => .ok r
          | .error e' => .error (ParseError.farther e e')
  | .rep a, fuel => fun cur => parseManyG a fuel cur
  | .opt a, fuel => fun cur =>
      match parseG a fuel cur with
      | .error _ => .ok (Option.none, cur)
      | .ok (x, cur') => .ok (Option.some x, cur')
  | .label n a, fuel => fun cur =>
      match parseG a fuel cur with
      | .error e =>
          .error { e with valid := [n], message := s!"expected {n}",
                          context := TextKit.Label.at n :: e.context }
      | .ok r => .ok r
  | .rel m _ _ _ nm vld sub, fuel => fun cur =>
      match parseG sub fuel cur with
      | .error e => .error e
      | .ok (raw, cur') =>
          match m.decode raw with
          | .some r => .ok (r, cur')
          | .none =>
              let got := String.ofList (cur.cs.take (cur.cs.length - cur'.cs.length))
              .error ({ Diag.closedWorld parseCode s!"invalid {nm}" .error got vld
                        with pos := cur.off })
  | .fix _ body _, fuel => fun cur => GrammarE.parseE body body fuel cur
termination_by g fuel => (fuel, sizeOf g, 0)

/-- The closed repetition engine. -/
def Grammar.parseManyG {A : Type} (a : Grammar A) :
    Nat → GParser (List A) :=
  fun fuel cur =>
    match fuel, cur with
    | 0, cur => .ok ([], cur)
    | fuel + 1, cur =>
        match parseG a (fuel + 1) cur with
        | .error _ => .ok ([], cur)
        | .ok (x, cur') =>
            if cur'.cs.length < cur.cs.length then
              match parseManyG a fuel cur' with
              | .ok (xs, cur'') => .ok (x :: xs, cur'')
              | .error e => .error e
            else .ok ([x], cur')
termination_by fuel => (fuel, sizeOf a, 1)
end

/-- The derived parser: the run entry's fold (fuel = length + 1 at
    `run`; the explicit fuel here for the law's fuel-sufficiency
    plumbing). -/
def Grammar.parse (g : Grammar R) (fuel : Nat) : GParser R :=
  parseG g fuel

/-! ## the derived printer -/

/-- The membership-threaded print-list (the path-carrying walk's rep
    engine: each element's print sees its membership proof). -/
def GrammarE.printList {A : Type} : (xs : List A) → ((z : A) → z ∈ xs → String) → String
  | [], _ => ""
  | z :: zs, f => f z (List.Mem.head zs) ++ printList zs (fun w hw => f w (List.Mem.tail z hw))

@[simp] theorem GrammarE.printList_nil {A : Type} (f : (z : A) → z ∈ ([] : List A) → String) :
    printList [] f = "" := rfl

@[simp] theorem GrammarE.printList_cons {A : Type} (z : A) (zs : List A)
    (f : (w : A) → w ∈ z :: zs → String) :
    printList (z :: zs) f =
      f z (List.Mem.head zs) ++ printList zs (fun w hw => f w (List.Mem.tail z hw)) := rfl

/-- printList respects pointwise-equal element printers. -/
theorem GrammarE.printList_congr {A : Type} : (xs : List A) →
    (f g : (z : A) → z ∈ xs → String) →
    (∀ z hz, f z hz = g z hz) → printList xs f = printList xs g
  | [], _, _, _ => rfl
  | z :: zs, f, g, h => by
      rw [printList_cons, printList_cons, h z (List.Mem.head zs),
        printList_congr zs _ _ (fun w hw => h w (List.Mem.tail z hw))]

/-- The printer's structural walk over the open family. `Hb` is the
    value-side handler (the altE branch discriminator — the SAME
    closure the laws quantify over); `H` is the string for each value
    the `selfE` sites receive, called with the path witnessing it (the
    decrease proof's input at the fix arm). -/
def GrammarE.printWalk : {R A : Type} → (g : GrammarE R A) → (x : A) →
    ((y : R) → SelfPathE g x y → Bool) →
    ((y : R) → SelfPathE g x y → String) → String :=
  fun {_ _} g x Hb H => match g, x, Hb, H with
  | .atomE L, x, _, _ => L.print x
  | .seqE a b, (p, q), Hb, H =>
      printWalk a p (fun y path => Hb y (.seqL path)) (fun y path => H y (.seqL path)) ++
      printWalk b q (fun y path => Hb y (.seqR path)) (fun y path => H y (.seqR path))
  | .altE a b, x, Hb, H =>
      if valueOkWalk a x (fun y path => Hb y (.altL path))
      then printWalk a x (fun y path => Hb y (.altL path)) (fun y path => H y (.altL path))
      else printWalk b x (fun y path => Hb y (.altR path)) (fun y path => H y (.altR path))
  | .repE a, xs, Hb, H =>
      printList xs (fun z hz =>
        printWalk a z (fun y path => Hb y (.repP hz path)) (fun y path => H y (.repP hz path)))
  | .optE a, x, Hb, H =>
      match x with
      | Option.some z =>
          printWalk a z (fun y path => Hb y (.optP path)) (fun y path => H y (.optP path))
      | Option.none => ""
  | .labelE _n a, x, Hb, H =>
      printWalk a x (fun y path => Hb y (.labelP path)) (fun y path => H y (.labelP path))
  | .relE m _ _ _ _ _ sub, x, Hb, H =>
      printWalk sub (m.encode x) (fun y path => Hb y (.relP path))
        (fun y path => H y (.relP path))
  | .selfE, x, _, H => H x (.selfP x)

/-! printWalk's per-node equations (iota; the congruence lemma's
    rewrite surface) -/
theorem GrammarE.printWalk_seqE (a : GrammarE R A) (b : GrammarE R B)
    (p : A) (q : B) (Hb H) :
    printWalk (.seqE a b) (p, q) Hb H =
      (printWalk a p (fun y path => Hb y (.seqL path)) (fun y path => H y (.seqL path)) ++
       printWalk b q (fun y path => Hb y (.seqR path)) (fun y path => H y (.seqR path))) := rfl

theorem GrammarE.printWalk_altE (a b : GrammarE R A) (x : A) (Hb H) :
    printWalk (.altE a b) x Hb H =
      (if valueOkWalk a x (fun y path => Hb y (.altL path))
       then printWalk a x (fun y path => Hb y (.altL path)) (fun y path => H y (.altL path))
       else printWalk b x (fun y path => Hb y (.altR path)) (fun y path => H y (.altR path))) := rfl

theorem GrammarE.printWalk_repE (a : GrammarE R A) (xs : List A) (Hb H) :
    printWalk (.repE a) xs Hb H =
      printList xs (fun z hz =>
        printWalk a z (fun y path => Hb y (.repP hz path)) (fun y path => H y (.repP hz path))) := rfl

theorem GrammarE.printWalk_optE_some (a : GrammarE R A) (z : A) (Hb H) :
    printWalk (.optE a) (Option.some z) Hb H =
      printWalk a z (fun y path => Hb y (.optP path)) (fun y path => H y (.optP path)) := rfl

theorem GrammarE.printWalk_optE_none (a : GrammarE R A) (Hb H) :
    printWalk (.optE a) Option.none Hb H = "" := rfl

theorem GrammarE.printWalk_labelE (n : String) (a : GrammarE R A) (x : A) (Hb H) :
    printWalk (.labelE n a) x Hb H =
      printWalk a x (fun y path => Hb y (.labelP path)) (fun y path => H y (.labelP path)) := rfl

theorem GrammarE.printWalk_relE (m : Kit.Codec Raw A) (owns : A → Bool)
    (don : ∀ raw r, m.decode raw = Option.some r → owns r = true)
    (ex : ∀ raw r, m.decode raw = Option.some r → m.encode r = raw)
    (nm : String) (vld : List String) (sub : GrammarE R Raw) (x : A) (Hb H) :
    printWalk (.relE m owns don ex nm vld sub) x Hb H =
      printWalk sub (m.encode x) (fun y path => Hb y (.relP path))
        (fun y path => H y (.relP path)) := rfl

theorem GrammarE.printWalk_atomE (L : Lexeme A) (x : A) (Hb H) :
    printWalk (.atomE L : GrammarE R A) x Hb H = L.print x := rfl

theorem GrammarE.printWalk_selfE (x : R) (Hb H) :
    printWalk (.selfE : GrammarE R R) x Hb H = H x (.selfP x) := rfl

/-- printWalk respects pointwise-equal handler pairs. -/
theorem GrammarE.printWalk_congr {R : Type} : {A : Type} → (g : GrammarE R A) → (x : A) →
    (Hb₁ Hb₂ : (y : R) → SelfPathE g x y → Bool) →
    (H₁ H₂ : (y : R) → SelfPathE g x y → String) →
    (∀ y path, Hb₁ y path = Hb₂ y path) → (∀ y path, H₁ y path = H₂ y path) →
    printWalk g x Hb₁ H₁ = printWalk g x Hb₂ H₂ := by
  intro A g
  induction g with
  | atomE L => intro x Hb₁ Hb₂ H₁ H₂ hb h; rfl
  | seqE a b iha ihb =>
      intro x Hb₁ Hb₂ H₁ H₂ hb h
      obtain ⟨p, q⟩ := x
      rw [printWalk_seqE a b p q Hb₁ H₁, printWalk_seqE a b p q Hb₂ H₂,
        iha p _ _ _ _ (fun y path => hb y (.seqL path)) (fun y path => h y (.seqL path)),
        ihb q _ _ _ _ (fun y path => hb y (.seqR path)) (fun y path => h y (.seqR path))]
  | altE a b iha ihb =>
      intro x Hb₁ Hb₂ H₁ H₂ hb h
      have hv : valueOkWalk a x (fun y path => Hb₁ y (.altL path)) =
          valueOkWalk a x (fun y path => Hb₂ y (.altL path)) :=
        valueOkWalk_congr a x _ _ (fun y path => hb y (.altL path))
      rw [printWalk_altE a b x Hb₁ H₁, printWalk_altE a b x Hb₂ H₂, hv]
      split
      · exact iha x _ _ _ _ (fun y path => hb y (.altL path)) (fun y path => h y (.altL path))
      · exact ihb x _ _ _ _ (fun y path => hb y (.altR path)) (fun y path => h y (.altR path))
  | repE a iha =>
      intro xs Hb₁ Hb₂ H₁ H₂ hb h
      rw [printWalk_repE a xs Hb₁ H₁, printWalk_repE a xs Hb₂ H₂]
      exact printList_congr xs _ _
        (fun z hz => iha z _ _ _ _
          (fun y path => hb y (.repP hz path)) (fun y path => h y (.repP hz path)))
  | optE a iha =>
      intro x Hb₁ Hb₂ H₁ H₂ hb h
      cases x with
      | none => rfl
      | some z =>
          rw [printWalk_optE_some a z Hb₁ H₁, printWalk_optE_some a z Hb₂ H₂]
          exact iha z _ _ _ _ (fun y path => hb y (.optP path)) (fun y path => h y (.optP path))
  | labelE n a iha =>
      intro x Hb₁ Hb₂ H₁ H₂ hb h
      rw [printWalk_labelE n a x Hb₁ H₁, printWalk_labelE n a x Hb₂ H₂]
      exact iha x _ _ _ _ (fun y path => hb y (.labelP path)) (fun y path => h y (.labelP path))
  | relE m owns don ex nm vld sub ih =>
      intro x Hb₁ Hb₂ H₁ H₂ hb h
      rw [printWalk_relE m owns don ex nm vld sub x Hb₁ H₁,
        printWalk_relE m owns don ex nm vld sub x Hb₂ H₂]
      exact ih (m.encode x) _ _ _ _
        (fun y path => hb y (.relP path)) (fun y path => h y (.relP path))
  | selfE => intro x Hb₁ Hb₂ H₁ H₂ hb h; exact h x (.selfP x)

/-- The fix-payload printer, ONE step of the AccD recursion: the body's
    walk with the closure as the discriminator and the recursive
    printer at the self-values (paid by the carried decrease proof). -/
def Grammar.printFixGo (m : R → Nat) (sb : GrammarE R R)
    (dec : ∀ x y, SelfPathE sb x y → m y < m x) :
    (x : R) → AccD m x → String
  | x, .intro _ h =>
      GrammarE.printWalk sb x
        (fun y _ => fixValueOk m sb dec y)
        (fun y path => printFixGo m sb dec y (h y (dec x y path)))

/-- The certificate is irrelevant: the printed string does not depend
    on the AccD derivation. -/
theorem Grammar.printFixGo_irrel (m : R → Nat) (sb : GrammarE R R)
    (dec : ∀ x y, SelfPathE sb x y → m y < m x) :
    (x : R) → (acc : AccD m x) → ∀ acc',
      printFixGo m sb dec x acc = printFixGo m sb dec x acc' := by
  intro x acc
  induction acc using AccD.rec with
  | intro x h ih =>
      intro acc'
      cases acc' with
      | intro _ h' =>
          show GrammarE.printWalk sb x _
                (fun y path => printFixGo m sb dec y (h y (dec x y path))) =
               GrammarE.printWalk sb x _
                (fun y path => printFixGo m sb dec y (h' y (dec x y path)))
          exact GrammarE.printWalk_congr sb x _ _ _ _ (fun _ _ => rfl)
            (fun y path => ih y (dec x y path) (h' y (dec x y path)))

/-- The fix-payload printer (the closure's entry). -/
def Grammar.printFix (m : R → Nat) (sb : GrammarE R R)
    (dec : ∀ x y, SelfPathE sb x y → m y < m x) (x : R) : String :=
  printFixGo m sb dec x (AccD.ofFuel m x (m x + 1) (Nat.lt_succ_self _))

/-- The one-step unfold of the fix printer (the laws' fix-case entry). -/
theorem Grammar.printFix_unfold (m : R → Nat) (sb : GrammarE R R)
    (dec : ∀ x y, SelfPathE sb x y → m y < m x) (x : R) :
    printFix m sb dec x =
      GrammarE.printWalk sb x
        (fun y _ => fixValueOk m sb dec y)
        (fun y _ => printFix m sb dec y) := by
  show printFixGo m sb dec x (AccD.ofFuel m x (m x + 1) _) = _
  have h1 : AccD.ofFuel m x (m x + 1) (Nat.lt_succ_self _) =
      AccD.intro x (fun y hy => AccD.ofFuel m y (m x)
        (Nat.lt_of_lt_of_le hy (Nat.le_of_lt_succ (Nat.lt_succ_self _)))) := rfl
  rw [h1]
  show GrammarE.printWalk sb x _
        (fun y path => printFixGo m sb dec y (AccD.ofFuel m y (m x) _)) = _
  exact GrammarE.printWalk_congr sb x _ _ _ _ (fun _ _ => rfl)
    (fun y _ => printFixGo_irrel m sb dec y _ _)

/-- The closed printer walk; the fix arm enters the measure-certified
    recursion. -/
def Grammar.printG : {A : Type} → Grammar A → A → String :=
  fun {_} g x => match g, x with
  | .atom L, x => L.print x
  | .seq a b, (p, q) => printG a p ++ printG b q
  | .alt a b, x => if valueOk a x then printG a x else printG b x
  | .rep a, xs => xs.foldr (fun z acc => printG a z ++ acc) ""
  | .opt a, x => match x with | Option.some z => printG a z | Option.none => ""
  | .label _ a, x => printG a x
  | .rel m _ _ _ _ _ sub, x => printG sub (m.encode x)
  | .fix m sb dec, x => printFix m sb dec x

/-- The derived printer. TOTAL, no premises (the measure is carried). -/
def Grammar.print (g : Grammar R) (x : R) : String := printG g x

/-! ## the run entry -/

/-- The run entry: fuel = length + 1, offset 0, full consumption or the
    trailing-garbage error at the final offset (design §3.1). -/
def Grammar.run (g : Grammar R) (s : String) : Except ParseError R :=
  match parse g (s.length + 1) ⟨0, s.toList⟩ with
  | .error e => .error e
  | .ok (x, cur) =>
      match cur.cs with
      | [] => .ok x
      | _ => .error (ParseError.base cur.off ["<end of input>"])

end TextKit
