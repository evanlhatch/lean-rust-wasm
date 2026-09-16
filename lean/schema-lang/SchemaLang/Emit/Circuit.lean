/-
# SchemaLang.Emit.Circuit — the dbsp `Ckt` → Rust emitter (W4.4)

Owner: the certified-circuit lane (canon: "a derived view = a circuit
maintained incrementally"). Contents: the demo `Func` family + the
order-total circuit over ℤ streams, its PROVEN `incrementalize`d form,
and the pure fold to a Rust evaluator; the emitted header cites
`Dbsp.incrementalize_ok` by name, shape-pinned by `#check_cert` below.
Excluded: `Rel → Ckt` lowering (W4.5); `par`/`feedback` fold to Node
data with a general evaluator, but the demo circuit is scalar.
-/

import CodegenCore
import Dbsp.Circuit
import SchemaLang.Emit.GenCtx

namespace SchemaLang.Emit.Circuit

open CodegenCore.Emit.Rust (Item renderModule)

/-! ## The demo circuit: order-total aggregation over ℤ streams -/

/-- The demo `Func` family — the closed set of external (compiled)
    function templates the demo circuit wires. Each constructor NAMES
    the Rust template fn the emitted module defines and calls. -/
inductive DemoFunc : (a b : Type) → [AddCommGroup a] → [AddCommGroup b] → Type where
  /-- The per-row line total (qty×price, stood in for by the square —
      NONLINEAR: `incrementalize` must wrap it). -/
  | lineTotal : DemoFunc ℤ ℤ
  /-- ×2 scaling — LINEAR: `incrementalize` keeps it bare. -/
  | double : DemoFunc ℤ ℤ

/-- The templates' meanings: the `denoteF` the certificate quantifies
    over, instantiated at the demo family. -/
def demoDenoteF : Dbsp.CktDenote DemoFunc
  | _, _, _, _, .lineTotal => fun x => x * x
  | _, _, _, _, .double => fun x => 2 * x

/-- The compiler's linearity oracle for the demo family. -/
def demoIsLinear : Dbsp.IsLinearOracle DemoFunc
  | _, _, _, _, .lineTotal => false
  | _, _, _, _, .double => true

/-- The oracle is truthful: the atoms it calls linear ARE additive. -/
theorem demoIsLinearOk :
    ∀ {a b : Type} [AddCommGroup a] [AddCommGroup b] (f : DemoFunc a b),
      demoIsLinear _ _ f = true → ∀ x y : a,
        demoDenoteF _ _ f (x + y) = demoDenoteF _ _ f x + demoDenoteF _ _ f y := by
  intro a b _ _ f h
  cases f with
  | lineTotal => simp [demoIsLinear] at h
  | double => intro x y; show 2 * (x + y) = 2 * x + 2 * y; omega

/-- The order-total aggregation circuit: per-tick line totals, scaled,
    then integrated into the running total. -/
def orderTotalCkt : Dbsp.Ckt DemoFunc ℤ ℤ :=
  .seq (.lifting .lineTotal) (.seq (.lifting .double) .integral)

/-- `denote` evaluates: over the constant-1 stream the running total at
    tick 3 is 2·(1+1+1+1) = 8. (Executable shadow — `Dbsp.fix` computes.) -/
theorem orderTotalCkt_denote_tick3 :
    Dbsp.Ckt.denote demoDenoteF orderTotalCkt (fun _ => 1) 3 = 8 := by
  native_decide

/-- `incrementalize` transforms: the nonlinear leaf wraps in
    `incremental`; the linear leaf and the integral stay bare. -/
theorem orderTotalCkt_incrementalize_eq :
    Dbsp.incrementalize demoIsLinear orderTotalCkt =
      Dbsp.Ckt.seq (Dbsp.Ckt.incremental (Dbsp.Ckt.lifting DemoFunc.lineTotal))
        (Dbsp.Ckt.seq (Dbsp.Ckt.lifting DemoFunc.double) Dbsp.Ckt.integral) := rfl

/-- The certificate's executable shadow: the incrementalized circuit,
    fed the DELTAS of the constant-1 stream (1, then 0), emits the batch
    output's differences — a constant 2 per tick. -/
theorem orderTotalIncr_denote_tick3 :
    Dbsp.Ckt.denote demoDenoteF (Dbsp.incrementalize demoIsLinear orderTotalCkt)
      (fun n => if n == 0 then 1 else 0) 3 = 2 := by
  native_decide

/-- The certificate, instantiated at the demo circuit. -/
theorem orderTotalCkt_incrementalize_ok :
    Dbsp.Ckt.denote demoDenoteF (Dbsp.incrementalize demoIsLinear orderTotalCkt) =
      Dbsp.incremental (Dbsp.Ckt.denote demoDenoteF orderTotalCkt) :=
  Dbsp.incrementalize_ok demoIsLinear demoIsLinearOk orderTotalCkt

/-! ## The certificate pin (the Dbsp.Certs CI mechanism)

The emitted Rust header CITES `Dbsp.incrementalize_ok`; this command is
the citation's enforcement — the name must be a `@[cert]`-registered
theorem whose type is defeq to the required shape, checked at
elaboration of THIS module (certification drift = build error). -/

#check_cert Dbsp.incrementalize_ok :
  ∀ {Func : (a b : Type) → [AddCommGroup a] → [AddCommGroup b] → Type}
    {a b : Type} [AddCommGroup a] [AddCommGroup b]
    {denoteF : Dbsp.CktDenote Func} (isLinear : Dbsp.IsLinearOracle Func)
    (_isLinearOk : ∀ {a b : Type} [AddCommGroup a] [AddCommGroup b] (f : Func a b),
      isLinear _ _ f = true → ∀ x y : a,
        denoteF _ _ f (x + y) = denoteF _ _ f x + denoteF _ _ f y)
    (f : Dbsp.Ckt Func a b),
    Dbsp.Ckt.denote denoteF (Dbsp.incrementalize isLinear f) =
      Dbsp.incremental (Dbsp.Ckt.denote denoteF f)

/-! ## The fold: circuit structure → Rust -/

/-- The type-erased circuit tree the Rust side renders. Type indices are
    erased (the evaluator's `Val` carries the pair structure); `Lift`
    names a Rust template fn. -/
inductive Node where
  | delay | derivative | integral
  | incremental (g : Node)
  | lift (template : String)
  | seq (f g : Node)
  | par (f g : Node)
  | feedback (body : Node)

/-- `Func` atoms → Rust template fn names. -/
def demoTemplate : {a b : Type} → [AddCommGroup a] → [AddCommGroup b] → DemoFunc a b → String
  | _, _, _, _, .lineTotal => "demo_line_total"
  | _, _, _, _, .double => "demo_double"

/-- The pure fold: `Ckt DemoFunc` structure → the node tree. -/
def toNode : {a b : Type} → [AddCommGroup a] → [AddCommGroup b] → Dbsp.Ckt DemoFunc a b → Node
  | _, _, _, _, Dbsp.Ckt.delay => .delay
  | _, _, _, _, Dbsp.Ckt.derivative => .derivative
  | _, _, _, _, Dbsp.Ckt.integral => .integral
  | _, _, _, _, Dbsp.Ckt.incremental g => .incremental (toNode g)
  | _, _, _, _, Dbsp.Ckt.lifting f => .lift (demoTemplate f)
  | _, _, _, _, Dbsp.Ckt.seq f g => .seq (toNode f) (toNode g)
  | _, _, _, _, Dbsp.Ckt.par f g => .par (toNode f) (toNode g)
  | _, _, _, _, Dbsp.Ckt.feedback f => .feedback (toNode f)

/-- The node tree as a Rust expression over the emitted `Node` enum. -/
def Node.toRust : Node → String
  | .delay => "Node::Delay"
  | .derivative => "Node::Derivative"
  | .integral => "Node::Integral"
  | .incremental g => s!"Node::Incremental(Box::new({g.toRust}))"
  | .lift t => s!"Node::Lift({t})"
  | .seq f g => s!"Node::Seq(Box::new({f.toRust}), Box::new({g.toRust}))"
  | .par f g => s!"Node::Par(Box::new({f.toRust}), Box::new({g.toRust}))"
  | .feedback f => s!"Node::Feedback(Box::new({f.toRust}))"

/-- The batch circuit as a Rust expression. -/
def orderTotalCktRust : String := (toNode orderTotalCkt).toRust

/-- The proven incrementalization as a Rust expression. -/
def orderTotalIncrRust : String :=
  (toNode (Dbsp.incrementalize demoIsLinear orderTotalCkt)).toRust

/-- The `Val` arithmetic: the Rust shadow of the `AddCommGroup` the
    circuits are indexed over (pairs add componentwise, mirroring
    mathlib's `Prod` instance). The mismatched-shape arms are dead for
    well-typed circuits — the Lean side is typed; `Val` is the erasure. -/
def valImpl : List String :=
  [ "impl Val {"
  , "    fn zero() -> Val {"
  , "        Val::I(0)"
  , "    }"
  , "    fn fst(&self) -> Val {"
  , "        match self {"
  , "            Val::P(a, _) => (**a).clone(),"
  , "            v => v.clone(),"
  , "        }"
  , "    }"
  , "    fn snd(&self) -> Val {"
  , "        match self {"
  , "            Val::P(_, b) => (**b).clone(),"
  , "            v => v.clone(),"
  , "        }"
  , "    }"
  , "    fn add(&self, o: &Val) -> Val {"
  , "        match (self, o) {"
  , "            (Val::I(x), Val::I(y)) => Val::I(x + y),"
  , "            (Val::P(a1, b1), Val::P(a2, b2)) => {"
  , "                Val::P(Box::new(a1.add(a2)), Box::new(b1.add(b2)))"
  , "            }"
  , "            // dead for well-typed circuits (the Lean side is typed)"
  , "            (v, _) => v.clone(),"
  , "        }"
  , "    }"
  , "    fn sub(&self, o: &Val) -> Val {"
  , "        match (self, o) {"
  , "            (Val::I(x), Val::I(y)) => Val::I(x - y),"
  , "            (Val::P(a1, b1), Val::P(a2, b2)) => {"
  , "                Val::P(Box::new(a1.sub(a2)), Box::new(b1.sub(b2)))"
  , "            }"
  , "            (v, _) => v.clone(),"
  , "        }"
  , "    }"
  , "}" ]

/-- The evaluator: the executable shadow of `Dbsp.Ckt.denote` (`Dbsp.I`
    is the prefix sum, `Dbsp.D` the difference, `Dbsp.delay` the shift,
    `Dbsp.incremental Q = D ∘ Q ∘ I`, `Dbsp.fix` the memoized delayed
    loop — causality makes the recursion well-founded). -/
def evaluator : List String :=
  [ "/// Integrate a stream: the prefix-sum shadow of `Dbsp.I`."
  , "fn integrated(s: &dyn Fn(usize) -> Val) -> impl Fn(usize) -> Val + '_ {"
  , "    move |i| {"
  , "        let mut acc = Val::zero();"
  , "        let mut j = 0;"
  , "        while j <= i {"
  , "            acc = acc.add(&s(j));"
  , "            j += 1;"
  , "        }"
  , "        acc"
  , "    }"
  , "}"
  , ""
  , "/// Evaluate a circuit at tick `n` over the input stream `s` — the"
  , "/// executable shadow of `Dbsp.Ckt.denote`."
  , "pub fn eval(node: &Node, s: &dyn Fn(usize) -> Val, n: usize) -> Val {"
  , "    match node {"
  , "        Node::Delay => {"
  , "            if n == 0 { Val::zero() } else { s(n - 1) }"
  , "        }"
  , "        Node::Derivative => {"
  , "            let prev = if n == 0 { Val::zero() } else { s(n - 1) };"
  , "            s(n).sub(&prev)"
  , "        }"
  , "        Node::Integral => integrated(s)(n),"
  , "        Node::Incremental(g) => {"
  , "            // Dbsp.incremental Q = D . Q . I"
  , "            let integ = integrated(s);"
  , "            let cur = eval(g, &integ, n);"
  , "            let prev = if n == 0 { Val::zero() } else { eval(g, &integ, n - 1) };"
  , "            cur.sub(&prev)"
  , "        }"
  , "        Node::Lift(f) => match s(n) {"
  , "            Val::I(x) => Val::I(f(x)),"
  , "            v => v,"
  , "        },"
  , "        Node::Seq(f, g) => {"
  , "            let mid = |i: usize| eval(f, s, i);"
  , "            eval(g, &mid, n)"
  , "        }"
  , "        Node::Par(f, g) => {"
  , "            let left = |i: usize| s(i).fst();"
  , "            let right = |i: usize| s(i).snd();"
  , "            Val::P(Box::new(eval(f, &left, n)), Box::new(eval(g, &right, n)))"
  , "        }"
  , "        Node::Feedback(body) => {"
  , "            // Dbsp.fix of the delayed body: alpha(n) = body(s x delay alpha)(n);"
  , "            // causality reads alpha only at ticks < n (the memo terminates)."
  , "            let memo: std::cell::RefCell<Vec<Option<Val>>> ="
  , "                std::cell::RefCell::new(Vec::new());"
  , "            fn go("
  , "                body: &Node,"
  , "                s: &dyn Fn(usize) -> Val,"
  , "                i: usize,"
  , "                memo: &std::cell::RefCell<Vec<Option<Val>>>,"
  , "            ) -> Val {"
  , "                let cached = memo.borrow().get(i).cloned().flatten();"
  , "                if let Some(v) = cached {"
  , "                    return v;"
  , "                }"
  , "                let delayed = |j: usize| {"
  , "                    if j == 0 { Val::zero() } else { go(body, s, j - 1, memo) }"
  , "                };"
  , "                let paired = |j: usize| Val::P(Box::new(s(j)), Box::new(delayed(j)));"
  , "                let v = eval(body, &paired, i);"
  , "                let mut m = memo.borrow_mut();"
  , "                if m.len() <= i {"
  , "                    m.resize(i + 1, None);"
  , "                }"
  , "                m[i] = Some(v.clone());"
  , "                v"
  , "            }"
  , "            go(body, s, n, &memo)"
  , "        }"
  , "    }"
  , "}" ]

/-- The generated module: header comment cites the certificate BY NAME
    (the cert-citation discipline — pinned by the `#check_cert` above);
    the template fns + the evaluator are fixed template text; the fold
    contributes the two circuit values (batch + incrementalized). -/
def circuitRust : String :=
  renderModule
    ([ Item.comment "The certified-circuit pipeline (W4.4): folded from the LEAN circuit"
     , Item.comment "`SchemaLang.Emit.Circuit.orderTotalCkt` and its PROVEN"
     , Item.comment "incrementalization. Certificate: `Dbsp.incrementalize_ok`"
     , Item.comment "(denote (incrementalize isLinear c) = incremental (denote c)) —"
     , Item.comment "a registered @[cert] theorem, shape-pinned by #check_cert in"
     , Item.comment "SchemaLang/Emit/Circuit.lean. Do not edit — regenerate (just gen)."
     , Item.raw ""
     , Item.enum "Val" ["Clone", "Debug", "PartialEq"] ["I(i64)", "P(Box<Val>, Box<Val>)"]
     , Item.raw ""
     ]
    ++ (valImpl.map Item.raw)
    ++ [ Item.raw ""
       , Item.enum "Node" ["Clone", "Debug"]
           [ "Delay", "Derivative", "Integral", "Incremental(Box<Node>)"
           , "Lift(fn(i64) -> i64)", "Seq(Box<Node>, Box<Node>)"
           , "Par(Box<Node>, Box<Node>)", "Feedback(Box<Node>)" ]
       , Item.raw ""
       , Item.comment "The Rust template fns the `DemoFunc` atoms name"
       , Item.comment "(`demoDenoteF` in SchemaLang.Emit.Circuit is their Lean meaning)."
       , Item.fn "fn demo_line_total(x: i64) -> i64" "x * x"
       , Item.raw ""
       , Item.fn "fn demo_double(x: i64) -> i64" "2 * x"
       , Item.raw ""
       , Item.comment "The order-total aggregation circuit, batch form (Lean: `orderTotalCkt`)."
       , Item.fn "fn order_total_circuit() -> Node" orderTotalCktRust
       , Item.raw ""
       , Item.comment "Its proven incrementalization (Lean: `Dbsp.incrementalize"
       , Item.comment "demoIsLinear orderTotalCkt`; cert `Dbsp.incrementalize_ok`)."
       , Item.fn "fn order_total_incremental() -> Node" orderTotalIncrRust
       , Item.raw ""
       ]
    ++ (evaluator.map Item.raw))

/-- The emitter. `run` ignores the ctx: the circuit is DATA in this
    module (the demo scale — a registry lane for circuits is the W4.5
    follow-up), and the byte-tie pins the output. -/
def circuitEmitter : CodegenCore.Emit.Emitter GenCtx where
  name := "circuit"
  style := .doubleSlash
  specSource := "SchemaLang.Emit.Circuit (orderTotalCkt; cert Dbsp.incrementalize_ok)"
  outputs := ["../../src/circuit_generated.rs"]
  run _ctx :=
    [{ path := "../../src/circuit_generated.rs"
       contents := circuitRust }]

end SchemaLang.Emit.Circuit
