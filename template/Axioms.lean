/- Axiom gate — the skeleton. This file exists so `just lean-axioms`
   covers the package uniformly (the gate runs `lean Tests/Axioms.lean`
   in every lean_pkgs entry). The scaffold ships no theorems; the
   headline defs must print only the core triple
   (propext/Classical.choice/Quot.sound + disclosed native_decide).
   Add a `#print axioms` row per headline theorem as they land — a
   missing row is silent coverage, a stub row is a lie. -/
import ThingFn

#print axioms ThingImpl.thing_get
