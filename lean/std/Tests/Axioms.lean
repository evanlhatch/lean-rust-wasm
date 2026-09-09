/- Axiom gate: the std ops' bodies (the differential ORACLE — the wasm
   intrinsics must compute the same answers) and the guest impls must
   depend only on the core triple (propext / Classical.choice /
   Quot.sound) plus native_decide's disclosed trust base. -/
import GuestlangStd

#print axioms GuestlangStd.strlen
#print axioms GuestlangStd.strcat
#print axioms GuestImpl.getUserImpl
#print axioms GuestImpl.greet
#print axioms GuestImpl.strLenDemo
