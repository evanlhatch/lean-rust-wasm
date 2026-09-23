/- # SchemaLang.TickCascade — the cascade's composition laws (at v2)

The cascade = folding the registered updates (in registration order)
over the table's rows. v1→v2 (the owner's canon row: a business rule /
batch update IS a `schema_update` on the v2 surface — Update2.lean's
multi-SET/INSERT/DELETE language): the fold's application semantics is
`Update2Item.apply`. THE LAWS ARE CITED, NOT RE-PROVED:

1. `cascadeSystem` — THE cascade IS a DeltaSystem (W4.3), at the
   NO-INSERT fragment: `Dbsp.Effects.DeltaSystem` at state = the
   table's rows, locations = column names, mutations = no-insert v2
   updates, application = `Update2Item.apply`. The one contract
   (`disjoint_commutes`) is `Update2.apply2_comm` — Update2's proved
   law; the `Update2Compat` premise pack is CONSTRUCTED here from
   influence-disjointness (the refuse/insert-separation fields are
   vacuous at `insert? = none`, the non-interference fields unpack the
   derived read/write sets). The general (insert-carrying) law is a
   PERMUTATION (`Update2.apply2_comm_perm`) — outside the class's
   patch equality; the full-instance follow-up is noted in Update2's
   header.
2. `cascade_disj_commutes` — two influence-disjoint no-insert updates
   compose in either order (plain equality — "frame order may differ;
   final state may not").
3. `cascade_applySeq_perm` — N-update order-freedom:
   `Dbsp.applySeq_perm` read off the instance.
4. `set_same_order_disagrees` — the NEGATIVE (the get-observable
   witness): same-column writes are order-DEPENDENT (later-wins,
   `ColPath.set_commute_same`); the journal's S0 policy exists exactly
   for this channel.

The v1→v2 impedance note (honest diff): v1's cascade ran single-set
updates (`UpdateItem` packed as `Σ f, UpdateItem fs f`) whose legality
rode the `UpdatePure`/`NonInterfering` instance binders; v2's rides
the `Update2Compat` premise pack over the DERIVED reads (never
hand-listed). The purity gate is shared — the registration's volatile
scan stores `volatileRefs` on BOTH surfaces and emits both pure locks.
v1's packed-Σ shape is subsumed by `Update2Item`'s clause list.

Honest scope: the cascade is sequential single-table; the full
schedule-equivalence (stage-walker ≡ queue-cascade, relational shape)
needs these laws PLUS the row-shape certification — the growth
path is noted in notes/flatland-alignment.md §2.
-/

module

public import SchemaLang.Update
public import SchemaLang.Update2
public import Dbsp.Effects

@[expose] public section

namespace SchemaLang

/-! ## The cascade IS a DeltaSystem (W4.3, at the no-insert v2 fragment)

`Dbsp.Effects.DeltaSystem` (which extends the shared law family's
`CodegenCore.DisjointCommute` — the SAME disjoint-commutes shape
`SchemaLang.Lens`'s put_comm instantiates via
`SchemaLang.instDisjointCommuteOfSchemaPath`, the class's OTHER
instance, whose law field cites `put_comm`; Lens.lean stays the site
of that instance) at: state = the table's rows, locations = column
names, mutations = no-insert v2 updates. The static influence of an update is its DERIVED reads plus
its SET columns — write sets ALONE cannot certify commutation, because
`Update2Item.apply` READS the row: a guard, set value, or insert
template reading the other update's written column breaks
order-freedom (`Update2Compat`'s non-interference fields exist exactly
there). Influence-disjointness is the conservative form — it also
forbids SHARED reads, which are safe.

The fragment restriction is LOAD-BEARING: an insert-carrying pair
commutes only up to permutation (`Update2.apply2_comm_perm` — the
insert blocks swap), so `disjoint_commutes`' plain equality needs
`insert? = none` on both sides. Deletes are IN the fragment (a delete
commutes with an influence-disjoint write — the guard neutrality
survives, and a row set-then-deleted is absent either way;
`Update2Compat`'s proofs cover the delete flags). -/

/-- The no-insert fragment: the DeltaSystem's mutation type. The
    subtype carries the fragment's proof (a plain `Bool` fact, not a
    class — the fragment is a subtype, not a new surface). -/
def NoInsert (fs : List Field) : Type := {u : Update2Item fs // u.insert? = none}

/-- The static influence of a v2 update: every column whose change can
    alter the update's effect — the derived reads (guard + set values
    + insert template) plus the SET columns (never hand-listed;
    `Update2Item.reads`/`setNames` are folds). Deletes carry no
    location (they remove rows; their guard rides the reads). -/
def cascadeInfluence {fs : List Field} (u : Update2Item fs) : List String :=
  u.reads ++ u.setNames

-- the `warn.classDefReducibility` warning is silenced to say so: the
-- system is passed explicitly (`cascadeSystem fs`), never found by
-- instance search.
set_option warn.classDefReducibility false in
/-- THE INSTANCE: the row-table cascade is a delta system. Application
    IS patching (`Update2Item.apply`); the ONE contract
    (`disjoint_commutes`) delegates to `Update2.apply2_comm` — the
    law Update2 proved; here the influence-disjointness premise is
    unpacked into the `Update2Compat` premise pack, never re-proved. -/
def cascadeSystem (fs : List Field) :
    Dbsp.DeltaSystem (List (RowVals fs)) String (NoInsert fs) where
  -- the DISJOINTCOMMUTE parent fields (B3: the extends shape — a
  -- mutation's location IS its static influence list, DISJOINTNESS is
  -- write-set disjointness, and the ONE contract is `disjoint_commutes`)
  apply rows u := u.1.apply rows
  loc u := cascadeInfluence u.1
  Disjoint := Dbsp.LocDisjoint
  -- the DELTA-system fields (valid + writesOf + the relation's symmetry)
  valid _ _ := True
  writesOf u := cascadeInfluence u.1
  disjoint_symm := by
    intro l₁ l₂ hd
    -- `change` reduces the inherited `Disjoint` off the pending record
    change Dbsp.LocDisjoint l₁ l₂ at hd
    exact Dbsp.LocDisjoint.symm hd
  disjoint_commutes := by
    intro u₁ u₂ hd rows
    have h : List.Disjoint (u₁.1.reads ++ u₁.1.setNames)
        (u₂.1.reads ++ u₂.1.setNames) := hd
    have compat : Update2Compat u₁.1 u₂.1 rows :=
      { ni₁₂ := fun _ hn hmem => h (List.mem_append_left _ hn)
            (List.mem_append_right _ hmem)
        ni₂₁ := fun _ hn hmem => Dbsp.LocDisjoint.symm h
            (List.mem_append_left _ hn) (List.mem_append_right _ hmem)
        setDisj := fun _ hn hn' => h (List.mem_append_right _ hn)
            (List.mem_append_right _ hn')
        refuse₁₂ := fun r _ => by
          unfold Update2Item.newRow
          rw [u₁.2]
          split <;> rfl
        refuse₂₁ := fun r _ => by
          unfold Update2Item.newRow
          rw [u₂.2]
          split <;> rfl
        insertSep₁₂ := fun hsome => by
          rw [u₁.2] at hsome; simp at hsome
        insertSep₂₁ := fun hsome => by
          rw [u₂.2] at hsome; simp at hsome }
    -- the inherited law: Disjoint (loc m₁) (loc m₂) →
    -- apply (apply s m₁) m₂ = apply (apply s m₂) m₁; apply2_comm
    -- proves the reverse orientation — the cited law, `.symm`d
    exact (apply2_comm compat u₁.2 u₂.2).symm

/-- The class-vocabulary restatement: influence-disjoint no-insert v2
    updates commute — `disjoint_commutes` read off the instance. Thin
    BY DESIGN: the class site owns the proof (it cites
    `Update2.apply2_comm`). -/
theorem cascade_disj_commutes {fs : List Field} (u₁ u₂ : Update2Item fs)
    (h₁ : u₁.insert? = none) (h₂ : u₂.insert? = none)
    (hd : Dbsp.LocDisjoint (cascadeInfluence u₁) (cascadeInfluence u₂))
    (rows : List (RowVals fs)) :
    u₁.apply (u₂.apply rows) = u₂.apply (u₁.apply rows) := by
  -- the inherited law's conclusion reduces through the class
  -- projections; the law's orientation (apply (apply s m₁) m₂ = … m₂ m₁)
  -- is flipped to this theorem's (u₁ then u₂ — the registration order)
  exact ((cascadeSystem fs).disjoint_commutes ⟨u₁, h₁⟩ ⟨u₂, h₂⟩ hd rows).symm

/-- N-update order-freedom: a pairwise influence-disjoint batch of
    no-insert v2 updates computes the same final table under ANY
    ordering — `Dbsp.applySeq_perm` read off the instance (the
    permutation invariance of conflict-free batches, instantiated at
    the cascade). -/
theorem cascade_applySeq_perm {fs : List Field} {us₁ us₂ : List (NoInsert fs)}
    (hp : us₁.Perm us₂)
    (hpair : us₁.Pairwise
      (fun a b => Dbsp.LocDisjoint (cascadeInfluence a.1) (cascadeInfluence b.1)))
    (rows : List (RowVals fs)) :
    Dbsp.applySeq (cascadeSystem fs) us₁ rows
      = Dbsp.applySeq (cascadeSystem fs) us₂ rows :=
  Dbsp.applySeq_perm hp hpair rows

/-- The NEGATIVE (the get-observable witness): same-column writes are
    ORDER-DEPENDENT — `set 0` then `set 5` reads 5; the other order
    reads 0. The journal's S0 policy exists exactly for this channel
    (later-wins; `set_commute_same` is its composition law). -/
theorem set_same_order_disagrees (row : RowVals [(⟨"id", Ty.u64⟩ : Field)])
    (p : ColPath "id" .u64 [(⟨"id", Ty.u64⟩ : Field)]) :
    p.get (p.set (p.set row (.u64 0)) (.u64 5))
      ≠ p.get (p.set row (.u64 0)) := by
  intro h
  cases p with
  | here => cases row; simp [ColPath.get, ColPath.set] at h
  | there p' => cases p'

end SchemaLang
