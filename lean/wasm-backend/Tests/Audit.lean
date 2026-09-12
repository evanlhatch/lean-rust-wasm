import WasmBackend
import WasmBackend.Audit

/-!
# The audit's tests — hand-programs, positive + negative

The audit is a CHECKER: the tests are its evidence. Every rejection
path is OBSERVED — the negative controls pin the watch-users bug's
class (the store through an uninitialized / unknown-provenance
pointer) and the failure modes the v1 exclusions promise to flag.

The finding index = the LEAF position in the depth-first traversal
(structured forms do not consume an index) — the STORE's leaf index.

The range lane's controls (R1–R9) pin the FIT half: the store's
(offset, width) against the region's known extent — the static-region
registry (the return-areas) and Layout's PROVED record stride. The
field-overlap class is NOT re-proven here — Layout's `go_pairwise`
owns it.
-/

open WasmBackend.Wat WasmBackend.Wat.Audit

/-! ## Positive controls: the emit-shaped idioms audit CLEAN -/

-- 1. alloc + store through it (the ctor/tag idiom).
#guard audit [ .i32const 32, .call "alloc", .localset "p"
             , .localget "p", .i32const 250, .mem .i32store8 4 none ] == []

-- 2. a STATIC absolute base (the return-area idiom: i32const 48 …) —
--    the range lane needs the STATIC-REGION REGISTRY (the (base, extent)
--    pairs); with it registered, the store fits = clean.
#guard audit [ .i32const 48, .localget "v", .mem .i32store 0 none ]
             [ (48, 8) ] == []

-- 3. the pointer-copy chain: q = load(p + 8) from a KNOWN p.
#guard audit [ .i32const 32, .call "alloc", .localset "p"
             , .localget "p", .mem .i32load 8 none, .localset "q"
             , .localget "q", .localget "v", .mem .i32store 0 none ] == []

-- 4. known base + const offset (stringCtor's dst + 16 memory.copy).
#guard audit [ .i32const 40, .call "alloc", .localset "d"
             , .localget "d", .i32const 16, .op .i32add
             , .localget "s", .localget "l", .memcopy ] == []

-- 5. auditFunc seeds params: a store through a param pointer is CLEAN.
#guard auditFunc {
  name := "f",
  params := [⟨some "p", "i32"⟩],
  result := none,
  locals := [],
  body := [ .localget "p", .localget "v", .mem .i32store 0 none ]
} == []

-- 6. a plain branch-join where BOTH branches set p the same way.
#guard audit [ .localget "t"
             , .if_ none [ .i32const 32, .call "alloc", .localset "p" ]
                         [ .i32const 40, .call "alloc", .localset "p" ]
             , .localget "p", .localget "v", .mem .i32store 0 none ] == []

-- 7. a nested block: the walk recurses; a clean store inside stays clean.
#guard audit [ .block "" [ .i32const 32, .call "alloc", .localset "p"
             , .localget "p", .i32const 1, .mem .i32store 8 none ] ] == []

/-! ## Negative controls: the flagged classes -/

-- N1. THE CLOBBER PATTERN: store through a NEVER-SET local
--     (the watch-users bug's class — the uninit/garbage pointer).
--     Leaves: localget junk (0), localget v (1), store (2).
#guard audit [ .localget "junk", .localget "v", .mem .i32store 0 none ] ==
  [ (2, "store through local 'junk' of unknown provenance (never set from alloc/const/load/param)") ]

-- N2. store through a local set from a NON-alloc call's result (opaque).
--     Leaves: call (0), localset (1), localget (2), const (3), store (4).
#guard audit [ .call "f", .localset "p"
             , .localget "p", .i32const 1, .mem .i32store 0 none ] ==
  [ (4, "store through local 'p' of unknown provenance (never set from alloc/const/load/param)") ]

-- N3. store through a mul-computed address (v1: non-const offset = unknown).
--     Leaves: localget (0), const (1), mul (2), localset (3),
--     localget (4), const (5), store (6).
#guard audit [ .localget "i", .i32const 8, .op .i32mul, .localset "p"
             , .localget "p", .i32const 1, .mem .i32store 0 none ] ==
  [ (6, "store through local 'p' of unknown provenance (never set from alloc/const/load/param)") ]

-- N4. store through a pointer LOADED from an object of unknown provenance
--     (the DIRECT shape: the load result IS the address).
--     Leaves: localget (0), load (1), localget (2), store (3).
#guard audit [ .localget "junk", .mem .i32load 8 none
             , .localget "v", .mem .i32store 0 none ] ==
  [ (3, "store through a pointer loaded from an object of unknown provenance") ]

-- N4b. the INDIRECT shape: the loaded pointer lands in a local first —
--     the local's stored value carries the unknown provenance through.
--     Leaves: localget (0), load (1), localset (2), localget (3),
--     localget (4), store (5).
#guard audit [ .localget "junk", .mem .i32load 8 none, .localset "q"
             , .localget "q", .localget "v", .mem .i32store 0 none ] ==
  [ (5, "store through local 'q' of unknown provenance (never set from alloc/const/load/param)") ]

-- N5. the bare `audit` (no param seeding): a param pointer IS flagged —
--     the same body that `auditFunc` clears (contrast with #guard 5).
#guard audit [ .localget "p", .localget "v", .mem .i32store 0 none ] ==
  [ (2, "store through local 'p' of unknown provenance (never set from alloc/const/load/param)") ]

-- N6. raw lines are fail-closed: the audit cannot see inside.
#guard audit [ .raw "  i32.store offset=0" ] ==
  [ (0, "raw instruction — the audit cannot analyze a verbatim WAT line") ]

-- N7. the conservative branch join: p set in ONE branch only → the
--     post-if store is flagged (honest over silent).
--     Leaves: localget t (0), const (1), call (2), localset (3),
--     localget (4), localget (5), store (6).
#guard audit [ .localget "t"
             , .if_ none [ .i32const 32, .call "alloc", .localset "p" ] []
             , .localget "p", .localget "v", .mem .i32store 0 none ] ==
  [ (6, "store through local 'p' of unknown provenance (never set from alloc/const/load/param)") ]

-- N8. memory.copy through an unknown destination.
--     Leaves: localget (0), const (1), add (2), localget (3),
--     localget (4), memcopy (5).
#guard audit [ .localget "junk", .i32const 16, .op .i32add
             , .localget "s", .localget "l", .memcopy ] ==
  [ (5, "memory.copy store through local 'junk' of unknown provenance (never set from alloc/const/load/param)") ]

-- N9. an i32add whose stack shape is underflowed (an unmodeled
--     producer) — the add's result degrades to opaque → flagged.
--     Leaves: op (0), localget (1), store (2).
#guard audit [ .op .i32add, .localget "v", .mem .i32store 0 none ] ==
  [ (2, "store through an opaque/unmodeled value") ]

/-! ## Range controls: the store's (offset + width) vs the region's extent

The FIT half of the audit (seam #6's region-disjointness statement):
the provenance walk vouches for the POINTER; these controls pin the
RANGE lane — the store's byte range [addr + offset, addr + offset +
width) against the region's KNOWN extent. The field-OVERLAP class (the
same-offset clobber) is NOT here — Layout's `go_pairwise` already
proves the offsets strictly increasing. What is here: the PAST-END /
PAST-STRIDE class. -/

-- R1. the return-area idiom: a static region 56..64 (8 bytes — the
--     demo's); the store's bytes [56, 64) fit = clean.
#guard audit [ .i32const 56, .localget "v", .mem .i64store 0 none ]
             [ (56, 8) ] == []

-- R2. PAST-END STATIC: a 4-wide store at 56 + 8 = [64, 68) escapes
--     the 8-byte return-area = FLAGGED (the demo's past-end class).
#guard audit [ .i32const 56, .localget "v", .mem .i32store 8 none ]
             [ (56, 8) ] ==
  [ (2, "static-region overflow: the store's byte range [64, 68) escapes every registered static region") ]

-- R3. FAIL-CLOSED: an UNREGISTERED static base = flagged (v1 has no
--     way to know the extent; honest over silent — contrast #guard 2).
#guard audit [ .i32const 48, .localget "v", .mem .i32store 0 none ] ==
  [ (2, "static-region overflow: the store's byte range [48, 52) escapes every registered static region") ]

-- R4. a static base via the tracked (base + const) idiom: 56 + 8 = 64
--     — the same past-end as R2, through pointer arithmetic.
#guard audit [ .i32const 56, .i32const 8, .op .i32add, .localget "v"
             , .mem .i32store 0 none ] [ (56, 8) ] ==
  [ (4, "static-region overflow: the store's byte range [64, 68) escapes every registered static region") ]

-- R5. PAST-STRIDE: an alloc'd record region; a 4-wide store at offset
--     30 ends at byte 34 > 32 = Layout's PROVED user_size = FLAGGED.
#guard audit [ .i32const 32, .call "alloc", .localset "p"
             , .localget "p", .localget "v", .mem .i32store 30 none ] ==
  [ (5, "record-stride overflow: the store's offset 30 + width 4 exceeds the record's size 32") ]

-- R6. the boundary: offset 28 + width 4 = 32 ≤ 32 = clean (the
--     user-record's last field's store shape).
#guard audit [ .i32const 32, .call "alloc", .localset "p"
             , .localget "p", .localget "v", .mem .i32store 28 none ] == []

-- R7. the demo's four field stores at the PROVED offsets
--     (Layout.user_offsets 0/8/16/24, width 8): all clean — the last
--     ends EXACTLY at the stride (24 + 8 = 32 = Layout.user_size).
#guard audit [ .i32const 32, .call "alloc", .localset "p"
             , .localget "p", .localget "v", .mem .i64store 0 none
             , .localget "p", .localget "v", .mem .i64store 8 none
             , .localget "p", .localget "v", .mem .i64store 16 none
             , .localget "p", .localget "v", .mem .i64store 24 none ] == []

-- R8. the ELEMENT-CURSOR shape: q = load(p + 8) — a loaded pointer's
--     VALUE is a runtime fact, so the range through q is UNCHECKED in
--     v1 (the provenance walk still vouches; the honest limit).
#guard audit [ .i32const 32, .call "alloc", .localset "p"
             , .localget "p", .mem .i32load 8 none, .localset "q"
             , .localget "q", .localget "v", .mem .i32store 30 none ] == []

-- R9. the tracked (base + const) idiom FOLDS into the region: the
--     store at (p + 16) + offset 12 + width 8 = byte 36 > 32 = FLAGGED.
#guard audit [ .i32const 32, .call "alloc", .localset "p"
             , .localget "p", .i32const 16, .op .i32add, .localset "d"
             , .localget "d", .localget "v", .mem .i64store 12 none ] ==
  [ (9, "record-stride overflow: the store's offset 28 + width 8 exceeds the record's size 32") ]

-- The index semantics: a bad store INSIDE a block reports its LEAF
-- index within the whole traversal (the block body's localgets are
-- leaves 0 and 1; the store = 2; the trailing drop = 3).
#guard audit [ .block "" [ .localget "junk", .localget "v"
             , .mem .i32store 0 none ], .drop ] ==
  [ (2, "store through local 'junk' of unknown provenance (never set from alloc/const/load/param)") ]

-- The trivial theorem holds.
#guard audit [] == []
