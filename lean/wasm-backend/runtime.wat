;; guestlang runtime — pooled allocator + Perceus RC (guestlang-owned;
;; NOT Lean's C runtime). GenMain splices these funcs/globals into the
;; emitted module — single module, no imports.
;;
;; Object layout: { rc: u32 @0, tag: u8 @4, class: u8 @5, pad[2], fields @8 }
;; (one 8-byte slot per scalar field — matches the LCNF sproj offsets).
;;
;; Allocation: size-class free lists (class = (size-1)>>4, 16-byte
;; granularity, classes 0..5 = 16..96 bytes) — O(1) alloc AND free.
;; Freelist heads live at memory[0..24). Blocks >96 bytes bump-allocate
;; and never free (v1: the scalars-only demo never exceeds a class).
;; Perceus: rc_inc/rc_dec; dec→0 pushes the block back to its class.

(global $heap (mut i32) (i32.const 64))
(global $heap-end (mut i32) (i32.const 65536))

(func $alloc (param $size i32) (result i32)
  (local $cls i32) (local $blk i32) (local $old i32) (local $new i32)
  ;; class = (size-1) >> 4
  local.get $size
  i32.const 1
  i32.sub
  i32.const 4
  i32.shr_u
  local.set $cls
  ;; pooled path: class < 6 AND freelist non-empty
  local.get $cls
  i32.const 6
  i32.lt_u
  if (result i32)
    local.get $cls
    i32.const 4
    i32.mul
    i32.load
    local.set $blk
    local.get $blk
    if (result i32)
      ;; pop: freelist[cls] = blk.next; rc reset to 1
      local.get $cls
      i32.const 4
      i32.mul
      local.get $blk
      i32.load
      i32.store
      local.get $blk
      i32.const 1
      i32.store
      local.get $blk
    else
      ;; empty class → bump
      global.get $heap
      local.set $old
      global.get $heap
      local.get $size
      i32.add
      global.set $heap
      ;; grow past the page end
      global.get $heap
      global.get $heap-end
      i32.gt_u
      if
        i32.const 1
        memory.grow
        i32.const -1
        i32.eq
        if
          unreachable ;; OOM: memory.grow failed
        end
        global.get $heap-end
        i32.const 65536
        i32.add
        global.set $heap-end
      end
      ;; init header: rc = 1, class byte
      local.get $old
      i32.const 1
      i32.store
      local.get $old
      local.get $cls
      i32.store8 offset=5
      local.get $old
    end
  else
    ;; oversized (class ≥ 6): bump, class byte marks never-free
    global.get $heap
    local.set $old
    global.get $heap
    local.get $size
    i32.add
    global.set $heap
    global.get $heap
    global.get $heap-end
    i32.gt_u
    if
      i32.const 1
      memory.grow
      i32.const -1
      i32.eq
      if
        unreachable ;; OOM
      end
      global.get $heap-end
      i32.const 65536
      i32.add
      global.set $heap-end
    end
    local.get $old
    i32.const 1
    i32.store
    local.get $old
    i32.const 255
    i32.store8 offset=5
    local.get $old
  end
)

(func $rc_inc (param $p i32)
  local.get $p
  local.get $p
  i32.load
  i32.const 1
  i32.add
  i32.store
)

(func $rc_dec (param $p i32)
  (local $rc i32) (local $cls i32)
  local.get $p
  local.get $p
  i32.load
  i32.const 1
  i32.sub
  local.tee $rc
  i32.store
  ;; rc == 0 → return the block to its class pool
  local.get $rc
  if
    local.get $p
    i32.load8_u offset=5
    local.set $cls
    ;; p.next = freelist[cls]
    local.get $p
    local.get $cls
    i32.const 4
    i32.mul
    i32.load
    i32.store
    ;; freelist[cls] = p
    local.get $cls
    i32.const 4
    i32.mul
    local.get $p
    i32.store
  end
)

;; ── guestlang-std strings ──────────────────────────────────────────
;; Layout: {rc@0, tag=250@4, len u32@8, bytes@16} — variable-size
;; object, bytes INLINE (RC frees the whole string; no byte leak).
;; Byte-length semantics (== Lean's char length on ASCII only).

(func $string_len (param $s i32) (result i64)
  local.get $s
  i32.load offset=8
  i64.extend_i32_u)

(func $string_cat (param $a i32) (param $b i32) (result i32)
  (local $na i32) (local $nb i32) (local $p i32)
  local.get $a
  i32.load offset=8
  local.set $na
  local.get $b
  i32.load offset=8
  local.set $nb
  ;; alloc 16 + na + nb
  i32.const 16
  local.get $na
  i32.add
  local.get $nb
  i32.add
  call $alloc
  local.set $p
  ;; tag = 250
  local.get $p
  i32.const 250
  i32.store8 offset=4
  ;; len = na + nb
  local.get $p
  local.get $na
  local.get $nb
  i32.add
  i32.store offset=8
  ;; copy a's bytes: dst = p+16
  local.get $p
  i32.const 16
  i32.add
  local.get $a
  i32.const 16
  i32.add
  local.get $na
  memory.copy
  ;; copy b's bytes: dst = p+16+na
  local.get $p
  i32.const 16
  i32.add
  local.get $na
  i32.add
  local.get $b
  i32.const 16
  i32.add
  local.get $nb
  memory.copy
  local.get $p)
