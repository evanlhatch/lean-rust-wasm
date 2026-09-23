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

;; 48..256 = the canonical-ABI RETURN AREAS (static scratch: the string
;; pair @48, the option<user> tuple @56..96; single-threaded, so fixed
;; slots don't clobber) — the heap starts ABOVE the reserve.
(global $heap (mut i32) (i32.const 256))
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
      ;; empty class → bump (16-BYTE ALIGNED: the canonical ABI's list
      ;; pointers must align to the element's alignment (4..8) — an
      ;; unaligned bump (odd-size strings) fails the lift's check)
      global.get $heap
      local.set $old
      global.get $heap
      local.get $size
      i32.add
      i32.const 15
      i32.add
      i32.const 15
      i32.const -1
      i32.xor
      i32.and
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
  ;; (the guard MUST be eqz: push ONLY when the count HIT zero. An
  ;; inverted guard recycles LIVE blocks — every 2→1 decrement of a
  ;; shared/borrowed reference pushed the still-referenced block to the
  ;; freelist and the next alloc aliased it — observed as the
  ;; evalWBool? verdict corruption + the alloc fault / component wedge.)
  local.get $rc
  i32.eqz
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

;; String equality: pointer-equal fast path, length check, then a
;; byte-wise walk over the inline bytes (@16..). Result = the raw i32
;; scalar Bool convention (1/0). Byte-wise == the oracle's `a == b` on
;; ASCII (the StrOps v1 byte/char stance).
(func $string_eq (param $a i32) (param $b i32) (result i32)
  (local $na i32) (local $nb i32) (local $i i32)
  ;; the same object: equal
  local.get $a
  local.get $b
  i32.eq
  if
    i32.const 1
    return
  end
  local.get $a
  i32.load offset=8
  local.set $na
  local.get $b
  i32.load offset=8
  local.set $nb
  ;; length mismatch: not equal
  local.get $na
  local.get $nb
  i32.ne
  if
    i32.const 0
    return
  end
  ;; byte-wise compare
  i32.const 0
  local.set $i
  (loop $cmp
    ;; walked all na bytes: equal
    local.get $i
    local.get $na
    i32.eq
    if
      i32.const 1
      return
    end
    local.get $a
    local.get $i
    i32.add
    i32.load8_u offset=16
    local.get $b
    local.get $i
    i32.add
    i32.load8_u offset=16
    i32.eq
    if
      local.get $i
      i32.const 1
      i32.add
      local.set $i
      br $cmp
    end
    ;; byte differs: not equal
    i32.const 0
    return
  )
  ;; the loop never falls through (every path returns); unreachable
  ;; but stack-valid
  i32.const 0
)

;; String construction from a char list (the `String.ofList` lowering —
;; the W9.6 decode lane's string atom, Codec.decString?). The list: the
;; guest cons chain {tag=0 nil / 1 cons @4, head @8, tail @16}; each
;; head = a BOXED char (the Char structure erases to its u32 scalar —
;; payload @8). Two passes: count the UTF-8 byte length, then alloc the
;; string object {rc, tag=250 @4, len u32 @8, bytes @16} and encode.
;; UTF-8: 1/2/3/4 bytes by codepoint range (the oracle's String.ofList
;; encodes the same way; the byte/char ASCII stance of $string_len
;; does not apply here — the LENGTH is byte-exact for all of Unicode).
(func $string_oflist (param $lst i32) (result i32)
  (local $cur i32) (local $cp i32) (local $n i32) (local $p i32)
  (local $w i32) (local $tag i32)
  ;; ── pass 1: count encoded bytes ──
  local.get $lst
  local.set $cur
  (block $count-done
    (loop $count
      local.get $cur
      i32.load8_u offset=4
      i32.eqz
      br_if $count-done
      ;; cp = head box's u32 payload
      local.get $cur
      i32.load offset=8
      i32.load offset=8
      local.set $cp
      ;; +1 for cp < 0x80; +2 for < 0x800; +3 for < 0x10000; else +4
      local.get $cp
      i32.const 0x80
      i32.lt_u
      if (result i32)
        i32.const 1
      else
        local.get $cp
        i32.const 0x800
        i32.lt_u
        if (result i32)
          i32.const 2
        else
          local.get $cp
          i32.const 0x10000
          i32.lt_u
          if (result i32)
            i32.const 3
          else
            i32.const 4
          end
        end
      end
      local.set $tag
      local.get $n
      local.get $tag
      i32.add
      local.set $n
      local.get $cur
      i32.load offset=16
      local.set $cur
      br $count
    )
  )
  ;; ── alloc the string ──
  i32.const 16
  local.get $n
  i32.add
  call $alloc
  local.set $p
  local.get $p
  i32.const 250
  i32.store8 offset=4
  local.get $p
  local.get $n
  i32.store offset=8
  local.get $p
  i32.const 16
  i32.add
  local.set $w
  ;; ── pass 2: encode ──
  local.get $lst
  local.set $cur
  (block $fill-done
    (loop $fill
      local.get $cur
      i32.load8_u offset=4
      i32.eqz
      br_if $fill-done
      local.get $cur
      i32.load offset=8
      i32.load offset=8
      local.set $cp
      ;; 1 byte: 0xxxxxxx
      local.get $cp
      i32.const 0x80
      i32.lt_u
      if
        local.get $w
        local.get $cp
        i32.store8
        local.get $w
        i32.const 1
        i32.add
        local.set $w
      else
        ;; 2 bytes: 110xxxxx 10xxxxxx
        local.get $cp
        i32.const 0x800
        i32.lt_u
        if
          local.get $w
          local.get $cp
          i32.const 6
          i32.shr_u
          i32.const 0xC0
          i32.or
          i32.store8
          local.get $w
          i32.const 1
          i32.add
          local.get $cp
          i32.const 0x3F
          i32.and
          i32.const 0x80
          i32.or
          i32.store8
          local.get $w
          i32.const 2
          i32.add
          local.set $w
        else
          ;; 3 bytes: 1110xxxx 10xxxxxx 10xxxxxx
          local.get $cp
          i32.const 0x10000
          i32.lt_u
          if
            local.get $w
            local.get $cp
            i32.const 12
            i32.shr_u
            i32.const 0xE0
            i32.or
            i32.store8
            local.get $w
            i32.const 1
            i32.add
            local.get $cp
            i32.const 6
            i32.shr_u
            i32.const 0x3F
            i32.and
            i32.const 0x80
            i32.or
            i32.store8
            local.get $w
            i32.const 1
            i32.add
            local.get $cp
            i32.const 0x3F
            i32.and
            i32.const 0x80
            i32.or
            i32.store8
            local.get $w
            i32.const 3
            i32.add
            local.set $w
          else
            ;; 4 bytes: 11110xxx 10xxxxxx 10xxxxxx 10xxxxxx
            local.get $w
            local.get $cp
            i32.const 18
            i32.shr_u
            i32.const 0xF0
            i32.or
            i32.store8
            local.get $w
            i32.const 1
            i32.add
            local.get $cp
            i32.const 12
            i32.shr_u
            i32.const 0x3F
            i32.and
            i32.const 0x80
            i32.or
            i32.store8
            local.get $w
            i32.const 1
            i32.add
            local.get $cp
            i32.const 6
            i32.shr_u
            i32.const 0x3F
            i32.and
            i32.const 0x80
            i32.or
            i32.store8
            local.get $w
            i32.const 1
            i32.add
            local.get $cp
            i32.const 0x3F
            i32.and
            i32.const 0x80
            i32.or
            i32.store8
            local.get $w
            i32.const 4
            i32.add
            local.set $w
          end
        end
      end
      local.get $cur
      i32.load offset=16
      local.set $cur
      br $fill
    )
  )
  local.get $p
)
