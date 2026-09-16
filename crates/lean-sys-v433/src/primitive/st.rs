/*! ST Ref primitives

4.33 (lean.h:2972-2976): the upstream `lean_st_mk_ref_*` names never existed —
the header's real entry points are `lean_st_mk_ref` / `lean_st_ref_*`, and the
world argument is gone. Symbol presence verified against `libleanrt.a`:
`lean_st_ref_reset` is DECLARED in lean.h but DEFINED nowhere in the shipped
v4.33.0 libs — calling it is a link error (see lean-compat.md).
*/
use crate::*;

extern "C" {
    pub fn lean_st_mk_ref(_: lean_obj_arg) -> lean_obj_res;
    pub fn lean_st_ref_get(_: b_lean_obj_arg) -> lean_obj_res;
    pub fn lean_st_ref_set(_: b_lean_obj_arg, _: lean_obj_arg) -> lean_obj_res;
    /// Declared in lean.h at 4.33 but not defined in any shipped library.
    pub fn lean_st_ref_reset(_: b_lean_obj_arg) -> lean_obj_res;
    pub fn lean_st_ref_swap(_: b_lean_obj_arg, _: lean_obj_arg) -> lean_obj_res;
}
