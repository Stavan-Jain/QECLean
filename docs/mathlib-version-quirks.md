# Mathlib version drift quirks

Workarounds and renamings encountered during mathlib version bumps in
this repo. Entries are grouped by the mathlib version where the quirk
was first observed.

**Maintenance**: when you hit a mathlib API quirk during proof work, add
a one-line entry to the appropriate version section (or create a new
section if a fresh bump just landed). Date the entry by when you
verified it. Once a quirk is no longer triggerable (e.g. you upgraded
past the deprecation window and the legacy form is gone), move the
entry to a `## Resolved` section at the bottom rather than deleting it
— the historical record helps with future bisection.

This file is intentionally less compact than `CLAUDE.md` because
version-specific knowledge ages quickly and isn't worth the
must-read-on-every-invocation cost.

---

## v4.30 (verified 2026-05-24)

- `Subgroup.normalizer` takes `Set G`, not `Subgroup G` — no dot notation.
  Write `Subgroup.normalizer S.toSubgroup` not `S.toSubgroup.normalizer`.
- `simp [ZMod, ← even_iff_two_dvd]` no longer turns `(c : ZMod 2) = 0` into
  `Even c`. Use `Finset.sum_boole` + `ZMod.natCast_eq_zero_iff_even` instead.
- `Matrix.mulVec_smul` rewrites can fail to unify when scalar type and
  matrix-entry type differ (`ℝ` vs `ℂ`). Workaround: wrap in an explicit
  `show ∀ (M : Matrix _ _ ℂ) (b : ℝ) (w : NQubitVec n), M.mulVec (b • w) =
  b • M.mulVec w from fun _ _ _ => Matrix.mulVec_smul _ _ _`.
- `push_neg` is deprecated — prefer `push Not`.
- mathlib's `Matrix.mul_eq_one_comm`, `Matrix.isUnit_of_right_inverse` are
  deprecated; use `mul_eq_one_comm` and `IsUnit.of_mul_eq_one`.
  **Signature gotcha**: `IsUnit.of_mul_eq_one` is `(b : M) (h : a * b = 1)`
  — the right-hand operand is explicit. For a square `h_mul : M * M = 1`
  write `IsUnit.of_mul_eq_one M h_mul`, not `IsUnit.of_mul_eq_one h_mul`.
- `Finset.filter_union_filter_neg_eq` → `Finset.filter_union_filter_not_eq`
  (`neg` → `not`). Same renaming on `Finset.disjoint_filter_filter_neg` →
  `Finset.disjoint_filter_filter_not`.
- `Nat.xor_cancel_left` / `Nat.xor_cancel_right` don't exist under those
  names — they're in Batteries as `Nat.xor_xor_cancel_left` /
  `Nat.xor_xor_cancel_right` (note the extra `xor_`). Used in
  `QuantumHamming.lean`'s involution proof.
- `Prod.mk.inj_iff` is gone — use `Prod.mk_inj`.
- `((List.finRange L).product (List.finRange L)).length = L * L` doesn't
  reduce by `simp` directly. Workaround: `unfold List.product; simp [List.length_flatMap]`.
- The `List.countP_eq_count_of_decide_iff`, `List.countP_add_countP_eq_length`,
  `List.length_filter_eq_countP` family doesn't exist (or moved). For
  `(L.filter p).length` arithmetic, route through `List.toFinset_card_of_nodup`
  (when the list is `Nodup`) and `Finset.card_erase_of_mem` — see
  `coordsTrimmed_length` in `ToricCodeNStabilizerCode.lean` for the pattern.
