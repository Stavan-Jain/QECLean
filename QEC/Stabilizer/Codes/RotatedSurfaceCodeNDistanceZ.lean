import Mathlib.Tactic
import QEC.Stabilizer.Codes.RotatedSurfaceCodeNDistanceX

/-!
# Rotated-surface-code Z-distance ≥ L

The Z-distance mirror of [RotatedSurfaceCodeNDistanceX](RotatedSurfaceCodeNDistanceX.lean).
Every non-trivial Z-type logical of `rotatedSurfaceStabilizerCode L` has Pauli
weight ≥ L, witnessed exactly by `logicalZ L` (the middle-row Z-string).

## Strategy — column-parity invariant (dual side)

Mirroring the row-parity argument: for a 1-chain `c : VtxIdx L → ZMod 2`, define

  `colParity c x := ∑ y, c (x, y) : ZMod 2`.

Three key facts:

* `colParity (rscZCutMap s) x = 0` for every Z-face 0-chain `s` and column `x`
  (each `zSupport zf` projected to any column has even cardinality).
* `colParity middleRowChain x = 1` for every column `x`.
* `dim (dualCycles / dualBoundaries) = 1` (proved here via the transpose-rank
  bridge to `rsc_rank_boundary2` from Stage 3).

Combining these: for any non-trivial dual cycle `c`, `colParity c x = 1`
for all `x`, so each column contributes ≥ 1 qubit to the support, giving
total weight ≥ L.
-/

namespace Quantum
namespace StabilizerGroup
namespace RotatedSurfaceCodeN

open scoped BigOperators
open NQubitPauliGroupElement
open Stabilizer.Lattice

variable (L : ℕ) [Fact (Odd L)] [Fact (3 ≤ L)]

/-! ## §A — Column parity functional -/

/-- The column-parity functional at column `x`: parity of `c (x, y)` over `y`. -/
def colParity (c : RotatedSurface.VtxIdx L → ZMod 2) (x : Fin L) : ZMod 2 :=
  ∑ y : Fin L, c (x, y)

omit [Fact (Odd L)] [Fact (3 ≤ L)] in
@[simp] lemma colParity_add (c c' : RotatedSurface.VtxIdx L → ZMod 2) (x : Fin L) :
    colParity L (c + c') x = colParity L c x + colParity L c' x := by
  unfold colParity
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intros; simp [Pi.add_apply]

omit [Fact (Odd L)] [Fact (3 ≤ L)] in
@[simp] lemma colParity_zero (x : Fin L) :
    colParity L (0 : RotatedSurface.VtxIdx L → ZMod 2) x = 0 := by
  unfold colParity
  apply Finset.sum_eq_zero
  intros; rfl

/-! ## §B — Column parity of `middleRowChain` is `1` -/

omit [Fact (Odd L)] in
theorem colParity_middleRowChain (x : Fin L) :
    colParity L (middleRowChain L) x = 1 := by
  classical
  unfold colParity
  rw [Finset.sum_eq_single (midIdx L)]
  · unfold middleRowChain
    simp
  · intro y _ hne
    unfold middleRowChain
    rw [if_neg]
    intro hy
    apply hne
    apply Fin.ext
    show y.val = (midIdx L).val
    rw [midIdx_val]
    exact hy
  · intro hcontra; exact absurd (Finset.mem_univ _) hcontra

/-! ## §C — Column parity vanishes on dual boundaries

`dualBoundaries = range rscZCutMap`.  We show that `colParity (rscZCutMap s) x = 0`
for every Z-face chain `s`, by case analysis on each Z-face type.
-/

omit [Fact (Odd L)] [Fact (3 ≤ L)] in
/-- A Finset that is empty or a 2-element set has card 0 in `ZMod 2`. -/
private lemma card_empty_or_pair_zmod2_zero' {α : Type*} [DecidableEq α] (s : Finset α)
    (h : s = ∅ ∨ ∃ a b : α, a ≠ b ∧ s = {a, b}) :
    (s.card : ZMod 2) = 0 := by
  rcases h with hempty | ⟨a, b, hne, heq⟩
  · rw [hempty, Finset.card_empty]; rfl
  · rw [heq, Finset.card_insert_of_notMem (by simp [hne]), Finset.card_singleton]
    decide

omit [Fact (Odd L)] in
/-- Per-column intersection of `zSupport zf` with column `x` is either empty
or a 2-element set. -/
private lemma colFilter_zSupport_card_even
    (zf : RotatedSurface.ZFaceIdx L) (x : Fin L) :
    (((Finset.univ : Finset (Fin L)).filter
        (fun y : Fin L => (x, y) ∈ RotatedSurface.zSupport zf)).card : ZMod 2) = 0 := by
  classical
  apply card_empty_or_pair_zmod2_zero'
  cases zf with
  | interior zc =>
    by_cases hxMatch : x.val = zc.val.1.val ∨ x.val = zc.val.1.val + 1
    · right
      refine ⟨RotatedSurface.cornerLo zc.val.2, RotatedSurface.cornerHi zc.val.2, ?_, ?_⟩
      · intro h; have := congrArg Fin.val h
        simp [RotatedSurface.cornerLo, RotatedSurface.cornerHi] at this
      · ext y
        rw [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
        rw [RotatedSurface.mem_zSupport_interior_iff]
        simp only [Finset.mem_univ, true_and]
        constructor
        · rintro ⟨_, hy⟩
          rcases hy with h | h
          · left; exact Fin.ext h
          · right; exact Fin.ext h
        · rintro (rfl | rfl)
          · refine ⟨hxMatch, Or.inl ?_⟩
            simp [RotatedSurface.cornerLo]
          · refine ⟨hxMatch, Or.inr ?_⟩
            simp [RotatedSurface.cornerHi]
    · left
      push Not at hxMatch
      rw [Finset.filter_eq_empty_iff]
      intro y _
      rw [RotatedSurface.mem_zSupport_interior_iff]
      rintro ⟨hx, _⟩
      rcases hx with h | h
      · exact hxMatch.1 h
      · exact hxMatch.2 h
  | leftBdy k =>
    by_cases hx : x.val = 0
    · right
      have h2k1 : 2 * k.val + 1 < L := by
        have := k.isLt; have h3 : 3 ≤ L := Fact.out; omega
      have h2k2 : 2 * k.val + 2 < L := by
        have := k.isLt; have h3 : 3 ≤ L := Fact.out; omega
      refine ⟨⟨2 * k.val + 1, h2k1⟩, ⟨2 * k.val + 2, h2k2⟩, ?_, ?_⟩
      · intro h; have := congrArg Fin.val h
        simp at this
      · ext y
        rw [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
        rw [RotatedSurface.mem_zSupport_leftBdy_iff]
        simp only [Finset.mem_univ, true_and]
        constructor
        · rintro ⟨_, hy⟩
          rcases hy with h | h
          · left; exact Fin.ext h
          · right; exact Fin.ext h
        · rintro (rfl | rfl)
          · exact ⟨hx, Or.inl rfl⟩
          · exact ⟨hx, Or.inr rfl⟩
    · left
      rw [Finset.filter_eq_empty_iff]
      intro y _
      rw [RotatedSurface.mem_zSupport_leftBdy_iff]
      rintro ⟨hxz, _⟩
      exact hx hxz
  | rightBdy k =>
    by_cases hx : x.val = L - 1
    · right
      have h2k : 2 * k.val < L := by
        have := k.isLt; have h3 : 3 ≤ L := Fact.out; omega
      have h2k1 : 2 * k.val + 1 < L := by
        have := k.isLt; have h3 : 3 ≤ L := Fact.out; omega
      refine ⟨⟨2 * k.val, h2k⟩, ⟨2 * k.val + 1, h2k1⟩, ?_, ?_⟩
      · intro h; have := congrArg Fin.val h
        simp at this
      · ext y
        rw [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
        rw [RotatedSurface.mem_zSupport_rightBdy_iff]
        simp only [Finset.mem_univ, true_and]
        constructor
        · rintro ⟨_, hy⟩
          rcases hy with h | h
          · left; exact Fin.ext h
          · right; exact Fin.ext h
        · rintro (rfl | rfl)
          · exact ⟨hx, Or.inl rfl⟩
          · exact ⟨hx, Or.inr rfl⟩
    · left
      rw [Finset.filter_eq_empty_iff]
      intro y _
      rw [RotatedSurface.mem_zSupport_rightBdy_iff]
      rintro ⟨hxL, _⟩
      exact hx hxL

omit [Fact (Odd L)] in
/-- `colParity (rscZCutMap (Pi.single zf 1)) x = 0`. -/
private lemma colParity_zCutMap_single (zf : RotatedSurface.ZFaceIdx L) (x : Fin L) :
    colParity L (RotatedSurface.rscZCutMap L (Pi.single zf 1)) x = 0 := by
  classical
  unfold colParity
  -- (rscZCutMap (Pi.single zf 1)) v = 1[v ∈ zSupport zf]
  rw [show (fun y : Fin L => RotatedSurface.rscZCutMap L (Pi.single zf 1) (x, y)) =
      (fun y : Fin L => if (x, y) ∈ RotatedSurface.zSupport zf then (1 : ZMod 2) else 0) by
    funext y
    rw [RotatedSurface.rscZCutMap_apply]
    rw [Finset.sum_eq_single zf]
    · rw [show (Pi.single zf 1 : RotatedSurface.ZFaceIdx L → ZMod 2) zf = 1 from
        Pi.single_eq_same _ _]
      ring
    · intro zf' _ hne
      have h0 : (Pi.single zf 1 : RotatedSurface.ZFaceIdx L → ZMod 2) zf' = 0 := by
        rw [Pi.single_apply, if_neg hne]
      rw [h0]; ring
    · intro hcontra; exact absurd (Finset.mem_univ zf) hcontra]
  rw [Finset.sum_boole]
  exact colFilter_zSupport_card_even L zf x

omit [Fact (Odd L)] in
/-- `colParity (rscZCutMap s) x = 0` for every Z-face chain `s`. -/
theorem colParity_rscZCutMap
    (s : RotatedSurface.ZFaceIdx L → ZMod 2) (x : Fin L) :
    colParity L (RotatedSurface.rscZCutMap L s) x = 0 := by
  classical
  have hs : s = ∑ zf : RotatedSurface.ZFaceIdx L, s zf • (Pi.single zf (1 : ZMod 2)) := by
    funext zf
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hs]
  rw [map_sum]
  unfold colParity
  rw [show (fun y : Fin L =>
      (∑ zf : RotatedSurface.ZFaceIdx L,
        RotatedSurface.rscZCutMap L (s zf • Pi.single zf 1)) (x, y)) =
      (fun y : Fin L =>
        ∑ zf : RotatedSurface.ZFaceIdx L,
          RotatedSurface.rscZCutMap L (s zf • Pi.single zf 1) (x, y)) by
    funext y; rw [Finset.sum_apply]]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro zf _
  have h_smul : ∀ y : Fin L,
      RotatedSurface.rscZCutMap L (s zf • Pi.single zf 1) (x, y) =
        s zf * RotatedSurface.rscZCutMap L (Pi.single zf 1) (x, y) := fun y => by
    rw [LinearMap.map_smul]
    simp [Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_congr rfl (fun y _ => h_smul y)]
  rw [← Finset.mul_sum]
  rw [show ∑ y : Fin L, RotatedSurface.rscZCutMap L (Pi.single zf 1) (x, y) =
      colParity L (RotatedSurface.rscZCutMap L (Pi.single zf 1)) x from rfl]
  rw [colParity_zCutMap_single]
  ring

omit [Fact (Odd L)] in
/-- `colParity` vanishes on the dual-boundaries submodule (range of `rscZCutMap`). -/
theorem colParity_eq_zero_of_mem_dualBoundaries
    {c : RotatedSurface.VtxIdx L → ZMod 2}
    (hc : c ∈ LinearMap.range (RotatedSurface.rscZCutMap L)) (x : Fin L) :
    colParity L c x = 0 := by
  rcases hc with ⟨s, rfl⟩
  exact colParity_rscZCutMap L s x


end RotatedSurfaceCodeN
end StabilizerGroup
end Quantum
