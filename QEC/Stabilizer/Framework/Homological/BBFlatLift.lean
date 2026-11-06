import QEC.Stabilizer.Framework.Homological.BBDoubling
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

namespace Quantum.Stabilizer.Homological.BB.XDoubleCoverData
open scoped BigOperators
variable {G H : Type}
  [Fintype G] [AddCommGroup G] [DecidableEq G]
  [Fintype H] [AddCommGroup H] [DecidableEq H]
  (D : XDoubleCoverData G H)

/-- Adding a chain supported inside a shadow preserves its paired weight. -/
lemma paired_weight_eq {I : Type} [Fintype I]
    (a b c : I → ZMod 2) (hc : ∀ i, c i ≠ 0 → b i ≠ 0) :
    (Finset.univ.filter fun i => (a + c) i ≠ 0).card +
        (Finset.univ.filter fun i => (a + c + b) i ≠ 0).card =
      (Finset.univ.filter fun i => b i ≠ 0).card +
        2 * (Finset.univ.filter fun i => a i ≠ 0 ∧ b i = 0).card := by
  classical
  have hpoint : ∀ i,
      (if (a + c) i ≠ 0 then (1 : ℕ) else 0) +
          (if (a + c + b) i ≠ 0 then 1 else 0) =
        (if b i ≠ 0 then 1 else 0) +
          2 * (if a i ≠ 0 ∧ b i = 0 then 1 else 0) := by
    intro i
    have key : ∀ a b c : ZMod 2, (c ≠ 0 → b ≠ 0) →
        (if a + c ≠ 0 then (1 : ℕ) else 0) +
            (if a + c + b ≠ 0 then 1 else 0) =
          (if b ≠ 0 then 1 else 0) +
            2 * (if a ≠ 0 ∧ b = 0 then 1 else 0) := by decide
    exact key (a i) (b i) (c i) (hc i)
  have hs := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ)
    rfl (fun i _ => hpoint i)
  simpa only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_boole, Nat.cast_id] using hs

/-- A cycle over a flat boundary is a paired base cycle with exactly the same total weight. -/
theorem exists_paired_cycle_of_flat_boundary
    {c v : G × Fin 2 → ZMod 2}
    (hc : c ∈ D.coverComplex.boundaries)
    (hflat : ∀ j, D.sheet0 c j ≠ 0 → D.push1 c j ≠ 0)
    (hv : v ∈ D.coverComplex.cycles)
    (hpush : D.push1 v = D.push1 c) :
    ∃ u : H × Fin 2 → ZMod 2,
      u ∈ D.baseComplex.cycles ∧ v + c = D.pull1 u ∧
      D.baseComplex.chainWeight u + D.baseComplex.chainWeight (u + D.push1 c) =
        D.coverComplex.chainWeight v := by
  classical
  have hzero : D.push1 (v + c) = 0 := by
    rw [map_add, hpush]
    funext j
    exact CharTwo.add_self_eq_zero _
  obtain ⟨u, hu⟩ := (D.push1_eq_zero_iff _).mp hzero
  have huc : u ∈ D.baseComplex.cycles := by
    apply D.descend_cycle
    rw [← hu]
    exact add_mem hv (D.coverComplex.boundaries_le_cycles hc)
  refine ⟨u, huc, hu, ?_⟩
  have hu0 : u = D.sheet0 v + D.sheet0 c := by
    have hh := congrArg D.sheet0 hu
    rw [D.sheet0_pull1] at hh
    exact hh.symm
  rw [D.chainWeight_sheet_eq, hpush, D.baseComplex_chainWeight_eq,
    D.baseComplex_chainWeight_eq, D.baseComplex_chainWeight_eq, hu0]
  exact paired_weight_eq (D.sheet0 v) (D.push1 c) (D.sheet0 c) hflat

/-- Up to swapping sheets, a light lift of a flat boundary comes from a base cycle
of at most half its weight. This replaces a large lift search by a small-cycle census. -/
theorem exists_light_cycle_of_flat_boundary {w : ℕ}
    {c v : G × Fin 2 → ZMod 2}
    (hc : c ∈ D.coverComplex.boundaries)
    (hflat : ∀ j, D.sheet0 c j ≠ 0 → D.push1 c j ≠ 0)
    (hv : v ∈ D.coverComplex.cycles)
    (hpush : D.push1 v = D.push1 c)
    (hweight : D.coverComplex.chainWeight v ≤ 2 * w + 1) :
    ∃ u : H × Fin 2 → ZMod 2,
      u ∈ D.baseComplex.cycles ∧ D.baseComplex.chainWeight u ≤ w ∧
      (v + c = D.pull1 u ∨ D.deckShift1 v + c = D.pull1 u) := by
  obtain ⟨u, huc, hu, hweights⟩ :=
    D.exists_paired_cycle_of_flat_boundary hc hflat hv hpush
  by_cases hlight : D.baseComplex.chainWeight u ≤ w
  · exact ⟨u, huc, hlight, Or.inl hu⟩
  · refine ⟨u + D.push1 c, add_mem huc
      (D.baseComplex.boundaries_le_cycles (D.push1_mem_boundaries hc)), by omega, Or.inr ?_⟩
    rw [map_add, ← hu, ← hpush, D.pull1_push1]
    funext j
    simp only [Pi.add_apply]
    have hself : v j + v j = 0 := CharTwo.add_self_eq_zero _
    linear_combination -hself

/-- A flat boundary lift gives a doubled logical distance floor for its shadow. -/
theorem chainWeight_ge_double_of_flat_boundary {d : ℕ}
    (hbase : D.LogicalFloor d)
    {c v : G × Fin 2 → ZMod 2}
    (hc : c ∈ D.coverComplex.boundaries)
    (hflat : ∀ j, D.sheet0 c j ≠ 0 → D.push1 c j ≠ 0)
    (hv : v ∈ D.coverComplex.cycles)
    (hnb : v ∉ D.coverComplex.boundaries)
    (hpush : D.push1 v = D.push1 c) :
    2 * d ≤ D.coverComplex.chainWeight v := by
  classical
  have hzero : D.push1 (v + c) = 0 := by
    rw [map_add, hpush]
    funext j
    exact CharTwo.add_self_eq_zero _
  obtain ⟨u, hu⟩ := (D.push1_eq_zero_iff _).mp hzero
  have huc : u ∈ D.baseComplex.cycles := by
    apply D.descend_cycle
    rw [← hu]
    exact add_mem hv (D.coverComplex.boundaries_le_cycles hc)
  have hunb : u ∉ D.baseComplex.boundaries := by
    intro hb
    apply hnb
    have hm : v + c ∈ D.coverComplex.boundaries := by
      rw [hu]
      exact D.pull1_mem_boundaries hb
    have hcancel : v = v + c + c := by
      funext j
      simp only [Pi.add_apply, add_assoc, CharTwo.add_self_eq_zero, add_zero]
    rw [hcancel]
    exact add_mem hm hc
  have hb : D.push1 c ∈ D.baseComplex.boundaries := D.push1_mem_boundaries hc
  have hubc : u + D.push1 c ∈ D.baseComplex.cycles :=
    add_mem huc (D.baseComplex.boundaries_le_cycles hb)
  have hubnb : u + D.push1 c ∉ D.baseComplex.boundaries := by
    intro hub
    apply hunb
    have hcancel : u = u + D.push1 c + D.push1 c := by
      funext j
      simp only [Pi.add_apply, add_assoc, CharTwo.add_self_eq_zero, add_zero]
    rw [hcancel]
    exact add_mem hub hb
  have hu0 : u = D.sheet0 v + D.sheet0 c := by
    have hh := congrArg D.sheet0 hu
    rw [D.sheet0_pull1] at hh
    exact hh.symm
  have hweights : D.baseComplex.chainWeight u +
      D.baseComplex.chainWeight (u + D.push1 c) = D.coverComplex.chainWeight v := by
    rw [D.chainWeight_sheet_eq, hpush, D.baseComplex_chainWeight_eq,
      D.baseComplex_chainWeight_eq, D.baseComplex_chainWeight_eq, hu0]
    exact paired_weight_eq (D.sheet0 v) (D.push1 c) (D.sheet0 c) hflat
  have hleft := hbase u huc hunb
  have hright := hbase (u + D.push1 c) hubc hubnb
  omega

#print axioms chainWeight_ge_double_of_flat_boundary
end Quantum.Stabilizer.Homological.BB.XDoubleCoverData
