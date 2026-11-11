import QEC.Stabilizer.Framework.Homological.BBDoubling

/-!
# Cover cycles over a flat boundary

Let `D : XDoubleCoverData G H` be a free double cover of bivariate bicycle
codes, with pushforward `p = push1`, pullback `τ = pull1` and deck translation
`σ = deckShift1` on 1-chains. A cover 1-chain `c` is *flat* when no fiber of the
projection contains two points of its support; this is stated as
`sheet0 c j ≠ 0 → p c j ≠ 0` for every base qubit `j`.

For a flat cover boundary `c`, the cover cycles `v` with `p v = p c` are
controlled by base cycles: `v + c` has zero pushforward, so it is `τ u` for the
base cycle `u = sheet0 v + sheet0 c`, and flatness makes the weights add up
exactly.

## Main statements

* `exists_paired_cycle_of_flat_boundary`: `v + c = τ u` for a base cycle `u`
  with `|u| + |u + p c| = |v|`.
* `exists_light_cycle_of_flat_boundary`: if `|v| ≤ 2 * w + 1`, then `v + c` or
  `σ v + c` is the pullback of a base cycle of weight at most `w`. This reduces
  a search over light cover cycles to one over light base cycles.
* `chainWeight_ge_double_of_flat_boundary`: if every base cycle that is not a
  boundary has weight at least `d` and `v` is not a cover boundary, then
  `|v| ≥ 2 * d`. This bounds the cycles of the dangerous sector of the doubling
  theorem that lie over the base boundary `p c`.
-/

namespace Quantum
namespace Stabilizer
namespace Homological
namespace BB

open scoped BigOperators

/-- For chains `a`, `b`, `c` with the support of `c` contained in that of `b`,
`|a + c| + |a + c + b| = |b| + 2 * |supp a \ supp b|`: a point of the support of
`b` lies in exactly one of the two supports on the left, and a point outside it
lies in both or in neither according to `a`. -/
lemma paired_weight_eq {I : Type} [Fintype I]
    (a b c : I → ZMod 2) (hc : ∀ i, c i ≠ 0 → b i ≠ 0) :
    (Finset.univ.filter fun i => (a + c) i ≠ 0).card
        + (Finset.univ.filter fun i => (a + c + b) i ≠ 0).card
      = (Finset.univ.filter fun i => b i ≠ 0).card
        + 2 * (Finset.univ.filter fun i => a i ≠ 0 ∧ b i = 0).card := by
  have key : ∀ a b c : ZMod 2, (c ≠ 0 → b ≠ 0) →
      ((if a + c ≠ 0 then 1 else 0) + (if a + c + b ≠ 0 then 1 else 0) : ℕ)
        = (if b ≠ 0 then 1 else 0) + 2 * (if a ≠ 0 ∧ b = 0 then 1 else 0) := by
    decide
  simp only [Finset.card_filter, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => key (a i) (b i) (c i) (hc i)

namespace XDoubleCoverData

variable {G H : Type}
  [Fintype G] [AddCommGroup G] [DecidableEq G]
  [Fintype H] [AddCommGroup H] [DecidableEq H]
  (D : XDoubleCoverData G H)

/-- A cover 1-chain with zero pushforward is the pullback of its restriction to
sheet 0. -/
lemma pull1_sheet0_of_push1_eq_zero {w : G × Fin 2 → ZMod 2} (hw : D.push1 w = 0) :
    D.pull1 (D.sheet0 w) = w := by
  obtain ⟨u, rfl⟩ := (D.push1_eq_zero_iff w).mp hw
  rw [D.sheet0_pull1]

/-- Let `c` be a flat cover boundary and `v` a cover cycle with `p v = p c`.
Then `v + c = τ u` for a base cycle `u` with `|u| + |u + p c| = |v|`. -/
theorem exists_paired_cycle_of_flat_boundary
    {c v : G × Fin 2 → ZMod 2}
    (hc : c ∈ D.coverComplex.boundaries)
    (hflat : ∀ j, D.sheet0 c j ≠ 0 → D.push1 c j ≠ 0)
    (hv : v ∈ D.coverComplex.cycles)
    (hpush : D.push1 v = D.push1 c) :
    ∃ u : H × Fin 2 → ZMod 2,
      u ∈ D.baseComplex.cycles ∧ v + c = D.pull1 u ∧
      D.baseComplex.chainWeight u + D.baseComplex.chainWeight (u + D.push1 c)
        = D.coverComplex.chainWeight v := by
  have hu : D.pull1 (D.sheet0 (v + c)) = v + c :=
    D.pull1_sheet0_of_push1_eq_zero (by rw [map_add, hpush, ZModModule.add_self])
  refine ⟨D.sheet0 (v + c), D.descend_cycle ?_, hu.symm, ?_⟩
  · rw [hu]
    exact add_mem hv (D.coverComplex.boundaries_le_cycles hc)
  · rw [D.chainWeight_sheet_eq, hpush]
    exact paired_weight_eq (D.sheet0 v) (D.push1 c) (D.sheet0 c) hflat

/-- Let `c` be a flat cover boundary and `v` a cover cycle with `p v = p c` and
`|v| ≤ 2 * w + 1`. Then `v + c` or `σ v + c` is the pullback of a base cycle of
weight at most `w`: of the two base cycles `u` and `u + p c` of
`exists_paired_cycle_of_flat_boundary`, one has weight at most `w`. -/
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
    rw [map_add, ← hu, ← hpush, D.pull1_push1, add_add_add_comm, ZModModule.add_self, zero_add,
      add_comm]

/-- Let `c` be a flat cover boundary and `v` a cover cycle with `p v = p c`
that is not a cover boundary. If every base cycle that is not a boundary has
weight at least `d`, then `|v| ≥ 2 * d`: neither of the base cycles `u` and
`u + p c` of `exists_paired_cycle_of_flat_boundary` is a boundary. -/
theorem chainWeight_ge_double_of_flat_boundary {d : ℕ}
    (hbase : D.LogicalFloor d)
    {c v : G × Fin 2 → ZMod 2}
    (hc : c ∈ D.coverComplex.boundaries)
    (hflat : ∀ j, D.sheet0 c j ≠ 0 → D.push1 c j ≠ 0)
    (hv : v ∈ D.coverComplex.cycles)
    (hnb : v ∉ D.coverComplex.boundaries)
    (hpush : D.push1 v = D.push1 c) :
    2 * d ≤ D.coverComplex.chainWeight v := by
  obtain ⟨u, huc, hu, hweights⟩ :=
    D.exists_paired_cycle_of_flat_boundary hc hflat hv hpush
  have hb := D.push1_mem_boundaries hc
  have hunb : u ∉ D.baseComplex.boundaries := fun h =>
    hnb ((Submodule.add_mem_iff_left _ hc).mp (hu ▸ D.pull1_mem_boundaries h))
  have h₁ := hbase u huc hunb
  have h₂ := hbase (u + D.push1 c) (add_mem huc (D.baseComplex.boundaries_le_cycles hb))
    fun h => hunb ((Submodule.add_mem_iff_left _ hb).mp h)
  omega

end XDoubleCoverData

end BB
end Homological
end Stabilizer
end Quantum
