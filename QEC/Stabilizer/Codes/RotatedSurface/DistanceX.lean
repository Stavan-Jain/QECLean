import QEC.Stabilizer.Codes.RotatedSurface.StabilizerCode

/-!
# X-distance of the rotated surface code

Every cycle of the rotated surface code that is not a boundary has weight at
least `L` (`chainWeight_ge_L_of_nontrivial`), and the logical X operator, the
X-string on the middle column, has weight exactly `L` (`logicalX_weight_eq_L`).

The bound is an instance of a parity argument that also gives the Z-distance,
`Homological.card_le_card_support_of_fiber_parity`. Let `B ≤ Z` be spaces of
`ZMod 2`-valued chains with `dim Z ≤ dim B + 1`, and let the cells be
partitioned into lines, the fibers of a map `π`. If every element of `B` has
an even number of cells on every line, and some element of `Z` has an odd
number of cells on every line, then so has every element of `Z` outside `B`
(`Homological.apply_ne_zero_of_finrank_le_succ`), which therefore has at least
as many cells as there are lines
(`Homological.card_le_card_support_of_fiber_sum_ne_zero`).

Here the lines are the rows of the grid. A combination of X-checks has an even
number of qubits in every row (`sum_row_rscBoundary2`), the middle column
`middleColChain L` has one (`sum_row_middleColChain`), and the boundaries have
codimension one in the cycles (`rsc_finrank_cycles_eq_boundaries_add_one`).
-/

namespace Quantum
namespace Stabilizer
namespace Homological

open scoped Homology

/-! ## A weight bound from line parities -/

/-- A linear functional that vanishes on a subspace `B` of codimension at most
one in `Z`, but not on all of `Z`, is nonzero at every element of `Z` outside
`B`: its kernel in `Z` is a proper subspace containing `B`, hence equal to
`B`. -/
lemma apply_ne_zero_of_finrank_le_succ {K M : Type*} [DivisionRing K] [AddCommGroup M]
    [Module K M] [FiniteDimensional K M] {Z B : Submodule K M} (hBZ : B ≤ Z)
    (hdim : Module.finrank K Z ≤ Module.finrank K B + 1) (ψ : M →ₗ[K] K)
    (hB : ∀ b ∈ B, ψ b = 0) {m : M} (hm : m ∈ Z) (hψm : ψ m ≠ 0)
    {c : M} (hc : c ∈ Z) (hcB : c ∉ B) : ψ c ≠ 0 := by
  have hlt : Z ⊓ LinearMap.ker ψ < Z :=
    lt_of_le_of_ne inf_le_left fun h => hψm (LinearMap.mem_ker.1 (h.ge hm).2)
  have hBK : B = Z ⊓ LinearMap.ker ψ :=
    Submodule.eq_of_le_of_finrank_le (le_inf hBZ fun b hb => LinearMap.mem_ker.2 (hB b hb))
      (by have := Submodule.finrank_lt_finrank_of_lt hlt; omega)
  exact fun h => hcB (hBK.ge ⟨hc, LinearMap.mem_ker.2 h⟩)

/-- A `ZMod 2`-valued chain with an odd number of cells on every fiber of `π`
has at least as many cells as `π` has fibers. -/
lemma card_le_card_support_of_fiber_sum_ne_zero {V κ : Type*} [Fintype V] [Fintype κ]
    [DecidableEq κ] (π : V → κ) {c : V → ZMod 2} (h : ∀ y, ∑ v with π v = y, c v ≠ 0) :
    Fintype.card κ ≤ (Finset.univ.filter fun v => c v ≠ 0).card := by
  rw [← Finset.card_univ]
  refine Finset.card_le_card_of_surjOn π fun y _ => ?_
  obtain ⟨v, hv, hcv⟩ := Finset.exists_ne_zero_of_sum_ne_zero (h y)
  exact ⟨v, by simpa using hcv, (Finset.mem_filter.1 hv).2⟩

/-- **Line-parity bound.** Let `B ≤ Z` be spaces of `ZMod 2`-valued chains
with `dim Z ≤ dim B + 1`, and call the fibers of `π` lines. If every chain in
`B` has an even number of cells on every line and some chain `m` in `Z` has an
odd number of cells on every line, then so has every chain in `Z` outside `B`,
whose support therefore has at least as many cells as there are lines. -/
theorem card_le_card_support_of_fiber_parity {V κ : Type*} [Fintype V] [Fintype κ]
    [DecidableEq κ] (π : V → κ) {Z B : Submodule (ZMod 2) (V → ZMod 2)} (hBZ : B ≤ Z)
    (hdim : dim₂ Z ≤ dim₂ B + 1) (hB : ∀ b ∈ B, ∀ y, ∑ v with π v = y, b v = 0)
    {m : V → ZMod 2} (hm : m ∈ Z) (hm1 : ∀ y, ∑ v with π v = y, m v = 1)
    {c : V → ZMod 2} (hc : c ∈ Z) (hcB : c ∉ B) :
    Fintype.card κ ≤ (Finset.univ.filter fun v => c v ≠ 0).card := by
  refine card_le_card_support_of_fiber_sum_ne_zero π fun y => ?_
  let ψ : (V → ZMod 2) →ₗ[ZMod 2] ZMod 2 := ∑ v with π v = y, LinearMap.proj v
  have hψ : ∀ a, ψ a = ∑ v with π v = y, a v := fun a => by simp [ψ]
  have h := apply_ne_zero_of_finrank_le_succ hBZ hdim ψ (fun b hb => (hψ b).trans (hB b hb y))
    hm (by rw [hψ, hm1]; exact one_ne_zero) hc hcB
  rwa [hψ] at h

end Homological
end Stabilizer

namespace StabilizerGroup
namespace RotatedSurfaceCodeN

open scoped Homology RotatedSurfaceChain
open NQubitPauliGroupElement Stabilizer.Homological Stabilizer.Lattice.RotatedSurface

variable (L : ℕ) [Fact (Odd L)] [Fact (3 ≤ L)]

/-! ## The middle column -/

omit [Fact (Odd L)] in
/-- The middle column has exactly one qubit in every row. -/
lemma sum_row_middleColChain (y : Fin L) :
    ∑ v : VtxIdx L with v.2 = y, middleColChain L v = 1 := by
  rw [Finset.sum_eq_single_of_mem (midIdx L, y) (by simp)]
  · simp [middleColChain]
  · rintro ⟨a, b⟩ hv hne
    obtain rfl : b = y := by simpa using hv
    exact if_neg fun h => hne (Prod.ext (Fin.ext h) rfl)

omit [Fact (Odd L)] [Fact (3 ≤ L)] in
/-- A boundary has an even number of qubits in every row. -/
lemma sum_row_eq_zero_of_mem_boundaries {c : VtxIdx L → ZMod 2} (hc : c ∈ B₁ L) (y : Fin L) :
    ∑ v : VtxIdx L with v.2 = y, c v = 0 := by
  obtain ⟨f, rfl⟩ := hc
  exact sum_row_rscBoundary2 L f y

omit [Fact (Odd L)] in
/-- The middle column is not a boundary: it has one qubit in every row, and a
boundary an even number. -/
theorem middleColChain_not_mem_boundaries : middleColChain L ∉ B₁ L := fun h =>
  one_ne_zero <| (sum_row_middleColChain L (midIdx L)).symm.trans
    (sum_row_eq_zero_of_mem_boundaries L h (midIdx L))

/-! ## The weight of a nontrivial cycle -/

/-- A cycle that is not a boundary has weight at least `L`: it has a qubit in
every row, by `card_le_card_support_of_fiber_parity` applied to the rows. -/
theorem chainWeight_ge_L_of_nontrivial {c : VtxIdx L → ZMod 2} (hc : c ∈ Z₁ L)
    (hcB : c ∉ B₁ L) : L ≤ (rotatedSurfaceHomologicalCode L).chainWeight c :=
  (Fintype.card_fin L).ge.trans <|
    card_le_card_support_of_fiber_parity (Prod.snd : VtxIdx L → Fin L)
      (rscBoundaries_le_rscCycles L) rsc_finrank_cycles_eq_boundaries_add_one.le
      (fun _ hb y => sum_row_eq_zero_of_mem_boundaries L hb y)
      (middleColChain_mem_cycles L) (sum_row_middleColChain L) hc hcB

/-! ## The logical X operator -/

/-- The logical X operator is a nontrivial logical operator of the homological
stabilizer group: the middle column is a cycle and not a boundary. -/
theorem logicalX_isNontrivialLogicalOperator :
    IsNontrivialLogicalOperator (logicalX L)
      (rotatedSurfaceHomologicalCode L).homologicalStabilizerGroup :=
  (HomologicalCode.chainXOperator_isNontrivialLogical_iff _).2
    ⟨middleColChain_mem_cycles L, middleColChain_not_mem_boundaries L⟩

/-- The logical X operator has weight `L`: it acts on the `L` qubits of the
middle column. -/
theorem logicalX_weight_eq_L : weight (logicalX L) = L := by
  have h : (Finset.univ.filter fun v : VtxIdx L => middleColChain L v ≠ 0) =
      {midIdx L} ×ˢ Finset.univ := by
    ext ⟨a, b⟩
    simp [middleColChain, Fin.ext_iff, eq_comm]
  exact (HomologicalCode.weight_chainXOperator (X := rotatedSurfaceHomologicalCode L) _).trans
    ((congrArg Finset.card h).trans (by simp))

end RotatedSurfaceCodeN
end StabilizerGroup
end Quantum
