import QEC.Stabilizer.Framework.Homological.BZCertificate
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open scoped BigOperators
namespace Quantum.Stabilizer.Homological

variable {Q J M : Type*} [DecidableEq Q] [AddCommMonoid M]

/-- Additive dual witnesses exclude every low-overflow solution when they annihilate
all on-support columns and cover every admissible off-support subset. -/
theorem no_solution_of_dual_cover
    (cols : Q → M) (rhs : M) (support : Finset Q) (cap : ℕ)
    (dual : J → M →+ ZMod 2)
    (on_support : ∀ j q, q ∈ support → dual j (cols q) = 0)
    (cover : ∀ t : Finset Q, Disjoint t support → t.card ≤ cap →
      ∃ j, dual j rhs = 1 ∧ ∑ q ∈ t, dual j (cols q) = 0)
    (u : Finset Q) (small : (u \ support).card ≤ cap) :
    ∑ q ∈ u, cols q ≠ rhs := by
  intro heq
  obtain ⟨j, hr, hz⟩ := cover (u \ support) Finset.sdiff_disjoint small
  have hsum : ∑ q ∈ u \ support, dual j (cols q) = ∑ q ∈ u, dual j (cols q) := by
    apply Finset.sum_subset Finset.sdiff_subset
    intro q hqu hqn
    apply on_support j q
    simpa only [Finset.mem_sdiff, hqu, true_and, not_not] using hqn
  have hd := congrArg (dual j) heq
  rw [map_sum] at hd
  rw [← hsum, hz, hr] at hd
  exact zero_ne_one hd

/-- A single annihilator witness excludes a flat lift. -/
theorem no_flat_solution_of_dual
    (cols : Q → M) (rhs : M) (support : Finset Q)
    (dual : M →+ ZMod 2)
    (on_support : ∀ q, q ∈ support → dual (cols q) = 0)
    (hit_rhs : dual rhs = 1)
    (u : Finset Q) (small : u ⊆ support) :
    ∑ q ∈ u, cols q ≠ rhs := by
  intro heq
  have hd := congrArg dual heq
  rw [map_sum, Finset.sum_eq_zero (fun q hq => on_support q (small hq)), hit_rhs] at hd
  exact zero_ne_one hd

/-- Dual witnesses certify completeness of a listed family of off-support subsets;
this also permits witnesses whose value on the right-hand side is zero. -/
theorem off_support_mem_of_dual_cover
    (cols : Q → M) (rhs : M) (support : Finset Q) (cap : ℕ)
    (dual : J → M →+ ZMod 2) (allowed : Finset (Finset Q))
    (on_support : ∀ j q, q ∈ support → dual j (cols q) = 0)
    (cover : ∀ t : Finset Q, Disjoint t support → t.card ≤ cap →
      t ∉ allowed → ∃ j, dual j rhs ≠ ∑ q ∈ t, dual j (cols q))
    (u : Finset Q) (small : (u \ support).card ≤ cap)
    (solution : ∑ q ∈ u, cols q = rhs) :
    u \ support ∈ allowed := by
  by_contra hn
  obtain ⟨j, hj⟩ := cover (u \ support) Finset.sdiff_disjoint small hn
  have hsum : ∑ q ∈ u \ support, dual j (cols q) = ∑ q ∈ u, dual j (cols q) := by
    apply Finset.sum_subset Finset.sdiff_subset
    intro q hqu hqn
    apply on_support j q
    simpa only [Finset.mem_sdiff, hqu, true_and, not_not] using hqn
  have hd := congrArg (dual j) solution
  rw [map_sum] at hd
  exact hj (hd.symm.trans hsum.symm)

end Quantum.Stabilizer.Homological
