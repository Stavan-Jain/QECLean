import QEC.Stabilizer.Framework.Homological.BZCertificate
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Dual witnesses excluding subset-sum solutions

Let `cols : Q → M` be a family of columns in an additive monoid and `rhs : M` a
target. A *dual witness* is an additive map `M →+ ZMod 2`; applying it to a
subset sum `∑ q ∈ u, cols q = rhs` gives an equation in `ZMod 2` that the
subset `u` must satisfy. When every witness annihilates the columns indexed by
a set `support`, that equation only involves the part of `u` outside
`support`:

* `off_support_mem_of_dual_cover`: if every small off-support subset outside a
  list `allowed` is refuted by some witness, the off-support part of every
  solution with a small off-support part is in `allowed`;
* `no_solution_of_dual_cover`: if every small off-support subset is refuted,
  there is no solution with a small off-support part;
* `no_flat_solution_of_dual`: one witness with value `1` on `rhs` excludes
  every solution inside `support`.
-/

open scoped BigOperators
namespace Quantum.Stabilizer.Homological

variable {Q J M : Type*} [AddCommMonoid M]

/-- Dual witnesses certify completeness of a listed family of off-support
subsets: if every witness annihilates the on-support columns and every
off-support subset of size at most `cap` outside `allowed` is refuted by some
witness, then the off-support part of any solution `u` is in `allowed`. -/
theorem off_support_mem_of_dual_cover [DecidableEq Q]
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
  refine hj ?_
  rw [← solution, map_sum]
  exact (Finset.sum_subset Finset.sdiff_subset fun q hqu hqn =>
    on_support j q (by simpa [hqu] using hqn)).symm

/-- Dual witnesses exclude every solution with a small off-support part: if
every witness annihilates the on-support columns and every off-support subset
of size at most `cap` has a witness with value `1` on `rhs` and `0` on the
subset sum, then no `u` with `(u \ support).card ≤ cap` sums to `rhs`. -/
theorem no_solution_of_dual_cover [DecidableEq Q]
    (cols : Q → M) (rhs : M) (support : Finset Q) (cap : ℕ)
    (dual : J → M →+ ZMod 2)
    (on_support : ∀ j q, q ∈ support → dual j (cols q) = 0)
    (cover : ∀ t : Finset Q, Disjoint t support → t.card ≤ cap →
      ∃ j, dual j rhs = 1 ∧ ∑ q ∈ t, dual j (cols q) = 0)
    (u : Finset Q) (small : (u \ support).card ≤ cap) :
    ∑ q ∈ u, cols q ≠ rhs := fun heq =>
  Finset.notMem_empty _ <|
    off_support_mem_of_dual_cover cols rhs support cap dual ∅ on_support
      (fun t ht hc _ => by
        obtain ⟨j, hr, hz⟩ := cover t ht hc
        exact ⟨j, by rw [hr, hz]; exact one_ne_zero⟩) u small heq

/-- A single witness that annihilates the on-support columns and has value `1`
on `rhs` excludes every solution contained in `support`. -/
theorem no_flat_solution_of_dual
    (cols : Q → M) (rhs : M) (support : Finset Q)
    (dual : M →+ ZMod 2)
    (on_support : ∀ q, q ∈ support → dual (cols q) = 0)
    (hit_rhs : dual rhs = 1)
    (u : Finset Q) (small : u ⊆ support) :
    ∑ q ∈ u, cols q ≠ rhs := by
  intro heq
  have hd := congrArg dual heq
  rw [map_sum, Finset.sum_eq_zero fun q hq => on_support q (small hq), hit_rhs] at hd
  exact zero_ne_one hd

end Quantum.Stabilizer.Homological
