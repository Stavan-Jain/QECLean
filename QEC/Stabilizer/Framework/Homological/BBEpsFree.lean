import QEC.Stabilizer.Framework.Homological.BBDeckTower
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.LinearAlgebra.Basis.Basic

/-!
# `EpsFree` for chain rings and free extensions

`BBDeckTower.EpsFree ε N` says that an element killed by `ε ^ t` is a multiple
of `ε ^ (N - t)`. It is the ring hypothesis of
`BBDeckTower.eps_mem_of_deckTrivial`, and its case `N = 4`, `t = 1` is the
annihilator hypothesis `Ann(ε) = (ε ^ 3)` of
`BocksteinLift.bockstein_element_form`. This file provides the two general
sources of `EpsFree`:

- `epsFree_quot_pow_of_monic`: in the chain ring `R[X] ⧸ (f ^ N)` with `f`
  monic, the class of `f` is `EpsFree` of order `N`; `epsFree_quotXpow` is the
  case `f = X`;
- `epsFree_of_free`: `EpsFree` passes from a ring `Λ` to any commutative
  `Λ`-algebra that is free as a `Λ`-module;

together with `hann_of_epsFree`, which extracts the annihilator hypothesis from
`EpsFree ε 4`, and `two_eq_zero_of_algebra`.
-/

namespace Quantum
namespace Stabilizer
namespace Homological
namespace BBEpsFree

open Polynomial BBDeckTower

/-- If `2 = 0` in `k` then `2 = 0` in every `k`-algebra. -/
lemma two_eq_zero_of_algebra {k : Type*} (A : Type*) [CommSemiring k] [Semiring A]
    [Algebra k A] (h2 : (2 : k) = 0) : (2 : A) = 0 := by
  rw [← map_ofNat (algebraMap k A) 2, h2, map_zero]

/-- In `R[X] ⧸ (f ^ N)` with `f` monic, the class of `f` is `EpsFree` of order
`N`: `f ^ t` is monic, hence a non-zero-divisor of `R[X]`, so it cancels from
`f ^ t * p = f ^ N * r`. -/
theorem epsFree_quot_pow_of_monic {R : Type*} [CommRing R] {f : R[X]} (hf : f.Monic)
    (N : ℕ) : EpsFree (Ideal.Quotient.mk (Ideal.span {f ^ N}) f) N := by
  intro t _ htN x hx
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [← map_pow, ← map_mul, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at hx
  obtain ⟨r, hr⟩ := hx
  have hp : p = f ^ (N - t) * r := (hf.pow t).isRegular.left <|
    show f ^ t * p = f ^ t * (f ^ (N - t) * r) by
      rw [hr, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' htN]
  exact ⟨Ideal.Quotient.mk _ r, by rw [hp, ← map_pow, ← map_mul]⟩

/-- In the chain ring `R[X] ⧸ (X ^ N)`, the class of `X` is `EpsFree` of order
`N`, over any commutative base ring `R`. -/
theorem epsFree_quotXpow {R : Type*} [CommRing R] (N : ℕ) :
    EpsFree (Ideal.Quotient.mk (Ideal.span {(X : R[X]) ^ N}) X) N :=
  epsFree_quot_pow_of_monic monic_X N

/-- `EpsFree` passes to free extensions: if `S` is a commutative `Λ`-algebra
that is free as a `Λ`-module and `ε₀ : Λ` is `EpsFree` of order `N`, then so is
its image in `S`. In a `Λ`-basis, `ε₀ ^ t` kills `x` iff it kills every
coordinate of `x`, and each coordinate is then a multiple of `ε₀ ^ (N - t)`. -/
theorem epsFree_of_free {Λ S : Type*} [CommRing Λ] [CommRing S] [Algebra Λ S]
    [Module.Free Λ S] {ε₀ : Λ} {N : ℕ} (hΛ : EpsFree ε₀ N) :
    EpsFree (algebraMap Λ S ε₀) N := by
  classical
  intro t ht1 htN x hx
  set b := Module.Free.chooseBasis Λ S
  have hcoord : ∀ i, ε₀ ^ t * b.repr x i = 0 := fun i => by
    rw [← smul_eq_mul, ← Finsupp.smul_apply, ← map_smul, Algebra.smul_def, map_pow, hx,
      map_zero, Finsupp.zero_apply]
  choose y hy using fun i => hΛ t ht1 htN (b.repr x i) (hcoord i)
  refine ⟨∑ i ∈ (b.repr x).support, y i • b i, ?_⟩
  conv_lhs => rw [← b.linearCombination_repr x]
  rw [Finsupp.linearCombination_apply, Finsupp.sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [hy i, mul_smul, Algebra.smul_def, map_pow]

/-- `EpsFree ε 4` at `t = 1` is the annihilator hypothesis `Ann(ε) = (ε ^ 3)`
of `BocksteinLift.bockstein_element_form`. -/
theorem hann_of_epsFree {S : Type*} [CommRing S] {ε : S} (h : EpsFree ε 4) :
    ∀ w : S, ε * w = 0 → ∃ v, w = ε ^ 3 * v := fun w hw => by
  simpa using h 1 le_rfl (by norm_num) w (by rwa [pow_one])

end BBEpsFree
end Homological
end Stabilizer
end Quantum
