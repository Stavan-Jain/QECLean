import QEC.Stabilizer.Framework.Homological.BocksteinLift
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# `EpsFree` for group algebras

Let `k` be a commutative ring, `G` an abelian group and `σ : G`, and write
`x^g` for the basis element `AddMonoidAlgebra.single g 1` of the group algebra
`k[G]`. This file proves `BBDeckTower.EpsFree` for the deck element of `k[G]`:

- `epsFree_single_sub_one_of_transversal`: if `(i, j) ↦ t i + j • σ` is a
  bijection `T × Fin N → G` and `(x^σ - 1) ^ N = 0`, then `x^σ - 1` is `EpsFree`
  of order `N`. Indeed `k[G]` is an algebra over the chain ring
  `Λ = k[X] ⧸ ((X - 1) ^ N)` with `X` acting as `x^σ`, the family `x^(t i)` is a
  `Λ`-basis (`span_transversal_eq_top`, `linearIndependent_transversal`), and
  `epsFree_of_free` transports `epsFree_quot_pow_of_monic` along it.
- `epsFree_one_add_single_of_addOrderOf`: if `2 = 0` in `k` and `σ` has order
  `2 ^ r`, then `1 + x^σ` is `EpsFree` of order `2 ^ r`. The transversal is
  `Quotient.out` on `G ⧸ ⟨σ⟩` (`transversal_out_bijective`).
- `bockstein_element_form_group_algebra`: for `σ` of order four,
  `BocksteinLift.bockstein_element_form` holds in `k[G] ⧸ ((1 + x^σ) ^ 2)`
  with no further hypothesis.
-/

namespace Quantum
namespace Stabilizer
namespace Homological
namespace BBEpsFree

open Polynomial BBDeckTower

/-! ## Frobenius in characteristic two -/

/-- If `2 = 0` in `A` then `(a + b) ^ 2 ^ r = a ^ 2 ^ r + b ^ 2 ^ r`; no `CharP`
instance is needed, so this also covers the zero ring. -/
lemma add_pow_two_pow_of_two_eq_zero {A : Type*} [CommRing A]
    (h2 : (2 : A) = 0) (a b : A) (r : ℕ) :
    (a + b) ^ 2 ^ r = a ^ 2 ^ r + b ^ 2 ^ r := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [pow_succ 2 r, pow_mul, pow_mul, pow_mul, ih, add_sq, h2, zero_mul, zero_mul, add_zero]

/-! ## Orbit sums in the group algebra -/

section GroupAlgebra

variable {k : Type*} [CommRing k] {G : Type*} [AddCommGroup G]

/-- `(x^σ) ^ j = x^(j • σ)`. -/
lemma single_pow_one (σ : G) (j : ℕ) :
    (AddMonoidAlgebra.single σ (1 : k)) ^ j
      = AddMonoidAlgebra.single (j • σ) 1 := by
  rw [AddMonoidAlgebra.single_pow, one_pow]

/-- A polynomial `q` of degree below `N`, evaluated at `x^σ` and multiplied by
`c · x^g`, is the orbit sum `∑ j < N, (q.coeff j * c) · x^(g + j • σ)`. -/
lemma aeval_single_mul_single (σ g : G) (c : k) {q : k[X]} {N : ℕ}
    (hq : q.natDegree < N) :
    aeval (AddMonoidAlgebra.single σ (1 : k)) q * AddMonoidAlgebra.single g c
      = ∑ j ∈ Finset.range N,
          AddMonoidAlgebra.single (g + j • σ) (q.coeff j * c) := by
  rw [aeval_eq_sum_range' hq, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [smul_mul_assoc, single_pow_one, AddMonoidAlgebra.single_mul_single,
    AddMonoidAlgebra.smul_single', one_mul, add_comm (j • σ) g]

/-- If `(i, j) ↦ t i + j • σ` is injective on `T × Fin N`, then the coefficient
of the double orbit sum `∑ i ∈ s, ∑ j < N, c i j · x^(t i + j • σ)` at
`t i₀ + m • σ`, for `i₀ ∈ s` and `m < N`, is `c i₀ m`. -/
lemma sum_sum_single_orbit_apply {T : Type*} {σ : G} {N : ℕ} (t : T → G)
    (hinj : Function.Injective fun p : T × Fin N => t p.1 + (p.2 : ℕ) • σ)
    (s : Finset T) (c : T → ℕ → k) {i₀ : T} (hi₀ : i₀ ∈ s) {m : ℕ} (hm : m < N) :
    (∑ i ∈ s, ∑ j ∈ Finset.range N, Finsupp.single (t i + j • σ) (c i j) : G →₀ k)
        (t i₀ + m • σ) = c i₀ m := by
  classical
  have key : ∀ i, ∀ j ∈ Finset.range N, t i + j • σ = t i₀ + m • σ → i = i₀ ∧ j = m :=
    fun i j hj h => by
      simpa using hinj (a₁ := (i, ⟨j, Finset.mem_range.mp hj⟩)) (a₂ := (i₀, ⟨m, hm⟩)) h
  rw [Finsupp.finsetSum_apply, Finset.sum_eq_single_of_mem i₀ hi₀, Finsupp.finsetSum_apply,
    Finset.sum_eq_single_of_mem m (Finset.mem_range.mpr hm), Finsupp.single_eq_same]
  · intro j hj hjm
    rw [Finsupp.single_apply, if_neg fun h => hjm (key i₀ j hj h).2]
  · intro i _ hi
    rw [Finsupp.finsetSum_apply]
    exact Finset.sum_eq_zero fun j hj => by
      rw [Finsupp.single_apply, if_neg fun h => hi (key i j hj h).1]

end GroupAlgebra

/-! ## The transversal basis

Here `Λ = k[X] ⧸ ((X - 1) ^ N)` acts on `k[G]` through an algebra structure
with `X` acting as `x^σ` (hypothesis `halg`), and `t : T → G` is a family such
that `(i, j) ↦ t i + j • σ` is a bijection `T × Fin N → G`. The family
`i ↦ x^(t i)` then spans `k[G]` over `Λ` and is linearly independent. -/

section Transversal

variable {k : Type*} [CommRing k] {G : Type*} [AddCommGroup G] {σ : G} {N : ℕ}
variable [Algebra (AdjoinRoot ((X - C 1 : k[X]) ^ N)) (AddMonoidAlgebra k G)]

/-- If every element of `G` is of the form `t i + j • σ`, the family `x^(t i)`
spans `k[G]` over `Λ`: `c · x^(t i + j • σ)` is `(c * X ^ j) • x^(t i)`. -/
lemma span_transversal_eq_top
    (halg : ∀ p : k[X],
      algebraMap (AdjoinRoot ((X - C 1 : k[X]) ^ N)) (AddMonoidAlgebra k G)
          (AdjoinRoot.mk _ p)
        = aeval (AddMonoidAlgebra.single σ (1 : k)) p)
    {T : Type*} (t : T → G)
    (hsurj : Function.Surjective fun p : T × Fin N => t p.1 + (p.2 : ℕ) • σ) :
    ⊤ ≤ Submodule.span (AdjoinRoot ((X - C 1 : k[X]) ^ N))
        (Set.range fun i => AddMonoidAlgebra.single (t i) (1 : k)) := by
  intro s _
  rw [← AddMonoidAlgebra.sum_single s]
  refine Submodule.finsuppSum_mem _ _ _ _ fun g _ => ?_
  obtain ⟨⟨i, j⟩, hij⟩ := hsurj g
  have key : AdjoinRoot.mk ((X - C 1 : k[X]) ^ N) (C (s g) * X ^ (j : ℕ)) •
      AddMonoidAlgebra.single (t i) (1 : k) = AddMonoidAlgebra.single g (s g) := by
    rw [Algebra.smul_def, halg, map_mul, aeval_C, map_pow, aeval_X, single_pow_one, mul_assoc,
      AddMonoidAlgebra.single_mul_single, one_mul, ← Algebra.smul_def,
      AddMonoidAlgebra.smul_single', mul_one, add_comm, ← hij]
  rw [← key]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

/-- If `(i, j) ↦ t i + j • σ` is injective on `T × Fin N`, the family `x^(t i)`
is linearly independent over `Λ`. Each coefficient of a linear relation has a
representative `P i : k[X]` of degree below `N`; the relation then reads
`∑ i, ∑ j < N, (P i).coeff j · x^(t i + j • σ) = 0`, and comparing coefficients
gives `P i = 0`. -/
lemma linearIndependent_transversal
    (halg : ∀ p : k[X],
      algebraMap (AdjoinRoot ((X - C 1 : k[X]) ^ N)) (AddMonoidAlgebra k G)
          (AdjoinRoot.mk _ p)
        = aeval (AddMonoidAlgebra.single σ (1 : k)) p)
    (hN : 0 < N) {T : Type*} (t : T → G)
    (hinj : Function.Injective fun p : T × Fin N => t p.1 + (p.2 : ℕ) • σ) :
    LinearIndependent (AdjoinRoot ((X - C 1 : k[X]) ^ N))
      fun i => AddMonoidAlgebra.single (t i) (1 : k) := by
  classical
  rcases subsingleton_or_nontrivial k with hk | hk
  · haveI : Subsingleton (AdjoinRoot ((X - C 1 : k[X]) ^ N)) :=
      AdjoinRoot.mk_surjective.subsingleton
    exact linearIndependent_of_subsingleton
  have hg : ((X - C 1 : k[X]) ^ N).Monic := (monic_X_sub_C 1).pow N
  have hgN : ((X - C 1 : k[X]) ^ N).natDegree = N := by
    rw [(monic_X_sub_C 1).natDegree_pow, natDegree_X_sub_C, mul_one]
  rw [linearIndependent_iff]
  intro l hl
  -- representatives of degree below `N` of the coefficients `l i`
  have hrep : ∀ i, ∃ P : k[X], AdjoinRoot.mk _ P = l i ∧ P.natDegree < N := fun i => by
    obtain ⟨Q, hQ⟩ := AdjoinRoot.mk_surjective (l i)
    refine ⟨Q %ₘ (X - C 1) ^ N, ?_, ?_⟩
    · rw [← hQ, ← AdjoinRoot.modByMonicHom_mk hg]
      exact AdjoinRoot.mk_leftInverse hg _
    · have h := natDegree_modByMonic_lt Q hg (hg.natDegree_pos.mp (by rwa [hgN]))
      rwa [hgN] at h
  choose P hmk hdeg using hrep
  -- the linear relation, expanded along the orbits of `σ`
  have hsum : ∑ i ∈ l.support, ∑ j ∈ Finset.range N,
      AddMonoidAlgebra.single (t i + j • σ) ((P i).coeff j)
      = (0 : AddMonoidAlgebra k G) := by
    rw [← hl, Finsupp.linearCombination_apply, Finsupp.sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hmk i, Algebra.smul_def, halg, aeval_single_mul_single σ (t i) 1 (hdeg i)]
    simp only [mul_one]
  ext i₀
  by_cases hi₀ : i₀ ∈ l.support
  swap
  · exact Finsupp.notMem_support_iff.mp hi₀
  have hP : P i₀ = 0 := by
    ext m
    rw [coeff_zero]
    rcases lt_or_ge m N with hm | hm
    · have h : (∑ i ∈ l.support, ∑ j ∈ Finset.range N,
          Finsupp.single (t i + j • σ) ((P i).coeff j) : G →₀ k) (t i₀ + m • σ)
          = (0 : G →₀ k) (t i₀ + m • σ) :=
        congrArg (fun v : G →₀ k => v (t i₀ + m • σ)) hsum
      rwa [sum_sum_single_orbit_apply t hinj l.support _ hi₀ hm, Finsupp.zero_apply] at h
    · exact coeff_eq_zero_of_natDegree_lt ((hdeg i₀).trans_le hm)
  rw [Finsupp.zero_apply, ← hmk i₀, hP, map_zero]

end Transversal

/-! ## `EpsFree` in the group algebra -/

/-- If `(i, j) ↦ t i + j • σ` is a bijection `T × Fin N → G` and
`(x^σ - 1) ^ N = 0`, then `x^σ - 1` is `EpsFree` of order `N` in `k[G]`: the
group algebra is free on `x^(t i)` over the chain ring `k[X] ⧸ ((X - 1) ^ N)`,
with `X` acting as `x^σ`. -/
theorem epsFree_single_sub_one_of_transversal
    {k : Type*} [CommRing k] {G : Type*} [AddCommGroup G] {σ : G} {N : ℕ}
    (hN : 0 < N)
    (hεN : (AddMonoidAlgebra.single σ (1 : k) - 1) ^ N = 0)
    {T : Type*} (t : T → G)
    (he : Function.Bijective fun p : T × Fin N => t p.1 + (p.2 : ℕ) • σ) :
    EpsFree (AddMonoidAlgebra.single σ (1 : k) - 1) N := by
  have hev : ((X - C 1 : k[X]) ^ N).eval₂ (algebraMap k (AddMonoidAlgebra k G))
      (AddMonoidAlgebra.single σ (1 : k)) = 0 := by
    rw [eval₂_pow, eval₂_sub, eval₂_X, eval₂_C, map_one, hεN]
  letI : Algebra (AdjoinRoot ((X - C 1 : k[X]) ^ N)) (AddMonoidAlgebra k G) :=
    (AdjoinRoot.lift (algebraMap k (AddMonoidAlgebra k G))
      (AddMonoidAlgebra.single σ (1 : k)) hev).toAlgebra
  have halg : ∀ p : k[X],
      algebraMap (AdjoinRoot ((X - C 1 : k[X]) ^ N)) (AddMonoidAlgebra k G)
          (AdjoinRoot.mk _ p)
        = aeval (AddMonoidAlgebra.single σ (1 : k)) p := fun p => by
    rw [RingHom.algebraMap_toAlgebra, AdjoinRoot.lift_mk, aeval_def]
  letI : Module.Free (AdjoinRoot ((X - C 1 : k[X]) ^ N)) (AddMonoidAlgebra k G) :=
    Module.Free.of_basis (Module.Basis.mk
      (linearIndependent_transversal halg hN t he.injective)
      (span_transversal_eq_top halg t he.surjective))
  have h : EpsFree (algebraMap (AdjoinRoot ((X - C 1 : k[X]) ^ N)) (AddMonoidAlgebra k G)
      (AdjoinRoot.mk _ (X - C 1))) N :=
    epsFree_of_free (epsFree_quot_pow_of_monic (monic_X_sub_C 1) N)
  rwa [halg, map_sub, aeval_X, aeval_C, map_one] at h

/-! ## The transversal `Quotient.out` -/

/-- For `σ` of order `N > 0`, the map `(q, j) ↦ q.out + j • σ` is a bijection
`(G ⧸ ⟨σ⟩) × Fin N → G`. -/
lemma transversal_out_bijective {G : Type*} [AddCommGroup G] (σ : G) {N : ℕ}
    (hord : addOrderOf σ = N) (hN : 0 < N) :
    Function.Bijective
      fun p : (G ⧸ AddSubgroup.zmultiples σ) × Fin N =>
        Quotient.out p.1 + (p.2 : ℕ) • σ := by
  subst hord
  refine ⟨?_, fun g => ?_⟩
  · rintro ⟨q, j⟩ ⟨q', j'⟩ h
    have h' : Quotient.out q + (j : ℕ) • σ = Quotient.out q' + (j' : ℕ) • σ := h
    have hq : q = q' := by
      have h2 := congrArg (QuotientAddGroup.mk (s := AddSubgroup.zmultiples σ)) h'
      rwa [QuotientAddGroup.mk_add_of_mem _ (AddSubgroup.nsmul_mem_zmultiples σ _),
        QuotientAddGroup.mk_add_of_mem _ (AddSubgroup.nsmul_mem_zmultiples σ _),
        QuotientAddGroup.out_eq', QuotientAddGroup.out_eq'] at h2
    subst hq
    exact Prod.ext rfl (Fin.ext (nsmul_injOn_Iio_addOrderOf j.2 j'.2 (add_left_cancel h')))
  · obtain ⟨h, hh⟩ := QuotientAddGroup.mk_out_eq_mul (AddSubgroup.zmultiples σ) g
    obtain ⟨j, hj⟩ := (finEquivZMultiples (addOrderOf_pos_iff.mp hN)).surjective (-h)
    refine ⟨(QuotientAddGroup.mk g, j), ?_⟩
    have hj' : (j : ℕ) • σ = -(h : G) := congrArg Subtype.val hj
    change Quotient.out (QuotientAddGroup.mk g) + (j : ℕ) • σ = g
    rw [hj', hh, add_neg_cancel_right]

/-! ## Deck elements of order `2 ^ r` -/

/-- If `2 = 0` in `k` and `σ` has order `2 ^ r`, then `1 + x^σ` is `EpsFree` of
order `2 ^ r` in `k[G]`. -/
theorem epsFree_one_add_single_of_addOrderOf
    {k : Type*} [CommRing k] (h2 : (2 : k) = 0)
    {G : Type*} [AddCommGroup G] (σ : G) (r : ℕ)
    (hord : addOrderOf σ = 2 ^ r) :
    EpsFree (1 + AddMonoidAlgebra.single σ (1 : k)) (2 ^ r) := by
  have h2S : (2 : AddMonoidAlgebra k G) = 0 := two_eq_zero_of_algebra _ h2
  have hswap : 1 + AddMonoidAlgebra.single σ (1 : k)
      = AddMonoidAlgebra.single σ (1 : k) - 1 := by linear_combination h2S
  rw [hswap]
  refine epsFree_single_sub_one_of_transversal (pow_pos two_pos r) ?_ Quotient.out
    (transversal_out_bijective σ hord (pow_pos two_pos r))
  rw [← hswap, add_pow_two_pow_of_two_eq_zero h2S, one_pow, single_pow_one, ← hord,
    addOrderOf_nsmul_eq_zero, ← AddMonoidAlgebra.one_def, one_add_one_eq_two, h2S]

/-- For `σ` of order four over a base ring with `2 = 0`, and `ε = 1 + x^σ`:
in `k[G] ⧸ (ε ^ 2)`, whenever `A * z = ε * a` and `B * z = ε * b`, the element
`A * b + B * a` lies in `(ε * A, ε * B)`. This is
`BocksteinLift.bockstein_element_form`, whose annihilator hypothesis is
supplied by `epsFree_one_add_single_of_addOrderOf`. -/
theorem bockstein_element_form_group_algebra
    {k : Type*} [CommRing k] (h2 : (2 : k) = 0)
    {G : Type*} [AddCommGroup G] (σ : G) (hord : addOrderOf σ = 4)
    (A B : AddMonoidAlgebra k G)
    (z a b : AddMonoidAlgebra k G ⧸
      Ideal.span {(1 + AddMonoidAlgebra.single σ (1 : k)) ^ 2})
    (hAz : Ideal.Quotient.mk _ A * z
      = Ideal.Quotient.mk _ (1 + AddMonoidAlgebra.single σ (1 : k)) * a)
    (hBz : Ideal.Quotient.mk _ B * z
      = Ideal.Quotient.mk _ (1 + AddMonoidAlgebra.single σ (1 : k)) * b) :
    Ideal.Quotient.mk _ A * b + Ideal.Quotient.mk _ B * a ∈
      Ideal.span
        {Ideal.Quotient.mk (Ideal.span {(1 + AddMonoidAlgebra.single σ (1 : k)) ^ 2})
            (1 + AddMonoidAlgebra.single σ (1 : k)) * Ideal.Quotient.mk _ A,
          Ideal.Quotient.mk (Ideal.span {(1 + AddMonoidAlgebra.single σ (1 : k)) ^ 2})
            (1 + AddMonoidAlgebra.single σ (1 : k)) * Ideal.Quotient.mk _ B} :=
  BocksteinLift.bockstein_element_form _ A B (two_eq_zero_of_algebra _ h2)
    (hann_of_epsFree (epsFree_one_add_single_of_addOrderOf h2 σ 2 hord)) z a b hAz hBz

end BBEpsFree
end Homological
end Stabilizer
end Quantum
