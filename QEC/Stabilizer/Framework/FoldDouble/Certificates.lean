import QEC.Stabilizer.Framework.FoldDouble.Distance

/-!
# Certificates for condition (J): the averaging argument

Condition (J) of the fold-and-double theorem asks, for a light stabilizer fold
`b` (weight `< 2 d_K`), that `wt b + 2 m_b ≥ 2 d_K`, where the residual `m_b`
is the least weight of `(u * a) outside supp b` over the doubling logicals `u`,
for a lift `s = (a, a * b)` of `b`. This file gives the single-Pauli-type
certificates for it, all consequences of one averaging argument:

* `le_weight_restrictOutside_of_seam` — the averaging argument: if `L` is a
  finite set of X-type seam operators closed under products, with support `U`,
  then every X-type doubling logical `u` satisfies
  `wt (u outside U) ≥ d_K − ⌊|U|/2⌋`. Multiplying `u` by the elements of `L`
  keeps it a doubling logical, and on average over `L` exactly half of `U` is
  in the support of `u * l`, so some `u * l` has at most `⌊|U|/2⌋` of its
  weight inside `U`.
* `le_residualWeight_of_seam_support`, `condition_J_of_seam_support` — if
  moreover `U` contains the supports of `a` and `b`, then
  `m_b ≥ d_K − ⌊|U|/2⌋`, so (J) holds for `b` as soon as
  `⌊|U|/2⌋ ≤ ⌊wt b/2⌋`.
* `condition_J_of_two_cleanLifts` — two clean checks: if `b = b₁ * b₂` with
  `b₁, b₂ ∈ J ∩ T` having clean lifts, and `U = supp b₁ ∪ supp b₂` satisfies
  `⌊|U|/2⌋ ≤ ⌊wt b/2⌋`, then (J) holds for `b` (`L = {1, b₁, b₂, b₁ b₂}`).
* `condition_J_of_cleanLift` — one clean check: a stabilizer fold `b ∈ J ∩ T`
  with a clean lift satisfies (J) (the case `b₂ = 1`).

Everything here is for X-type operators; the Z-type statements are the same
with `X` and `Z` exchanged.
-/

namespace Quantum
namespace Stabilizer
namespace FoldDouble

open NQubitPauliOperator NQubitPauliGroupElement StabilizerGroup

variable {n m : ℕ} (e : Fin n ≃ Fin m × Fin 2) (S : StabilizerGroup n)

/-! ## Restriction to a set of qubits -/

/-- The restriction of `x` to the qubits in `U`. -/
def restrictTo (U : Finset (Fin m)) (x : NQubitPauliOperator m) : NQubitPauliOperator m :=
  fun j => if j ∈ U then x j else PauliOperator.I

/-- The restriction of `x` to the qubits outside `U`. -/
def restrictOutside (U : Finset (Fin m)) (x : NQubitPauliOperator m) : NQubitPauliOperator m :=
  fun j => if j ∈ U then PauliOperator.I else x j

@[simp] lemma restrictTo_apply (U : Finset (Fin m)) (x : NQubitPauliOperator m) (j : Fin m) :
    restrictTo U x j = if j ∈ U then x j else PauliOperator.I := rfl

@[simp] lemma restrictOutside_apply (U : Finset (Fin m)) (x : NQubitPauliOperator m)
    (j : Fin m) : restrictOutside U x j = if j ∈ U then PauliOperator.I else x j := rfl

/-- The weight splits along `U` and its complement. -/
lemma weight_eq_weight_restrictTo_add (U : Finset (Fin m)) (x : NQubitPauliOperator m) :
    weight x = weight (restrictTo U x) + weight (restrictOutside U x) := by
  simp only [weight_eq_sum, restrictTo_apply, restrictOutside_apply, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => by by_cases hj : j ∈ U <;> simp [hj]

/-- Restriction outside the support of `b` is restriction outside `supp b`. -/
lemma outsideSupport_eq_restrictOutside (b x : NQubitPauliOperator m) :
    outsideSupport b x = restrictOutside (support b) x := by
  ext j
  by_cases hj : b j = PauliOperator.I <;> simp [hj]

/-- Restricting outside a larger set gives a lighter operator. -/
lemma weight_restrictOutside_le_of_subset {U V : Finset (Fin m)} (h : U ⊆ V)
    (x : NQubitPauliOperator m) :
    weight (restrictOutside V x) ≤ weight (restrictOutside U x) := by
  simp only [weight_eq_sum, restrictOutside_apply]
  refine Finset.sum_le_sum fun j _ => ?_
  by_cases hjV : j ∈ V
  · simp [hjV]
  · simp [hjV, mt (@h j) hjV]

/-- Multiplying by an operator supported inside `U` does not change the
restriction outside `U`. -/
lemma restrictOutside_mul_of_support_subset {U : Finset (Fin m)} {x l : NQubitPauliOperator m}
    (hl : ∀ j, l j ≠ PauliOperator.I → j ∈ U) :
    restrictOutside U (x * l) = restrictOutside U x := by
  ext j
  by_cases hj : j ∈ U
  · simp [hj]
  · simp [hj, of_not_not (mt (hl j) hj), PauliOperator.mulOp_I]

/-- The weight of a restriction to `U`, as a sum over `U`. -/
lemma weight_restrictTo_eq_sum (U : Finset (Fin m)) (x : NQubitPauliOperator m) :
    weight (restrictTo U x) = ∑ j ∈ U, if x j ≠ PauliOperator.I then 1 else 0 := by
  rw [weight_eq_sum, ← Finset.sum_subset (Finset.subset_univ U)]
  · exact Finset.sum_congr rfl fun j hj => by simp [hj]
  · intro j _ hj
    simp [hj]

/-! ## Finite sets of X-type operators closed under products -/

/-- The support of a finite set of operators: the union of their supports. -/
def suppUnion (L : Finset (NQubitPauliOperator m)) : Finset (Fin m) :=
  L.sup support

lemma mem_suppUnion {L : Finset (NQubitPauliOperator m)} {j : Fin m} :
    j ∈ suppUnion L ↔ ∃ l ∈ L, l j ≠ PauliOperator.I := by
  simp only [suppUnion, Finset.mem_sup, NQubitPauliOperator.mem_support]

/-- In a finite set of X-type operators closed under products, if some element
acts at `j` then exactly half of the elements take any given X-type value at
`j`: multiplication by an element acting at `j` swaps the two fibers of
`l ↦ l j`. -/
lemma two_mul_card_filter_eq_card {L : Finset (NQubitPauliOperator m)}
    (hX : ∀ l ∈ L, IsXType l) (hmul : ∀ a ∈ L, ∀ b ∈ L, a * b ∈ L) {j : Fin m}
    {l₀ : NQubitPauliOperator m} (hl₀ : l₀ ∈ L) (hj : l₀ j = PauliOperator.X)
    {a : PauliOperator} (ha : a.IsXType) :
    2 * (L.filter fun l => l j ≠ a).card = L.card := by
  have hflip : ∀ l ∈ L, ((l₀ * l) j ≠ a ↔ l j = a) := fun l hl => by
    rw [mul_apply, hj]
    rcases hX l hl j with h | h <;> rcases ha with rfl | rfl <;> rw [h] <;> decide
  have hcard : (L.filter fun l => l j ≠ a).card = (L.filter fun l => ¬ l j ≠ a).card := by
    refine Finset.card_nbij' (l₀ * ·) (l₀ * ·) (fun l hl => ?_) (fun l hl => ?_)
      (fun l _ => mul_mul_cancel_left l₀ l) (fun l _ => mul_mul_cancel_left l₀ l)
    · rw [Finset.mem_coe, Finset.mem_filter] at hl ⊢
      exact ⟨hmul _ hl₀ _ hl.1, fun h => hl.2 ((hflip l hl.1).mp h)⟩
    · rw [Finset.mem_coe, Finset.mem_filter] at hl ⊢
      exact ⟨hmul _ hl₀ _ hl.1, (hflip l hl.1).mpr (not_not.mp hl.2)⟩
  have := Finset.card_filter_add_card_filter_not (s := L) fun l => l j ≠ a
  omega

/-! ## The averaging argument -/

/-- **Averaging.** Let `L` be a nonempty finite set of X-type seam operators
closed under products, with support `U = suppUnion L`. Then every X-type
doubling logical `u` has weight at least `d_K − ⌊|U|/2⌋` outside `U`, where
`d_K` is any lower bound on the weights of the doubling logicals. -/
theorem le_weight_restrictOutside_of_seam {L : Finset (NQubitPauliOperator m)}
    (hL : ∀ l ∈ L, l ∈ seamGroup e S) (hX : ∀ l ∈ L, IsXType l)
    (hmul : ∀ a ∈ L, ∀ b ∈ L, a * b ∈ L) (hne : L.Nonempty)
    {dK : ℕ} (hdK : ∀ u, IsDoublingLogical e S u → dK ≤ weight u)
    {u : NQubitPauliOperator m} (hu : IsDoublingLogical e S u) (huX : IsXType u) :
    dK - (suppUnion L).card / 2 ≤ weight (restrictOutside (suppUnion L) u) := by
  set U := suppUnion L
  -- every `u * l` is a doubling logical, and agrees with `u` outside `U`
  have key : ∀ l ∈ L, dK ≤ weight (restrictTo U (u * l)) + weight (restrictOutside U u) := by
    intro l hl
    rw [← restrictOutside_mul_of_support_subset (x := u) fun j hj => mem_suppUnion.mpr ⟨l, hl, hj⟩,
      ← weight_eq_weight_restrictTo_add]
    exact hdK _ (hu.mul_seam e S (hL l hl))
  -- double counting: on average half of `U` is in the support of `u * l`
  have hsum : 2 * ∑ l ∈ L, weight (restrictTo U (u * l)) = U.card * L.card := by
    simp only [weight_restrictTo_eq_sum]
    rw [Finset.sum_comm, Finset.mul_sum, Finset.card_eq_sum_ones U, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j hj => ?_
    obtain ⟨l₀, hl₀, hj₀⟩ := mem_suppUnion.mp hj
    rw [_root_.one_mul, ← Finset.card_filter, Finset.filter_congr fun l _ =>
      (PauliOperator.mulOp_operator_eq_I_iff (u j) (l j)).not.trans ne_comm]
    exact two_mul_card_filter_eq_card hX hmul hl₀ ((hX l₀ hl₀ j).resolve_left hj₀) (huX j)
  -- hence some `u * l` has at most `⌊|U|/2⌋` of its weight inside `U`
  obtain ⟨l, hl, hle⟩ : ∃ l ∈ L, 2 * weight (restrictTo U (u * l)) ≤ U.card :=
    Finset.exists_le_of_sum_le hne
      (by rw [← Finset.mul_sum, hsum, Finset.sum_const, smul_eq_mul, mul_comm])
  have := key l hl
  omega

/-! ## Supports of seam operators, and clean checks -/

/-- Let `s ∈ S` be an X-type lift of `b`, and `L` a nonempty finite set of
X-type seam operators closed under products whose support `U` contains the
supports of `sheet e 0 s` and of `b`. Then every X-type nontrivial logical
operator `v` folding to `b` has residual weight at least `d_K − ⌊|U|/2⌋`. -/
theorem le_residualWeight_of_seam_support {b : NQubitPauliOperator m}
    {s : NQubitPauliGroupElement n} (hs : s ∈ S.toSubgroup) (hsb : fold e s.operators = b)
    (hsX : IsXType s.operators)
    {L : Finset (NQubitPauliOperator m)} (hL : ∀ l ∈ L, l ∈ seamGroup e S)
    (hX : ∀ l ∈ L, IsXType l) (hmul : ∀ a ∈ L, ∀ b ∈ L, a * b ∈ L) (hne : L.Nonempty)
    (ha : ∀ j, sheet e 0 s.operators j ≠ PauliOperator.I → j ∈ suppUnion L)
    (hb : ∀ j, b j ≠ PauliOperator.I → j ∈ suppUnion L)
    {dK : ℕ} (hdK : ∀ u, IsDoublingLogical e S u → dK ≤ weight u)
    {v : NQubitPauliGroupElement n} (hv : IsNontrivialLogicalOperator v S)
    (hvX : IsXType v.operators) (hvb : fold e v.operators = b) :
    dK - (suppUnion L).card / 2 ≤ residualWeight e v := by
  have hu := isDoublingLogical_doublingPart e S hv hs (hsb.trans hvb.symm)
  have huX : IsXType (doublingPart e v s) :=
    isXType_mul (isXType_sheet e 0 hvX) (isXType_sheet e 0 hsX)
  have hbU : support b ⊆ suppUnion L := fun j hj =>
    hb j ((NQubitPauliOperator.mem_support b j).mp hj)
  calc dK - (suppUnion L).card / 2
      ≤ weight (restrictOutside (suppUnion L) (doublingPart e v s)) :=
        le_weight_restrictOutside_of_seam e S hL hX hmul hne hdK hu huX
    _ = weight (restrictOutside (suppUnion L) (doublingPart e v s * sheet e 0 s.operators)) := by
        rw [restrictOutside_mul_of_support_subset ha]
    _ ≤ weight (restrictOutside (support b) (doublingPart e v s * sheet e 0 s.operators)) :=
        weight_restrictOutside_le_of_subset hbU _
    _ = residualWeight e v := by
        rw [residualWeight, hvb, outsideSupport_eq_restrictOutside,
          sheet_zero_eq_doublingPart_mul e v s]

/-- Condition (J) from a set of seam operators: under the hypotheses of
`le_residualWeight_of_seam_support`, if `⌊|U|/2⌋ ≤ ⌊wt b/2⌋` then
`wt b + 2 · (residual weight of v) ≥ 2 d_K` for every X-type nontrivial
logical `v` folding to `b`. -/
theorem condition_J_of_seam_support {b : NQubitPauliOperator m}
    {s : NQubitPauliGroupElement n} (hs : s ∈ S.toSubgroup) (hsb : fold e s.operators = b)
    (hsX : IsXType s.operators)
    {L : Finset (NQubitPauliOperator m)} (hL : ∀ l ∈ L, l ∈ seamGroup e S)
    (hX : ∀ l ∈ L, IsXType l) (hmul : ∀ a ∈ L, ∀ b ∈ L, a * b ∈ L) (hne : L.Nonempty)
    (ha : ∀ j, sheet e 0 s.operators j ≠ PauliOperator.I → j ∈ suppUnion L)
    (hb : ∀ j, b j ≠ PauliOperator.I → j ∈ suppUnion L)
    (hcard : (suppUnion L).card / 2 ≤ weight b / 2)
    {dK : ℕ} (hdK : ∀ u, IsDoublingLogical e S u → dK ≤ weight u)
    {v : NQubitPauliGroupElement n} (hv : IsNontrivialLogicalOperator v S)
    (hvX : IsXType v.operators) (hvb : fold e v.operators = b) :
    2 * dK ≤ weight b + 2 * residualWeight e v := by
  have h := le_residualWeight_of_seam_support e S hs hsb hsX hL hX hmul hne ha hb hdK hv hvX hvb
  omega

/-- The four-element set `{1, b₁, b₂, b₁ * b₂}` is closed under products. -/
lemma mul_mem_quad_one (b₁ b₂ : NQubitPauliOperator m) :
    ∀ x ∈ ({1, b₁, b₂, b₁ * b₂} : Finset (NQubitPauliOperator m)),
      ∀ y ∈ ({1, b₁, b₂, b₁ * b₂} : Finset (NQubitPauliOperator m)),
        x * y ∈ ({1, b₁, b₂, b₁ * b₂} : Finset _) := by
  intro x hx y hy
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy ⊢
  have h1 : b₂ * (b₁ * b₂) = b₁ := by rw [mul_comm b₁, mul_mul_cancel_left]
  have h2 : b₁ * b₂ * b₁ = b₂ := by rw [mul_comm b₁, mul_mul_cancel_right]
  rcases hx with hx | hx | hx | hx <;> rcases hy with hy | hy | hy | hy <;>
    simp [hx, hy, h1, h2, mul_comm b₂ b₁]

/-- The support of `{1, b₁, b₂, b₁ * b₂}` is the union of the supports of `b₁`
and `b₂`. -/
lemma suppUnion_quad_one (b₁ b₂ : NQubitPauliOperator m) :
    suppUnion ({1, b₁, b₂, b₁ * b₂} : Finset (NQubitPauliOperator m)) =
      support b₁ ∪ support b₂ := by
  simp only [suppUnion, Finset.sup_insert, Finset.sup_singleton, Finset.sup_eq_union,
    NQubitPauliOperator.support_one, Finset.empty_union, ← Finset.union_assoc]
  exact Finset.union_eq_left.mpr (support_mul_subset b₁ b₂)

/-- **Two clean checks.** Let `b = b₁ * b₂` with `b₁, b₂` X-type stabilizer
folds in `J ∩ T` having X-type clean lifts `s₁, s₂ ∈ S`, and let
`U = supp b₁ ∪ supp b₂`. If `⌊|U|/2⌋ ≤ ⌊wt b/2⌋` then (J) holds for `b`: every
X-type nontrivial logical `v` folding to `b` has
`wt b + 2 · (residual weight of v) ≥ 2 d_K`. -/
theorem condition_J_of_two_cleanLifts {b₁ b₂ : NQubitPauliOperator m}
    (hb₁X : IsXType b₁) (hb₂X : IsXType b₂)
    (hb₁T : b₁ ∈ seamGroup e S) (hb₂T : b₂ ∈ seamGroup e S)
    {s₁ s₂ : NQubitPauliGroupElement n} (hs₁ : s₁ ∈ S.toSubgroup) (hs₂ : s₂ ∈ S.toSubgroup)
    (hclean₁ : IsCleanLift e b₁ s₁) (hclean₂ : IsCleanLift e b₂ s₂)
    (hs₁X : IsXType s₁.operators) (hs₂X : IsXType s₂.operators)
    (hcard : (support b₁ ∪ support b₂).card / 2 ≤ weight (b₁ * b₂) / 2)
    {dK : ℕ} (hdK : ∀ u, IsDoublingLogical e S u → dK ≤ weight u)
    {v : NQubitPauliGroupElement n} (hv : IsNontrivialLogicalOperator v S)
    (hvX : IsXType v.operators) (hvb : fold e v.operators = b₁ * b₂) :
    2 * dK ≤ weight (b₁ * b₂) + 2 * residualWeight e v := by
  refine condition_J_of_seam_support e S (s := s₁ * s₂) (S.mul_mem hs₁ hs₂) ?_
    (isXType_mul hs₁X hs₂X) (L := {1, b₁, b₂, b₁ * b₂}) ?_ ?_ (mul_mem_quad_one b₁ b₂)
    ⟨1, by simp⟩ (fun j hj => ?_) (fun j hj => ?_) ?_ hdK hv hvX hvb
  · rw [mul_operators, fold_mul, hclean₁.1, hclean₂.1]
  · simp [hb₁T, hb₂T, (seamGroup e S).mul_mem hb₁T hb₂T]
  · simp [isXType_one, hb₁X, hb₂X, isXType_mul hb₁X hb₂X]
  · rw [suppUnion_quad_one]
    exact Finset.union_subset_union (hclean₁.support_sheet_subset e)
      (hclean₂.support_sheet_subset e)
      (support_mul_subset _ _ ((NQubitPauliOperator.mem_support _ j).mpr hj))
  · rw [suppUnion_quad_one]
    exact support_mul_subset _ _ ((NQubitPauliOperator.mem_support _ j).mpr hj)
  · rwa [suppUnion_quad_one]

/-- **One clean check.** An X-type stabilizer fold `b ∈ J ∩ T` with an X-type
clean lift satisfies (J): every X-type nontrivial logical `v` folding to `b`
has `wt b + 2 · (residual weight of v) ≥ 2 d_K`. This is
`condition_J_of_two_cleanLifts` with `b₂ = 1`. -/
theorem condition_J_of_cleanLift {b : NQubitPauliOperator m} (hbX : IsXType b)
    (hbT : b ∈ seamGroup e S) {s : NQubitPauliGroupElement n} (hs : s ∈ S.toSubgroup)
    (hclean : IsCleanLift e b s) (hsX : IsXType s.operators)
    {dK : ℕ} (hdK : ∀ u, IsDoublingLogical e S u → dK ≤ weight u)
    {v : NQubitPauliGroupElement n} (hv : IsNontrivialLogicalOperator v S)
    (hvX : IsXType v.operators) (hvb : fold e v.operators = b) :
    2 * dK ≤ weight b + 2 * residualWeight e v := by
  have h := condition_J_of_two_cleanLifts e S hbX isXType_one hbT (seamGroup e S).one_mem hs
    S.one_mem hclean ⟨fold_one e, fun _ => Or.inl rfl⟩ hsX isXType_one
    (by rw [_root_.mul_one, NQubitPauliOperator.support_one, Finset.union_empty]; rfl) hdK hv hvX
    (by rwa [_root_.mul_one])
  rwa [_root_.mul_one] at h

end FoldDouble
end Stabilizer
end Quantum
