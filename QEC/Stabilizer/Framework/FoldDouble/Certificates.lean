import QEC.Stabilizer.Framework.FoldDouble.Distance

/-!
# Certificates for condition (J): the averaging argument

Condition (J) of the fold-and-double theorem asks, for a light stabilizer fold
`b` (weight `< 2 d_K`), that `wt b + 2 m_b ≥ 2 d_K`, where the residual `m_b`
is the least weight of `(u * a) outside supp b` over the doubling logicals `u`,
for a lift `s = (a, a * b)` of `b`. This file gives the single-Pauli-type
certificates for it, all consequences of one averaging argument:

* **Lemma 6.1** (`le_weight_restrictOutside_of_seam`): if `L` is a finite set
  of X-type seam operators closed under products, with support `U`, then every
  X-type doubling logical `u` satisfies `wt (u outside U) ≥ d_K − ⌊|U|/2⌋`.
  Multiplying `u` by the elements of `L` keeps it a doubling logical, and on
  average over `L` exactly half of `U` is in the support of `u * l`, so some
  `u * l` has at most `⌊|U|/2⌋` of its weight inside `U`.
* **Proposition 6.2** (`condition_J_of_seam_support`): if moreover `U` contains
  the supports of `a` and `b`, then `m_b ≥ d_K − ⌊|U|/2⌋`, so (J) holds for `b`
  as soon as `⌊|U|/2⌋ ≤ ⌊wt b/2⌋`.
* **Corollary 6.3** (`condition_J_of_cleanLift`): a stabilizer fold `b ∈ J ∩ T`
  with a clean lift satisfies (J) (`L = {1, b}`).
* **Corollary 6.4** (`condition_J_of_two_cleanLifts`): if `b = b₁ * b₂` with
  `b₁, b₂ ∈ J ∩ T` having clean lifts, and `U = supp b₁ ∪ supp b₂` satisfies
  `⌊|U|/2⌋ ≤ ⌊wt b/2⌋`, then (J) holds for `b` (`L = {1, b₁, b₂, b₁ b₂}`).

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
  simp only [weight_eq_sum, restrictTo_apply, restrictOutside_apply]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hj : j ∈ U <;> simp [hj]

/-- Restriction outside the support of `b` is restriction outside `supp b`. -/
lemma outsideSupport_eq_restrictOutside (b x : NQubitPauliOperator m) :
    outsideSupport b x = restrictOutside (support b) x := by
  ext j
  by_cases hj : b j = PauliOperator.I <;> simp [outsideSupport, hj]

/-- Restricting outside a larger set gives a lighter operator. -/
lemma weight_restrictOutside_le_of_subset {U V : Finset (Fin m)} (h : U ⊆ V)
    (x : NQubitPauliOperator m) :
    weight (restrictOutside V x) ≤ weight (restrictOutside U x) := by
  simp only [weight_eq_sum, restrictOutside_apply]
  refine Finset.sum_le_sum fun j _ => ?_
  by_cases hjV : j ∈ V
  · simp [hjV]
  · have hjU : j ∉ U := fun hjU => hjV (h hjU)
    simp [hjV, hjU]

/-- Multiplying by an operator supported inside `U` does not change the
restriction outside `U`. -/
lemma restrictOutside_mul_of_support_subset {U : Finset (Fin m)} {x l : NQubitPauliOperator m}
    (hl : ∀ j, l j ≠ PauliOperator.I → j ∈ U) :
    restrictOutside U (x * l) = restrictOutside U x := by
  ext j
  by_cases hj : j ∈ U
  · simp [hj]
  · have hlj : l j = PauliOperator.I := by
      by_contra h
      exact hj (hl j h)
    simp [hj, hlj, PauliOperator.mulOp_operator_I_right]

/-- The weight of a restriction to `U`, as a sum over `U`. -/
lemma weight_restrictTo_eq_sum (U : Finset (Fin m)) (x : NQubitPauliOperator m) :
    weight (restrictTo U x) = ∑ j ∈ U, if x j ≠ PauliOperator.I then 1 else 0 := by
  rw [weight_eq_sum]
  have h : ∀ j, (if restrictTo U x j ≠ PauliOperator.I then 1 else 0) =
      if j ∈ U then (if x j ≠ PauliOperator.I then 1 else 0) else 0 := by
    intro j
    by_cases hj : j ∈ U <;> simp [hj]
  simp only [h]
  rw [Finset.sum_ite_mem, Finset.univ_inter]

/-! ## X-type operators -/

lemma mulOp_operator_ne_I_iff_of_isXType {a b : PauliOperator} (ha : a.IsXType) (hb : b.IsXType) :
    (a.mulOp b).operator ≠ PauliOperator.I ↔ a ≠ b := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> decide

lemma eq_X_of_isXType_of_ne_I {a : PauliOperator} (ha : a.IsXType) (h : a ≠ PauliOperator.I) :
    a = PauliOperator.X := by
  rcases ha with rfl | rfl
  · exact absurd rfl h
  · rfl

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
  -- the two fibers have the same size
  have hfib : (L.filter fun l => l j = PauliOperator.X).card =
      (L.filter fun l => l j = PauliOperator.I).card := by
    refine Finset.card_nbij (fun l => l₀ * l) ?_ ?_ ?_
    · intro l hl
      rw [Finset.mem_coe, Finset.mem_filter] at hl ⊢
      refine ⟨hmul _ hl₀ _ hl.1, ?_⟩
      change (l₀ * l) j = PauliOperator.I
      rw [mul_apply, hj, hl.2]
      rfl
    · intro l _ l' _ h
      exact mul_left_cancel h
    · intro l' hl'
      rw [Finset.mem_coe, Finset.mem_filter] at hl'
      refine ⟨l₀ * l', ?_, ?_⟩
      · rw [Finset.mem_coe, Finset.mem_filter]
        refine ⟨hmul _ hl₀ _ hl'.1, ?_⟩
        change (l₀ * l') j = PauliOperator.X
        rw [mul_apply, hj, hl'.2]
        rfl
      · change l₀ * (l₀ * l') = l'
        rw [← _root_.mul_assoc, mul_self_eq_one, _root_.one_mul]
  have hsplit := Finset.card_filter_add_card_filter_not (s := L)
    (p := fun l => l j = PauliOperator.X)
  have hnotX : (L.filter fun l => ¬ l j = PauliOperator.X) =
      L.filter fun l => l j = PauliOperator.I := by
    refine Finset.filter_congr fun l hl => ?_
    rcases hX l hl j with h | h <;> rw [h] <;> decide
  rw [hnotX] at hsplit
  rcases ha with rfl | rfl
  · have : (L.filter fun l => l j ≠ PauliOperator.I) = L.filter fun l => l j = PauliOperator.X := by
      refine Finset.filter_congr fun l hl => ?_
      rcases hX l hl j with h | h <;> rw [h] <;> decide
    rw [this]
    omega
  · have : (L.filter fun l => l j ≠ PauliOperator.X) = L.filter fun l => l j = PauliOperator.I := by
      refine Finset.filter_congr fun l hl => ?_
      rcases hX l hl j with h | h <;> rw [h] <;> decide
    rw [this]
    omega

/-! ## Lemma 6.1: the averaging argument -/

/-- **Lemma 6.1** (averaging). Let `L` be a nonempty finite set of X-type seam
operators closed under products, with support `U = suppUnion L`. Then every
X-type doubling logical `u` has weight at least `d_K − ⌊|U|/2⌋` outside `U`,
where `d_K` is any lower bound on the weights of the doubling logicals. -/
theorem le_weight_restrictOutside_of_seam {L : Finset (NQubitPauliOperator m)}
    (hL : ∀ l ∈ L, l ∈ seamGroup e S) (hX : ∀ l ∈ L, IsXType l)
    (hmul : ∀ a ∈ L, ∀ b ∈ L, a * b ∈ L) (hne : L.Nonempty)
    {dK : ℕ} (hdK : ∀ u, IsDoublingLogical e S u → dK ≤ weight u)
    {u : NQubitPauliOperator m} (hu : IsDoublingLogical e S u) (huX : IsXType u) :
    dK - (suppUnion L).card / 2 ≤ weight (restrictOutside (suppUnion L) u) := by
  set U := suppUnion L with hU
  -- every `u * l` is a doubling logical, and agrees with `u` outside `U`
  have key : ∀ l ∈ L, dK ≤ weight (restrictTo U (u * l)) + weight (restrictOutside U u) := by
    intro l hl
    have h1 := hdK _ (hu.mul_seam e S (hL l hl))
    have hsub : ∀ j, l j ≠ PauliOperator.I → j ∈ U := fun j hj =>
      mem_suppUnion.mpr ⟨l, hl, hj⟩
    rwa [weight_eq_weight_restrictTo_add U (u * l), restrictOutside_mul_of_support_subset hsub]
      at h1
  -- double counting: on average half of `U` is in the support of `u * l`
  have hsum : 2 * ∑ l ∈ L, weight (restrictTo U (u * l)) = U.card * L.card := by
    simp only [weight_restrictTo_eq_sum]
    rw [Finset.sum_comm, Finset.mul_sum, Finset.card_eq_sum_ones U, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [_root_.one_mul, ← Finset.card_filter]
    obtain ⟨l₀, hl₀, hj₀⟩ := mem_suppUnion.mp hj
    have hfilter : (L.filter fun l => (u * l) j ≠ PauliOperator.I) =
        L.filter fun l => l j ≠ u j := by
      refine Finset.filter_congr fun l hl => ?_
      rw [mul_apply, mulOp_operator_ne_I_iff_of_isXType (huX j) (hX l hl j)]
      exact ne_comm
    rw [hfilter]
    exact two_mul_card_filter_eq_card hX hmul hl₀ (eq_X_of_isXType_of_ne_I (hX l₀ hl₀ j) hj₀)
      (huX j)
  -- hence some `u * l` has at most `⌊|U|/2⌋` of its weight inside `U`
  obtain ⟨l, hl, hle⟩ : ∃ l ∈ L, 2 * weight (restrictTo U (u * l)) ≤ U.card := by
    by_contra hcon
    push Not at hcon
    have h1 : ∑ _l ∈ L, (U.card + 1) ≤ ∑ l ∈ L, 2 * weight (restrictTo U (u * l)) :=
      Finset.sum_le_sum fun l hl => hcon l hl
    rw [Finset.sum_const, smul_eq_mul, ← Finset.mul_sum, hsum] at h1
    have hpos : 0 < L.card := Finset.card_pos.mpr hne
    nlinarith
  have := key l hl
  omega

/-! ## Proposition 6.2 and the clean-check corollaries -/

/-- **Proposition 6.2.** Let `s ∈ S` be an X-type lift of `b`, and `L` a
nonempty finite set of X-type seam operators closed under products whose
support `U` contains the supports of `sheet e 0 s` and of `b`. Then every
X-type nontrivial logical operator `v` folding to `b` has residual weight at
least `d_K − ⌊|U|/2⌋`; in particular (J) holds for `b` as soon as
`⌊|U|/2⌋ ≤ ⌊wt b/2⌋`. -/
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
  have h1 := le_weight_restrictOutside_of_seam e S hL hX hmul hne hdK hu huX
  have hbU : support b ⊆ suppUnion L := fun j hj =>
    hb j ((NQubitPauliOperator.mem_support b j).mp hj)
  calc dK - (suppUnion L).card / 2
      ≤ weight (restrictOutside (suppUnion L) (doublingPart e v s)) := h1
    _ = weight (restrictOutside (suppUnion L) (doublingPart e v s * sheet e 0 s.operators)) := by
        rw [restrictOutside_mul_of_support_subset ha]
    _ ≤ weight (restrictOutside (support b) (doublingPart e v s * sheet e 0 s.operators)) :=
        weight_restrictOutside_le_of_subset hbU _
    _ = residualWeight e v := by
        rw [residualWeight, hvb, outsideSupport_eq_restrictOutside,
          sheet_zero_eq_doublingPart_mul e v s]

/-- **Proposition 6.2**, in the form of condition (J): under the hypotheses of
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

/-- The two-element set `{1, b}` is closed under products when `b * b = 1`. -/
lemma mul_mem_pair_one (b : NQubitPauliOperator m) :
    ∀ x ∈ ({1, b} : Finset (NQubitPauliOperator m)),
      ∀ y ∈ ({1, b} : Finset (NQubitPauliOperator m)), x * y ∈ ({1, b} : Finset _) := by
  intro x hx y hy
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy ⊢
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> simp

lemma suppUnion_pair_one (b : NQubitPauliOperator m) :
    suppUnion ({1, b} : Finset (NQubitPauliOperator m)) = support b := by
  ext j
  simp only [mem_suppUnion, Finset.mem_insert, Finset.mem_singleton,
    NQubitPauliOperator.mem_support]
  constructor
  · rintro ⟨l, (rfl | rfl), hl⟩
    · exact absurd rfl hl
    · exact hl
  · intro h
    exact ⟨b, Or.inr rfl, h⟩

/-- **Corollary 6.3** (one clean check). An X-type stabilizer fold `b ∈ J ∩ T`
with an X-type clean lift satisfies (J): every X-type nontrivial logical `v`
folding to `b` has `wt b + 2 · (residual weight of v) ≥ 2 d_K`. -/
theorem condition_J_of_cleanLift {b : NQubitPauliOperator m} (hbX : IsXType b)
    (hbT : b ∈ seamGroup e S) {s : NQubitPauliGroupElement n} (hs : s ∈ S.toSubgroup)
    (hclean : IsCleanLift e b s) (hsX : IsXType s.operators)
    {dK : ℕ} (hdK : ∀ u, IsDoublingLogical e S u → dK ≤ weight u)
    {v : NQubitPauliGroupElement n} (hv : IsNontrivialLogicalOperator v S)
    (hvX : IsXType v.operators) (hvb : fold e v.operators = b) :
    2 * dK ≤ weight b + 2 * residualWeight e v := by
  refine condition_J_of_seam_support e S hs hclean.1 hsX (L := {1, b}) ?_ ?_ (mul_mem_pair_one b)
    ⟨1, by simp⟩ ?_ ?_ ?_ hdK hv hvX hvb
  · intro l hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact (seamGroup e S).one_mem
    · exact hbT
  · intro l hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact isXType_one
    · exact hbX
  · intro j hj
    rw [suppUnion_pair_one, NQubitPauliOperator.mem_support]
    rcases hclean.2 j with h | h
    · exact absurd h hj
    · rw [← h]
      exact hj
  · intro j hj
    rw [suppUnion_pair_one, NQubitPauliOperator.mem_support]
    exact hj
  · rw [suppUnion_pair_one]
    rfl

/-- The four-element set `{1, b₁, b₂, b₁ * b₂}` is closed under products. -/
lemma mul_mem_quad_one (b₁ b₂ : NQubitPauliOperator m) :
    ∀ x ∈ ({1, b₁, b₂, b₁ * b₂} : Finset (NQubitPauliOperator m)),
      ∀ y ∈ ({1, b₁, b₂, b₁ * b₂} : Finset (NQubitPauliOperator m)),
        x * y ∈ ({1, b₁, b₂, b₁ * b₂} : Finset _) := by
  intro x hx y hy
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy ⊢
  have h1 : b₁ * (b₁ * b₂) = b₂ := by rw [← _root_.mul_assoc, mul_self_eq_one, _root_.one_mul]
  have h2 : b₂ * (b₁ * b₂) = b₁ := by
    rw [mul_comm b₁ b₂, ← _root_.mul_assoc, mul_self_eq_one, _root_.one_mul]
  have h3 : b₁ * b₂ * b₁ = b₂ := by rw [mul_comm (b₁ * b₂) b₁, h1]
  have h4 : b₁ * b₂ * b₂ = b₁ := by rw [mul_comm (b₁ * b₂) b₂, h2]
  have hc : b₂ * b₁ = b₁ * b₂ := mul_comm b₂ b₁
  rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
    simp only [_root_.one_mul, _root_.mul_one, mul_self_eq_one, h1, h2, h3, h4, hc, true_or,
      or_true]

lemma suppUnion_quad_one (b₁ b₂ : NQubitPauliOperator m) :
    suppUnion ({1, b₁, b₂, b₁ * b₂} : Finset (NQubitPauliOperator m)) =
      support b₁ ∪ support b₂ := by
  ext j
  simp only [mem_suppUnion, Finset.mem_insert, Finset.mem_singleton, Finset.mem_union,
    NQubitPauliOperator.mem_support]
  constructor
  · rintro ⟨l, (rfl | rfl | rfl | rfl), hl⟩
    · exact absurd rfl hl
    · exact Or.inl hl
    · exact Or.inr hl
    · by_contra hcon
      push Not at hcon
      apply hl
      rw [mul_apply, hcon.1, hcon.2]
      rfl
  · rintro (h | h)
    · exact ⟨b₁, Or.inr (Or.inl rfl), h⟩
    · exact ⟨b₂, Or.inr (Or.inr (Or.inl rfl)), h⟩

/-- **Corollary 6.4** (two clean checks). Let `b = b₁ * b₂` with `b₁, b₂` X-type
stabilizer folds in `J ∩ T` having X-type clean lifts `s₁, s₂ ∈ S`, and let
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
    (by rw [mul_operators]; exact isXType_mul hs₁X hs₂X) (L := {1, b₁, b₂, b₁ * b₂}) ?_ ?_
    (mul_mem_quad_one b₁ b₂) ⟨1, by simp⟩ ?_ ?_ ?_ hdK hv hvX hvb
  · rw [mul_operators, fold_mul, hclean₁.1, hclean₂.1]
  · intro l hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl | rfl | rfl
    · exact (seamGroup e S).one_mem
    · exact hb₁T
    · exact hb₂T
    · exact (seamGroup e S).mul_mem hb₁T hb₂T
  · intro l hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl | rfl | rfl
    · exact isXType_one
    · exact hb₁X
    · exact hb₂X
    · exact isXType_mul hb₁X hb₂X
  · intro j hj
    rw [suppUnion_quad_one, Finset.mem_union, NQubitPauliOperator.mem_support,
      NQubitPauliOperator.mem_support]
    rw [mul_operators, sheet_mul, mul_apply] at hj
    by_contra hcon
    push Not at hcon
    apply hj
    have h₁ : sheet e 0 s₁.operators j = PauliOperator.I := by
      rcases hclean₁.2 j with h | h
      · exact h
      · rw [h, hcon.1]
    have h₂ : sheet e 0 s₂.operators j = PauliOperator.I := by
      rcases hclean₂.2 j with h | h
      · exact h
      · rw [h, hcon.2]
    rw [h₁, h₂]
    rfl
  · intro j hj
    rw [suppUnion_quad_one, Finset.mem_union, NQubitPauliOperator.mem_support,
      NQubitPauliOperator.mem_support]
    by_contra hcon
    push Not at hcon
    apply hj
    rw [mul_apply, hcon.1, hcon.2]
    rfl
  · rw [suppUnion_quad_one]
    exact hcard

end FoldDouble
end Stabilizer
end Quantum
