import QEC.Stabilizer.Framework.FoldDouble.Groups
import QEC.Stabilizer.Framework.Core.Logical.CodeDistance

/-!
# The fold-and-double distance theorem

Fix a stabilizer group `S` on `n` qubits with a pairing
`e : Fin n ≃ Fin m × Fin 2`, and the four groups `J ≤ P`, `T ≤ K` of
`Groups.lean`. A nontrivial logical
operator `v` of `S` is of one of two kinds, according to its fold `b = fold v`:

* **kind (L)**, `b ∉ J`: then `wt v ≥ wt b ≥ d_P` (Lemma 4.2);
* **kind (S)**, `b ∈ J`: choose a stabilizer `s` with `fold s = b`; then
  `v = double u * s` for a unique `u`, the **doubling part** of `v`, which is a
  doubling logical (Lemma 4.3), and the **slice inequality**
  `wt v ≥ wt b + 2 · wt (v₀ outside supp b)` holds, with equality for
  operators of a single Pauli type (Proposition 4.4).

The **residual** `m_b` (Definition 4.5) is the least value of
`wt (v₀ outside supp b)` over the nontrivial logicals `v` folding to `b`;
through the doubling part it is the least value of `wt ((u * a) outside supp b)`
over the doubling logicals `u`, for any lift `s = (a, a * b)` of `b`
(Lemma 4.6 (1)), and `m_1 = d_K` (Lemma 4.6 (2)).

**Theorem 5.1** (`isLeast_logicalWeight_two_mul_of_floors`, and its floor form
`isLeast_logicalWeight_two_mul`): if `K ≠ T` with doubling floor `d_K`, if
every logical fold has weight `≥ 2 d_K` (condition (P)), and if
`wt b + 2 m_b ≥ 2 d_K` for every stabilizer fold `b ≠ 1` of weight `< 2 d_K`
(condition (J)), then the distance of `S` is exactly `2 d_K`. No symmetry is
needed.

**Corollary 5.3** (`isLeast_logicalWeight_two_mul_of_symmetric`,
`hasCodeDistance_two_mul_of_symmetric`): for a symmetric pairing and a folded
code `F` of distance `d₀`, the four conditions
(W) some doubling logical has weight `d₀`,
(R) `g * g^σ ∈ G` for every logical operator `g`,
(F) every seam logical has weight `≥ 2 d₀`,
(S) `wt b + 2 m_b ≥ 2 d₀` for every stabilizer fold `b ≠ 1` of weight
`< 2 d₀`, give distance exactly `2 d₀` for `S`, in the library's sense
(`IsLeast` over the nontrivial logical operators, and `HasCodeDistance` for a
packaged code).

**Corollary 5.5** (`min_le_logicalWeight`): with no hypotheses at all,
`d(S) ≥ min (2 d_K, μ_P)`, where `μ_P` is the least weight of a non-identity
logical fold. **Corollary 4.7** (`weight_eq_add_of_clean`,
`two_mul_le_weight_of_clean`): over a clean lift, `wt v = wt u + wt (u * b)`,
and if moreover `b ∈ T` then `wt v ≥ 2 d_K`.
-/

namespace Quantum
namespace Stabilizer
namespace FoldDouble

open NQubitPauliOperator NQubitPauliGroupElement StabilizerGroup

variable {n m : ℕ} (e : Fin n ≃ Fin m × Fin 2) (S : StabilizerGroup n)

/-! ## Restriction outside a support, and the slice inequality -/

/-- The restriction of `x` to the qubits outside the support of `b` (identity
on the support of `b`). -/
def outsideSupport (b x : NQubitPauliOperator m) : NQubitPauliOperator m :=
  fun j => if b j = PauliOperator.I then x j else PauliOperator.I

@[simp] lemma outsideSupport_apply (b x : NQubitPauliOperator m) (j : Fin m) :
    outsideSupport b x j = if b j = PauliOperator.I then x j else PauliOperator.I := rfl

@[simp] lemma outsideSupport_one (x : NQubitPauliOperator m) : outsideSupport 1 x = x := by
  ext j
  simp

lemma indicator_slice_le (x y : PauliOperator) :
    (if (x.mulOp y).operator ≠ PauliOperator.I then 1 else 0) +
      2 * (if (if (x.mulOp y).operator = PauliOperator.I then x else PauliOperator.I) ≠
        PauliOperator.I then 1 else 0) ≤
      (if x ≠ PauliOperator.I then 1 else 0) + (if y ≠ PauliOperator.I then 1 else 0) := by
  cases x <;> cases y <;> decide

/-- Proposition 4.4, the **slice inequality**: the weight of `P` is at least
the weight of its fold plus twice the weight of its sheet-`0` part outside the
support of the fold. On the support of the fold the two sheets differ, so at
least one acts; outside it they agree, so they contribute `0` or `2`. -/
theorem weight_fold_add_two_mul_weight_outsideSupport_le (P : NQubitPauliOperator n) :
    weight (fold e P) + 2 * weight (outsideSupport (fold e P) (sheet e 0 P)) ≤ weight P := by
  rw [weight_eq_sum, weight_eq_sum, weight_eq_sum_pairs e, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun j _ => indicator_slice_le _ _

lemma indicator_slice_eq_of_isXType {x y : PauliOperator} (hx : x.IsXType) (hy : y.IsXType) :
    (if (x.mulOp y).operator ≠ PauliOperator.I then 1 else 0) +
      2 * (if (if (x.mulOp y).operator = PauliOperator.I then x else PauliOperator.I) ≠
        PauliOperator.I then 1 else 0) =
      (if x ≠ PauliOperator.I then 1 else 0) + (if y ≠ PauliOperator.I then 1 else 0) := by
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> decide

lemma indicator_slice_eq_of_isZType {x y : PauliOperator} (hx : x.IsZType) (hy : y.IsZType) :
    (if (x.mulOp y).operator ≠ PauliOperator.I then 1 else 0) +
      2 * (if (if (x.mulOp y).operator = PauliOperator.I then x else PauliOperator.I) ≠
        PauliOperator.I then 1 else 0) =
      (if x ≠ PauliOperator.I then 1 else 0) + (if y ≠ PauliOperator.I then 1 else 0) := by
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> decide

/-- Proposition 4.4, equality case: for an operator of a single Pauli type the
slice inequality is an equality. -/
theorem weight_eq_weight_fold_add_two_mul_weight_outsideSupport (P : NQubitPauliOperator n)
    (hP : IsXType P ∨ IsZType P) :
    weight P = weight (fold e P) + 2 * weight (outsideSupport (fold e P) (sheet e 0 P)) := by
  rw [weight_eq_sum_pairs e, weight_eq_sum, weight_eq_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rcases hP with hP | hP
  · exact (indicator_slice_eq_of_isXType (hP _) (hP _)).symm
  · exact (indicator_slice_eq_of_isZType (hP _) (hP _)).symm

/-! ## Lemma 4.2: kind (L) -/

/-- Lemma 4.2: a logical operator whose fold is not a stabilizer fold has
weight at least the weight of its fold, hence at least any lower bound on the
logical folds. -/
theorem le_weight_of_fold_not_mem_foldImage {v : NQubitPauliGroupElement n}
    (hv : v ∈ centralizer S) (hb : fold e v.operators ∉ foldImage e S) {D : ℕ}
    (hP : ∀ b, IsLogicalFold e S b → D ≤ weight b) :
    D ≤ NQubitPauliGroupElement.weight v :=
  (hP _ ⟨fold_operators_mem_logicalFoldImage e S hv, hb⟩).trans (weight_fold_le e _)

/-! ## Lemma 4.3: kind (S) and the doubling part -/

/-- The **doubling part** of `v` relative to a lift `s` of its fold:
`u := v₀ * s₀`, so that `v = double u * s`. -/
noncomputable def doublingPart (v s : NQubitPauliGroupElement n) : NQubitPauliOperator m :=
  sheet e 0 v.operators * sheet e 0 s.operators

/-- Lemma 4.3: if `s` and `v` have the same fold then `v = double u * s` with
`u` the doubling part. -/
theorem operators_eq_double_doublingPart_mul {v s : NQubitPauliGroupElement n}
    (h : fold e s.operators = fold e v.operators) :
    v.operators = double e (doublingPart e v s) * s.operators := by
  have hw : fold e (v.operators * s.operators) = 1 := by
    rw [fold_mul, ← h, mul_self_eq_one]
  have hw' := (fold_eq_one_iff e _).mp hw
  rw [sheet_mul] at hw'
  calc v.operators = v.operators * s.operators * s.operators := by
        rw [_root_.mul_assoc, mul_self_eq_one, _root_.mul_one]
    _ = double e (doublingPart e v s) * s.operators := by rw [hw', doublingPart]

/-- Lemma 4.3: the doubling part is the unique `u` with `v = double u * s`. -/
theorem eq_doublingPart_of_eq_double_mul {v s : NQubitPauliGroupElement n}
    {u : NQubitPauliOperator m} (h : v.operators = double e u * s.operators) :
    u = doublingPart e v s := by
  have hfold : fold e s.operators = fold e v.operators := by
    rw [h, fold_mul, fold_double, _root_.one_mul]
  have h2 := operators_eq_double_doublingPart_mul e hfold
  apply double_injective e
  calc double e u = v.operators * s.operators := by
        rw [h, _root_.mul_assoc, mul_self_eq_one, _root_.mul_one]
    _ = double e (doublingPart e v s) := by
        rw [h2, _root_.mul_assoc, mul_self_eq_one, _root_.mul_one]

/-- The sheet-`0` part of `v` is the doubling part times the sheet-`0` part of
the lift: `v₀ = u * a`. -/
lemma sheet_zero_eq_doublingPart_mul (v s : NQubitPauliGroupElement n) :
    sheet e 0 v.operators = doublingPart e v s * sheet e 0 s.operators := by
  rw [doublingPart, _root_.mul_assoc, mul_self_eq_one, _root_.mul_one]

/-- Lemma 4.3: for a nontrivial logical operator `v` and a stabilizer lift `s`
of its fold, the doubling part of `v` is a doubling logical. -/
theorem isDoublingLogical_doublingPart {v s : NQubitPauliGroupElement n}
    (hv : IsNontrivialLogicalOperator v S) (hs : s ∈ S.toSubgroup)
    (h : fold e s.operators = fold e v.operators) :
    IsDoublingLogical e S (doublingPart e v s) := by
  have hvs := operators_eq_double_doublingPart_mul e h
  have hdu : double e (doublingPart e v s) = v.operators * s.operators := by
    rw [hvs, _root_.mul_assoc, mul_self_eq_one, _root_.mul_one]
  rw [isNontrivialLogicalOperator_iff_operators] at hv
  constructor
  · rw [mem_doublingGroup, hdu, ← mul_operators]
    exact operators_mem_operatorImage
      ((centralizer S).mul_mem hv.1 (stabilizer_le_centralizer S hs))
  · intro ht
    rw [mem_seamGroup, hdu] at ht
    apply hv.2
    have := (operatorImage S.toSubgroup).mul_mem ht (operators_mem_operatorImage hs)
    rwa [_root_.mul_assoc, mul_self_eq_one, _root_.mul_one] at this

lemma fold_double_mul (u : NQubitPauliOperator m) (t : NQubitPauliOperator n) :
    fold e (double e u * t) = fold e t := by
  rw [fold_mul, fold_double, _root_.one_mul]

/-- Conversely, every doubling logical `u` and stabilizer `s` give a nontrivial
logical operator `double u * s` folding to `fold s`. -/
theorem isNontrivialLogicalOperator_ofOperator_double_mul {u : NQubitPauliOperator m}
    (hu : IsDoublingLogical e S u) {s : NQubitPauliGroupElement n} (hs : s ∈ S.toSubgroup) :
    IsNontrivialLogicalOperator (ofOperator (double e u * s.operators)) S := by
  rw [isNontrivialLogicalOperator_ofOperator_iff]
  constructor
  · exact (operatorImage (centralizer S)).mul_mem ((mem_doublingGroup e S).mp hu.1)
      (operatorImage_le_operatorImage_centralizer S (operators_mem_operatorImage hs))
  · intro h
    apply hu.2
    rw [mem_seamGroup]
    have := (operatorImage S.toSubgroup).mul_mem h (operators_mem_operatorImage hs)
    rwa [_root_.mul_assoc, mul_self_eq_one, _root_.mul_one] at this

/-! ## Definition 4.5 and Lemma 4.6: the residual `m_b` -/

/-- The residual weight of a logical operator `v`: the weight of its sheet-`0`
part outside the support of its fold. For `v = double u * s` with
`s = (a, a * b)` a lift of `b = fold v`, this is `wt ((u * a) outside supp b)`.
-/
noncomputable def residualWeight (v : NQubitPauliGroupElement n) : ℕ :=
  weight (outsideSupport (fold e v.operators) (sheet e 0 v.operators))

/-- The **residual** `m_b` of a stabilizer fold `b` (Definition 4.5): the least
residual weight of a nontrivial logical operator folding to `b`; `⊤` if there
is none. -/
noncomputable def residual (b : NQubitPauliOperator m) : ℕ∞ :=
  sInf ((fun v => (residualWeight e v : ℕ∞)) ''
    {v | IsNontrivialLogicalOperator v S ∧ fold e v.operators = b})

lemma residual_le {v : NQubitPauliGroupElement n} (hv : IsNontrivialLogicalOperator v S) :
    residual e S (fold e v.operators) ≤ residualWeight e v :=
  sInf_le ⟨v, ⟨hv, rfl⟩, rfl⟩

lemma le_residual_iff {b : NQubitPauliOperator m} {k : ℕ∞} :
    k ≤ residual e S b ↔
      ∀ v, IsNontrivialLogicalOperator v S → fold e v.operators = b → k ≤ residualWeight e v := by
  rw [residual, le_sInf_iff, Set.forall_mem_image]
  exact ⟨fun h v hv hb => h ⟨hv, hb⟩, fun h v hv => h v hv.1 hv.2⟩

/-- Lemma 4.6 (3), slice form: every nontrivial logical operator `v` folding to
`b` has weight at least `wt b + 2 m_b`. -/
theorem weight_fold_add_two_mul_residual_le {v : NQubitPauliGroupElement n}
    (hv : IsNontrivialLogicalOperator v S) :
    (weight (fold e v.operators) : ℕ∞) + 2 * residual e S (fold e v.operators) ≤
      NQubitPauliGroupElement.weight v := by
  calc (weight (fold e v.operators) : ℕ∞) + 2 * residual e S (fold e v.operators)
      ≤ weight (fold e v.operators) + 2 * (residualWeight e v : ℕ∞) := by
        have := residual_le e S hv
        gcongr
    _ = ((weight (fold e v.operators) + 2 * residualWeight e v : ℕ) : ℕ∞) := by norm_cast
    _ ≤ NQubitPauliGroupElement.weight v :=
        ENat.coe_le_coe.mpr (weight_fold_add_two_mul_weight_outsideSupport_le e _)

/-- Lemma 4.6 (1): the residual through a lift. For a stabilizer `s` with
`fold s = b`, `m_b` is the least value of `wt ((u * s₀) outside supp b)` over
the doubling logicals `u`: in particular it does not depend on the lift. -/
theorem residual_eq_of_lift {b : NQubitPauliOperator m} {s : NQubitPauliGroupElement n}
    (hs : s ∈ S.toSubgroup) (hb : fold e s.operators = b) :
    residual e S b =
      sInf ((fun u => (weight (outsideSupport b (u * sheet e 0 s.operators)) : ℕ∞)) ''
        {u | IsDoublingLogical e S u}) := by
  unfold residual
  congr 1
  ext w
  constructor
  · rintro ⟨v, ⟨hv, hvb⟩, rfl⟩
    refine ⟨doublingPart e v s, isDoublingLogical_doublingPart e S hv hs (hb.trans hvb.symm), ?_⟩
    simp only [residualWeight, hvb]
    rw [sheet_zero_eq_doublingPart_mul e v s]
  · rintro ⟨u, hu, rfl⟩
    refine ⟨ofOperator (double e u * s.operators),
      ⟨isNontrivialLogicalOperator_ofOperator_double_mul e S hu hs, ?_⟩, ?_⟩
    · rw [ofOperator_operators, fold_double_mul, hb]
    · simp only [residualWeight, ofOperator_operators, fold_double_mul, hb, sheet_double_mul]

/-- Lemma 4.6 (2): the residual of the identity is the doubling floor,
`m_1 = d_K`. -/
theorem residual_one : residual e S 1 = doublingFloor e S := by
  unfold residual doublingFloor
  congr 1
  ext w
  constructor
  · rintro ⟨v, ⟨hv, hv1⟩, rfl⟩
    refine ⟨sheet e 0 v.operators, isDoublingLogical_sheet_of_fold_eq_one e S hv hv1, ?_⟩
    simp only [residualWeight, hv1, outsideSupport_one]
  · rintro ⟨u, hu, rfl⟩
    refine ⟨ofOperator (double e u),
      ⟨isNontrivialLogicalOperator_ofOperator_double e S hu, by simp⟩, ?_⟩
    simp [residualWeight]

/-! ## Theorem 5.1: fold and double, any pairing -/

/-- A nontrivial logical operator folding to the identity is a double, so its
weight is twice the weight of a doubling logical: at least `2 d_K`. -/
theorem two_mul_le_weight_of_fold_eq_one {v : NQubitPauliGroupElement n}
    (hv : IsNontrivialLogicalOperator v S) (h : fold e v.operators = 1) {dK : ℕ}
    (hdK : ∀ u, IsDoublingLogical e S u → dK ≤ weight u) :
    2 * dK ≤ NQubitPauliGroupElement.weight v := by
  have hu := hdK _ (isDoublingLogical_sheet_of_fold_eq_one e S hv h)
  have hw : NQubitPauliGroupElement.weight v = 2 * weight (sheet e 0 v.operators) := by
    rw [weight_eq_weight_operators]
    conv_lhs => rw [(fold_eq_one_iff e _).mp h]
    rw [weight_double]
  omega

/-- **Theorem 5.1** (any pairing, no symmetry). Let `d_K` be the least weight of
a doubling logical. Suppose (P) every logical fold has weight `≥ 2 d_K`, and
(J) for every stabilizer fold `b ≠ 1` of weight `< 2 d_K`, every nontrivial
logical operator `v` folding to `b` satisfies `wt b + 2 · (residual weight of v)
≥ 2 d_K`. Then `2 d_K` is the least weight of a nontrivial logical operator of
`S`: the distance of `S` is exactly `2 d_K`. -/
theorem isLeast_logicalWeight_two_mul_of_floors {dK : ℕ}
    (hdK : IsLeast {w | ∃ u, IsDoublingLogical e S u ∧ weight u = w} dK)
    (hP : ∀ b, IsLogicalFold e S b → 2 * dK ≤ weight b)
    (hJ : ∀ b ∈ foldImage e S, b ≠ 1 → weight b < 2 * dK →
      ∀ v, IsNontrivialLogicalOperator v S → fold e v.operators = b →
        2 * dK ≤ weight b + 2 * residualWeight e v) :
    IsLeast {w | ∃ g, IsNontrivialLogicalOperator g S ∧ NQubitPauliGroupElement.weight g = w}
      (2 * dK) := by
  constructor
  · obtain ⟨u, hu, hw⟩ := hdK.1
    exact ⟨ofOperator (double e u), isNontrivialLogicalOperator_ofOperator_double e S hu,
      by rw [weight_ofOperator_double, hw]⟩
  · rintro w ⟨v, hv, rfl⟩
    have hvc : v ∈ centralizer S := ((isNontrivialLogicalOperator_iff_operators S v).mp hv).1
    by_cases hbJ : fold e v.operators ∈ foldImage e S
    · by_cases hb1 : fold e v.operators = 1
      · exact two_mul_le_weight_of_fold_eq_one e S hv hb1 fun u hu => hdK.2 ⟨u, hu, rfl⟩
      · by_cases hlt : weight (fold e v.operators) < 2 * dK
        · have h1 := hJ _ hbJ hb1 hlt v hv rfl
          have h2 := weight_fold_add_two_mul_weight_outsideSupport_le e v.operators
          rw [weight_eq_weight_operators]
          unfold residualWeight at h1
          omega
        · push Not at hlt
          exact hlt.trans (weight_fold_le e _)
    · exact le_weight_of_fold_not_mem_foldImage e S hvc hbJ hP

/-- **Theorem 5.1**, floor form: with `d_K`, `d_P` and `m_b` as the floors
`doublingFloor`, `logicalFoldFloor` and `residual` (in `ℕ∞`, so that (P) is
vacuous when `P = J`): if `d_K = dK` is finite, `2 d_K ≤ d_P`, and
`2 d_K ≤ wt b + 2 m_b` for every stabilizer fold `b ≠ 1` of weight `< 2 d_K`,
then the distance of `S` is exactly `2 d_K`. -/
theorem isLeast_logicalWeight_two_mul {dK : ℕ} (hdK : doublingFloor e S = dK)
    (hP : 2 * doublingFloor e S ≤ logicalFoldFloor e S)
    (hJ : ∀ b ∈ foldImage e S, b ≠ 1 → weight b < 2 * dK →
      2 * (dK : ℕ∞) ≤ weight b + 2 * residual e S b) :
    IsLeast {w | ∃ g, IsNontrivialLogicalOperator g S ∧ NQubitPauliGroupElement.weight g = w}
      (2 * dK) := by
  refine isLeast_logicalWeight_two_mul_of_floors e S ((doublingFloor_eq_coe_iff e S dK).mp hdK)
    ?_ ?_
  · intro b hb
    have h := (hP.trans (logicalFoldFloor_le e S hb))
    rw [hdK] at h
    exact_mod_cast h
  · intro b hbJ hb1 hlt v hv hvb
    have h1 := hJ b hbJ hb1 hlt
    have h2 : residual e S b ≤ residualWeight e v := hvb ▸ residual_le e S hv
    have h3 : (2 * dK : ℕ∞) ≤ ((weight b + 2 * residualWeight e v : ℕ) : ℕ∞) := by
      push_cast
      refine h1.trans ?_
      gcongr
    exact_mod_cast h3

/-! ## Corollary 5.3: the symmetric form -/

/-- **Corollary 5.3** (symmetric pairing). Let the pairing be symmetric for `S`,
let `F` be a folded code (a stabilizer group on the pairs whose operator image
is the stabilizer folds `J`) and `d₀` its distance. Suppose
(W) some doubling logical has weight `d₀`;
(R) `g * g^σ` is a stabilizer for every logical operator `g`;
(F) every seam logical has weight `≥ 2 d₀`;
(S) every stabilizer fold `b ≠ 1` of weight `< 2 d₀` satisfies
`wt b + 2 · (residual weight of v) ≥ 2 d₀` for every nontrivial logical `v`
folding to `b`.
Then `2 d₀` is the least weight of a nontrivial logical operator of `S`. -/
theorem isLeast_logicalWeight_two_mul_of_symmetric (hsym : IsSymmetric e S)
    {F : StabilizerGroup m} (hF : operatorImage F.toSubgroup = foldImage e S) {d₀ : ℕ}
    (hd₀ : IsLeast {w | ∃ g, IsNontrivialLogicalOperator g F ∧
      NQubitPauliGroupElement.weight g = w} d₀)
    (hW : ∃ u, IsDoublingLogical e S u ∧ weight u = d₀)
    (hR : ∀ g ∈ centralizer S, g.operators * sheetSwap e g.operators ∈ operatorImage S.toSubgroup)
    (hFl : ∀ b, IsSeamLogical e S b → 2 * d₀ ≤ weight b)
    (hS : ∀ b ∈ foldImage e S, b ≠ 1 → weight b < 2 * d₀ →
      ∀ v, IsNontrivialLogicalOperator v S → fold e v.operators = b →
        2 * d₀ ≤ weight b + 2 * residualWeight e v) :
    IsLeast {w | ∃ g, IsNontrivialLogicalOperator g S ∧ NQubitPauliGroupElement.weight g = w}
      (2 * d₀) := by
  have hd₀' := (isLeast_logicalWeight_iff_of_operatorImage_eq e S hF d₀).mp hd₀
  have hdK := isLeast_doubling_of_witness e S hsym hd₀' hW
  have hPT := (logicalFoldImage_le_seamGroup_iff e S).mp hR
  exact isLeast_logicalWeight_two_mul_of_floors e S hdK (fun b hb => hFl b ⟨hPT hb.1, hb.2⟩) hS

/-- A nontrivial logical operator has positive weight: a weight-`0` element has
the operator part of the identity, which is a stabilizer. -/
lemma one_le_weight_of_isNontrivialLogicalOperator {F : StabilizerGroup m}
    {g : NQubitPauliGroupElement m} (hg : IsNontrivialLogicalOperator g F) :
    1 ≤ NQubitPauliGroupElement.weight g := by
  by_contra h
  push Not at h
  have h0 : NQubitPauliGroupElement.weight g = 0 := by omega
  rw [NQubitPauliGroupElement.weight_eq_zero_iff] at h0
  exact hg.2 1 F.one_mem (h0.symm ▸ rfl)

/-- Corollary 5.3 for a packaged `[[n, k]]` code: under the hypotheses of
`isLeast_logicalWeight_two_mul_of_symmetric`, a stabilizer code with stabilizer
group `S` has distance `2 d₀`. -/
theorem hasCodeDistance_two_mul_of_symmetric {k : ℕ} (C : StabilizerCode n k)
    (hC : C.toStabilizerGroup.toSubgroup = S.toSubgroup) (hsym : IsSymmetric e S)
    {F : StabilizerGroup m} (hF : operatorImage F.toSubgroup = foldImage e S) {d₀ : ℕ}
    (hd₀ : IsLeast {w | ∃ g, IsNontrivialLogicalOperator g F ∧
      NQubitPauliGroupElement.weight g = w} d₀)
    (hW : ∃ u, IsDoublingLogical e S u ∧ weight u = d₀)
    (hR : ∀ g ∈ centralizer S, g.operators * sheetSwap e g.operators ∈ operatorImage S.toSubgroup)
    (hFl : ∀ b, IsSeamLogical e S b → 2 * d₀ ≤ weight b)
    (hS : ∀ b ∈ foldImage e S, b ≠ 1 → weight b < 2 * d₀ →
      ∀ v, IsNontrivialLogicalOperator v S → fold e v.operators = b →
        2 * d₀ ≤ weight b + 2 * residualWeight e v) :
    HasCodeDistance C (2 * d₀) := by
  have h1 : 1 ≤ d₀ := by
    obtain ⟨g, hg, hw⟩ := hd₀.1
    exact hw ▸ one_le_weight_of_isNontrivialLogicalOperator hg
  exact has_code_distance_of_isLeast C hC (by omega)
    (isLeast_logicalWeight_two_mul_of_symmetric e S hsym hF hd₀ hW hR hFl hS)

/-! ## Corollary 5.5: the unconditional floor -/

/-- **Corollary 5.5** (any pairing, no hypotheses): if every doubling logical
has weight `≥ dK` and every non-identity logical fold has weight `≥ μ`, then
every nontrivial logical operator of `S` has weight `≥ min (2 dK) μ`. -/
theorem min_le_logicalWeight {dK μ : ℕ}
    (hK : ∀ u, IsDoublingLogical e S u → dK ≤ weight u)
    (hP : ∀ b ∈ logicalFoldImage e S, b ≠ 1 → μ ≤ weight b)
    {v : NQubitPauliGroupElement n} (hv : IsNontrivialLogicalOperator v S) :
    min (2 * dK) μ ≤ NQubitPauliGroupElement.weight v := by
  have hvc : v ∈ centralizer S := ((isNontrivialLogicalOperator_iff_operators S v).mp hv).1
  by_cases h1 : fold e v.operators = 1
  · exact (min_le_left _ _).trans (two_mul_le_weight_of_fold_eq_one e S hv h1 hK)
  · exact (min_le_right _ _).trans
      ((hP _ (fold_operators_mem_logicalFoldImage e S hvc) h1).trans (weight_fold_le e _))

/-- Corollary 5.5 in the symmetric case: `d(S) ≥ min (2 d₀, μ_K)`, where `d₀`
bounds the weights on `K ∖ J` and `μ_K` those of the non-identity elements of
`K`. -/
theorem min_le_logicalWeight_of_symmetric (hsym : IsSymmetric e S) {d₀ μ : ℕ}
    (hd₀ : ∀ u, u ∈ doublingGroup e S → u ∉ foldImage e S → d₀ ≤ weight u)
    (hμ : ∀ u ∈ doublingGroup e S, u ≠ 1 → μ ≤ weight u)
    {v : NQubitPauliGroupElement n} (hv : IsNontrivialLogicalOperator v S) :
    min (2 * d₀) μ ≤ NQubitPauliGroupElement.weight v :=
  min_le_logicalWeight e S (fun _ hu => le_weight_of_isDoublingLogical e S hsym hd₀ hu)
    (fun b hb hb1 => hμ b (logicalFoldImage_le_doublingGroup e S hsym hb) hb1) hv

/-! ## Corollary 4.7: clean lifts -/

/-- A lift `s` of `b` is **clean** if its sheet-`0` part is `I` or `b` on every
pair: `s = (a, a * b)` with `a_j ∈ {I, b_j}`. -/
def IsCleanLift (b : NQubitPauliOperator m) (s : NQubitPauliGroupElement n) : Prop :=
  fold e s.operators = b ∧
    ∀ j, sheet e 0 s.operators j = PauliOperator.I ∨ sheet e 0 s.operators j = b j

lemma indicator_clean (x a c : PauliOperator)
    (ha : a = PauliOperator.I ∨ a = (a.mulOp c).operator) :
    (if (x.mulOp a).operator ≠ PauliOperator.I then 1 else 0) +
      (if (x.mulOp c).operator ≠ PauliOperator.I then 1 else 0) =
      (if x ≠ PauliOperator.I then 1 else 0) +
        (if (x.mulOp (a.mulOp c).operator).operator ≠ PauliOperator.I then 1 else 0) := by
  cases x <;> cases a <;> cases c <;> revert ha <;> decide

/-- Corollary 4.7: over a clean lift `s` of `b`, the operator `double u * s`
has weight `wt u + wt (u * b)`, for any Pauli type. -/
theorem weight_double_mul_of_clean {b : NQubitPauliOperator m} {s : NQubitPauliGroupElement n}
    (hs : IsCleanLift e b s) (u : NQubitPauliOperator m) :
    weight (double e u * s.operators) = weight u + weight (u * b) := by
  rw [weight_eq_sum_pairs e, weight_eq_sum, weight_eq_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hb : b j = ((s.operators (e.symm (j, 0))).mulOp (s.operators (e.symm (j, 1)))).operator := by
    rw [← fold_apply, hs.1]
  have ha := hs.2 j
  rw [sheet_apply, hb] at ha
  simp only [mul_apply, double_apply, Equiv.apply_symm_apply, hb]
  exact indicator_clean _ _ _ ha

/-- Corollary 4.7: over a clean lift `s ∈ S` of a seam operator `b`, every
nontrivial logical operator `v` folding to `b` has weight `≥ 2 d_K`. -/
theorem two_mul_le_weight_of_clean {b : NQubitPauliOperator m} {s : NQubitPauliGroupElement n}
    (hs : s ∈ S.toSubgroup) (hclean : IsCleanLift e b s) (hbT : b ∈ seamGroup e S) {dK : ℕ}
    (hdK : ∀ u, IsDoublingLogical e S u → dK ≤ weight u)
    {v : NQubitPauliGroupElement n} (hv : IsNontrivialLogicalOperator v S)
    (hvb : fold e v.operators = b) :
    2 * dK ≤ NQubitPauliGroupElement.weight v := by
  have hu := isDoublingLogical_doublingPart e S hv hs (hclean.1.trans hvb.symm)
  have hub := hu.mul_seam e S hbT
  have hw : NQubitPauliGroupElement.weight v =
      weight (doublingPart e v s) + weight (doublingPart e v s * b) := by
    rw [weight_eq_weight_operators,
      operators_eq_double_doublingPart_mul e (hclean.1.trans hvb.symm),
      weight_double_mul_of_clean e hclean]
  have h1 := hdK _ hu
  have h2 := hdK _ hub
  omega

/-! ## Theorem 5.1 restricted to a sector

For a CSS code one wants the theorem one Pauli type at a time: hypotheses on
the X-type operators only, and a conclusion on the X-type nontrivial logical
operators. The proof of Theorem 5.1 only ever passes from a logical operator
`v` to its fold and to its sheet-`0` part, and from a doubling logical to its
double, so it goes through verbatim for any pair of predicates `Q` (on the
paired code) and `Qm` (on the pairs) with `Q P → Qm (fold P)`,
`Q P → Qm (sheet 0 P)` and `Qm u → Q (double u)`. Theorem 5.1 itself is the
case where both predicates are trivial. -/

/-- The `b = 1` rung within a sector: a nontrivial logical operator folding to
the identity has weight `≥ 2 d_K` as soon as `d_K` bounds the doubling
logicals of the sector containing its sheet-`0` part. -/
theorem two_mul_le_weight_of_fold_eq_one_of {Qm : NQubitPauliOperator m → Prop}
    {v : NQubitPauliGroupElement n} (hv : IsNontrivialLogicalOperator v S)
    (h : fold e v.operators = 1) {dK : ℕ}
    (hdK : ∀ u, IsDoublingLogical e S u → Qm u → dK ≤ weight u)
    (hQ : Qm (sheet e 0 v.operators)) :
    2 * dK ≤ NQubitPauliGroupElement.weight v := by
  have hu := hdK _ (isDoublingLogical_sheet_of_fold_eq_one e S hv h) hQ
  have hw : NQubitPauliGroupElement.weight v = 2 * weight (sheet e 0 v.operators) := by
    rw [weight_eq_weight_operators]
    conv_lhs => rw [(fold_eq_one_iff e _).mp h]
    rw [weight_double]
  omega

/-- **Theorem 5.1 in a sector.** Let `Q`, `Qm` be predicates on the operators of
the paired code and of the pairs, with `Q P → Qm (fold P)`,
`Q P → Qm (sheet 0 P)` and `Qm u → Q (double u)`. Let `d_K` be the least weight
of a doubling logical satisfying `Qm`. Suppose (P) every logical fold
satisfying `Qm` has weight `≥ 2 d_K`, and (J) for every stabilizer fold `b ≠ 1`
of weight `< 2 d_K`, every nontrivial logical operator `v` satisfying `Q` and
folding to `b` has `wt b + 2 · (residual weight of v) ≥ 2 d_K`. Then `2 d_K` is
the least weight of a nontrivial logical operator of `S` satisfying `Q`. -/
theorem isLeast_logicalWeight_two_mul_of_floors_sector
    (Q : NQubitPauliOperator n → Prop) (Qm : NQubitPauliOperator m → Prop)
    (hQfold : ∀ P, Q P → Qm (fold e P)) (hQsheet : ∀ P, Q P → Qm (sheet e 0 P))
    (hQdouble : ∀ u, Qm u → Q (double e u))
    {dK : ℕ} (hdK : IsLeast {w | ∃ u, IsDoublingLogical e S u ∧ Qm u ∧ weight u = w} dK)
    (hP : ∀ b, IsLogicalFold e S b → Qm b → 2 * dK ≤ weight b)
    (hJ : ∀ b ∈ foldImage e S, b ≠ 1 → weight b < 2 * dK →
      ∀ v, IsNontrivialLogicalOperator v S → Q v.operators → fold e v.operators = b →
        2 * dK ≤ weight b + 2 * residualWeight e v) :
    IsLeast {w | ∃ g, IsNontrivialLogicalOperator g S ∧ Q g.operators ∧
      NQubitPauliGroupElement.weight g = w} (2 * dK) := by
  constructor
  · obtain ⟨u, hu, hQu, hw⟩ := hdK.1
    exact ⟨ofOperator (double e u), isNontrivialLogicalOperator_ofOperator_double e S hu,
      hQdouble u hQu, by rw [weight_ofOperator_double, hw]⟩
  · rintro w ⟨v, hv, hQv, rfl⟩
    have hvc : v ∈ centralizer S := ((isNontrivialLogicalOperator_iff_operators S v).mp hv).1
    by_cases hbJ : fold e v.operators ∈ foldImage e S
    · by_cases hb1 : fold e v.operators = 1
      · exact two_mul_le_weight_of_fold_eq_one_of e S hv hb1
          (fun u hu hQu => hdK.2 ⟨u, hu, hQu, rfl⟩) (hQsheet _ hQv)
      · by_cases hlt : weight (fold e v.operators) < 2 * dK
        · have h1 := hJ _ hbJ hb1 hlt v hv hQv rfl
          have h2 := weight_fold_add_two_mul_weight_outsideSupport_le e v.operators
          rw [weight_eq_weight_operators]
          unfold residualWeight at h1
          omega
        · push Not at hlt
          exact hlt.trans (weight_fold_le e _)
    · exact (hP _ ⟨fold_operators_mem_logicalFoldImage e S hvc, hbJ⟩ (hQfold _ hQv)).trans
        (weight_fold_le e _)

end FoldDouble
end Stabilizer
end Quantum
