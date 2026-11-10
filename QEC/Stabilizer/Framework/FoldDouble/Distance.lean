import QEC.Stabilizer.Framework.FoldDouble.Groups
import QEC.Stabilizer.Framework.Core.Logical.CodeDistance

/-!
# The fold-and-double distance theorem

Fix a stabilizer group `S` on `n` qubits with a pairing
`e : Fin n ≃ Fin m × Fin 2`, and the four groups `J ≤ P`, `T ≤ K` of
`FoldDouble.Groups`. A nontrivial logical operator `v` of `S` is of one of two
kinds, according to its fold `b = fold v`:

* **kind (L)**, `b ∉ J`: then `wt v ≥ wt b ≥ d_P`
  (`le_weight_of_fold_not_mem_foldImage`);
* **kind (S)**, `b ∈ J`: choose a stabilizer `s` with `fold s = b`; then
  `v = double u * s` for a unique `u`, the **doubling part** of `v`
  (`doublingPart`), which is a doubling logical
  (`isDoublingLogical_doublingPart`), and the **slice inequality**
  `wt v ≥ wt b + 2 · wt (v₀ outside supp b)` holds
  (`weight_fold_add_two_mul_weight_outsideSupport_le`), with equality for
  operators of a single Pauli type.

The **residual** `m_b` (`residual`) is the least value of
`wt (v₀ outside supp b)` over the nontrivial logicals `v` folding to `b`;
through the doubling part it is the least value of `wt ((u * a) outside supp b)`
over the doubling logicals `u`, for any lift `s = (a, a * b)` of `b`
(`residual_eq_of_lift`), and `m_1 = d_K` (`residual_one`).

Main results:

* `isLeast_logicalWeight_two_mul_of_floors`, and its floor form
  `isLeast_logicalWeight_two_mul` — the **fold-and-double theorem**: if
  `K ≠ T` with doubling floor `d_K`, if every logical fold has weight
  `≥ 2 d_K` (condition (P)), and if `wt b + 2 m_b ≥ 2 d_K` for every
  stabilizer fold `b ≠ 1` of weight `< 2 d_K` (condition (J)), then the
  distance of `S` is exactly `2 d_K`. No symmetry is needed.
  `isLeast_logicalWeight_two_mul_of_floors_sector` is the same statement
  restricted to the operators satisfying a predicate, such as the X-type
  operators of a CSS code.
* `isLeast_logicalWeight_two_mul_of_symmetric`,
  `hasCodeDistance_two_mul_of_symmetric` — the symmetric form: for a symmetric
  pairing and a folded code `F` of distance `d₀`, the four conditions
  (W) some doubling logical has weight `d₀`,
  (R) `g * g^σ ∈ G` for every logical operator `g`,
  (F) every seam logical has weight `≥ 2 d₀`,
  (S) `wt b + 2 m_b ≥ 2 d₀` for every stabilizer fold `b ≠ 1` of weight
  `< 2 d₀`, give distance exactly `2 d₀` for `S` (`IsLeast` over the nontrivial
  logical operators, and `HasCodeDistance` for a packaged code).
* `min_le_logicalWeight` — with no hypotheses at all,
  `d(S) ≥ min (2 d_K, μ_P)`, where `μ_P` is the least weight of a non-identity
  logical fold.
* `weight_double_mul_of_clean`, `two_mul_le_weight_of_clean` — over a clean
  lift, `wt v = wt u + wt (u * b)`, and if moreover `b ∈ T` then
  `wt v ≥ 2 d_K`.
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

/-- Two single-qubit Paulis contribute to the weight at least what their
product contributes, plus `2` if they are equal and not the identity. -/
private lemma indicator_slice_le (x y : PauliOperator) :
    (if (x.mulOp y).operator ≠ PauliOperator.I then 1 else 0) +
      2 * (if (if (x.mulOp y).operator = PauliOperator.I then x else PauliOperator.I) ≠
        PauliOperator.I then 1 else 0) ≤
      (if x ≠ PauliOperator.I then 1 else 0) + (if y ≠ PauliOperator.I then 1 else 0) := by
  cases x <;> cases y <;> decide

/-- The **slice inequality**: the weight of `P` is at least the weight of its
fold plus twice the weight of its sheet-`0` part outside the support of the
fold. On the support of the fold the two sheets differ, so at least one acts;
outside it they agree, so they contribute `0` or `2`. -/
theorem weight_fold_add_two_mul_weight_outsideSupport_le (P : NQubitPauliOperator n) :
    weight (fold e P) + 2 * weight (outsideSupport (fold e P) (sheet e 0 P)) ≤ weight P := by
  rw [weight_eq_sum, weight_eq_sum, weight_eq_sum_pairs e, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun j _ => indicator_slice_le _ _

/-- `indicator_slice_le` is an equality for two single-qubit Paulis that agree
unless one of them is the identity. -/
private lemma indicator_slice_eq {x y : PauliOperator}
    (h : x = PauliOperator.I ∨ y = PauliOperator.I ∨ x = y) :
    (if x ≠ PauliOperator.I then 1 else 0) + (if y ≠ PauliOperator.I then 1 else 0) =
      (if (x.mulOp y).operator ≠ PauliOperator.I then 1 else 0) +
        2 * (if (if (x.mulOp y).operator = PauliOperator.I then x else PauliOperator.I) ≠
          PauliOperator.I then 1 else 0) := by
  revert h
  cases x <;> cases y <;> decide

/-- For an operator of a single Pauli type the slice inequality is an
equality. -/
theorem weight_eq_weight_fold_add_two_mul_weight_outsideSupport (P : NQubitPauliOperator n)
    (hP : IsXType P ∨ IsZType P) :
    weight P = weight (fold e P) + 2 * weight (outsideSupport (fold e P) (sheet e 0 P)) := by
  rw [weight_eq_sum_pairs e, weight_eq_sum, weight_eq_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ =>
    indicator_slice_eq (eq_I_or_eq_I_or_eq_of_isXType_or_isZType hP _ _)

/-! ## Kind (L): the fold is not a stabilizer fold -/

/-- A logical operator whose fold is not a stabilizer fold has weight at least
the weight of its fold, hence at least any lower bound on the logical folds. -/
theorem le_weight_of_fold_not_mem_foldImage {v : NQubitPauliGroupElement n}
    (hv : v ∈ centralizer S) (hb : fold e v.operators ∉ foldImage e S) {D : ℕ}
    (hP : ∀ b, IsLogicalFold e S b → D ≤ weight b) :
    D ≤ NQubitPauliGroupElement.weight v :=
  (hP _ ⟨fold_operators_mem_logicalFoldImage e S hv, hb⟩).trans (weight_fold_le e _)

/-! ## Kind (S): the fold is a stabilizer fold, and the doubling part -/

/-- The **doubling part** of `v` relative to a lift `s` of its fold:
`u := v₀ * s₀`, so that `v = double u * s`. -/
noncomputable def doublingPart (v s : NQubitPauliGroupElement n) : NQubitPauliOperator m :=
  sheet e 0 v.operators * sheet e 0 s.operators

/-- If `s` and `v` have the same fold then `v = double u * s` with `u` the
doubling part. -/
theorem operators_eq_double_doublingPart_mul {v s : NQubitPauliGroupElement n}
    (h : fold e s.operators = fold e v.operators) :
    v.operators = double e (doublingPart e v s) * s.operators := by
  have hw : fold e (v.operators * s.operators) = 1 := by rw [fold_mul, h, mul_self_eq_one]
  rw [doublingPart, ← sheet_mul, ← (fold_eq_one_iff e _).mp hw, mul_mul_cancel_right]

/-- The doubling part is the unique `u` with `v = double u * s`. -/
theorem eq_doublingPart_of_eq_double_mul {v s : NQubitPauliGroupElement n}
    {u : NQubitPauliOperator m} (h : v.operators = double e u * s.operators) :
    u = doublingPart e v s := by
  rw [doublingPart, h, sheet_double_mul, mul_mul_cancel_right]

/-- The sheet-`0` part of `v` is the doubling part times the sheet-`0` part of
the lift: `v₀ = u * a`. -/
lemma sheet_zero_eq_doublingPart_mul (v s : NQubitPauliGroupElement n) :
    sheet e 0 v.operators = doublingPart e v s * sheet e 0 s.operators := by
  rw [doublingPart, mul_mul_cancel_right]

/-- For a nontrivial logical operator `v` and a stabilizer lift `s` of its
fold, the doubling part of `v` is a doubling logical. -/
theorem isDoublingLogical_doublingPart {v s : NQubitPauliGroupElement n}
    (hv : IsNontrivialLogicalOperator v S) (hs : s ∈ S.toSubgroup)
    (h : fold e s.operators = fold e v.operators) :
    IsDoublingLogical e S (doublingPart e v s) := by
  have hdu : double e (doublingPart e v s) = v.operators * s.operators := by
    rw [operators_eq_double_doublingPart_mul e h, mul_mul_cancel_right]
  rw [isNontrivialLogicalOperator_iff_operators] at hv
  rw [IsDoublingLogical, mem_doublingGroup, mem_seamGroup, hdu]
  exact ⟨operators_mem_operatorImage
      ((centralizer S).mul_mem hv.1 (stabilizer_le_centralizer S hs)),
    fun ht => hv.2 ((Subgroup.mul_mem_cancel_right _ (operators_mem_operatorImage hs)).mp ht)⟩

/-- Conversely, every doubling logical `u` and stabilizer `s` give a nontrivial
logical operator `double u * s` folding to `fold s`. -/
theorem isNontrivialLogicalOperator_ofOperator_double_mul {u : NQubitPauliOperator m}
    (hu : IsDoublingLogical e S u) {s : NQubitPauliGroupElement n} (hs : s ∈ S.toSubgroup) :
    IsNontrivialLogicalOperator (ofOperator (double e u * s.operators)) S :=
  (isNontrivialLogicalOperator_ofOperator_iff S _).mpr
    ⟨(operatorImage (centralizer S)).mul_mem ((mem_doublingGroup e S).mp hu.1)
        (operatorImage_le_operatorImage_centralizer S (operators_mem_operatorImage hs)),
      fun h => hu.2 ((Subgroup.mul_mem_cancel_right _ (operators_mem_operatorImage hs)).mp h)⟩

/-! ## The residual `m_b` -/

/-- The residual weight of a logical operator `v`: the weight of its sheet-`0`
part outside the support of its fold. For `v = double u * s` with
`s = (a, a * b)` a lift of `b = fold v`, this is `wt ((u * a) outside supp b)`.
-/
noncomputable def residualWeight (v : NQubitPauliGroupElement n) : ℕ :=
  weight (outsideSupport (fold e v.operators) (sheet e 0 v.operators))

/-- The slice inequality for a Pauli group element: its weight is at least the
weight of its fold plus twice its residual weight. -/
lemma weight_fold_add_two_mul_residualWeight_le (v : NQubitPauliGroupElement n) :
    weight (fold e v.operators) + 2 * residualWeight e v ≤ NQubitPauliGroupElement.weight v :=
  weight_fold_add_two_mul_weight_outsideSupport_le e v.operators

/-- The **residual** `m_b` of a stabilizer fold `b`: the least residual weight
of a nontrivial logical operator folding to `b`; `⊤` if there is none. -/
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

/-- Every nontrivial logical operator `v` folding to `b` has weight at least
`wt b + 2 m_b`. -/
theorem weight_fold_add_two_mul_residual_le {v : NQubitPauliGroupElement n}
    (hv : IsNontrivialLogicalOperator v S) :
    (weight (fold e v.operators) : ℕ∞) + 2 * residual e S (fold e v.operators) ≤
      NQubitPauliGroupElement.weight v := by
  have h := residual_le e S hv
  calc (weight (fold e v.operators) : ℕ∞) + 2 * residual e S (fold e v.operators)
      ≤ ((weight (fold e v.operators) + 2 * residualWeight e v : ℕ) : ℕ∞) := by
        push_cast
        gcongr
    _ ≤ NQubitPauliGroupElement.weight v :=
        ENat.coe_le_coe.mpr (weight_fold_add_two_mul_residualWeight_le e v)

/-- The residual through a lift. For a stabilizer `s` with `fold s = b`, `m_b`
is the least value of `wt ((u * s₀) outside supp b)` over the doubling logicals
`u`: in particular it does not depend on the lift. -/
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

/-- The residual of the identity is the doubling floor: `m_1 = d_K`. -/
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

/-! ## The fold-and-double theorem, for any pairing

For a CSS code one wants the theorem one Pauli type at a time: hypotheses on
the X-type operators only, and a conclusion on the X-type nontrivial logical
operators. The argument only ever passes from a logical operator `v` to its
fold and to its sheet-`0` part, and from a doubling logical to its double, so
it is carried out for any pair of predicates `Q` (on the paired code) and `Qm`
(on the pairs) with `Q P → Qm (fold P)`, `Q P → Qm (sheet 0 P)` and
`Qm u → Q (double u)`. The unrestricted theorem is the case where both
predicates are trivial. -/

/-- An operator folding to the identity is a double, so its weight is twice
the weight of its sheet-`0` part. -/
lemma weight_eq_two_mul_weight_sheet_of_fold_eq_one {v : NQubitPauliGroupElement n}
    (h : fold e v.operators = 1) :
    NQubitPauliGroupElement.weight v = 2 * weight (sheet e 0 v.operators) := by
  rw [weight_eq_weight_operators, ← weight_double e, ← (fold_eq_one_iff e _).mp h]

/-- A nontrivial logical operator folding to the identity is the double of a
doubling logical, so its weight is at least `2 d_K`. -/
theorem two_mul_le_weight_of_fold_eq_one {v : NQubitPauliGroupElement n}
    (hv : IsNontrivialLogicalOperator v S) (h : fold e v.operators = 1) {dK : ℕ}
    (hdK : ∀ u, IsDoublingLogical e S u → dK ≤ weight u) :
    2 * dK ≤ NQubitPauliGroupElement.weight v := by
  rw [weight_eq_two_mul_weight_sheet_of_fold_eq_one e h]
  exact Nat.mul_le_mul_left 2 (hdK _ (isDoublingLogical_sheet_of_fold_eq_one e S hv h))

/-- **The fold-and-double theorem in a sector.** Let `Q`, `Qm` be predicates on
the operators of the paired code and of the pairs, with `Q P → Qm (fold P)`,
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
    by_cases hbJ : fold e v.operators ∈ foldImage e S
    · by_cases hb1 : fold e v.operators = 1
      · rw [weight_eq_two_mul_weight_sheet_of_fold_eq_one e hb1]
        exact Nat.mul_le_mul_left 2 (hdK.2
          ⟨_, isDoublingLogical_sheet_of_fold_eq_one e S hv hb1, hQsheet _ hQv, rfl⟩)
      · rcases lt_or_ge (weight (fold e v.operators)) (2 * dK) with hlt | hge
        · exact (hJ _ hbJ hb1 hlt v hv hQv rfl).trans
            (weight_fold_add_two_mul_residualWeight_le e v)
        · exact hge.trans (weight_fold_le e _)
    · exact (hP _ ⟨fold_operators_mem_logicalFoldImage e S hv.1, hbJ⟩ (hQfold _ hQv)).trans
        (weight_fold_le e _)

/-- **The fold-and-double theorem** (any pairing, no symmetry). Let `d_K` be the
least weight of a doubling logical. Suppose (P) every logical fold has weight
`≥ 2 d_K`, and (J) for every stabilizer fold `b ≠ 1` of weight `< 2 d_K`, every
nontrivial logical operator `v` folding to `b` satisfies
`wt b + 2 · (residual weight of v) ≥ 2 d_K`. Then `2 d_K` is the least weight
of a nontrivial logical operator of `S`: the distance of `S` is exactly
`2 d_K`. -/
theorem isLeast_logicalWeight_two_mul_of_floors {dK : ℕ}
    (hdK : IsLeast {w | ∃ u, IsDoublingLogical e S u ∧ weight u = w} dK)
    (hP : ∀ b, IsLogicalFold e S b → 2 * dK ≤ weight b)
    (hJ : ∀ b ∈ foldImage e S, b ≠ 1 → weight b < 2 * dK →
      ∀ v, IsNontrivialLogicalOperator v S → fold e v.operators = b →
        2 * dK ≤ weight b + 2 * residualWeight e v) :
    IsLeast {w | ∃ g, IsNontrivialLogicalOperator g S ∧ NQubitPauliGroupElement.weight g = w}
      (2 * dK) := by
  simpa only [true_and] using
    isLeast_logicalWeight_two_mul_of_floors_sector e S (fun _ => True) (fun _ => True)
      (fun _ _ => trivial) (fun _ _ => trivial) (fun _ _ => trivial)
      (by simpa only [true_and] using hdK) (fun b hb _ => hP b hb)
      fun b hbJ hb1 hlt v hv _ hvb => hJ b hbJ hb1 hlt v hv hvb

/-- **The fold-and-double theorem**, floor form: with `d_K`, `d_P` and `m_b` as
the floors `doublingFloor`, `logicalFoldFloor` and `residual` (in `ℕ∞`, so that
(P) is vacuous when `P = J`): if `d_K = dK` is finite, `2 d_K ≤ d_P`, and
`2 d_K ≤ wt b + 2 m_b` for every stabilizer fold `b ≠ 1` of weight `< 2 d_K`,
then the distance of `S` is exactly `2 d_K`. -/
theorem isLeast_logicalWeight_two_mul {dK : ℕ} (hdK : doublingFloor e S = dK)
    (hP : 2 * doublingFloor e S ≤ logicalFoldFloor e S)
    (hJ : ∀ b ∈ foldImage e S, b ≠ 1 → weight b < 2 * dK →
      2 * (dK : ℕ∞) ≤ weight b + 2 * residual e S b) :
    IsLeast {w | ∃ g, IsNontrivialLogicalOperator g S ∧ NQubitPauliGroupElement.weight g = w}
      (2 * dK) := by
  refine isLeast_logicalWeight_two_mul_of_floors e S ((doublingFloor_eq_coe_iff e S dK).mp hdK)
    (fun b hb => ?_) fun b hbJ hb1 hlt v hv hvb => ?_
  · have h := hP.trans (logicalFoldFloor_le e S hb)
    rw [hdK] at h
    exact_mod_cast h
  · have h2 : residual e S b ≤ residualWeight e v := hvb ▸ residual_le e S hv
    have h3 : (2 * dK : ℕ∞) ≤ ((weight b + 2 * residualWeight e v : ℕ) : ℕ∞) := by
      push_cast
      refine (hJ b hbJ hb1 hlt).trans ?_
      gcongr
    exact_mod_cast h3

/-! ## The symmetric form -/

/-- **The fold-and-double theorem for a symmetric pairing.** Let the pairing be
symmetric for `S`, let `F` be a folded code (a stabilizer group on the pairs
whose operator image is the stabilizer folds `J`) and `d₀` its distance.
Suppose
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
      (2 * d₀) :=
  isLeast_logicalWeight_two_mul_of_floors e S
    (isLeast_doubling_of_witness e S hsym
      ((isLeast_logicalWeight_iff_of_operatorImage_eq e S hF d₀).mp hd₀) hW)
    (fun b hb => hFl b ⟨(logicalFoldImage_le_seamGroup_iff e S).mp hR hb.1, hb.2⟩) hS

/-- A nontrivial logical operator has positive weight: a weight-`0` element has
the operator part of the identity, which is a stabilizer. -/
lemma one_le_weight_of_isNontrivialLogicalOperator {F : StabilizerGroup m}
    {g : NQubitPauliGroupElement m} (hg : IsNontrivialLogicalOperator g F) :
    1 ≤ NQubitPauliGroupElement.weight g :=
  Nat.one_le_iff_ne_zero.mpr fun h0 =>
    hg.2 1 F.one_mem ((NQubitPauliGroupElement.weight_eq_zero_iff g).mp h0).symm

/-- The symmetric form for a packaged `[[n, k]]` code: under the hypotheses of
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
  exact hasCodeDistance_of_isLeast C hC (by omega)
    (isLeast_logicalWeight_two_mul_of_symmetric e S hsym hF hd₀ hW hR hFl hS)

/-! ## The unconditional floor -/

/-- With no hypotheses on the pairing: if every doubling logical has weight
`≥ dK` and every non-identity logical fold has weight `≥ μ`, then every
nontrivial logical operator of `S` has weight `≥ min (2 dK) μ`. -/
theorem min_le_logicalWeight {dK μ : ℕ}
    (hK : ∀ u, IsDoublingLogical e S u → dK ≤ weight u)
    (hP : ∀ b ∈ logicalFoldImage e S, b ≠ 1 → μ ≤ weight b)
    {v : NQubitPauliGroupElement n} (hv : IsNontrivialLogicalOperator v S) :
    min (2 * dK) μ ≤ NQubitPauliGroupElement.weight v := by
  by_cases h1 : fold e v.operators = 1
  · exact (min_le_left _ _).trans (two_mul_le_weight_of_fold_eq_one e S hv h1 hK)
  · exact (min_le_right _ _).trans
      ((hP _ (fold_operators_mem_logicalFoldImage e S hv.1) h1).trans (weight_fold_le e _))

/-- The unconditional floor in the symmetric case: `d(S) ≥ min (2 d₀, μ_K)`,
where `d₀` bounds the weights on `K ∖ J` and `μ_K` those of the non-identity
elements of `K`. -/
theorem min_le_logicalWeight_of_symmetric (hsym : IsSymmetric e S) {d₀ μ : ℕ}
    (hd₀ : ∀ u, u ∈ doublingGroup e S → u ∉ foldImage e S → d₀ ≤ weight u)
    (hμ : ∀ u ∈ doublingGroup e S, u ≠ 1 → μ ≤ weight u)
    {v : NQubitPauliGroupElement n} (hv : IsNontrivialLogicalOperator v S) :
    min (2 * d₀) μ ≤ NQubitPauliGroupElement.weight v :=
  min_le_logicalWeight e S (fun _ hu => le_weight_of_isDoublingLogical e S hsym hd₀ hu)
    (fun b hb hb1 => hμ b (logicalFoldImage_le_doublingGroup e S hsym hb) hb1) hv

/-! ## Clean lifts -/

/-- A lift `s` of `b` is **clean** if its sheet-`0` part is `I` or `b` on every
pair: `s = (a, a * b)` with `a_j ∈ {I, b_j}`. -/
def IsCleanLift (b : NQubitPauliOperator m) (s : NQubitPauliGroupElement n) : Prop :=
  fold e s.operators = b ∧
    ∀ j, sheet e 0 s.operators j = PauliOperator.I ∨ sheet e 0 s.operators j = b j

/-- The sheet-`0` part of a clean lift of `b` is supported inside the support
of `b`. -/
lemma IsCleanLift.support_sheet_subset {b : NQubitPauliOperator m}
    {s : NQubitPauliGroupElement n} (h : IsCleanLift e b s) :
    support (sheet e 0 s.operators) ⊆ support b := by
  intro j hj
  rw [NQubitPauliOperator.mem_support] at hj ⊢
  exact (h.2 j).elim (fun h0 => absurd h0 hj) fun h0 => h0 ▸ hj

/-- The pair-by-pair weight count behind `weight_double_mul_of_clean`: with
`(a, c)` the two sheets of a clean lift on one pair and `x` the doubled
operator there. -/
private lemma indicator_clean (x a c : PauliOperator)
    (ha : a = PauliOperator.I ∨ a = (a.mulOp c).operator) :
    (if (x.mulOp a).operator ≠ PauliOperator.I then 1 else 0) +
      (if (x.mulOp c).operator ≠ PauliOperator.I then 1 else 0) =
      (if x ≠ PauliOperator.I then 1 else 0) +
        (if (x.mulOp (a.mulOp c).operator).operator ≠ PauliOperator.I then 1 else 0) := by
  revert ha
  cases x <;> cases a <;> cases c <;> decide

/-- Over a clean lift `s` of `b`, the operator `double u * s` has weight
`wt u + wt (u * b)`, for any Pauli type. -/
theorem weight_double_mul_of_clean {b : NQubitPauliOperator m} {s : NQubitPauliGroupElement n}
    (hs : IsCleanLift e b s) (u : NQubitPauliOperator m) :
    weight (double e u * s.operators) = weight u + weight (u * b) := by
  obtain ⟨rfl, ha⟩ := hs
  rw [weight_eq_sum_pairs e, weight_eq_sum, weight_eq_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [mul_apply, double_apply, Equiv.apply_symm_apply, fold_apply]
  exact indicator_clean _ _ _ (ha j)

/-- Over a clean lift `s ∈ S` of a seam operator `b`, every nontrivial logical
operator `v` folding to `b` has weight `≥ 2 d_K`. -/
theorem two_mul_le_weight_of_clean {b : NQubitPauliOperator m} {s : NQubitPauliGroupElement n}
    (hs : s ∈ S.toSubgroup) (hclean : IsCleanLift e b s) (hbT : b ∈ seamGroup e S) {dK : ℕ}
    (hdK : ∀ u, IsDoublingLogical e S u → dK ≤ weight u)
    {v : NQubitPauliGroupElement n} (hv : IsNontrivialLogicalOperator v S)
    (hvb : fold e v.operators = b) :
    2 * dK ≤ NQubitPauliGroupElement.weight v := by
  have hfold := hclean.1.trans hvb.symm
  have hu := isDoublingLogical_doublingPart e S hv hs hfold
  rw [weight_eq_weight_operators, operators_eq_double_doublingPart_mul e hfold,
    weight_double_mul_of_clean e hclean, two_mul]
  exact add_le_add (hdK _ hu) (hdK _ (hu.mul_seam e S hbT))

end FoldDouble
end Stabilizer
end Quantum
