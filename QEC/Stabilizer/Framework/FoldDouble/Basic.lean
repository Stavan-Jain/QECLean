import Mathlib.Tactic
import QEC.Stabilizer.Foundations.PauliGroup.Commutation
import QEC.Stabilizer.Foundations.BinarySymplectic.SymplecticInner
import QEC.Stabilizer.Framework.Core.CSS.CSSPredicates

/-!
# Fold and double along a qubit pairing

A **pairing** of `n = 2m` qubits is an equivalence
`e : Fin n ≃ Fin m × Fin 2`: the qubit `e.symm (j, 0)` is the sheet-`0` member
of pair `j` and `e.symm (j, 1)` is its sheet-`1` partner. This file sets up
the elementary calculus of a pairing on phase-free Pauli operators
`NQubitPauliOperator n`:

* the phase-free Pauli group itself: `NQubitPauliOperator n` is a commutative
  group under the qubit-wise product (every element is an involution), and
  forgetting the phase of a Pauli group element is the group homomorphism
  `NQubitPauliGroupElement.operatorsHom`;
* the two **sheets** `sheet e s P` of an operator, the **sheet swap**
  `sheetSwap e P` (written `P^σ` below), the **fold**
  `fold e P = sheet e 0 P * sheet e 1 P` and the **double**
  `double e u = (u, u)`;
* the algebra of fold and double: `fold (double u) = 1`,
  `double (fold P) = P * P^σ`, `fold P = 1 ↔ P^σ = P ↔ P = double u` (with
  `u = sheet e 0 P`), and all four maps are group homomorphisms;
* the weight identities `wt (double u) = 2 wt u`, `wt (fold P) ≤ wt P`, and
  the exact pair-by-pair bookkeeping `wt P = wt (fold P) + 2 · overlap` for
  operators of a single Pauli type;
* the two commutation rules `⟪double u, P⟫ = ⟪u, fold P⟫` and
  `⟪fold P, fold Q⟫ = ⟪P, Q⟫ + ⟪P, Q^σ⟫` for the symplectic form, and
  the invariance of weight and symplectic form under the sheet swap.

The stabilizer-theoretic consequences — the four groups attached to a paired
stabilizer code, the folded code, and the fold-and-double distance theorem —
are developed in the sibling files of `QEC/Stabilizer/Framework/FoldDouble/`.
-/

namespace Quantum

open scoped BigOperators

variable {n m : ℕ}

/-! ## The phase-free Pauli group

`NQubitPauliOperator n` is `Fin n → PauliOperator`. The qubit-wise product of
operator parts (`PauliOperator.mulOp` with the phase discarded) makes it a
commutative group in which every element is its own inverse: it is the
quotient of the `n`-qubit Pauli group by its centre `{±1, ±i}`. -/

namespace PauliOperator

lemma mulOp_operator_assoc (a b c : PauliOperator) :
    ((a.mulOp b).operator.mulOp c).operator = (a.mulOp (b.mulOp c).operator).operator := by
  cases a <;> cases b <;> cases c <;> rfl

lemma mulOp_operator_I_left (a : PauliOperator) :
    (PauliOperator.I.mulOp a).operator = a := by
  cases a <;> rfl

lemma mulOp_operator_I_right (a : PauliOperator) :
    (a.mulOp PauliOperator.I).operator = a := by
  cases a <;> rfl

lemma mulOp_operator_self (a : PauliOperator) :
    (a.mulOp a).operator = PauliOperator.I := by
  cases a <;> rfl

/-- The operator part of a product of single-qubit Paulis is the identity iff
the two factors agree. -/
lemma mulOp_operator_eq_I_iff (a b : PauliOperator) :
    (a.mulOp b).operator = PauliOperator.I ↔ a = b := by
  cases a <;> cases b <;> decide

end PauliOperator

namespace NQubitPauliOperator

/-- The phase-free product: the operator part of the qubit-wise product. -/
noncomputable instance instMul : Mul (NQubitPauliOperator n) :=
  ⟨fun u v i => ((u i).mulOp (v i)).operator⟩

/-- The identity operator is the unit of the phase-free product. -/
instance instOne : One (NQubitPauliOperator n) := ⟨identity n⟩

/-- Every phase-free Pauli operator is its own inverse. -/
instance instInv : Inv (NQubitPauliOperator n) := ⟨fun u => u⟩

@[simp] lemma mul_apply (u v : NQubitPauliOperator n) (i : Fin n) :
    (u * v) i = ((u i).mulOp (v i)).operator := rfl

lemma one_eq_identity : (1 : NQubitPauliOperator n) = identity n := rfl

@[simp] lemma one_apply (i : Fin n) : (1 : NQubitPauliOperator n) i = PauliOperator.I := rfl

@[simp] lemma inv_eq_self (u : NQubitPauliOperator n) : u⁻¹ = u := rfl

/-- The phase-free Pauli group: `NQubitPauliOperator n` with the qubit-wise
product is a commutative group (an elementary abelian `2`-group). -/
noncomputable instance instCommGroup : CommGroup (NQubitPauliOperator n) where
  mul_assoc u v w := by
    ext i
    exact PauliOperator.mulOp_operator_assoc (u i) (v i) (w i)
  one_mul u := by
    ext i
    exact PauliOperator.mulOp_operator_I_left (u i)
  mul_one u := by
    ext i
    exact PauliOperator.mulOp_operator_I_right (u i)
  inv_mul_cancel u := by
    ext i
    exact PauliOperator.mulOp_operator_self (u i)
  mul_comm u v := by
    ext i
    exact PauliOperator.mulOp_operator_comm (u i) (v i)

/-- Every phase-free Pauli operator is an involution. -/
@[simp] lemma mul_self_eq_one (u : NQubitPauliOperator n) : u * u = 1 :=
  inv_mul_cancel u

/-- Two phase-free Pauli operators multiply to the identity iff they are equal.
-/
lemma mul_eq_one_iff (u v : NQubitPauliOperator n) : u * v = 1 ↔ u = v := by
  rw [mul_eq_one_iff_eq_inv, inv_eq_self]

@[simp] lemma weight_one : weight (1 : NQubitPauliOperator n) = 0 :=
  weight_identity n

/-- The weight as a sum of indicators over the qubits. -/
lemma weight_eq_sum (P : NQubitPauliOperator n) :
    weight P = ∑ i, if P i ≠ PauliOperator.I then 1 else 0 := by
  unfold weight support
  exact Finset.card_filter _ _

end NQubitPauliOperator

namespace NQubitPauliGroupElement

/-- Forgetting the phase is a group homomorphism from the Pauli group onto the
phase-free Pauli group. -/
def operatorsHom : NQubitPauliGroupElement n →* NQubitPauliOperator n where
  toFun := operators
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp] lemma operatorsHom_apply (g : NQubitPauliGroupElement n) :
    operatorsHom g = g.operators := rfl

/-- The operator part of a product is the phase-free product of the operator
parts. -/
lemma mul_operators (g h : NQubitPauliGroupElement n) :
    (g * h).operators = g.operators * h.operators := rfl

/-- The weight of a Pauli group element is the weight of its operator part. -/
lemma weight_eq_weight_operators (g : NQubitPauliGroupElement n) :
    weight g = NQubitPauliOperator.weight g.operators := rfl

end NQubitPauliGroupElement

namespace Stabilizer
namespace FoldDouble

open NQubitPauliOperator

/-! ## Pairings, sheets and the sheet swap -/

variable (e : Fin n ≃ Fin m × Fin 2)

@[simp] lemma rev_zero_two : Fin.rev (0 : Fin 2) = 1 := rfl

@[simp] lemma rev_one_two : Fin.rev (1 : Fin 2) = 0 := rfl

/-- The partner of a qubit: the other member of its pair. -/
def partner (i : Fin n) : Fin n := e.symm ((e i).1, Fin.rev (e i).2)

@[simp] lemma apply_partner (i : Fin n) :
    e (partner e i) = ((e i).1, Fin.rev (e i).2) := by
  simp [partner]

@[simp] lemma partner_partner (i : Fin n) : partner e (partner e i) = i := by
  simp [partner]

@[simp] lemma partner_symm_apply (j : Fin m) (s : Fin 2) :
    partner e (e.symm (j, s)) = e.symm (j, Fin.rev s) := by
  simp [partner]

/-- The partner map as a permutation of the qubits. -/
def partnerPerm : Equiv.Perm (Fin n) :=
  Function.Involutive.toPerm (partner e) (partner_partner e)

@[simp] lemma partnerPerm_apply (i : Fin n) : partnerPerm e i = partner e i := rfl

/-- Two operators agree once they agree on both members of every pair. -/
lemma ext_pairs {P Q : NQubitPauliOperator n}
    (h0 : ∀ j, P (e.symm (j, 0)) = Q (e.symm (j, 0)))
    (h1 : ∀ j, P (e.symm (j, 1)) = Q (e.symm (j, 1))) : P = Q := by
  ext i
  obtain ⟨⟨j, s⟩, rfl⟩ := e.symm.surjective i
  fin_cases s
  · exact h0 j
  · exact h1 j

/-- The sheet-`s` part of an operator: the `m`-qubit operator
`j ↦ P (j, s)`. -/
def sheet (s : Fin 2) (P : NQubitPauliOperator n) : NQubitPauliOperator m :=
  fun j => P (e.symm (j, s))

/-- The sheet swap `P ↦ P^σ`: exchange the two members of every pair. -/
def sheetSwap (P : NQubitPauliOperator n) : NQubitPauliOperator n :=
  fun i => P (partner e i)

/-- The fold `P ↦ P₀ * P₁`: multiply the two sheets. -/
noncomputable def fold (P : NQubitPauliOperator n) : NQubitPauliOperator m :=
  sheet e 0 P * sheet e 1 P

/-- The double `u ↦ (u, u)`: put `u` on both sheets. -/
def double (u : NQubitPauliOperator m) : NQubitPauliOperator n :=
  fun i => u (e i).1

@[simp] lemma sheet_apply (s : Fin 2) (P : NQubitPauliOperator n) (j : Fin m) :
    sheet e s P j = P (e.symm (j, s)) := rfl

@[simp] lemma sheetSwap_apply (P : NQubitPauliOperator n) (i : Fin n) :
    sheetSwap e P i = P (partner e i) := rfl

@[simp] lemma double_apply (u : NQubitPauliOperator m) (i : Fin n) :
    double e u i = u (e i).1 := rfl

lemma fold_apply (P : NQubitPauliOperator n) (j : Fin m) :
    fold e P j = ((P (e.symm (j, 0))).mulOp (P (e.symm (j, 1)))).operator := rfl

/-! ### The four maps are group homomorphisms (Lemma 2.3 (4)) -/

@[simp] lemma sheet_mul (s : Fin 2) (P Q : NQubitPauliOperator n) :
    sheet e s (P * Q) = sheet e s P * sheet e s Q := rfl

@[simp] lemma sheet_one (s : Fin 2) : sheet e s (1 : NQubitPauliOperator n) = 1 := rfl

@[simp] lemma sheetSwap_mul (P Q : NQubitPauliOperator n) :
    sheetSwap e (P * Q) = sheetSwap e P * sheetSwap e Q := rfl

@[simp] lemma sheetSwap_one : sheetSwap e (1 : NQubitPauliOperator n) = 1 := rfl

@[simp] lemma double_mul (u v : NQubitPauliOperator m) :
    double e (u * v) = double e u * double e v := rfl

@[simp] lemma double_one : double e (1 : NQubitPauliOperator m) = 1 := rfl

lemma fold_mul (P Q : NQubitPauliOperator n) : fold e (P * Q) = fold e P * fold e Q := by
  unfold fold
  rw [sheet_mul, sheet_mul, mul_mul_mul_comm]

@[simp] lemma fold_one : fold e (1 : NQubitPauliOperator n) = 1 := by
  unfold fold
  rw [sheet_one, sheet_one, one_mul]

/-- The sheet-`s` projection as a group homomorphism. -/
noncomputable def sheetHom (s : Fin 2) : NQubitPauliOperator n →* NQubitPauliOperator m :=
  MonoidHom.mk' (sheet e s) (sheet_mul e s)

/-- The sheet swap as a group homomorphism. -/
noncomputable def sheetSwapHom : NQubitPauliOperator n →* NQubitPauliOperator n :=
  MonoidHom.mk' (sheetSwap e) (sheetSwap_mul e)

/-- The fold as a group homomorphism. -/
noncomputable def foldHom : NQubitPauliOperator n →* NQubitPauliOperator m :=
  MonoidHom.mk' (fold e) (fold_mul e)

/-- The double as a group homomorphism. -/
noncomputable def doubleHom : NQubitPauliOperator m →* NQubitPauliOperator n :=
  MonoidHom.mk' (double e) (double_mul e)

@[simp] lemma sheetHom_apply (s : Fin 2) (P : NQubitPauliOperator n) :
    sheetHom e s P = sheet e s P := rfl

@[simp] lemma sheetSwapHom_apply (P : NQubitPauliOperator n) :
    sheetSwapHom e P = sheetSwap e P := rfl

@[simp] lemma foldHom_apply (P : NQubitPauliOperator n) : foldHom e P = fold e P := rfl

@[simp] lemma doubleHom_apply (u : NQubitPauliOperator m) : doubleHom e u = double e u := rfl

/-! ### Sheets of doubles and swaps -/

@[simp] lemma sheet_double (s : Fin 2) (u : NQubitPauliOperator m) :
    sheet e s (double e u) = u := by
  ext j
  simp

@[simp] lemma sheet_sheetSwap (s : Fin 2) (P : NQubitPauliOperator n) :
    sheet e s (sheetSwap e P) = sheet e (Fin.rev s) P := by
  ext j
  simp

@[simp] lemma sheetSwap_sheetSwap (P : NQubitPauliOperator n) :
    sheetSwap e (sheetSwap e P) = P := by
  ext i
  simp

@[simp] lemma sheetSwap_double (u : NQubitPauliOperator m) :
    sheetSwap e (double e u) = double e u := by
  ext i
  simp

lemma fold_sheetSwap (P : NQubitPauliOperator n) : fold e (sheetSwap e P) = fold e P := by
  unfold fold
  rw [sheet_sheetSwap, sheet_sheetSwap, rev_zero_two, rev_one_two, mul_comm]

/-! ### Lemma 2.3: the algebra of fold and double -/

/-- Lemma 2.3 (1): the fold of a double is the identity. -/
@[simp] theorem fold_double (u : NQubitPauliOperator m) : fold e (double e u) = 1 := by
  unfold fold
  rw [sheet_double, sheet_double, mul_self_eq_one]

/-- Lemma 2.3 (2): the double of the fold is `P * P^σ`. -/
theorem double_fold (P : NQubitPauliOperator n) : double e (fold e P) = P * sheetSwap e P := by
  refine ext_pairs e (fun j => ?_) (fun j => ?_)
  · simp [fold_apply]
  · simp [fold_apply, PauliOperator.mulOp_operator_comm]

/-- Lemma 2.3 (3): an operator folds to the identity iff it is the double of
its sheet-`0` part. -/
theorem fold_eq_one_iff (P : NQubitPauliOperator n) :
    fold e P = 1 ↔ P = double e (sheet e 0 P) := by
  constructor
  · intro h
    refine ext_pairs e (fun j => ?_) (fun j => ?_)
    · simp
    · have hj := congrFun h j
      rw [fold_apply, one_apply, PauliOperator.mulOp_operator_eq_I_iff] at hj
      simp [hj]
  · intro h
    rw [h, fold_double]

/-- Lemma 2.3 (3): an operator is fixed by the sheet swap iff it folds to the
identity. -/
theorem sheetSwap_eq_self_iff (P : NQubitPauliOperator n) :
    sheetSwap e P = P ↔ fold e P = 1 := by
  constructor
  · intro h
    have h1 : sheet e 1 P = sheet e 0 P := by
      conv_lhs => rw [← h]
      rw [sheet_sheetSwap, rev_one_two]
    unfold fold
    rw [h1, mul_self_eq_one]
  · intro h
    rw [(fold_eq_one_iff e P).mp h, sheetSwap_double]

/-- Lemma 2.3 (3): an operator folds to the identity iff it is a double. -/
theorem fold_eq_one_iff_exists (P : NQubitPauliOperator n) :
    fold e P = 1 ↔ ∃ u, P = double e u := by
  rw [fold_eq_one_iff]
  constructor
  · intro h
    exact ⟨_, h⟩
  · rintro ⟨u, rfl⟩
    rw [sheet_double]

/-- Lemma 2.3 (3): the double is injective. -/
theorem double_injective : Function.Injective (double e) :=
  Function.LeftInverse.injective (sheet_double e 0)

/-- The double of `u` is the product of its sheet-`0` lift with the sheet-`1`
lift; in particular the sheet-`0` part of `double u * t` is `u * sheet e 0 t`.
-/
lemma sheet_double_mul (s : Fin 2) (u : NQubitPauliOperator m) (t : NQubitPauliOperator n) :
    sheet e s (double e u * t) = u * sheet e s t := by
  rw [sheet_mul, sheet_double]

/-! ### Lemma 2.4: weights -/

/-- A sum over the qubits, pair by pair. -/
lemma sum_pairs {M : Type*} [AddCommMonoid M] (F : Fin n → M) :
    ∑ i, F i = ∑ j : Fin m, (F (e.symm (j, 0)) + F (e.symm (j, 1))) := by
  rw [← Equiv.sum_comp e.symm F, Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two]

/-- The weight as a sum of indicators, pair by pair. -/
lemma weight_eq_sum_pairs (P : NQubitPauliOperator n) :
    weight P = ∑ j : Fin m, ((if P (e.symm (j, 0)) ≠ PauliOperator.I then 1 else 0) +
      (if P (e.symm (j, 1)) ≠ PauliOperator.I then 1 else 0)) := by
  rw [weight_eq_sum, sum_pairs e]

/-- Lemma 2.4 (1): doubling doubles the weight. -/
theorem weight_double (u : NQubitPauliOperator m) : weight (double e u) = 2 * weight u := by
  rw [weight_eq_sum_pairs e, weight_eq_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [double_apply, Equiv.apply_symm_apply]
  ring

/-- The sheet swap preserves weight. -/
theorem weight_sheetSwap (P : NQubitPauliOperator n) : weight (sheetSwap e P) = weight P := by
  rw [weight_eq_sum, weight_eq_sum]
  exact Fintype.sum_equiv (partnerPerm e) _ _ (fun i => rfl)

lemma indicator_mulOp_le (a b : PauliOperator) :
    (if (a.mulOp b).operator ≠ PauliOperator.I then 1 else 0) ≤
      (if a ≠ PauliOperator.I then 1 else 0) + (if b ≠ PauliOperator.I then 1 else 0) := by
  cases a <;> cases b <;> decide

/-- Lemma 2.4 (2): folding does not increase weight. -/
theorem weight_fold_le (P : NQubitPauliOperator n) : weight (fold e P) ≤ weight P := by
  rw [weight_eq_sum, weight_eq_sum_pairs e]
  exact Finset.sum_le_sum fun j _ => indicator_mulOp_le _ _

/-- The number of pairs on which both sheets of `P` act nontrivially. -/
def overlap (P : NQubitPauliOperator n) : ℕ :=
  (Finset.univ.filter fun j : Fin m =>
    sheet e 0 P j ≠ PauliOperator.I ∧ sheet e 1 P j ≠ PauliOperator.I).card

lemma indicator_add_eq_of_isXType {a b : PauliOperator} (ha : a.IsXType) (hb : b.IsXType) :
    (if a ≠ PauliOperator.I then 1 else 0) + (if b ≠ PauliOperator.I then 1 else 0) =
      (if (a.mulOp b).operator ≠ PauliOperator.I then 1 else 0) +
        2 * (if a ≠ PauliOperator.I ∧ b ≠ PauliOperator.I then 1 else 0) := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> decide

lemma indicator_add_eq_of_isZType {a b : PauliOperator} (ha : a.IsZType) (hb : b.IsZType) :
    (if a ≠ PauliOperator.I then 1 else 0) + (if b ≠ PauliOperator.I then 1 else 0) =
      (if (a.mulOp b).operator ≠ PauliOperator.I then 1 else 0) +
        2 * (if a ≠ PauliOperator.I ∧ b ≠ PauliOperator.I then 1 else 0) := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> decide

/-- Lemma 2.4 (3): for an operator of a single Pauli type, the weight is the
weight of the fold plus twice the number of pairs on which both sheets act. -/
theorem weight_eq_weight_fold_add_two_mul_overlap (P : NQubitPauliOperator n)
    (hP : IsXType P ∨ IsZType P) :
    weight P = weight (fold e P) + 2 * overlap e P := by
  rw [weight_eq_sum_pairs e, weight_eq_sum, overlap, Finset.card_filter, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rcases hP with hP | hP
  · exact indicator_add_eq_of_isXType (hP _) (hP _)
  · exact indicator_add_eq_of_isZType (hP _) (hP _)

/-! ### Lemma 2.5: the two commutation rules -/

lemma symplecticProductSingle_comm (a b : PauliOperator) :
    PauliOperator.symplecticProductSingle a b = PauliOperator.symplecticProductSingle b a := by
  cases a <;> cases b <;> decide

lemma symplecticProductSingle_mulOp_right (a b c : PauliOperator) :
    PauliOperator.symplecticProductSingle a (b.mulOp c).operator =
      PauliOperator.symplecticProductSingle a b + PauliOperator.symplecticProductSingle a c := by
  cases a <;> cases b <;> cases c <;> decide

lemma symplecticProductSingle_mulOp_left (a b c : PauliOperator) :
    PauliOperator.symplecticProductSingle (a.mulOp b).operator c =
      PauliOperator.symplecticProductSingle a c + PauliOperator.symplecticProductSingle b c := by
  cases a <;> cases b <;> cases c <;> decide

/-- The symplectic form is symmetric. -/
lemma symplecticInner_comm (P Q : NQubitPauliOperator n) :
    symplecticInner P Q = symplecticInner Q P := by
  unfold symplecticInner
  exact Finset.sum_congr rfl fun i _ => symplecticProductSingle_comm _ _

/-- The symplectic form is additive in the right argument. -/
lemma symplecticInner_mul_right (P Q R : NQubitPauliOperator n) :
    symplecticInner P (Q * R) = symplecticInner P Q + symplecticInner P R := by
  unfold symplecticInner
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => symplecticProductSingle_mulOp_right _ _ _

/-- The symplectic form is additive in the left argument. -/
lemma symplecticInner_mul_left (P Q R : NQubitPauliOperator n) :
    symplecticInner (P * Q) R = symplecticInner P R + symplecticInner Q R := by
  unfold symplecticInner
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => symplecticProductSingle_mulOp_left _ _ _

/-- Lemma 2.5, first rule: `⟪double u, P⟫ = ⟪u, fold P⟫`. -/
theorem symplecticInner_double_left (u : NQubitPauliOperator m) (P : NQubitPauliOperator n) :
    symplecticInner (double e u) P = symplecticInner u (fold e P) := by
  unfold symplecticInner
  rw [sum_pairs e]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [double_apply, Equiv.apply_symm_apply, fold_apply]
  exact (symplecticProductSingle_mulOp_right _ _ _).symm

/-- Lemma 2.5, first rule, mirrored: `⟪P, double u⟫ = ⟪fold P, u⟫`. -/
theorem symplecticInner_double_right (P : NQubitPauliOperator n) (u : NQubitPauliOperator m) :
    symplecticInner P (double e u) = symplecticInner (fold e P) u := by
  rw [symplecticInner_comm, symplecticInner_double_left, symplecticInner_comm]

/-- The sheet swap preserves the symplectic form. -/
theorem symplecticInner_sheetSwap (P Q : NQubitPauliOperator n) :
    symplecticInner (sheetSwap e P) (sheetSwap e Q) = symplecticInner P Q := by
  unfold symplecticInner
  exact Fintype.sum_equiv (partnerPerm e) _ _ (fun i => rfl)

/-- The sheet swap is self-adjoint for the symplectic form. -/
theorem symplecticInner_sheetSwap_left (P Q : NQubitPauliOperator n) :
    symplecticInner (sheetSwap e P) Q = symplecticInner P (sheetSwap e Q) := by
  rw [← symplecticInner_sheetSwap e (sheetSwap e P) Q, sheetSwap_sheetSwap]

/-- Lemma 2.5, second rule:
`⟪fold P, fold Q⟫ = ⟪P, Q⟫ + ⟪P, Q^σ⟫`. -/
theorem symplecticInner_fold_fold (P Q : NQubitPauliOperator n) :
    symplecticInner (fold e P) (fold e Q) =
      symplecticInner P Q + symplecticInner P (sheetSwap e Q) := by
  rw [← symplecticInner_double_right, double_fold, symplecticInner_mul_right]

/-! ### The commutation rules for Pauli group elements -/

open NQubitPauliGroupElement in
/-- The phase-zero lift of a double commutes with `g` iff
`⟪u, fold g⟫ = 0`. -/
theorem ofOperator_double_commute_iff (u : NQubitPauliOperator m)
    (g : NQubitPauliGroupElement n) :
    ofOperator (double e u) * g = g * ofOperator (double e u) ↔
      symplecticInner u (fold e g.operators) = 0 := by
  rw [commutes_iff_symplectic_inner_zero, ofOperator_operators, symplecticInner_double_left]

open NQubitPauliGroupElement in
/-- Commutation of Pauli group elements depends only on their operator parts.
-/
theorem commute_iff_of_operators_eq {g g' h : NQubitPauliGroupElement n}
    (hg : g.operators = g'.operators) :
    g * h = h * g ↔ g' * h = h * g' := by
  rw [commutes_iff_symplectic_inner_zero, commutes_iff_symplectic_inner_zero, hg]

end FoldDouble
end Stabilizer
end Quantum
