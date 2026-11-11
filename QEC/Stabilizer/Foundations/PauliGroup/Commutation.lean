import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Nat.Even
import Mathlib.Algebra.Ring.Parity
import QEC.Foundations.Foundations
import QEC.Stabilizer.Foundations.PauliGroup.NQubitElement
import QEC.Stabilizer.Foundations.PauliGroup.Representation

/-!
# Commutation in the n-qubit Pauli group

The operator part of a product does not depend on the order of the factors, so
two n-qubit Pauli group elements commute or anticommute according to the phase
contributed by `mulOp`. Qubit by qubit, that phase changes by `2` exactly at the
positions where the single-qubit factors anticommute (`anticommutesAt`), which
gives the parity characterizations:

- `commutes_iff_even_anticommutes`: `p` and `q` commute iff they anticommute at
  an even number of qubits;
- `anticommutes_iff_odd_anticommutes`: `p` and `q` anticommute iff they
  anticommute at an odd number of qubits;
- `commute_or_anticommute`: one of the two always holds.
-/

namespace Quantum
open Matrix
open scoped BigOperators

variable {n : ℕ}

namespace NQubitPauliGroupElement

/-!
## Commutation and the phase of `mulOp`
-/

/-- The operator part of a product is independent of the order of the factors;
only the phase can differ. -/
lemma operators_mul_comm (p q : NQubitPauliGroupElement n) :
    (p * q).operators = (q * p).operators := by
  ext i
  exact PauliOperator.mulOp_operator_comm _ _

/-- Two n-qubit Pauli group elements commute iff their operators contribute the
same phase when multiplied in either order. -/
lemma commutes_iff_mulOp_phasePower (p q : NQubitPauliGroupElement n) :
    p * q = q * p ↔
      (mulOp p.operators q.operators).phasePower =
        (mulOp q.operators p.operators).phasePower := by
  constructor
  · intro h
    simpa [mul, add_comm q.phasePower] using congrArg phasePower h
  · intro h
    refine NQubitPauliGroupElement.ext _ _ ?_ (operators_mul_comm p q)
    simp [mul, h, add_comm q.phasePower]

/-- Two n-qubit Pauli group elements commute if they commute at every qubit. -/
lemma commutes_of_componentwise_commutes (p q : NQubitPauliGroupElement n) :
    (∀ i : Fin n,
      (p.operators i).mulOp (q.operators i) = (q.operators i).mulOp (p.operators i)) →
      p * q = q * p := by
  intro h
  refine (commutes_iff_mulOp_phasePower p q).2 ?_
  simp only [mulOp, h]

/-- An element whose operator part is the identity (a pure phase) commutes with
every element. -/
lemma commutes_of_operators_identity (p q : NQubitPauliGroupElement n)
    (h : p.operators = NQubitPauliOperator.identity n) : p * q = q * p := by
  rw [commutes_iff_mulOp_phasePower, h, mulOp_identity_left_phase, mulOp_identity_right_phase]

/-- The identity commutes with every element. -/
lemma commutes_one_left (p : NQubitPauliGroupElement n) : 1 * p = p * 1 := by
  rw [one_mul, mul_one]

/-- Every element commutes with the identity. -/
lemma commutes_one_right (p : NQubitPauliGroupElement n) : p * 1 = 1 * p := by
  rw [mul_one, one_mul]

/-!
## Parity characterization

At each qubit the single-qubit factors either commute or anticommute, and
`mulOp p q` differs in phase from `mulOp q p` by `2` for every anticommuting
position.
-/

/-- At qubit `i`, the single-qubit factors of `p` and `q` anticommute: swapping
their order changes the phase by `2`, a factor of `-1`. -/
def anticommutesAt (p q : NQubitPauliOperator n) (i : Fin n) : Prop :=
  ((p i).mulOp (q i)).phasePower = ((q i).mulOp (p i)).phasePower + 2

/-- In `Fin 4`, a multiple `k • 2` is `0` or `2` according to the parity of
`k`. -/
private lemma nsmul_two (k : ℕ) : k • (2 : Fin 4) = if Even k then 0 else 2 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [succ_nsmul, ih]
    by_cases h : Even k <;> simp [h, Nat.even_add_one]

/-- Swapping the factors of `mulOp` changes the phase by `2` for each qubit at
which the factors anticommute. -/
lemma mulOp_phasePower_eq_add_card (p q : NQubitPauliOperator n)
    [DecidablePred (anticommutesAt p q)] :
    (mulOp p q).phasePower =
      (mulOp q p).phasePower + (Finset.univ.filter (anticommutesAt p q)).card • (2 : Fin 4) := by
  have h : ∀ i, ((p i).mulOp (q i)).phasePower =
      ((q i).mulOp (p i)).phasePower + if anticommutesAt p q i then 2 else 0 := by
    intro i
    by_cases hi : anticommutesAt p q i
    · rw [if_pos hi]
      exact hi
    · rw [if_neg hi, add_zero]
      exact (PauliOperator.mulOp_phasePower_eq_or_eq_add_two (p i) (q i)).resolve_right hi
  simp only [mulOp]
  rw [Finset.sum_congr rfl fun i _ => h i, Finset.sum_add_distrib, Finset.sum_ite,
    Finset.sum_const, Finset.sum_const_zero, add_zero]

/-- Two n-qubit Pauli group elements commute iff the number of qubits at which
their single-qubit factors anticommute is even. -/
lemma commutes_iff_even_anticommutes (p q : NQubitPauliGroupElement n) :
    p * q = q * p ↔
      (by
        classical
        exact Even ((Finset.univ.filter
          (anticommutesAt (n := n) p.operators q.operators)).card)) := by
  classical
  rw [commutes_iff_mulOp_phasePower, mulOp_phasePower_eq_add_card, add_eq_left, nsmul_two]
  simp

/-!
## Anticommutation
-/

/-- Two n-qubit Pauli group elements anticommute: `p * q = (-1) * (q * p)`. -/
def Anticommute (p q : NQubitPauliGroupElement n) : Prop :=
  p * q = minusOne n * (q * p)

/-! ### Decidability of equality and `Anticommute`

Equality of n-qubit Pauli operators is decidable qubit by qubit, so equality of
group elements is decidable field by field, and `Anticommute p q`, an equality
of two group elements, is decidable too. The `Anticommute` instance is
necessarily `noncomputable`, because multiplication on
`NQubitPauliGroupElement` is; the kernel still reduces `decide` through it, so
concrete commutation facts between literal elements close by `decide`. -/

/-- Equality of Pauli group elements is decidable, field by field. -/
instance instDecidableEq : DecidableEq (NQubitPauliGroupElement n) := fun p q =>
  decidable_of_iff (p.phasePower = q.phasePower ∧ p.operators = q.operators)
    ⟨fun ⟨h1, h2⟩ => NQubitPauliGroupElement.ext p q h1 h2, fun h => by cases h; exact ⟨rfl, rfl⟩⟩

/-- `Anticommute p q` is an equality of group elements, hence decidable. -/
noncomputable instance instDecidableAnticommute (p q : NQubitPauliGroupElement n) :
    Decidable (Anticommute p q) :=
  inferInstanceAs (Decidable (p * q = minusOne n * (q * p)))

/-- Multiplying by `minusOne n` shifts the phase by `2` and leaves the operator
part unchanged. -/
lemma minusOne_mul (g : NQubitPauliGroupElement n) :
    minusOne n * g = ⟨2 + g.phasePower, g.operators⟩ := by
  ext i <;> simp [mul, mulOp_identity_left_phase, mulOp_identity_left_op]

open Fin.CommRing in
/-- Two elements anticommute iff the phases contributed by `mulOp` in the two
orders differ by `2`. -/
lemma anticommutes_iff_mulOp_phasePower (p q : NQubitPauliGroupElement n) :
    Anticommute p q ↔
      (mulOp p.operators q.operators).phasePower =
        (mulOp q.operators p.operators).phasePower + 2 := by
  rw [Anticommute, minusOne_mul, NQubitPauliGroupElement.ext_iff,
    and_iff_left (operators_mul_comm p q)]
  simp only [mul_eq, mul]
  constructor <;> intro h <;> linear_combination h

/-- Anticommuting elements do not commute. -/
lemma Anticommute.not_commute {p q : NQubitPauliGroupElement n} (h : Anticommute p q) :
    p * q ≠ q * p := fun hc => by
  rw [anticommutes_iff_mulOp_phasePower, (commutes_iff_mulOp_phasePower p q).1 hc] at h
  exact absurd (left_eq_add.mp h) (by decide)

/-- Anticommutation only depends on operator parts: elements with equal
operator parts anticommute with the same elements. -/
lemma anticommute_congr_left {p q r : NQubitPauliGroupElement n} (h : p.operators = q.operators) :
    Anticommute p r ↔ Anticommute q r := by
  rw [anticommutes_iff_mulOp_phasePower, anticommutes_iff_mulOp_phasePower, h]

/-- If `p` and `q` anticommute, the matrix of `p * q` is `-1` times that of
`q * p`. -/
lemma Anticommute.toMatrix_neg (p q : NQubitPauliGroupElement n) (h : Anticommute p q) :
    (p * q).toMatrix = (-1 : ℂ) • (q * p).toMatrix := by
  unfold Anticommute at h
  rw [h, toMatrix_mul, minusOne_toMatrix, Matrix.smul_mul, Matrix.one_mul, toMatrix_mul]

/-- If `p` and `q` anticommute, so do their matrices. -/
lemma Anticommute.toMatrix_mul_neg (p q : NQubitPauliGroupElement n) (h : Anticommute p q) :
    p.toMatrix * q.toMatrix = (-1 : ℂ) • (q.toMatrix * p.toMatrix) := by
  rw [← toMatrix_mul, ← toMatrix_mul, Anticommute.toMatrix_neg p q h]

/-- Two n-qubit Pauli group elements anticommute iff the number of qubits at
which their single-qubit factors anticommute is odd. -/
lemma anticommutes_iff_odd_anticommutes (p q : NQubitPauliGroupElement n) :
    Anticommute p q ↔
      (by classical exact Odd ((Finset.univ.filter
        (anticommutesAt (n := n) p.operators q.operators)).card)) := by
  classical
  rw [anticommutes_iff_mulOp_phasePower, mulOp_phasePower_eq_add_card, add_right_inj, nsmul_two,
    ← Nat.not_even_iff_odd]
  split_ifs with h <;> simp [h]

/-- Anticommutation is symmetric. -/
lemma anticommute_symm (p q : NQubitPauliGroupElement n) :
    Anticommute p q → Anticommute q p := by
  unfold Anticommute
  intro h
  calc q * p = (minusOne n)⁻¹ * (minusOne n * (q * p)) := by rw [inv_mul_cancel_left]
    _ = minusOne n * (p * q) := by rw [← h, minusOne_inv]

/-- Any two n-qubit Pauli group elements either commute or anticommute. -/
lemma commute_or_anticommute (p q : NQubitPauliGroupElement n) :
    p * q = q * p ∨ Anticommute p q := by
  classical
  rcases Nat.even_or_odd
    (Finset.univ.filter (anticommutesAt (n := n) p.operators q.operators)).card with h | h
  · exact Or.inl ((commutes_iff_even_anticommutes p q).mpr h)
  · exact Or.inr ((anticommutes_iff_odd_anticommutes p q).mpr h)

end NQubitPauliGroupElement

end Quantum
