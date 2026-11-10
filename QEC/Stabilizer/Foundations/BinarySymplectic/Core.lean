import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import QEC.Stabilizer.Foundations.PauliGroupSingle
import QEC.Stabilizer.Foundations.PauliGroupSingle.Operator
import QEC.Stabilizer.Foundations.PauliGroup.NQubitOperator

/-!
# Binary symplectic representation

Up to phase, a Pauli operator is a vector over `ZMod 2`:

- a single-qubit Pauli `X ^ x * Z ^ z` is the pair `(x, z)`
  (`PauliOperator.toSymplecticSingle`);
- an n-qubit Pauli operator is the vector of length `n + n` whose first `n`
  entries are the `X`-bits and whose last `n` entries are the `Z`-bits
  (`NQubitPauliOperator.toSymplectic`).
-/

namespace Quantum

variable {n : ℕ}

namespace PauliOperator

/-- The bits `(x, z)` with `P = X ^ x * Z ^ z` up to phase: `I ↦ (0, 0)`,
`X ↦ (1, 0)`, `Y ↦ (1, 1)`, `Z ↦ (0, 1)`. -/
def toSymplecticSingle (P : PauliOperator) : ZMod 2 × ZMod 2 :=
  match P with
  | I => (0, 0)
  | X => (1, 0)
  | Y => (1, 1)
  | Z => (0, 1)

@[simp] lemma toSymplecticSingle_I : toSymplecticSingle I = (0, 0) := rfl
@[simp] lemma toSymplecticSingle_X : toSymplecticSingle X = (1, 0) := rfl
@[simp] lemma toSymplecticSingle_Y : toSymplecticSingle Y = (1, 1) := rfl
@[simp] lemma toSymplecticSingle_Z : toSymplecticSingle Z = (0, 1) := rfl

/-- Distinct Pauli operators have distinct symplectic bits. -/
lemma toSymplecticSingle_injective : Function.Injective toSymplecticSingle := by
  rintro a b h
  cases a <;> cases b <;> simp at h <;> rfl

/-- The symplectic bits of a product are the sums of the symplectic bits of the
factors. -/
lemma toSymplecticSingle_add (P Q : PauliOperator) :
    ((P.mulOp Q).operator).toSymplecticSingle =
      (P.toSymplecticSingle.1 + Q.toSymplecticSingle.1,
        P.toSymplecticSingle.2 + Q.toSymplecticSingle.2) := by
  cases P <;> cases Q <;> rfl

end PauliOperator

namespace NQubitPauliOperator

/-- The symplectic vector of an n-qubit Pauli operator, indexed by
`Fin (n + n)`: positions `0, …, n - 1` hold the `X`-bits and positions
`n, …, 2n - 1` the `Z`-bits. The index type is `Fin (n + n)` so that
`Fin.castAdd` and `Fin.natAdd` address the two halves. -/
def toSymplectic (op : NQubitPauliOperator n) (j : Fin (n + n)) : ZMod 2 :=
  if h : j.val < n then
    (op ⟨j.val, h⟩).toSymplecticSingle.1
  else
    (op ⟨j.val - n, by have := j.2; omega⟩).toSymplecticSingle.2

/-- Position `Fin.castAdd n i` holds the `X`-bit of qubit `i`. -/
lemma toSymplectic_X_part (op : NQubitPauliOperator n) (i : Fin n) :
    toSymplectic op (Fin.castAdd n i) = (op i).toSymplecticSingle.1 := by
  simp [toSymplectic]

/-- Position `Fin.natAdd n i` holds the `Z`-bit of qubit `i`. -/
lemma toSymplectic_Z_part (op : NQubitPauliOperator n) (i : Fin n) :
    toSymplectic op (Fin.natAdd n i) = (op i).toSymplecticSingle.2 := by
  simp [toSymplectic]

/-- The all-`X` operator has `X`-bit `1` at every qubit. -/
lemma toSymplectic_X_one (i : Fin n) :
    toSymplectic (X n) (Fin.castAdd n i) = 1 := by
  rw [toSymplectic_X_part]; simp only [X, PauliOperator.toSymplecticSingle_X]

/-- The all-`Z` operator has `Z`-bit `1` at every qubit. -/
lemma toSymplectic_Z_one (i : Fin n) :
    toSymplectic (Z n) (Fin.natAdd n i) = 1 := by
  rw [toSymplectic_Z_part]; simp only [Z, PauliOperator.toSymplecticSingle_Z]

/-- An n-qubit Pauli operator is determined by its symplectic vector. -/
theorem toSymplectic_injective :
    Function.Injective (toSymplectic : NQubitPauliOperator n → Fin (n + n) → ZMod 2) := by
  intro op₁ op₂ h
  ext i
  apply PauliOperator.toSymplecticSingle_injective
  ext
  · have hX := congrFun h (Fin.castAdd n i)
    rwa [toSymplectic_X_part, toSymplectic_X_part] at hX
  · have hZ := congrFun h (Fin.natAdd n i)
    rwa [toSymplectic_Z_part, toSymplectic_Z_part] at hZ

end NQubitPauliOperator

end Quantum
