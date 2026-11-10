import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic
import Mathlib.Algebra.Group.Defs
import QEC.Foundations.Foundations
import QEC.Stabilizer.Foundations.PauliGroupSingle

/-!
# N-qubit Pauli operators

- `tensorMatrix`: the tensor product of a family of single-qubit matrices, with
  the lemmas that compute products, adjoints, scalar multiples and traces
  qubit by qubit.
- `NQubitPauliOperator n`: a Pauli operator on each of `n` qubits, with basic
  constructors (`identity`, `X`, `Y`, `Z`, `set`), its matrix and gate
  (`toMatrix`, `toGate`), and its `support` and `weight`.
-/

namespace Quantum
open Matrix
open scoped BigOperators

variable {n : ℕ}

/-!
## Tensor products of single-qubit matrices
-/

/-- The tensor product of a family of single-qubit matrices, one per qubit: its
entry at `(b₁, b₂)` is the product of the entries `A i (b₁ i) (b₂ i)`. -/
def tensorMatrix (A : Fin n → Matrix QubitBasis QubitBasis ℂ) :
    Matrix (NQubitBasis n) (NQubitBasis n) ℂ :=
  fun b₁ b₂ => ∏ i, A i (b₁ i) (b₂ i)

lemma tensorMatrix_apply (A : Fin n → Matrix QubitBasis QubitBasis ℂ) (b₁ b₂ : NQubitBasis n) :
    tensorMatrix A b₁ b₂ = ∏ i, A i (b₁ i) (b₂ i) := rfl

/-- Tensor products multiply qubit by qubit. -/
lemma tensorMatrix_mul (A B : Fin n → Matrix QubitBasis QubitBasis ℂ) :
    tensorMatrix A * tensorMatrix B = tensorMatrix fun i => A i * B i := by
  ext b₁ b₂
  simp only [Matrix.mul_apply, tensorMatrix_apply, ← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum fun i k => A i (b₁ i) k * B i k (b₂ i)).symm

/-- The tensor product of identity matrices is the identity matrix. -/
@[simp] lemma tensorMatrix_one :
    tensorMatrix (fun _ : Fin n => (1 : Matrix QubitBasis QubitBasis ℂ)) = 1 := by
  ext b₁ b₂
  simp [tensorMatrix_apply, Matrix.one_apply, Finset.prod_ite_zero, funext_iff]

/-- The adjoint of a tensor product is the tensor product of the adjoints. -/
lemma star_tensorMatrix (A : Fin n → Matrix QubitBasis QubitBasis ℂ) :
    star (tensorMatrix A) = tensorMatrix fun i => star (A i) := by
  ext b₁ b₂
  simp [tensorMatrix_apply, Matrix.star_apply]

/-- Scalars on the factors of a tensor product multiply out. -/
lemma tensorMatrix_smul (c : Fin n → ℂ) (A : Fin n → Matrix QubitBasis QubitBasis ℂ) :
    tensorMatrix (fun i => c i • A i) = (∏ i, c i) • tensorMatrix A := by
  ext b₁ b₂
  simp [tensorMatrix_apply, Finset.prod_mul_distrib]

/-- The trace of a tensor product is the product of the traces. -/
lemma trace_tensorMatrix (A : Fin n → Matrix QubitBasis QubitBasis ℂ) :
    (tensorMatrix A).trace = ∏ i, (A i).trace := by
  simp only [Matrix.trace, Matrix.diag_apply, tensorMatrix_apply]
  exact (Fintype.prod_sum fun i k => A i k k).symm

/-- A tensor product of unitary matrices is unitary. -/
lemma tensorMatrix_mem_unitaryGroup {A : Fin n → Matrix QubitBasis QubitBasis ℂ}
    (h : ∀ i, A i ∈ Matrix.unitaryGroup QubitBasis ℂ) :
    tensorMatrix A ∈ Matrix.unitaryGroup (NQubitBasis n) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, star_tensorMatrix, tensorMatrix_mul]
  simp [fun i => Matrix.mem_unitaryGroup_iff.1 (h i)]

/-!
## N-qubit Pauli operators
-/

/-- An n-qubit Pauli operator: a single-qubit Pauli operator on each of the `n`
qubits. Its matrix is the tensor product of the single-qubit Pauli matrices. -/
def NQubitPauliOperator (n : ℕ) : Type := Fin n → PauliOperator

namespace NQubitPauliOperator

/-- Two n-qubit Pauli operators are equal when they agree on every qubit. -/
@[ext] theorem ext {op₁ op₂ : NQubitPauliOperator n} (h : ∀ i, op₁ i = op₂ i) : op₁ = op₂ :=
  funext h

/-- Equality of n-qubit Pauli operators is decidable, qubit by qubit. The
instance is computable, so `decide` evaluates equalities of concrete operators. -/
instance : DecidableEq (NQubitPauliOperator n) :=
  inferInstanceAs (DecidableEq (Fin n → PauliOperator))

/-- The identity n-qubit Pauli operator `I ⊗ I ⊗ ... ⊗ I`. -/
def identity (n : ℕ) : NQubitPauliOperator n :=
  fun _ => PauliOperator.I

/-- The all-`X` n-qubit Pauli operator `X ⊗ X ⊗ ... ⊗ X`. -/
def X (n : ℕ) : NQubitPauliOperator n :=
  fun _ => PauliOperator.X

/-- The all-`Y` n-qubit Pauli operator `Y ⊗ Y ⊗ ... ⊗ Y`. -/
def Y (n : ℕ) : NQubitPauliOperator n :=
  fun _ => PauliOperator.Y

/-- The all-`Z` n-qubit Pauli operator `Z ⊗ Z ⊗ ... ⊗ Z`. -/
def Z (n : ℕ) : NQubitPauliOperator n :=
  fun _ => PauliOperator.Z

/-- The Pauli operator at qubit `i`. -/
def get (op : NQubitPauliOperator n) (i : Fin n) : PauliOperator := op i

/-- Replace the Pauli operator at qubit `i` by `p`. -/
def set (op : NQubitPauliOperator n) (i : Fin n) (p : PauliOperator) :
    NQubitPauliOperator n :=
  fun j => if j = i then p else op j

/-- Apply `PauliOperator.swapXZ` (exchange `X` and `Z`) on every qubit. -/
def transversalSwapXZ (op : NQubitPauliOperator n) : NQubitPauliOperator n :=
  fun i => PauliOperator.swapXZ (op i)

/-- The matrix of an n-qubit Pauli operator: the tensor product of its
single-qubit Pauli matrices, with entry `∏ i, (op i).toMatrix (b₁ i) (b₂ i)` at
`(b₁, b₂)`. -/
noncomputable def toMatrix (op : NQubitPauliOperator n) :
    Matrix (NQubitBasis n) (NQubitBasis n) ℂ :=
  fun b₁ b₂ => (Finset.univ : Finset (Fin n)).prod (fun i => (op i).toMatrix (b₁ i) (b₂ i))

/-- `toMatrix` is the tensor product of the single-qubit Pauli matrices. -/
lemma toMatrix_eq_tensorMatrix (op : NQubitPauliOperator n) :
    op.toMatrix = tensorMatrix fun i => (op i).toMatrix := rfl

/-- The n-qubit Pauli operator whose `i`-th factor is the `i`-th entry of a
list of length `n`. -/
def ofList (ops : List PauliOperator) (h : ops.length = n) :
    NQubitPauliOperator n :=
  fun i => ops.get ⟨i.val, h ▸ i.isLt⟩

/-- The list of single-qubit factors of an n-qubit Pauli operator. -/
def toList (op : NQubitPauliOperator n) : List PauliOperator :=
  List.ofFn op

/-- The matrix of the identity operator is the identity matrix. -/
lemma identity_toMatrix (n : ℕ) :
    (identity n).toMatrix = (1 : Matrix (NQubitBasis n) (NQubitBasis n) ℂ) :=
  tensorMatrix_one

/-- The matrix of an n-qubit Pauli operator is unitary. -/
lemma toMatrix_mem_unitaryGroup (op : NQubitPauliOperator n) :
    op.toMatrix ∈ Matrix.unitaryGroup (NQubitBasis n) ℂ :=
  tensorMatrix_mem_unitaryGroup fun i => (op i).toMatrix_mem_unitaryGroup

/-- The quantum gate of an n-qubit Pauli operator; its underlying matrix is
`toMatrix` (`toGate_val`). -/
noncomputable def toGate (op : NQubitPauliOperator n) : QuantumGate (NQubitBasis n) :=
  ⟨op.toMatrix, toMatrix_mem_unitaryGroup op⟩

/-- The matrix underlying `toGate` is `toMatrix`. -/
@[simp] lemma toGate_val (op : NQubitPauliOperator n) : (op.toGate).val = op.toMatrix := rfl

/-!
## Pauli weight and support

The **support** of an n-qubit Pauli operator is the set of qubits on which it
acts nontrivially (not as `I`). The **weight** is the size of the support.
-/

/-- The support of an n-qubit Pauli operator: the qubits where it is not `I`. -/
def support (op : NQubitPauliOperator n) : Finset (Fin n) :=
  Finset.univ.filter (fun i => op i ≠ PauliOperator.I)

/-- The Pauli weight: the number of qubits on which the operator is not `I`. -/
def weight (op : NQubitPauliOperator n) : ℕ :=
  (support op).card

@[simp] lemma mem_support (op : NQubitPauliOperator n) (i : Fin n) :
    i ∈ support op ↔ op i ≠ PauliOperator.I := by
  simp [support]

@[simp] lemma support_identity (n : ℕ) : support (identity n) = ∅ := by
  ext i
  simp [support, identity]

@[simp] lemma weight_identity (n : ℕ) : weight (identity n) = 0 := by
  simp [weight, support_identity]

lemma support_X (n : ℕ) : support (X n) = Finset.univ := by
  ext i
  simp [support, X]

@[simp] lemma weight_X (n : ℕ) : weight (X n) = n := by
  simp [weight, support_X]

lemma support_Z (n : ℕ) : support (Z n) = Finset.univ := by
  ext i
  simp [support, Z]

@[simp] lemma weight_Z (n : ℕ) : weight (Z n) = n := by
  simp [weight, support_Z]

lemma support_Y (n : ℕ) : support (Y n) = Finset.univ := by
  ext i
  simp [support, Y]

@[simp] lemma weight_Y (n : ℕ) : weight (Y n) = n := by
  simp [weight, support_Y]

/-- An operator has weight zero iff it is the identity. -/
lemma weight_eq_zero_iff (op : NQubitPauliOperator n) :
    weight op = 0 ↔ op = identity n := by
  simp [weight, support, Finset.filter_eq_empty_iff, NQubitPauliOperator.ext_iff, identity]

end NQubitPauliOperator

end Quantum
