import Mathlib.Tactic
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Data.Complex.Basic
import QEC.Foundations.Tensor
import QEC.Foundations.Gates
import QEC.Foundations.GateConjugation
import QEC.Stabilizer.Foundations.PauliGroup.NQubitOperator
import QEC.Stabilizer.Foundations.PauliGroup.NQubitElement

/-!
# Conjugating Pauli operators by uniform transversal gates

A physical gate is **uniform transversal** when it applies the same one-qubit
gate `G` to every physical qubit, i.e. it is the `n`-fold tensor power
`tensorPowGate n G`. Conjugating an n-qubit Pauli operator by such a gate acts
qubit by qubit (`uniformTransversalGateMatrix_conjugation`), so a rule for the
single-qubit conjugation lifts to the whole register
(`uniformTransversalGateMatrix_conj_op_of_localRule`). The file specializes this
to the Hadamard gate and to the inverse phase gate `inv_S`.

Conjugation by `U` always means `U P U†`, written out as
`U * P * star U`.
-/

namespace Quantum

open Matrix
open scoped BigOperators

variable {n : ℕ}

/-!
## Uniform transversal gates
-/

/-- The matrix of the uniform transversal gate on `n` qubits, applying the
one-qubit gate `G` to every qubit. Reducibly `tensorPowMatrix n G`. -/
noncomputable abbrev uniformTransversalGateMatrix (n : ℕ) (G : OneQubitGate) :
    Matrix (NQubitBasis n) (NQubitBasis n) ℂ :=
  tensorPowMatrix n G

/-- The uniform transversal gate on `n` qubits, applying the one-qubit gate `G`
to every qubit. Reducibly `tensorPowGate n G`. -/
noncomputable abbrev uniformTransversalGate (n : ℕ) (G : OneQubitGate) : NQubitGate n :=
  tensorPowGate n G

/-- Conjugating an n-qubit Pauli operator by a uniform transversal gate
conjugates each single-qubit factor. -/
lemma uniformTransversalGateMatrix_conjugation
    (n : ℕ) (G : OneQubitGate) (op : NQubitPauliOperator n) :
    (uniformTransversalGateMatrix n G) * op.toMatrix *
      star (uniformTransversalGateMatrix n G) =
    tensorMatrix fun i => G.val * (op i).toMatrix * star G.val := by
  change tensorMatrix (fun _ => G.val) * tensorMatrix _ * star (tensorMatrix fun _ => G.val) = _
  rw [star_tensorMatrix, tensorMatrix_mul, tensorMatrix_mul]

/-!
## Lifting a single-qubit conjugation rule
-/

/-- The image of an n-qubit Pauli operator under a map of single-qubit Pauli
operators, applied on every qubit. -/
def pointwiseImage (F : PauliOperator → PauliOperator) (op : NQubitPauliOperator n) :
    NQubitPauliOperator n :=
  fun i => F (op i)

/-- The product over all qubits of a scalar attached to each single-qubit
factor. -/
noncomputable def pointwiseScalarProduct (c : PauliOperator → ℂ) (op : NQubitPauliOperator n) : ℂ :=
  (Finset.univ : Finset (Fin n)).prod (fun i => c (op i))

/-- If `G` conjugates each single-qubit Pauli `p` in a domain `Dom` to
`c p • F p`, then the uniform transversal gate conjugates an operator with all
factors in `Dom` to its pointwise image under `F`, scaled by the product of the
scalars `c`. -/
lemma uniformTransversalGateMatrix_conj_op_of_localRule
    (n : ℕ) (G : OneQubitGate) (op : NQubitPauliOperator n)
    (F : PauliOperator → PauliOperator) (c : PauliOperator → ℂ)
    (Dom : PauliOperator → Prop)
    (hDom : ∀ i, Dom (op i))
    (h_local : ∀ p : PauliOperator,
      Dom p → G.val * p.toMatrix * star G.val = (c p) • (F p).toMatrix) :
    (uniformTransversalGateMatrix n G) * op.toMatrix *
      star (uniformTransversalGateMatrix n G) =
    (pointwiseScalarProduct c op) • (pointwiseImage F op).toMatrix := by
  rw [uniformTransversalGateMatrix_conjugation, NQubitPauliOperator.toMatrix_eq_tensorMatrix,
    pointwiseScalarProduct, ← tensorMatrix_smul]
  exact congrArg tensorMatrix (funext fun i => h_local (op i) (hDom i))

/-- Gate-level form of `uniformTransversalGateMatrix_conj_op_of_localRule` for
rules without scalars. -/
lemma uniformTransversalGate_conj_op_gate_of_localRule
    (n : ℕ) (G : OneQubitGate) (op : NQubitPauliOperator n)
    (F : PauliOperator → PauliOperator)
    (Dom : PauliOperator → Prop)
    (hDom : ∀ i, Dom (op i))
    (h_local : ∀ p : PauliOperator, Dom p → G.val * p.toMatrix * star G.val = (F p).toMatrix) :
    conjByGate (uniformTransversalGate n G) op.toGate =
      (pointwiseImage F op).toGate := by
  apply Subtype.ext
  simpa [conjByGate_val, pointwiseScalarProduct] using
    uniformTransversalGateMatrix_conj_op_of_localRule n G op F (fun _ => (1 : ℂ)) Dom hDom
      (fun p hp => by simpa using h_local p hp)

/-!
## The inverse phase gate
-/

/-- Transversal `inv_S` fixes every operator whose factors are all `Z` or `I`. -/
lemma uniformTransversalGateMatrix_inv_S_conj_Z_op (n : ℕ) (op : NQubitPauliOperator n)
    (h : ∀ i, op i = .Z ∨ op i = .I) :
    (uniformTransversalGateMatrix n inv_S) * op.toMatrix *
      star (uniformTransversalGateMatrix n inv_S) = op.toMatrix := by
  rw [uniformTransversalGateMatrix_conjugation, NQubitPauliOperator.toMatrix_eq_tensorMatrix]
  refine congrArg tensorMatrix (funext fun i => ?_)
  rcases h i with hZ | hI
  · simpa [hZ] using inv_S_conj_Z
  · simp [hI]

/-- The image of an `X`/`I`-valued operator under conjugation by `inv_S`:
`X ↦ Y` and `I ↦ I` on every qubit. -/
def invSConjXIImage (op : NQubitPauliOperator n) : NQubitPauliOperator n :=
  fun i => if op i = .X then .Y else .I

/-- The sign picked up when `inv_S` conjugates an `X`/`I`-valued operator: a
factor `-1` for every `X`. -/
noncomputable def invSConjXIScalar (op : NQubitPauliOperator n) : ℂ :=
  (Finset.univ : Finset (Fin n)).prod (fun i => if op i = .X then (-1 : ℂ) else 1)

/-- The qubits at which an n-qubit Pauli operator is `X`. -/
def xSupport (op : NQubitPauliOperator n) : Finset (Fin n) :=
  (Finset.univ : Finset (Fin n)).filter (fun i => op i = .X)

/-- `invSConjXIScalar` is `-1` to the number of `X` positions. -/
lemma invSConjXIScalar_eq_negOne_pow_xSupportCard (op : NQubitPauliOperator n) :
    invSConjXIScalar op = ((-1 : ℂ) ^ (xSupport op).card) := by
  simp [invSConjXIScalar, xSupport, Finset.prod_ite]

/-- Transversal `inv_S` conjugates an `X`/`I`-valued operator to its `Y`/`I`
image, with a factor `-1` for every `X`. -/
lemma uniformTransversalGateMatrix_inv_S_conj_XI_op (n : ℕ) (op : NQubitPauliOperator n)
    (hXI : ∀ i, op i = .X ∨ op i = .I) :
    (uniformTransversalGateMatrix n inv_S) * op.toMatrix *
      star (uniformTransversalGateMatrix n inv_S) =
    (invSConjXIScalar op) • (invSConjXIImage op).toMatrix := by
  refine uniformTransversalGateMatrix_conj_op_of_localRule n inv_S op
    (fun p => if p = .X then .Y else .I) (fun p => if p = .X then (-1 : ℂ) else 1)
    (fun p => p = .X ∨ p = .I) hXI ?_
  rintro p (hX | hI)
  · simpa [hX] using inv_S_conj_X
  · simp [hI]

/-- Transversal `inv_S` conjugates all-`X` to all-`Y`, with the sign `(-1) ^ n`.
-/
lemma uniformTransversalGateMatrix_inv_S_conj_allX (n : ℕ) :
    (uniformTransversalGateMatrix n inv_S) * (NQubitPauliOperator.X n).toMatrix *
      star (uniformTransversalGateMatrix n inv_S) =
    ((-1 : ℂ) ^ n) • (NQubitPauliOperator.Y n).toMatrix := by
  rw [uniformTransversalGateMatrix_inv_S_conj_XI_op n (NQubitPauliOperator.X n) fun _ => Or.inl rfl]
  congr 1
  simp [invSConjXIScalar, NQubitPauliOperator.X]

/-- Transversal `inv_S` on a phase-free `X`/`I`-valued group element. -/
lemma uniformTransversalGateMatrix_inv_S_conj_element_XI_phase0
    (n : ℕ) (g : NQubitPauliGroupElement n)
    (h_phase : g.phasePower = 0)
    (hXI : ∀ i, g.operators i = .X ∨ g.operators i = .I) :
    (uniformTransversalGateMatrix n inv_S) * g.toMatrix *
      star (uniformTransversalGateMatrix n inv_S) =
    (invSConjXIScalar g.operators) •
      (NQubitPauliGroupElement.ofOperator (invSConjXIImage g.operators)).toMatrix := by
  simpa [NQubitPauliGroupElement.toMatrix, h_phase] using
    uniformTransversalGateMatrix_inv_S_conj_XI_op n g.operators hXI

/-!
## The Hadamard gate
-/

/-- Conjugation by `H` exchanges `X` and `Z` and fixes `I`: `H P H† = swapXZ P`
for `P ≠ Y`. -/
lemma H_conj_mul_toMatrix_mul_H_adj
    (p : PauliOperator) (h : p ≠ .Y) :
    H.val * p.toMatrix * star H.val = (PauliOperator.swapXZ p).toMatrix := by
  cases p <;> simp_all +decide [PauliOperator.swapXZ]
  · simpa using (Matrix.mem_unitaryGroup_iff.1 H.2)
  · simpa using H_conj_X
  · simpa using H_conj_Z

/-- Transversal `H` conjugates an n-qubit Pauli operator without `Y` factors to
its image under `transversalSwapXZ`. -/
lemma uniformTransversalGateMatrix_H_conj_op (n : ℕ) (op : NQubitPauliOperator n)
    (h : ∀ i, op i ≠ .Y) :
    (uniformTransversalGateMatrix n H) * op.toMatrix * star (uniformTransversalGateMatrix n H) =
      (NQubitPauliOperator.transversalSwapXZ op).toMatrix := by
  rw [uniformTransversalGateMatrix_conjugation]
  exact congrArg tensorMatrix (funext fun i => H_conj_mul_toMatrix_mul_H_adj _ (h i))

end Quantum
