import QEC.Stabilizer.Foundations.BinarySymplectic.SymplecticInner

/-!
# Concatenation: block indexing and block embedding

A concatenated code lives on `n₁ * n₂` physical qubits, grouped into `n₂`
blocks of `n₁` qubits each. This file provides the indexing of the physical
qubits by block and position, and the embedding of an operator on one block.

- `qIdx b i` is the physical qubit at position `i` of block `b`, namely
  `b * n₁ + i`; `blockOf` and `posOf` recover the block and the position, and
  `blockEquiv : Fin n₂ × Fin n₁ ≃ Fin (n₁ * n₂)` packages the three.
- `sum_eq_sum_blocks`: a sum over the physical qubits is the sum over the
  blocks of the sums over the positions of a block.
- `embedBlockOp b op` is the operator acting as `op` on block `b` and as the
  identity on the other blocks, and `embedBlock b g` is the Pauli group element
  of phase `+1` with that operator part.
- `mulOp_embedBlockOp_operators`: up to phase, embedding into a block is
  multiplicative.
-/

namespace Quantum.Concatenation

open NQubitPauliGroupElement

variable {n₁ n₂ : ℕ}

/-! ## Indexing the physical qubits by block and position -/

/-- The physical qubit at position `i` of block `b`: `b * n₁ + i`. -/
def qIdx (b : Fin n₂) (i : Fin n₁) : Fin (n₁ * n₂) :=
  ⟨b.val * n₁ + i.val, by
    calc b.val * n₁ + i.val < (b.val + 1) * n₁ := by
          rw [Nat.succ_mul]
          exact Nat.add_lt_add_left i.isLt _
      _ ≤ n₁ * n₂ := by
          rw [Nat.mul_comm]
          exact Nat.mul_le_mul_left _ b.isLt⟩

/-- The block of a physical qubit: `q / n₁`. -/
def blockOf (q : Fin (n₁ * n₂)) : Fin n₂ :=
  ⟨q.val / n₁, Nat.div_lt_of_lt_mul q.isLt⟩

/-- The position of a physical qubit within its block: `q % n₁`. -/
def posOf (q : Fin (n₁ * n₂)) : Fin n₁ :=
  ⟨q.val % n₁, Nat.mod_lt _ (Nat.pos_of_ne_zero fun h => by
    have := q.isLt
    simp [h] at this)⟩

@[simp] lemma blockOf_qIdx (b : Fin n₂) (i : Fin n₁) : blockOf (qIdx b i) = b := by
  apply Fin.ext
  simp only [blockOf, qIdx]
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ i.pos, Nat.div_eq_of_lt i.isLt, Nat.zero_add]

@[simp] lemma posOf_qIdx (b : Fin n₂) (i : Fin n₁) : posOf (qIdx b i) = i := by
  apply Fin.ext
  simp only [posOf, qIdx]
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt i.isLt]

@[simp] lemma qIdx_blockOf_posOf (q : Fin (n₁ * n₂)) : qIdx (blockOf q) (posOf q) = q :=
  Fin.ext (Nat.div_add_mod' q.val n₁)

/-- The physical qubits are indexed by pairs of a block and a position. -/
def blockEquiv : Fin n₂ × Fin n₁ ≃ Fin (n₁ * n₂) where
  toFun p := qIdx p.1 p.2
  invFun q := (blockOf q, posOf q)
  left_inv p := Prod.ext (blockOf_qIdx p.1 p.2) (posOf_qIdx p.1 p.2)
  right_inv := qIdx_blockOf_posOf

/-- Distinct positions of a block are distinct physical qubits. -/
lemma qIdx_injective (b : Fin n₂) : Function.Injective (qIdx b : Fin n₁ → Fin (n₁ * n₂)) :=
  fun i i' h => by simpa using congrArg posOf h

/-- A sum over the physical qubits is the sum over the blocks of the sums over
the positions of a block. -/
lemma sum_eq_sum_blocks {M : Type*} [AddCommMonoid M] (f : Fin (n₁ * n₂) → M) :
    ∑ q, f q = ∑ b, ∑ i, f (qIdx b i) := by
  rw [← blockEquiv.sum_comp, Fintype.sum_prod_type]
  rfl

/-! ## Embedding an operator into a block -/

/-- The operator on `n₁ * n₂` qubits that acts as `op` on block `b` and as the
identity on the other blocks. -/
def embedBlockOp (b : Fin n₂) (op : NQubitPauliOperator n₁) : NQubitPauliOperator (n₁ * n₂) :=
  fun q => if blockOf q = b then op (posOf q) else PauliOperator.I

/-- The Pauli group element of phase `+1` that acts as `g` on block `b` and as
the identity on the other blocks. The phase of `g` is discarded. -/
def embedBlock (b : Fin n₂) (g : NQubitPauliGroupElement n₁) :
    NQubitPauliGroupElement (n₁ * n₂) :=
  ofOperator (embedBlockOp b g.operators)

@[simp] lemma embedBlock_phasePower (b : Fin n₂) (g : NQubitPauliGroupElement n₁) :
    (embedBlock b g).phasePower = 0 := rfl

@[simp] lemma embedBlock_operators (b : Fin n₂) (g : NQubitPauliGroupElement n₁) :
    (embedBlock b g).operators = embedBlockOp b g.operators := rfl

@[simp] lemma embedBlockOp_qIdx (b : Fin n₂) (op : NQubitPauliOperator n₁) (i : Fin n₁) :
    embedBlockOp b op (qIdx b i) = op i := by
  simp [embedBlockOp]

/-- An operator embedded in block `b` acts as the identity on the other
blocks. -/
lemma embedBlockOp_qIdx_ne {b b' : Fin n₂} (h : b ≠ b') (op : NQubitPauliOperator n₁)
    (i : Fin n₁) : embedBlockOp b op (qIdx b' i) = PauliOperator.I := by
  simp [embedBlockOp, h.symm]

/-- Embedding the identity operator gives the identity operator. -/
@[simp] lemma embedBlockOp_identity (b : Fin n₂) :
    embedBlockOp b (NQubitPauliOperator.identity n₁) = NQubitPauliOperator.identity (n₁ * n₂) := by
  funext q
  simp [embedBlockOp, NQubitPauliOperator.identity]

@[simp] lemma embedBlock_one (b : Fin n₂) : embedBlock b (1 : NQubitPauliGroupElement n₁) = 1 :=
  congrArg ofOperator (embedBlockOp_identity b)

/-- Up to phase, embedding into a block is multiplicative: the operator part of
a product of embedded operators is the embedded operator part of the product.
The phases differ, so there is no such statement for `embedBlock` itself. -/
lemma mulOp_embedBlockOp_operators (b : Fin n₂) (g h : NQubitPauliOperator n₁) :
    (embedBlockOp b g *ₚ embedBlockOp b h).operators = embedBlockOp b (g *ₚ h).operators := by
  funext q
  by_cases hb : blockOf q = b <;> simp [mulOp, embedBlockOp, hb]

end Quantum.Concatenation
