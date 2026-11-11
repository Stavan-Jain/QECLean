import Mathlib.Tactic
import QEC.Stabilizer.Codes.Toric.Chains
import QEC.Stabilizer.Geometry.GridIndexing
import QEC.Stabilizer.Foundations.PauliGroup

/-!
# Qubits and chain operators of the toric code

The toric code has one qubit per edge of the `L × L` periodic square lattice,
`toricNumQubits L = 2 * L * L` in all. The map `edgeToQubitIdx L` numbers them:
the horizontal edge `EdgeIdx.h x y` is qubit `y * L + x`, and the vertical edge
`EdgeIdx.v x y` is qubit `L * L + y * L + x`. The numbering is injective
(`edgeToQubitIdx_injective`), hence a bijection `toricEdgeEquiv L`.

A 1-chain `c` is encoded as a Pauli group element on these qubits:
`toricXOperatorOfChain L c` has `X` on the qubits of the edges where `c` is `1`
and `I` elsewhere, and `toricZOperatorOfChain L c` has `Z` there.
-/

namespace Quantum
namespace Stabilizer
namespace Lattice

/-! ## Numbering the edges -/

/-- The number of qubits of the `L × L` toric code: one per edge. -/
abbrev toricNumQubits (L : ℕ) : ℕ := 2 * L * L

/-- The qubit of an edge: `h x y ↦ y * L + x` and
`v x y ↦ L * L + y * L + x`. -/
def edgeToQubitIdx (L : ℕ) : EdgeIdx L → Fin (toricNumQubits L)
  | EdgeIdx.h x y => ⟨y.val * L + x.val, by have := x.isLt; have := y.isLt; nlinarith⟩
  | EdgeIdx.v x y => ⟨L * L + y.val * L + x.val, by have := x.isLt; have := y.isLt; nlinarith⟩

@[simp] lemma edgeToQubitIdx_h_val (L : ℕ) (x y : Fin L) :
    (edgeToQubitIdx L (EdgeIdx.h x y)).val = y.val * L + x.val := rfl

@[simp] lemma edgeToQubitIdx_v_val (L : ℕ) (x y : Fin L) :
    (edgeToQubitIdx L (EdgeIdx.v x y)).val = L * L + y.val * L + x.val := rfl

/-- The qubits of horizontal edges are numbered below `L * L`. -/
lemma edgeToQubitIdx_h_lt_sq (L : ℕ) (x y : Fin L) :
    (edgeToQubitIdx L (EdgeIdx.h x y)).val < L * L := by
  have := x.isLt
  have := y.isLt
  rw [edgeToQubitIdx_h_val]
  nlinarith

/-- The qubits of vertical edges are numbered from `L * L` on. -/
lemma edgeToQubitIdx_v_ge_sq (L : ℕ) (x y : Fin L) :
    L * L ≤ (edgeToQubitIdx L (EdgeIdx.v x y)).val := by
  rw [edgeToQubitIdx_v_val]
  omega

/-- Distinct edges have distinct qubits. -/
lemma edgeToQubitIdx_injective (L : ℕ) [Fact (0 < L)] :
    Function.Injective (edgeToQubitIdx L) := by
  rintro (⟨x₁, y₁⟩ | ⟨x₁, y₁⟩) (⟨x₂, y₂⟩ | ⟨x₂, y₂⟩) h
  · cases rowMajor_injective L (a₁ := (x₁, y₁)) (a₂ := (x₂, y₂)) (congrArg Fin.val h)
    rfl
  · exact absurd h (fin_ne_of_val_lt_offset_le
      (edgeToQubitIdx_h_lt_sq L x₁ y₁) (edgeToQubitIdx_v_ge_sq L x₂ y₂))
  · exact absurd h.symm (fin_ne_of_val_lt_offset_le
      (edgeToQubitIdx_h_lt_sq L x₂ y₂) (edgeToQubitIdx_v_ge_sq L x₁ y₁))
  · have hval : L * L + y₁.val * L + x₁.val = L * L + y₂.val * L + x₂.val :=
      congrArg Fin.val h
    cases rowMajor_injective L (a₁ := (x₁, y₁)) (a₂ := (x₂, y₂)) (by simpa [add_assoc] using hval)
    rfl

/-- The numbering of the edges as a bijection onto the qubit indices. -/
noncomputable def toricEdgeEquiv (L : ℕ) [Fact (0 < L)] :
    EdgeIdx L ≃ Fin (toricNumQubits L) :=
  Equiv.ofBijective (edgeToQubitIdx L)
    ((Fintype.bijective_iff_injective_and_card _).2
      ⟨edgeToQubitIdx_injective L, by simp [toricNumQubits]⟩)

lemma toricEdgeEquiv_apply (L : ℕ) [Fact (0 < L)] (e : EdgeIdx L) :
    toricEdgeEquiv L e = edgeToQubitIdx L e := rfl

/-! ## Chain operators -/

/-- Encode a 1-chain as an X-type Pauli group element: `X` on the qubits of the
edges where the chain is `1`. -/
def toricXOperatorOfChain (L : ℕ) (c : C1 L) :
    NQubitPauliGroupElement (toricNumQubits L) :=
  ⟨0, fun q =>
    if ∃ e : EdgeIdx L, edgeToQubitIdx L e = q ∧ c e = 1
    then PauliOperator.X else PauliOperator.I⟩

/-- Encode a 1-chain as a Z-type Pauli group element: `Z` on the qubits of the
edges where the chain is `1`. -/
def toricZOperatorOfChain (L : ℕ) (c : C1 L) :
    NQubitPauliGroupElement (toricNumQubits L) :=
  ⟨0, fun q =>
    if ∃ e : EdgeIdx L, edgeToQubitIdx L e = q ∧ c e = 1
    then PauliOperator.Z else PauliOperator.I⟩

/-- The X-chain operator at qubit `q`. -/
lemma toricXOperatorOfChain_op_at (L : ℕ) (c : C1 L) (q : Fin (toricNumQubits L)) :
    (toricXOperatorOfChain L c).operators q =
      if ∃ e, edgeToQubitIdx L e = q ∧ c e = 1
        then PauliOperator.X else PauliOperator.I := rfl

/-- The Z-chain operator at qubit `q`. -/
lemma toricZOperatorOfChain_op_at (L : ℕ) (c : C1 L) (q : Fin (toricNumQubits L)) :
    (toricZOperatorOfChain L c).operators q =
      if ∃ e, edgeToQubitIdx L e = q ∧ c e = 1
        then PauliOperator.Z else PauliOperator.I := rfl

end Lattice
end Stabilizer
end Quantum
