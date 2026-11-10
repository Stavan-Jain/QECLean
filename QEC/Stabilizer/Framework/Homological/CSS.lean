import QEC.Stabilizer.Framework.Homological.Code
import QEC.Stabilizer.Foundations.PauliGroup
import QEC.Stabilizer.Framework.Core

/-!
# Chain operators of a homological code

A 1-chain `c` of a `HomologicalCode` is encoded as a Pauli operator on the
qubits numbered by `edgeEquiv`: `chainXOperator c` has `X` on the edges with
`c e = 1` and `I` elsewhere, and `chainZOperator c` has `Z` there. Conversely,
`xChainOf g` and `zChainOf g` are the X-support and Z-support chains of an
arbitrary Pauli group element `g`.

Main results:

* `chainXOperator_operators_edgeEquiv`, `chainZOperator_operators_edgeEquiv`:
  the chain operators read on the qubit of an edge;
* `chainXOperator_isXType`, `chainZOperator_isZType`;
* `chainXOperator_zero`, `chainXOperator_add` and their Z analogues: the
  encodings turn sums of chains into products of operators;
* `xChainOf_chainXOperator`, `zChainOf_chainZOperator`: the support chains
  recover the chain, so the encodings are injective
  (`chainXOperator_injective`, `chainZOperator_injective`);
* `chainXOperator_xChainOf_op_at`, `chainZOperator_zChainOf_op_at`: the X-only
  and Z-only parts of a Pauli group element.
-/

namespace Quantum
namespace Stabilizer
namespace Homological

open scoped BigOperators
open NQubitPauliGroupElement (IsXTypeElement IsZTypeElement)

namespace HomologicalCode

variable (X : HomologicalCode)

/-- Encode a 1-chain as an X-type Pauli group element: `X` on the qubits of the
edges where the chain is `1`. -/
noncomputable def chainXOperator (c : X.C1 → ZMod 2) :
    NQubitPauliGroupElement X.numQubits :=
  ⟨0, fun q =>
    if ∃ e : X.C1, X.edgeEquiv e = q ∧ c e = 1
    then PauliOperator.X else PauliOperator.I⟩

/-- Encode a 1-chain as a Z-type Pauli group element: `Z` on the qubits of the
edges where the chain is `1`. -/
noncomputable def chainZOperator (c : X.C1 → ZMod 2) :
    NQubitPauliGroupElement X.numQubits :=
  ⟨0, fun q =>
    if ∃ e : X.C1, X.edgeEquiv e = q ∧ c e = 1
    then PauliOperator.Z else PauliOperator.I⟩

/-- The X-support chain of a Pauli group element: `1` on the edges where it
acts as `X` or `Y`. -/
noncomputable def xChainOf (g : NQubitPauliGroupElement X.numQubits) :
    X.C1 → ZMod 2 :=
  fun e =>
    if g.operators (X.edgeEquiv e) = PauliOperator.X ∨
       g.operators (X.edgeEquiv e) = PauliOperator.Y
    then 1 else 0

/-- The Z-support chain of a Pauli group element: `1` on the edges where it
acts as `Z` or `Y`. -/
noncomputable def zChainOf (g : NQubitPauliGroupElement X.numQubits) :
    X.C1 → ZMod 2 :=
  fun e =>
    if g.operators (X.edgeEquiv e) = PauliOperator.Z ∨
       g.operators (X.edgeEquiv e) = PauliOperator.Y
    then 1 else 0

variable {X}

/-! ## The chain operators qubit by qubit -/

/-- The X-chain operator at qubit `q`. -/
lemma chainXOperator_op_at (c : X.C1 → ZMod 2) (q : Fin X.numQubits) :
    (X.chainXOperator c).operators q =
      if ∃ e : X.C1, X.edgeEquiv e = q ∧ c e = 1
      then PauliOperator.X else PauliOperator.I := rfl

/-- The Z-chain operator at qubit `q`. -/
lemma chainZOperator_op_at (c : X.C1 → ZMod 2) (q : Fin X.numQubits) :
    (X.chainZOperator c).operators q =
      if ∃ e : X.C1, X.edgeEquiv e = q ∧ c e = 1
      then PauliOperator.Z else PauliOperator.I := rfl

/-- The X-chain operator of `c` at the qubit of the edge `e`. -/
lemma chainXOperator_operators_edgeEquiv (c : X.C1 → ZMod 2) (e : X.C1) :
    (X.chainXOperator c).operators (X.edgeEquiv e) =
      if c e = 1 then PauliOperator.X else PauliOperator.I := by
  simp only [chainXOperator_op_at, Equiv.apply_eq_iff_eq, exists_eq_left]

/-- The Z-chain operator of `c` at the qubit of the edge `e`. -/
lemma chainZOperator_operators_edgeEquiv (c : X.C1 → ZMod 2) (e : X.C1) :
    (X.chainZOperator c).operators (X.edgeEquiv e) =
      if c e = 1 then PauliOperator.Z else PauliOperator.I := by
  simp only [chainZOperator_op_at, Equiv.apply_eq_iff_eq, exists_eq_left]

/-- The qubit of an edge `e` is in the support of `chainXOperator c` iff
`c e = 1`. -/
lemma mem_support_chainXOperator_iff (c : X.C1 → ZMod 2) (e : X.C1) :
    X.edgeEquiv e ∈ (X.chainXOperator c).operators.support ↔ c e = 1 := by
  rw [NQubitPauliOperator.mem_support, chainXOperator_operators_edgeEquiv]
  split_ifs with h <;> simp [h]

/-- The qubit of an edge `e` is in the support of `chainZOperator c` iff
`c e = 1`. -/
lemma mem_support_chainZOperator_iff (c : X.C1 → ZMod 2) (e : X.C1) :
    X.edgeEquiv e ∈ (X.chainZOperator c).operators.support ↔ c e = 1 := by
  rw [NQubitPauliOperator.mem_support, chainZOperator_operators_edgeEquiv]
  split_ifs with h <;> simp [h]

/-- The X-chain operator is X-type: phase `0`, every factor `X` or `I`. -/
lemma chainXOperator_isXType (c : X.C1 → ZMod 2) :
    IsXTypeElement (X.chainXOperator c) :=
  ⟨rfl, fun q => by
    rw [chainXOperator_op_at]
    split_ifs
    exacts [PauliOperator.IsXType_X, PauliOperator.IsXType_I]⟩

/-- The Z-chain operator is Z-type: phase `0`, every factor `Z` or `I`. -/
lemma chainZOperator_isZType (c : X.C1 → ZMod 2) :
    IsZTypeElement (X.chainZOperator c) :=
  ⟨rfl, fun q => by
    rw [chainZOperator_op_at]
    split_ifs
    exacts [PauliOperator.IsZType_Z, PauliOperator.IsZType_I]⟩

/-! ## The encodings are group homomorphisms -/

/-- `chainXOperator 0 = 1`. -/
@[simp] lemma chainXOperator_zero : X.chainXOperator 0 = 1 :=
  NQubitPauliGroupElement.ext _ _ rfl <| funext fun q => by
    simp [chainXOperator_op_at, NQubitPauliOperator.identity]

/-- `chainZOperator 0 = 1`. -/
@[simp] lemma chainZOperator_zero : X.chainZOperator 0 = 1 :=
  NQubitPauliGroupElement.ext _ _ rfl <| funext fun q => by
    simp [chainZOperator_op_at, NQubitPauliOperator.identity]

/-- On one qubit, adding two `ZMod 2` coefficients multiplies the corresponding
powers of a Pauli operator `P`. -/
private lemma ite_add_eq_mulOp (P : PauliOperator) (a b : ZMod 2) :
    (if a + b = 1 then P else PauliOperator.I) =
      ((if a = 1 then P else PauliOperator.I).mulOp
        (if b = 1 then P else PauliOperator.I)).operator := by
  revert a b
  cases P <;> decide

/-- The X encoding turns sums of chains into products:
`chainXOperator (c + c') = chainXOperator c * chainXOperator c'`. -/
theorem chainXOperator_add (c c' : X.C1 → ZMod 2) :
    X.chainXOperator (c + c') = X.chainXOperator c * X.chainXOperator c' := by
  refine NQubitPauliGroupElement.ext _ _
    (NQubitPauliGroupElement.IsXTypeElement_mul (chainXOperator_isXType c)
      (chainXOperator_isXType c')).1.symm (funext fun q => ?_)
  obtain ⟨e, rfl⟩ := X.edgeEquiv.surjective q
  change _ = (((X.chainXOperator c).operators (X.edgeEquiv e)).mulOp
    ((X.chainXOperator c').operators (X.edgeEquiv e))).operator
  simp only [chainXOperator_operators_edgeEquiv, Pi.add_apply, ite_add_eq_mulOp]

/-- The Z encoding turns sums of chains into products:
`chainZOperator (c + c') = chainZOperator c * chainZOperator c'`. -/
theorem chainZOperator_add (c c' : X.C1 → ZMod 2) :
    X.chainZOperator (c + c') = X.chainZOperator c * X.chainZOperator c' := by
  refine NQubitPauliGroupElement.ext _ _
    (NQubitPauliGroupElement.IsZTypeElement_mul (chainZOperator_isZType c)
      (chainZOperator_isZType c')).1.symm (funext fun q => ?_)
  obtain ⟨e, rfl⟩ := X.edgeEquiv.surjective q
  change _ = (((X.chainZOperator c).operators (X.edgeEquiv e)).mulOp
    ((X.chainZOperator c').operators (X.edgeEquiv e))).operator
  simp only [chainZOperator_operators_edgeEquiv, Pi.add_apply, ite_add_eq_mulOp]

/-- `chainXOperator c` is its own inverse. -/
lemma chainXOperator_inv (c : X.C1 → ZMod 2) :
    (X.chainXOperator c)⁻¹ = X.chainXOperator c :=
  NQubitPauliGroupElement.ext _ _ (show -(0 : Fin 4) = 0 by decide) rfl

/-- `chainZOperator c` is its own inverse. -/
lemma chainZOperator_inv (c : X.C1 → ZMod 2) :
    (X.chainZOperator c)⁻¹ = X.chainZOperator c :=
  NQubitPauliGroupElement.ext _ _ (show -(0 : Fin 4) = 0 by decide) rfl

/-! ## Support chains -/

/-- The X-support chain of `chainXOperator c` is `c`. -/
lemma xChainOf_chainXOperator (c : X.C1 → ZMod 2) :
    X.xChainOf (X.chainXOperator c) = c := by
  funext e
  simp only [xChainOf, chainXOperator_operators_edgeEquiv]
  obtain h | h := zmod2_eq_zero_or_eq_one (c e) <;> simp [h]

/-- The Z-support chain of `chainZOperator c` is `c`. -/
lemma zChainOf_chainZOperator (c : X.C1 → ZMod 2) :
    X.zChainOf (X.chainZOperator c) = c := by
  funext e
  simp only [zChainOf, chainZOperator_operators_edgeEquiv]
  obtain h | h := zmod2_eq_zero_or_eq_one (c e) <;> simp [h]

/-- The X encoding of chains is injective. -/
lemma chainXOperator_injective : Function.Injective X.chainXOperator :=
  Function.LeftInverse.injective xChainOf_chainXOperator

/-- The Z encoding of chains is injective. -/
lemma chainZOperator_injective : Function.Injective X.chainZOperator :=
  Function.LeftInverse.injective zChainOf_chainZOperator

/-- The X-only part `chainXOperator (xChainOf g)` of `g` has `X` on the qubits
where `g` acts as `X` or `Y`, and `I` elsewhere. -/
lemma chainXOperator_xChainOf_op_at
    (g : NQubitPauliGroupElement X.numQubits) (i : Fin X.numQubits) :
    (X.chainXOperator (X.xChainOf g)).operators i =
      (if g.operators i = PauliOperator.X ∨ g.operators i = PauliOperator.Y
       then PauliOperator.X else PauliOperator.I) := by
  obtain ⟨e, rfl⟩ := X.edgeEquiv.surjective i
  rw [chainXOperator_operators_edgeEquiv, xChainOf]
  split_ifs <;> simp_all

/-- The Z-only part `chainZOperator (zChainOf g)` of `g` has `Z` on the qubits
where `g` acts as `Z` or `Y`, and `I` elsewhere. -/
lemma chainZOperator_zChainOf_op_at
    (g : NQubitPauliGroupElement X.numQubits) (i : Fin X.numQubits) :
    (X.chainZOperator (X.zChainOf g)).operators i =
      (if g.operators i = PauliOperator.Z ∨ g.operators i = PauliOperator.Y
       then PauliOperator.Z else PauliOperator.I) := by
  obtain ⟨e, rfl⟩ := X.edgeEquiv.surjective i
  rw [chainZOperator_operators_edgeEquiv, zChainOf]
  split_ifs <;> simp_all

end HomologicalCode

end Homological
end Stabilizer
end Quantum
