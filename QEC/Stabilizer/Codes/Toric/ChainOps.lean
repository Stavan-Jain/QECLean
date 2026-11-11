import QEC.Stabilizer.Framework.Homological.Distance
import QEC.Stabilizer.Codes.Toric.ChainComplex

/-!
# Algebra of the toric chain operators

`toricXOperatorOfChain L` and `toricZOperatorOfChain L` are the chain operators
of `toricHomologicalCode L`, so the general facts about chain operators hold for
them:

* `toricXOperatorOfChain_operators_edgeToQubitIdx` and
  `mem_support_toricXOperatorOfChain_edgeToQubitIdx_iff`: the operator and the
  support on the qubit of an edge;
* `toricXOperatorOfChain_isXType`: the encoded operator is X-type;
* `toricXOperatorOfChain_zero`, `toricXOperatorOfChain_add`: the encoding turns
  sums of chains into products of operators;
* `toricXOperatorOfChain_xChainOf`: every X-type Pauli group element is the
  X-chain operator of its X-support chain;
* `weight_toricXOperatorOfChain`: the operator has the weight `edgeWeight c` of
  its chain, which is the `chainWeight` of `toricHomologicalCode L`
  (`toricHomologicalCode_chainWeight_eq`);

and likewise for `toricZOperatorOfChain`.
-/

namespace Quantum
namespace Stabilizer
namespace Lattice

open Homological
open NQubitPauliGroupElement (IsXTypeElement IsZTypeElement)

variable (L : ℕ) [Fact (0 < L)]

/-! ## X-chain operators -/

/-- The X-chain operator of `c` at the qubit of the edge `e`. -/
lemma toricXOperatorOfChain_operators_edgeToQubitIdx (c : C1 L) (e : EdgeIdx L) :
    (toricXOperatorOfChain L c).operators (edgeToQubitIdx L e) =
      if c e = 1 then PauliOperator.X else PauliOperator.I :=
  HomologicalCode.chainXOperator_operators_edgeEquiv (X := toricHomologicalCode L) c e

/-- The qubit of an edge `e` is in the support of `toricXOperatorOfChain L c`
iff `c e = 1`. -/
lemma mem_support_toricXOperatorOfChain_edgeToQubitIdx_iff (c : C1 L) (e : EdgeIdx L) :
    edgeToQubitIdx L e ∈ (toricXOperatorOfChain L c).operators.support ↔ c e = 1 :=
  HomologicalCode.mem_support_chainXOperator_iff (X := toricHomologicalCode L) c e

/-- The X-chain operator is X-type. -/
lemma toricXOperatorOfChain_isXType (c : C1 L) :
    IsXTypeElement (toricXOperatorOfChain L c) :=
  HomologicalCode.chainXOperator_isXType (X := toricHomologicalCode L) c

/-- `toricXOperatorOfChain` sends the zero chain to the identity. -/
lemma toricXOperatorOfChain_zero : toricXOperatorOfChain L 0 = 1 :=
  HomologicalCode.chainXOperator_zero (X := toricHomologicalCode L)

/-- `toricXOperatorOfChain` sends sums of chains to products of operators. -/
lemma toricXOperatorOfChain_add (c c' : C1 L) :
    toricXOperatorOfChain L (c + c') =
      toricXOperatorOfChain L c * toricXOperatorOfChain L c' :=
  HomologicalCode.chainXOperator_add (X := toricHomologicalCode L) c c'

/-- Every X-type Pauli group element is the X-chain operator of its X-support
chain. -/
lemma toricXOperatorOfChain_xChainOf {g : NQubitPauliGroupElement (toricNumQubits L)}
    (hg : IsXTypeElement g) :
    toricXOperatorOfChain L ((toricHomologicalCode L).xChainOf g) = g :=
  HomologicalCode.chainXOperator_xChainOf (X := toricHomologicalCode L) hg

/-- The weight `edgeWeight c` of a 1-chain is its `chainWeight` in
`toricHomologicalCode L`. -/
theorem toricHomologicalCode_chainWeight_eq (c : C1 L) :
    (toricHomologicalCode L).chainWeight c = edgeWeight c := rfl

/-- The X-chain operator of `c` has the weight of `c`. -/
lemma weight_toricXOperatorOfChain (c : C1 L) :
    NQubitPauliGroupElement.weight (toricXOperatorOfChain L c) = edgeWeight c :=
  HomologicalCode.weight_chainXOperator (X := toricHomologicalCode L) c

/-! ## Z-chain operators -/

/-- The Z-chain operator of `c` at the qubit of the edge `e`. -/
lemma toricZOperatorOfChain_operators_edgeToQubitIdx (c : C1 L) (e : EdgeIdx L) :
    (toricZOperatorOfChain L c).operators (edgeToQubitIdx L e) =
      if c e = 1 then PauliOperator.Z else PauliOperator.I :=
  HomologicalCode.chainZOperator_operators_edgeEquiv (X := toricHomologicalCode L) c e

/-- The qubit of an edge `e` is in the support of `toricZOperatorOfChain L c`
iff `c e = 1`. -/
lemma mem_support_toricZOperatorOfChain_edgeToQubitIdx_iff (c : C1 L) (e : EdgeIdx L) :
    edgeToQubitIdx L e ∈ (toricZOperatorOfChain L c).operators.support ↔ c e = 1 :=
  HomologicalCode.mem_support_chainZOperator_iff (X := toricHomologicalCode L) c e

/-- The Z-chain operator is Z-type. -/
lemma toricZOperatorOfChain_isZType (c : C1 L) :
    IsZTypeElement (toricZOperatorOfChain L c) :=
  HomologicalCode.chainZOperator_isZType (X := toricHomologicalCode L) c

/-- `toricZOperatorOfChain` sends the zero chain to the identity. -/
lemma toricZOperatorOfChain_zero : toricZOperatorOfChain L 0 = 1 :=
  HomologicalCode.chainZOperator_zero (X := toricHomologicalCode L)

/-- `toricZOperatorOfChain` sends sums of chains to products of operators. -/
lemma toricZOperatorOfChain_add (c c' : C1 L) :
    toricZOperatorOfChain L (c + c') =
      toricZOperatorOfChain L c * toricZOperatorOfChain L c' :=
  HomologicalCode.chainZOperator_add (X := toricHomologicalCode L) c c'

/-- Every Z-type Pauli group element is the Z-chain operator of its Z-support
chain. -/
lemma toricZOperatorOfChain_zChainOf {g : NQubitPauliGroupElement (toricNumQubits L)}
    (hg : IsZTypeElement g) :
    toricZOperatorOfChain L ((toricHomologicalCode L).zChainOf g) = g :=
  HomologicalCode.chainZOperator_zChainOf (X := toricHomologicalCode L) hg

/-- The Z-chain operator of `c` has the weight of `c`. -/
lemma weight_toricZOperatorOfChain (c : C1 L) :
    NQubitPauliGroupElement.weight (toricZOperatorOfChain L c) = edgeWeight c :=
  HomologicalCode.weight_chainZOperator (X := toricHomologicalCode L) c

end Lattice
end Stabilizer
end Quantum
