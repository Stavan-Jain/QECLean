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

end Lattice
end Stabilizer
end Quantum
