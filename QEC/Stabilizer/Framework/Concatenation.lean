import QEC.Stabilizer.Framework.Concatenation.Embedding
import QEC.Stabilizer.Framework.Concatenation.Restriction
import QEC.Stabilizer.Framework.Concatenation.Promotion
import QEC.Stabilizer.Framework.Concatenation.Constructor
import QEC.Stabilizer.Framework.Concatenation.Correspondence
import QEC.Stabilizer.Framework.Concatenation.Distance
import QEC.Stabilizer.Framework.Concatenation.Independence

/-!
# Concatenation of CSS codes

The concatenation of an inner CSS code with one logical qubit and an outer CSS
code: each qubit of the outer code is encoded into a block carrying the inner
code. The concatenated code has `n₁ * n₂` qubits and `k₂` logical qubits, and
its distance is at least the product of the two distances.

- `Embedding`: the indexing `qIdx` / `blockOf` / `posOf` of the physical qubits
  by block and position, and `embedBlock`, which places an inner operator on
  one block.
- `Restriction`: `restrictBlock`, which reads off one block of an operator;
  weight and the symplectic inner product computed block by block, and the
  resulting commutation rules for embedded elements.
- `Promotion`: the promotion `promoteE` of an outer operator (`X ↦ X̄`,
  `Z ↦ Z̄`), its adjoint `inducedOuterOp`, the input bundle `ConcatCSSData`,
  and the generator list `ConcatCSSData.concatGeneratorsList`.
- `Constructor`: the stabilizer group `concatStabGroup`, the promoted outer
  logical operators, and the codes `concatenate` and `concatenateWithLogicals`.
- `Correspondence`: the outer operator `inducedOuter D g` induced by an element
  `g`, which is a nontrivial logical operator of the outer code whenever `g`
  is one of the concatenated code (`inducedOuter_isNontrivialLogical`).
- `Distance`: the bound `weight_ge_d1_mul_d2` and the distance statement
  `concat_hasCodeDistance`.
- `Independence`: `rowsLinearIndependent_concat`, the linear independence of
  the concatenated generators from that of the inner generators with the inner
  logical operators and that of the outer generators.
-/
