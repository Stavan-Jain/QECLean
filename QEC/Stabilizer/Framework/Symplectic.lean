import QEC.Stabilizer.Framework.Symplectic.IndependentEquiv
import QEC.Stabilizer.Framework.Symplectic.SymplecticOrthogonal
import QEC.Stabilizer.Framework.Symplectic.SymplecticSpan
import QEC.Stabilizer.Framework.Symplectic.SymplecticImage
import QEC.Stabilizer.Framework.Symplectic.Presentation
import QEC.Stabilizer.Framework.Symplectic.WeightTwoInSpan
import QEC.Stabilizer.Framework.Symplectic.SupportLemmas
import QEC.Stabilizer.Framework.Symplectic.CentralizerStructure

/-!
# Symplectic ↔ stabilizer bridge

Lemmas connecting binary-symplectic algebra (in `Foundations.BinarySymplectic`)
to stabilizer-formalism content (in `Framework.Core`). These files all depend
transitively on stabilizer-group content, so they cannot live in `Foundations`.

- `IndependentEquiv`: `rowsLinearIndependent ↔ independentGenerators`
- `SymplecticOrthogonal`: centralizer / coset / commutation characterizations
  via symplectic orthogonality
- `SymplecticSpan`: span structure of the symplectic image of stabilizer
  generators (added in the [[5,1,3]] formalization)
- `SymplecticImage`: the symplectic image of a whole stabilizer group, on which
  the symplectic map is injective, so `Nat.card S = 2 ^ rank` — the bridge
  between `StabilizerCode`'s cardinality and check-matrix rank
- `Presentation`: `StabilizerCode.Presentation`, a generator-list presentation
  of a code, and its soundness map `toCode` into `StabilizerCode`
- `WeightTwoInSpan`: weight-two structure of the symplectic image
- `SupportLemmas`: Pauli operator support, used in CSS reasoning
- `CentralizerStructure`: inner-centralizer classification for `k = 1` codes
  (concatenation M4) — the weak operator-part dichotomy (proven) and the
  decisive commutes-both-logicals direction (the dimension-2 long pole)
-/
