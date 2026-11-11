# Bivariate-bicycle codes

Concrete distance formalizations are maintained in
[bb-distance-lean](https://github.com/Stavan-Jain/bb-distance-lean), which pins
QECLean to an exact commit:

| Code | Parameters | Downstream import |
|---|---|---|
| Gross | `[[144,12,12]]`, with its `[[72,12,6]]` base | `BBDistance.Gross.Distance` |
| Bravyi360 | `[[360,12,24]]` | `BBDistance.Bravyi360.Distance` |

Their proof bodies, generated certificates, generators, and concrete regression
checks live together there, in the same declaration namespaces as this
library; importing `QEC` does not import them.

## General theory in QECLean

The family is defined for all parameters at once, so it lives under
`QEC/Stabilizer/Framework/`; `Codes/BivariateBicycle.lean` re-exports it:

- `Homological/BBChainComplex`, `BBCover`, `BBDuality`: complexes, free double
  covers, chain maps, weights, and X/Z duality.
- `Homological/BBStabilizerCode` and `BBLogicalQubits`: the bivariate bicycle
  code from its data, `bbStabilizerCode ℓ m A B : StabilizerCode (2ℓm)
  (2·dim(ker A ⊓ ker B))`, and the logical-qubit count
  `dim H₁ = 2·dim(ker A ⊓ ker B)` behind it.
- `Homological/BBDoubling` and `FoldDouble/BBCover`: parametric distance
  doubling and its connection to the code-agnostic fold-and-double theorem.
- `Homological/BBSmallCycle`, `BBSeamBZ`, `BBDeficitWall`, `BZCertificate` and
  `F2Mask`: certificate soundness for small-cycle floors, seam-coset bounds,
  and binary masks.
- `Homological/BBFlatLift`: flat-lift weight reductions.
- `Homological/BBTransferH1`, `BBBocksteinRank`, `BBBocksteinTransport`,
  `BBDeckTower`, `BBEpsFree*`: transfer on homology, the Bockstein rank
  criterion, and towers of double covers.
- `Homological/Certificate/{TrimChecks,DualCover,OrbitCensus,OrbitIndexedCensus}`:
  check trimming, dual witnesses, and completeness of finite orbit censuses.

`scripts/BBDoublingCheck.lean` exercises the general distance theorems on an
independent four-qubit cover. Every theorem follows the standard three-axiom
policy.

The `Z3Z6`, `Z5Z15F2A6`, and `BaseFloors` instances use `native_decide` and are
therefore not on `main`; they are parked on the branch `claude/z3z6-parked`.
