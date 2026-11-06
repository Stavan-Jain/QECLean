# Mitten `[[150,30,10]]`

The mitten instance uses a lifted-product chain complex over `C₅ × S₃`.
Its distance argument classifies chains of weight at most nine, joins the
resulting block triples into stabilizer rows, and supplies an explicit
nontrivial logical operator of weight ten.

## Proof structure

- `M150/Defs.lean` and `Data.lean` specify the group-algebra instance and
  certificate data. The shared `Framework/Homological/LiftedProduct.lean`
  supplies the chain-complex construction.
- `Sparse.lean` identifies the boundary maps with sparse entry formulas;
  `SparseSupport.lean` evaluates chains from their listed support.
- `StabilizerCode.lean` checks inverse-matrix certificates and uses the
  shared homological presentation to construct the canonical
  `StabilizerCode 150 30`. `Logicals.lean` and `Witness.lean` describe the
  logical operators and the weight-ten witness.
- `FloorCore.lean` proves mask enumeration and split-checker soundness.
  `FloorBridge.lean` reuses `F2Mask` to connect masks to chains.
  `FloorChecksX.lean` and `FloorChecksZ.lean` check the finite map identities
  and census-to-row correspondence after symbolic sparse reductions.
- `PackedSweep.lean`, `PackedClassification.lean`, and `SweepAdapters.lean`
  connect packed arithmetic certificates to the split checker.
  `PackedGridSweep.lean` checks rectangular batches of mask pairs through
  the shared `PackedGrid` broadcasting identities. The shared
  `PackedPopcount32` specialization counts each thirty-bit mask in its
  own thirty-two-bit lane using five pair-summing stages. Generated
  `MaskChunks`, `SweepMaps`, and classifier modules supply instance data.
  `GroupedJoin.lean` groups matching shared blocks; `JoinX.lean` and
  `JoinZ.lean` connect the resulting pairs to physical stabilizer rows.
- `FloorXSide.lean` and `FloorZSide.lean` expose the classification inputs as
  named hypotheses of `floorX_of_certificates` and
  `floorZ_of_certificates`. `Distance.lean` transfers chain floors to code
  distance and combines them with the explicit witness.

The generated classifier files must pass kernel checking before their
classification obligations are discharged. Their presence alone does not
establish the unconditional distance theorem.

## Provenance

The instance, census, and symbolic floor arguments come from
`claude/a32-lifted-product` at `2440ec8`. The parallel `[[360,12,24]]`
formalization on `codex/bravyi360-distance` supplied the packed arithmetic
approach: its reusable certificate modules were taken from `4d5ac9e`
(branch head `88ffe0a`) and placed under
`QEC/Stabilizer/Framework/Homological/Certificate/`. Mitten reuses those
modules for packed digits, popcount, equality flags, and reconstruction
instead of maintaining separate copies.

## Regeneration

Generators live in the sibling **qec-lab** repository under
`experiments/bb_lab/scripts/mitten_kernel/`. From that repository, run:

```sh
uv run --project experiments/bb_lab python \
  experiments/bb_lab/scripts/mitten_kernel/generate.py \
  --root ../QECLean --force
```

The wrapper invokes the existing `m150_gen_lean_data.py` instance and M4
exporter, then `generate_joins.py` and `generate_sweeps.py`. The M4 source
data is `experiments/bb_lab/data-a32/m4_triples.json`; the sweep generator
also reads the exported `FloorData.lean`. Generated Lean files carry a
banner naming their generator. Change the generator and regenerate those
files rather than editing the emitted declarations. Keep generator and
library changes together across the two repositories.

## Trust policy

Generators propose certificate data; Lean proves the coverage, map
identities, packed checks, and their mathematical consequences. All proof
dependencies must be among `propext`, `Classical.choice`, and `Quot.sound`,
as required by the repository's axiom policy in `CLAUDE.md`. Use
`#print axioms` on the floor and distance capstones and run
`lake env lean scripts/AxiomCheck.lean` after a completed build. Any input
that has not been proved must remain an explicit named theorem hypothesis.
