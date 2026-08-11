# Mitten codes

Non-abelian lifted-product qLDPC codes (Bhardwaj et al., *High-rate qLDPC
processors*, arXiv:2607.28795): `LP(A, B)` with 1×2 base rows of weight-3
subsets of a non-abelian group `G` — five qubit blocks (2×2 grid + one
shared), rate 1/5, check weight 9.  The family-agnostic chain complex
(`lconv`/`rconv`, the L/R-commutation chain law, `mittenChainComplex`)
lives in `QEC/Stabilizer/Framework/Homological/LiftedProduct.lean`.

## `M150/` — the `[[150, 30, 10]]` instance (`G = C₅×S₃`)

| File | Contents | Status |
|---|---|---|
| `Data.lean` | **GENERATED — DO NOT HAND-EDIT.** GAP dictionary, Table XIII sets, pivot/decoder certificates (`pivX/pivZ`, `wX/wZ`), symplectic logical supports (`logXsup/logZsup`), witness supports. Regen: `qec-lab$ uv run python experiments/bb_lab/scripts/m150_gen_lean_data.py instance --out <this dir> --force` (falsify-first: every table numpy-validated before emission). | green |
| `Defs.lean` | `M150G`, indicator polynomials `m150A/m150B`, `m150Complex`, card/`numQubits` lemmas. | green |
| `StabilizerCode.lean` | M2 packaging → `m150StabilizerCode : StabilizerCode m150Complex.numQubits 30` (`m150_numQubits : … = 150`): sparse `d2term`/`cmTerm` bridges, `wX/wZ` decoder identities (full rank ⟹ no drop sets), closure equality, block-split `rowsLinearIndependent`, the 30 logical qubits. Transport bridge: `m150StabilizerCode_toSubgroup_eq`. | green |
| `Witness.lean` | M3 `d ≤ 10` half: `witChain` (weight-10 dual cycle) ∉ dual boundaries via the pairing chain and `not_mem_dualBoundaries_of_witness`. Headline: `m150_exists_weight10_nontrivial_dualCycle`. | green |

Distance floors (`0 < |v| ≤ 9` kernel vector ⟹ generator row, per side —
M4) and the bundled `StabilizerCodeWithDistance 150 30 10` (M5) are the
remaining stages.  Ground truth: `d_X = d_Z = 10` SAT-certified
(`qec-lab:experiments/bb_lab/certificates/mitten_150_30_10_{X,Z}.cert.json`).

Attempt state, plan, and the binding build-time budget ledger:
`qec-lab:pipeline/attempts/mitten_150_30_10/`.  Read qec-lab's `CLAUDE.md`
before pipeline-side work; per the budget rules, decidable facts stay
batched (few `native_decide` invocations over packed tables) and
enumeration lives offline in the emitter.
