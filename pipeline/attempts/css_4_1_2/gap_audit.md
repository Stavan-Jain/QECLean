# Gap audit: [[4,1,2]] LNCY code

## Repo gaps (this code surfaces / requires new abstractions)

**None.** This code is the cleanest possible engineering-track CSS
formalization. It exercises the standard CSS path end-to-end:

- Z/X type predicates → already in `Framework/Core/CSS/CSSPredicates.lean`
- CSS no-`-I` shortcut → `Framework/Core/CSS/CSSNoNegI.lean`
- CSS commutation lemmas (ZType×ZType, XType×XType) →
  `Framework/Core/CSS/CSSCommutationLemmas.lean`
- Weight-1 anticomm-witness distance helper →
  `Framework/Core/CSS/CSSDistance.lean`
- `k = 1` packaging via `Subsingleton.elim` cross-commute shortcut →
  used in `Steane7.lean:510`
- `StabilizerCodeWithDistance` bundling → standard
- Distance proof via `hasCodeDistance_of` + `weight_one_anticomm_witness`
  → exactly the [[4,2,2]] pattern, with the only twist being a 2-way
  case-split on `i < 2` vs `i ≥ 2` for the Z-generator choice.

The skeleton is essentially a CSS-detection-code "second exerciser"
of the same path that `FourQubit_4_2_2.lean` walked. No new abstraction
is justified by this one code; if a third CSS detection code is added
(e.g. `iceberg / [[2m, 2m-2, 2]]` next in the queue), a small lemma
**`CSS.distance_two_of_anticomm_witness`** that bundles
`hasCodeDistance_of + weight_one_anticomm_witness + IsNontrivialLogicalOperator_iff`
into one call would deduplicate this distance-2 pattern. Not blocking
for this code.

## Mathlib gaps (lemmas not in mathlib v4.30)

**None anticipated.** Everything needed is either project-local (the
`pauli_*` tactics, `weightOneAt`, etc.) or in standard mathlib v4.30
(`Subgroup.closure`, `Finset.filter`, `decide`, `Fin.cases`,
`Subsingleton.elim`).

## Likely "BLOCKED(<reason>)" sorries

**None expected.** Stage 4 should close all 21 sorries in one or two
attempt rounds, with the only realistic source of friction being the
mechanical idioms documented in CLAUDE.md (most relevantly:
`_root_.mul_assoc` qualification when `open NQubitPauliGroupElement`
is in scope, `change` step before `rw [one_mul, mul_one]` in
`closure_induction` proofs — but those don't even arise here since the
centralizer proofs use `Subgroup.forall_comm_closure_iff` rather than
`closure_induction`).

## Potential mechanical friction points (not blockers, just heads-up)

1. **EC Zoo tableau confusion**. Stage-4 agents might be tempted to
   "verify" the stabilizer choice against the EC Zoo description, which
   quotes `(XXII, IIXX, ZZZZ)`. As documented in `informal_spec.md`
   § "Stabilizer generators" — this is the *dual* of our chosen
   `(ZZII, IIZZ, XXXX)`. The choice is dictated by the LNCY codewords
   (Eqs. 5–6) and the requirement that the chosen stabilizers
   stabilize those codewords. We have verified this in writing.

2. **`logicalZ = ZIZI` vs `IZIZ`**. Both are valid logical Z
   representatives (differ by `ZZZZ = S_Z1·S_Z2` which is in the
   stabilizer). We pick `ZIZI` for symmetry with `logicalX = XXII`
   (both have support `{0, 2}`-style: actually `logicalX` has support
   `{0, 1}` and `logicalZ` has support `{0, 2}`; the only shared
   support qubit is qubit 0, where they anticommute, hence the
   anticommute-filter `{0}`). Stage 4 should not silently switch
   choices; if the skeleton's pinned choice doesn't close T14 or T19
   cleanly, the right fix is to investigate why, not to change the
   logical operator.

3. **Filter cardinalities for cross-type commutations** (T13, T14):
   - `logicalX = XXII` vs `S_Z1 = ZZII`: anticommute filter `{0, 1}` (card 2).
   - `logicalX = XXII` vs `S_Z2 = IIZZ`: anticommute filter `{}` (card 0).
   - `logicalZ = ZIZI` vs `S_X1 = XXXX`: anticommute filter `{0, 2}` (card 2).
   - All three are even cardinality → commute. The empty-filter case
     is well-supported by `pauli_comm_componentwise` since when neither
     operator has X overlapping the other's Z, they commute
     componentwise.

4. **Distance-2 lower bound only requires w = 1**. The interval-case
   `interval_cases w` with `1 ≤ w < 2` reduces to the single case
   `w = 1`, which `no_weight_one_mem_centralizer_of_anticommute_witness`
   closes. There is no `w = 2` lower-bound case (the bound is `< d`,
   and `2 ≮ 2`). Less work than the [[5,1,3]] distance-3 case.
