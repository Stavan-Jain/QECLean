# Informal spec: [[6,2,2]] C_6 code

## Summary

The Knill C_6 code is a six-qubit normal self-dual CSS stabilizer code
encoding **two logical qubits** with code distance 2. It detects (but
does not correct) a single arbitrary Pauli error and, in Knill's
qubit-pair grouping, detects any error acting on one of the three pairs
(allowing pair-error correction when the location is already known). The
code was introduced in E. Knill, *Quantum computing with realistically
noisy devices* (Nature 434, 39 (2005); preprint arxiv:quant-ph/0410199),
where it is used at the second and higher concatenation levels of
Knill's C_4/C_6 fault-tolerant architecture (with [[4,2,2]] at the inner
level).

This file formalizes the standard distance-2 stabilizer-detection
structure of C_6 using the EC Zoo's canonical stabilizer presentation
(Qiskit preset ID 126) and logical-operator choice (Knill 2004).

## Parameters

- Physical qubits: **n = 6**
- Logical qubits: **k = 2**
- Distance: **d = 2**
- Family: **CSS** (2 Z-type stabilizers, 2 X-type stabilizers)
- Originally introduced in: E. Knill 2004/2005
  [arxiv:quant-ph/0410199 §-, fault-tolerance application]
- EC Zoo entry: `stab_6_2_2` ("[[6,2,2]] C_6 code")
- Geometric description (EC Zoo): color code on a triangular-prism ladder
  with three rungs and periodic boundary conditions; Z- and X-type
  stabilizers lie on the three square faces.

## Equivalence notes (informational; NOT formalized here)

The EC Zoo entry lists C_6 as a special case of several other codes:

1. **Ganti-Onunkwo-Young (GOY) code at r = 1**: "The Ganti-Onunkwo-Young
   code for r = 1 is the C_6 code." GOY's natural family presentation has
   2 weight-2 + 2 weight-4 generators at r = 1, which differs from the
   uniform-weight-4 Knill presentation formalized here. The codes are
   mathematically equivalent (same stabilizer subgroup / same codespace)
   under generator-set replacement. Future GOY parametric formalization
   will need a bridge lemma.

2. **`[[k+4, k, 2]]` "H code" at k = 2**: "The [[k+4,k,2]] H code for
   k = 2 is the C_6 code." Same caveat — equivalent code, different
   parametric presentation.

3. **Khesin-Lu-Shor code at r = 2, m = 2^r - 1 = 3**: equivalence detail
   per EC Zoo.

4. **`stab_4_2_2` cousin**: the [[4,2,2]] code (`FourQubit_4_2_2.lean`) is
   the inner code in Knill's C_4/C_6 concatenation; C_6 is the outer
   code. Same `(n, k, d) = (?, 2, 2)` parameters as [[4,2,2]] is to
   [[6,2,2]] — both are k = 2 CSS detection codes, structurally the
   closest existing formalization template.

We formalize **only** the Knill C_6 presentation (the EC Zoo entry's
canonical stabilizer + logicals).

## Stabilizer generators

Four independent generators (n − k = 4), in canonical Z-then-X order.
The stabilizer tableau is from EC Zoo (citing Qiskit preset ID 126):

| Name | Pauli string (qubits 0,1,2,3,4,5) | Weight | Type | Support (set) |
|------|-----------------------------------|--------|------|---------------|
| `S_Z1` | `Z Z Z Z I I` | 4 | Z-type | {0,1,2,3} |
| `S_Z2` | `Z Z I I Z Z` | 4 | Z-type | {0,1,4,5} |
| `S_X1` | `X X X X I I` | 4 | X-type | {0,1,2,3} |
| `S_X2` | `X X I I X X` | 4 | X-type | {0,1,4,5} |

(All four generators have uniform weight 4. This is the **normal
self-dual** structure: the X-side check matrix equals the Z-side check
matrix.)

**Geometric interpretation** (per EC Zoo `parents:2d_color`): Each
stabilizer corresponds to a square face of a triangular prism with three
rungs and periodic boundary conditions. Qubits {0,1} are the "top" pair,
{2,3} the "second" pair, {4,5} the "third" pair. `S_Z1`/`S_X1` cover the
first two pairs; `S_Z2`/`S_X2` cover the first and third pairs. (The
implicit third face would be the {2,3,4,5} support, which is the product
`S_Z1 · S_Z2` modulo X-side, so it is dependent — only 4 independent
generators total.)

**Pairwise overlap structure** (matters for the §4 cross-commutation
proof):

| | `S_X1` support = {0,1,2,3} | `S_X2` support = {0,1,4,5} |
|---|---|---|
| `S_Z1` support = {0,1,2,3} | overlap = {0,1,2,3}, weight 4 (even) ⇒ commute | overlap = {0,1}, weight 2 (even) ⇒ commute |
| `S_Z2` support = {0,1,4,5} | overlap = {0,1}, weight 2 (even) ⇒ commute | overlap = {0,1,4,5}, weight 4 (even) ⇒ commute |

All four ZX cross-pairs commute (even overlap counts). The two ZZ pairs
trivially commute (both Z-type). The two XX pairs trivially commute
(both X-type). So all six pairs are confirmed abelian.

## Logical operators

(Two logical qubits ⇒ two pairs `(X̄_L, Z̄_L)` and `(X̄_S, Z̄_S)`,
following Knill's L/S labelling.)

From [arxiv:quant-ph/0410199] via EC Zoo:

| Name | Pauli string | Weight | Support (set) |
|------|--------------|--------|---------------|
| `logicalX_L` (=`X_L`) | `I I X X I I` | 2 | {2,3} |
| `logicalZ_L` (=`Z_L`) | `Z I I Z Z I` | 3 | {0,3,4} |
| `logicalX_S` (=`X_S`) | `I X I X X I` | 3 | {1,3,4} |
| `logicalZ_S` (=`Z_S`) | `I I I I Z Z` | 2 | {4,5} |

**Naming convention**: we name them `logicalX_1`, `logicalZ_1`,
`logicalX_2`, `logicalZ_2` in the Lean file (matching `FourQubit_4_2_2.lean`'s
naming convention for k = 2 codes), where `_1` corresponds to Knill's
"L" pair and `_2` corresponds to his "S" pair.

**Verification of (anti)commutation with stabilizers**: every logical
must commute with every stabilizer (4 stabilizers × 4 logicals = 16
checks).

| | `S_Z1=ZZZZ II` (q 0,1,2,3) | `S_Z2=ZZ II ZZ` (q 0,1,4,5) | `S_X1=XXXX II` (q 0,1,2,3) | `S_X2=XX II XX` (q 0,1,4,5) |
|---|---|---|---|---|
| `X_L=IIXXII` (q 2,3) | overlap {2,3}: 2 (even) ✓ | overlap {}: 0 ✓ | both X ✓ | both X ✓ |
| `Z_L=ZIIZZI` (q 0,3,4) | both Z ✓ | both Z ✓ | overlap {0,3}: 2 (even) ✓ | overlap {0,4}: 2 (even) ✓ |
| `X_S=IXIXXI` (q 1,3,4) | overlap {1,3}: 2 (even) ✓ | overlap {1,4}: 2 (even) ✓ | both X ✓ | both X ✓ |
| `Z_S=IIIIZZ` (q 4,5) | both Z ✓ | both Z ✓ | overlap {}: 0 ✓ | overlap {4,5}: 2 (even) ✓ |

All 16 stabilizer-vs-logical checks commute. ✓

**Verification of pairwise logical (anti)commutation**: 6 checks (4 logicals choose 2).

| Pair | Overlap | Anti-count | Result |
|------|---------|------------|--------|
| `X_L` vs `Z_L` | {3} | 1 (odd) | **anticommute** ✓ |
| `X_S` vs `Z_S` | {4} | 1 (odd) | **anticommute** ✓ |
| `X_L` vs `Z_S` | {} | 0 (even) | commute ✓ |
| `X_S` vs `Z_L` | {3,4} | 2 (even) | commute ✓ |
| `X_L` vs `X_S` | — | — (both X-type) | commute ✓ |
| `Z_L` vs `Z_S` | — | — (both Z-type) | commute ✓ |

All pairwise checks correct. ✓

**Verification of nontriviality** (each logical is not in the
stabilizer subgroup):

- The X-side stabilizer subgroup is `⟨S_X1, S_X2⟩ = {I, S_X1, S_X2,
  S_X1·S_X2}`. The four possible X-type elements have supports {} (I),
  {0,1,2,3} (S_X1), {0,1,4,5} (S_X2), {2,3,4,5} (S_X1·S_X2 = II XX XX).
  None of these equal `X_L = IIXXII` (support {2,3}) or `X_S = IXIXXI`
  (support {1,3,4}, with mixed weight-3 — clearly not a product of two
  weight-4 X-stabs). ✓

- The Z-side analog: `Z_L = ZIIZZI` (support {0,3,4}, weight 3) and
  `Z_S = IIIIZZ` (support {4,5}, weight 2) — neither equals any element
  of `⟨S_Z1, S_Z2⟩` = {I, ZZZZ II, ZZ II ZZ, II ZZ ZZ}. ✓

## Codespace

The codespace is `2^k = 4`-dimensional. The stabilizer projector is
```
P_C = (1/16)(I + S_Z1)(I + S_Z2)(I + S_X1)(I + S_X2)
```
which projects onto this 4-d subspace. We do not formalize `P_C`
explicitly in this skeleton — it follows from the abstract `Codespace`
framework once the `StabilizerGroup 6` is in hand.

## Theorems to formalize

The skeleton mirrors `FourQubit_4_2_2.lean` (the structurally closest
existing CSS k = 2 detection code) and `CSS_4_1_2.lean` (for the
multi-Z-stabilizer cross-commutation and weight-1 anti-witness patterns).

The numbered theorems below are the `TODO(stab_6_2_2-T<n>)` markers in
the Lean skeleton.

### T1: each Z-generator is Z-type (operators in `{I, Z}`)
**Statement.** `∀ g ∈ ZGenerators, IsZTypeElement g`.
Reference: standard CSS predicate from
`Framework/Core/CSS/CSSPredicates.lean`. Two generators (`S_Z1`, `S_Z2`)
to check.

### T2: each X-generator is X-type (operators in `{I, X}`)
**Statement.** `∀ g ∈ XGenerators, IsXTypeElement g`.
Two generators (`S_X1`, `S_X2`).

### T3: `S_Z1 * S_X1 = S_X1 * S_Z1` (`ZZZZ II` and `XXXX II` commute)
**Statement.** `S_Z1 * S_X1 = S_X1 * S_Z1`.
**Justification.** Anticommute at all four overlap qubits {0,1,2,3};
count 4 (even) ⇒ commute. Standard CSS argument.

### T4: `S_Z1 * S_X2 = S_X2 * S_Z1` (`ZZZZ II` and `XX II XX` commute)
**Statement.** `S_Z1 * S_X2 = S_X2 * S_Z1`.
**Justification.** Anticommute at qubits {0,1}; count 2 (even) ⇒ commute.

### T5: `S_Z2 * S_X1 = S_X1 * S_Z2` (`ZZ II ZZ` and `XXXX II` commute)
**Statement.** `S_Z2 * S_X1 = S_X1 * S_Z2`.
**Justification.** Anticommute at qubits {0,1}; count 2 (even) ⇒ commute.

### T6: `S_Z2 * S_X2 = S_X2 * S_Z2` (`ZZ II ZZ` and `XX II XX` commute)
**Statement.** `S_Z2 * S_X2 = S_X2 * S_Z2`.
**Justification.** Anticommute at qubits {0,1,4,5}; count 4 (even) ⇒ commute.

### T7: `ZGenerators_commute_XGenerators`
**Statement.** `∀ z ∈ ZGenerators, ∀ x ∈ XGenerators, z * x = x * z`.
Combines T3–T6 by `rcases`.

### T8: all-pair generator commutation
**Statement.** `∀ g h ∈ generators, g * h = h * g`.
Combines T1, T2, T7 via the CSS-type-commutation lemmas from
`CSSCommutationLemmas.lean`.

### T9: `negIdentity 6 ∉ subgroup`
**Statement.** `negIdentity 6 ∉ Subgroup.closure generators`.
**Justification.** One-line consequence of T1, T2, T7 via
`CSS.negIdentity_not_mem_closure_union`.

### T10: `listToSet generatorsList = generators`
**Statement.** `NQubitPauliGroupElement.listToSet [S_Z1, S_Z2, S_X1, S_X2] = generators`.
Four elements in the list, four in the set (split as 2-Z + 2-X union).

### T11: `AllPhaseZero generatorsList`
**Statement.** `NQubitPauliGroupElement.AllPhaseZero [S_Z1, S_Z2, S_X1, S_X2]`.
**Justification.** All generators are constructed with `phasePower = 0`.

### T12: rows of the symplectic check matrix are linearly independent
**Statement.** `rowsLinearIndependent [S_Z1, S_Z2, S_X1, S_X2]`.
**Justification.** Closes by `decide` on the 4-row, 12-column (over
GF(2)) check matrix.

### T13: generators independent
**Statement.** `GeneratorsIndependent 6 generatorsList`.
**Justification.** One-line consequence of T12 via
`GeneratorsIndependent_of_rowsLinearIndependent`.

### T14: `stabilizerGroup.toSubgroup = subgroup`
**Statement.** The bundled `StabilizerGroup 6` from
`mkStabilizerFromGenerators` has the expected underlying subgroup.

### T15: `Anticommute logicalX_1 logicalZ_1` (i.e. `X_L = IIXXII` vs `Z_L = ZIIZZI`)
**Statement.** `NQubitPauliGroupElement.Anticommute logicalX_1 logicalZ_1`.
**Justification.** Overlap = {3}; anticommute-count 1 (odd) ⇒ anticommute.
[Knill 2004 via EC Zoo Logical operators section.]

### T16: `Anticommute logicalX_2 logicalZ_2` (i.e. `X_S = IXIXXI` vs `Z_S = IIIIZZ`)
**Statement.** `NQubitPauliGroupElement.Anticommute logicalX_2 logicalZ_2`.
**Justification.** Overlap = {4}; anticommute-count 1 (odd) ⇒ anticommute.

### T17: `logicalX_1 * logicalX_2 = logicalX_2 * logicalX_1` (`X_L` and `X_S` commute)
**Statement.** Standard equation form.
**Justification.** Both X-type ⇒ trivially commute (componentwise X·X = X·X).

### T18: `logicalX_1 * logicalZ_2 = logicalZ_2 * logicalX_1` (`X_L` and `Z_S` commute)
**Statement.** Standard equation form.
**Justification.** Overlap = {} (X_L on {2,3}, Z_S on {4,5}); 0 anticommute (even).

### T19: `logicalX_2 * logicalZ_1 = logicalZ_1 * logicalX_2` (`X_S` and `Z_L` commute)
**Statement.** Standard equation form.
**Justification.** Overlap = {3,4} (X_S on {1,3,4}, Z_L on {0,3,4}); 2 anticommute (even).

### T20: `logicalZ_1 * logicalZ_2 = logicalZ_2 * logicalZ_1` (`Z_L` and `Z_S` commute)
**Statement.** Standard equation form.
**Justification.** Both Z-type ⇒ trivially commute.

### T21: `logicalX_1` commutes with each generator
Four per-generator lemmas:
- vs `S_Z1=ZZZZ II`: overlap {2,3}; count 2 (even) ✓
- vs `S_Z2=ZZ II ZZ`: overlap {}; count 0 ✓
- vs `S_X1=XXXX II`: both X-type ✓
- vs `S_X2=XX II XX`: both X-type ✓

### T22: `logicalX_2` commutes with each generator
Four per-generator lemmas:
- vs `S_Z1=ZZZZ II`: overlap {1,3}; count 2 (even) ✓
- vs `S_Z2=ZZ II ZZ`: overlap {1,4}; count 2 (even) ✓
- vs `S_X1`, `S_X2`: both X-type ✓

### T23: `logicalZ_1` commutes with each generator
Four per-generator lemmas:
- vs `S_Z1`, `S_Z2`: both Z-type ✓
- vs `S_X1=XXXX II`: overlap {0,3}; count 2 (even) ✓
- vs `S_X2=XX II XX`: overlap {0,4}; count 2 (even) ✓

### T24: `logicalZ_2` commutes with each generator
Four per-generator lemmas:
- vs `S_Z1`, `S_Z2`: both Z-type ✓
- vs `S_X1=XXXX II`: overlap {}; count 0 ✓
- vs `S_X2=XX II XX`: overlap {4,5}; count 2 (even) ✓

### T25: `logicalX_1 ∈ centralizer stabilizerGroup`
Builds on T21 via standard `Subgroup.forall_comm_closure_iff` pattern.

### T26: `logicalX_2 ∈ centralizer stabilizerGroup`
Builds on T22.

### T27: `logicalZ_1 ∈ centralizer stabilizerGroup`
Builds on T23.

### T28: `logicalZ_2 ∈ centralizer stabilizerGroup`
Builds on T24.

### T29: `StabilizerCode 6 2` packaging
**Statement.** Construct `stabilizerCode : StabilizerCode 6 2` with the
fields populated from T8, T10, T11, T13, T15, T16, T25–T28. The
`logical_commute_cross` field requires `fin_cases ℓ <;> fin_cases ℓ'` (4
cases) and consumes T17–T20 to fill the off-diagonal commutation
quadruple.

### T30: `stabilizerCode.toStabilizerGroup.toSubgroup = closure generators`
**Statement.** Bridge between the `StabilizerCode`-derived subgroup and
the `closure generators` form. Needed for the distance proof.

### T31: weight-1 anticommute witness
**Statement.** `∀ i : Fin 6, ∀ P ≠ I, ∃ g ∈ generators, Anticommute (weightOneAt i P) g`.

**Strategy.** Dispatch on `P` (X, Y, Z) and (for X, Y) on which Z-stab
covers qubit `i`. Support structure (key for the dichotomy):
- Qubits {0,1}: BOTH `S_Z1` and `S_Z2` cover (overlap). EITHER stab works for `P ∈ {X,Y}`.
- Qubits {2,3}: ONLY `S_Z1` covers. Use `S_Z1` for `P ∈ {X,Y}`.
- Qubits {4,5}: ONLY `S_Z2` covers. Use `S_Z2` for `P ∈ {X,Y}`.

For `P = Z`, the dual support structure on the X-stabs is identical
(same partition), so we can use either `S_X1` (covers {0,1,2,3}) or
`S_X2` (covers {0,1,4,5}):
- Qubits {0,1}: BOTH work; pick `S_X1`.
- Qubits {2,3}: ONLY `S_X1` works.
- Qubits {4,5}: ONLY `S_X2` works.

The cleanest dispatch is therefore a **three-way partition** of qubits
{0,1} / {2,3} / {4,5} for both P = X/Y and P = Z. Conceptually similar
to `CSS_4_1_2.lean`'s `hi_dichotomy : (i ∈ {0,1}) ∨ (i ∈ {2,3})` but with
three branches instead of two. See gap_audit.md for further
discussion.

### T32: `HasCodeDistance stabilizerCode 2`
**Statement.** Uses `hasCodeDistance_two_of_anticommute_witness`
(PR #34, `Framework/Core/CSS/CSSDistance.lean`) with witness function
T31 and an explicit weight-2 nontrivial logical (`logicalX_1 = IIXXII`,
weight 2; or `logicalZ_2 = IIIIZZ`, weight 2).

### T33: `StabilizerCodeWithDistance 6 2 2` packaging
One-line bundle of T29 + T32.

## Edge cases / convention notes

1. **Qubit indexing is 0-based** throughout, matching the rest of the repo.
   EC Zoo's tableau text uses qubit-leftmost convention (qubit 0 on the
   left), as do we.

2. **Logical pair labelling.** Knill labels the two logical pairs "L"
   and "S" (presumably "long" and "short" referring to support weight).
   We index them as `_1` (= Knill's "L", `(X_L, Z_L)` = (IIXXII, ZIIZZI))
   and `_2` (= Knill's "S", `(X_S, Z_S)` = (IXIXXI, IIIIZZ)). This
   matches the indexing convention of `FourQubit_4_2_2.lean`.

3. **Phase conventions.** All four stabilizers and all four logicals
   have `phasePower = 0` (no `i` or `−1` factor). This matches Knill
   2004's convention; the EC Zoo tableau implicitly assumes this.

4. **Generator weight is uniform = 4.** Unlike GOY (parametric family,
   2 weight-2 + 2 weight-4 at r = 1), Knill's C_6 presentation uses
   all-weight-4 generators. This makes the CSS structure especially
   clean for formalization.

5. **Distance is exactly 2** (not greater). The witness for `d ≤ 2` is
   either `logicalX_1 = IIXXII` (weight 2) or `logicalZ_2 = IIIIZZ`
   (weight 2). The lower bound `d ≥ 2` reduces to "no weight-1 logical",
   which is the T31 witness function.

6. **Non-overlap subtlety for weight-1 witness (T31).** Both Z-stabs
   together cover all qubits, BUT each individual Z-stab covers only 4
   of 6 qubits. So the witness function needs a per-qubit dispatch
   ("which Z-stab covers qubit i?"). Crucially, `S_Z1` and `S_Z2`
   **overlap** at qubits {0,1} (both contain Z there). The qubits where
   they disagree are {2,3} (only `S_Z1`) and {4,5} (only `S_Z2`). See
   gap_audit.md for the dichotomy structure.

## Citations

- **Primary**: E. Knill, *Quantum computing with realistically noisy
  devices*, Nature 434, 39 (2005); arxiv:quant-ph/0410199.
- **Stabilizer tableau source**: EC Zoo `stab_6_2_2` entry citing
  Qiskit preset ID 126.
- **Logical operator source**: EC Zoo `stab_6_2_2` entry citing
  Knill 2004 (arxiv:quant-ph/0410199).
- **Related codes** (for equivalence notes, not formalized here):
  GOY (`goy`), [[k+4,k,2]] H code (`quantum_h`), KLS (`kls`), [[4,2,2]]
  (`stab_4_2_2`).
