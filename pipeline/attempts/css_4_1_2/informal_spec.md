# Informal spec: [[4,1,2]] LNCY code

## Summary

The Leung-Nielsen-Chuang-Yamamoto (LNCY) [[4,1,2]] code is a four-qubit
CSS stabilizer code encoding one logical qubit with code distance 2. It
detects (but does not correct) a single arbitrary Pauli error and is the
**unique** four-qubit qubit-CSS code with these parameters. The code was
introduced in Leung, Nielsen, Chuang, Yamamoto, *Approximate quantum
error correction can lead to better codes* [arxiv:quant-ph/9704002], where
it is also shown to approximately correct a single amplitude-damping
error with recovery fidelity `1 − 5γ² + O(γ³)`. We formalize the standard
distance-2 stabilizer-detection structure here; the AD-recovery result is
out of scope for this skeleton.

## Parameters

- Physical qubits: **n = 4**
- Logical qubits: **k = 1**
- Distance: **d = 2**
- Family: **CSS** (two Z-type stabilizers, one X-type stabilizer)
- Originally introduced in: Leung-Nielsen-Chuang-Yamamoto 1997
  [arxiv:quant-ph/9704002 §II, Eqs. 5–6]
- EC Zoo entry: `css_4_1_2` ("[[4,1,2]] LNCY code")

## Codeword basis (LNCY convention)

From [arxiv:quant-ph/9704002 §II, Eqs. 5–6]:

```
|0_L⟩ = (|0000⟩ + |1111⟩)/√2
|1_L⟩ = (|0011⟩ + |1100⟩)/√2
```

Qubit indexing in this skeleton is 0-based (so the four qubits are
indexed 0, 1, 2, 3). The kets above are written in qubit-0-leftmost
convention.

## Stabilizer generators

Three independent generators (n − k = 3), in canonical Z-then-X order.
The paper presents the code by its codewords, not by stabilizers; we use
the standard stabilizer presentation that stabilizes the LNCY codewords:

| Name | Pauli string (qubits 0,1,2,3) | Type |
|------|-------------------------------|------|
| `S_Z1` | `Z Z I I` | Z-type |
| `S_Z2` | `I I Z Z` | Z-type |
| `S_X1` | `X X X X` | X-type |

(2 Z-type + 1 X-type, totalling `n − k = 3` independent generators.)

**Verification that these stabilize the LNCY codewords:**

- `S_Z1 = ZZII`: eigenvalue +1 on `|0000⟩` (q₀q₁=00), `|1111⟩` (q₀q₁=11),
  `|0011⟩` (q₀q₁=00), `|1100⟩` (q₀q₁=11). So +1 on `|0_L⟩` and `|1_L⟩`. ✓
- `S_Z2 = IIZZ`: same reasoning on q₂q₃. +1 on both codewords. ✓
- `S_X1 = XXXX`: maps `|0000⟩ ↔ |1111⟩` and `|0011⟩ ↔ |1100⟩`, so
  `|0_L⟩ → |0_L⟩` and `|1_L⟩ → |1_L⟩`. ✓

**Alternative tableau in EC Zoo description.** The EC Zoo entry quotes
the Qiskit preset tableau `(XXII, IIXX, ZZZZ)`. That tableau does *not*
stabilize the LNCY codewords above — instead, `XXII` and `IIXX` are
*logical X representatives* (each takes `|0_L⟩ ↦ |1_L⟩`). The two
presentations are equivalent up to a swap of the X-side and Z-side roles,
but they describe different codes-as-subspaces unless the codeword
conventions are also swapped. We use the LNCY paper's codeword
convention as the ground truth; the stabilizer triple
`(ZZII, IIZZ, XXXX)` is the canonical stabilizer for those codewords.
This is the same convention used implicitly by the parent code
`[[4,2,2]]` (`FourQubit_4_2_2.lean`), where `XXXX` and `ZZZZ` are the
stabilizers and `IIZZ`, `IZIZ` etc. become logical operators.

## Logical operators

(One logical qubit ⇒ a single `logicalX` and `logicalZ`.)

| Name | Pauli string | Weight | Role |
|------|--------------|--------|------|
| `logicalX` | `X X I I` | 2 | Maps `|0_L⟩ ↔ |1_L⟩` |
| `logicalZ` | `Z I Z I` | 2 | `+|0_L⟩`, `−|1_L⟩` |

**Verification:**

- `logicalX = XXII`: maps `|0000⟩ ↔ |1100⟩`, `|1111⟩ ↔ |0011⟩`. So
  `|0_L⟩ = (|0000⟩+|1111⟩)/√2 ↦ (|1100⟩+|0011⟩)/√2 = |1_L⟩`. ✓
- `logicalZ = ZIZI`: eigenvalues — `|0000⟩ → +`, `|1111⟩ → +1·−1 = +1` (Z·I·Z·I = +1 on bits q₀,q₂ = 0,0; +1 on q₀,q₂=1,1). Wait, recompute: ZIZI on `|q₀q₁q₂q₃⟩` gives `(-1)^(q₀+q₂)`. On `|0000⟩`: `(-1)^0 = +1`. On `|1111⟩`: `(-1)^2 = +1`. So `|0_L⟩ → +|0_L⟩` ✓. On `|0011⟩`: `(-1)^(0+1) = -1`. On `|1100⟩`: `(-1)^(1+0) = -1`. So `|1_L⟩ → -|1_L⟩` ✓.

**Commutation/anticommutation table** (✓ = commute, ✗ = anticommute):

| | `S_Z1=ZZII` | `S_Z2=IIZZ` | `S_X1=XXXX` |
|---|---|---|---|
| `logicalX = XXII` | ✓ (anti at q0,q1: 2 = even) | ✓ (no overlap) | ✓ (both X-type) |
| `logicalZ = ZIZI` | ✓ (both Z-type) | ✓ (both Z-type) | ✓ (anti at q0,q2: 2 = even) |
| `logicalX vs logicalZ` | ✗ — anti at q0 only (1 = odd) → anticommute |

## Codespace

The codespace is `2^k = 2`-dimensional, spanned by `|0_L⟩` and `|1_L⟩`
as above. The stabilizer projector is
```
P_C = (1/8)(I + S_Z1)(I + S_Z2)(I + S_X1)
```
which projects onto this 2-d subspace. We do not formalize `P_C`
explicitly in this skeleton — it follows from the abstract
`Codespace` framework once the `StabilizerGroup 4` is in hand.

## Theorems to formalize

The skeleton mirrors `Steane7.lean` adapted for `(n,k,d) = (4,1,2)` and
the 2-Z / 1-X CSS structure. With three Z×X cross-commutation pairs only
two are needed (since there is one X-generator and two Z-generators):
`S_Z1·S_X1` and `S_Z2·S_X1`.

### T1: each Z-generator is Z-type (operators in `{I, Z}`)
**Statement.** `∀ g ∈ ZGenerators, IsZTypeElement g`.
Reference: standard CSS predicate from
`Framework/Core/CSS/CSSPredicates.lean`. No paper citation; this is a
verification of the generator definitions.

### T2: the X-generator is X-type (operators in `{I, X}`)
**Statement.** `∀ g ∈ XGenerators, IsXTypeElement g`.
Reference: same as T1.

### T3: cross-commutation `S_Z1 · S_X1 = S_X1 · S_Z1`
**Statement.** `ZZII` and `XXXX` overlap (anticommute pairwise) at qubits
0 and 1, total 2 anticommuting positions (even) → operators commute.
Reference: paper's stabilizer structure (implicit in Eqs. 5–6); standard
CSS argument via `commutes_iff_even_anticommutes`.

### T4: cross-commutation `S_Z2 · S_X1 = S_X1 · S_Z2`
**Statement.** `IIZZ` and `XXXX` anticommute pairwise at qubits 2 and 3,
total 2 anticommuting positions (even) → commute. Same reference as T3.

### T5: all-pair generator commutation
**Statement.** `∀ g h ∈ generators, g * h = h * g`. Follows from T1–T4
plus the CSS shortcuts `ZType_commutes`, `XType_commutes`.
Reference: implicit in [LNCY §II] (any stabilizer code requires this).

### T6: `−I ∉ stabilizer subgroup`
**Statement.** `negIdentity 4 ∉ Subgroup.closure generators`. Standard
CSS proof via `CSS.negIdentity_not_mem_closure_union`.

### T7: generator list ↔ generator set equality
**Statement.** `listToSet generatorsList = generators` where
`generatorsList = [S_Z1, S_Z2, S_X1]`.

### T8: all generators have phase 0
**Statement.** `AllPhaseZero generatorsList`.

### T9: rows of the check matrix are linearly independent
**Statement.** `rowsLinearIndependent generatorsList`. The check matrix
has 3 rows over `GF(2)^8` and is verifiable by `decide` for n = 4.

### T10: generator independence
**Statement.** `GeneratorsIndependent 4 generatorsList`. Follows from T9.

### T11: `stabilizerGroup.toSubgroup = subgroup`
**Statement.** The bundled `StabilizerGroup 4` built from
`generatorsList` has the same underlying subgroup as
`Subgroup.closure generators`.

### T12: logical X and logical Z anticommute
**Statement.** `Anticommute logicalX logicalZ`. `XXII · ZIZI`
anticommute pairwise only at qubit 0 (X·Z, then X·I, then I·Z, then I·I);
exactly 1 anticommuting position (odd) → anticommute.

### T13: logical X commutes with each stabilizer generator
**Statement.** `XXII` commutes with each of `ZZII`, `IIZZ`, `XXXX`:
- vs `ZZII`: anticommuting at qubits 0, 1; total 2 (even) → commute.
- vs `IIZZ`: no overlap → commute.
- vs `XXXX`: both X-type → commute.

### T14: logical Z commutes with each stabilizer generator
**Statement.** `ZIZI` commutes with each of `ZZII`, `IIZZ`, `XXXX`:
- vs `ZZII`: both Z-type → commute.
- vs `IIZZ`: both Z-type → commute.
- vs `XXXX`: anticommuting at qubits 0, 2; total 2 (even) → commute.

### T15: `logicalX ∈ centralizer stabilizerGroup`
**Statement.** Follows from T13 via `Subgroup.forall_comm_closure_iff`.

### T16: `logicalZ ∈ centralizer stabilizerGroup`
**Statement.** Follows from T14 via the same idiom.

### T17: `StabilizerCode 4 1` packaging
**Statement.** The bundled `StabilizerCode 4 1` `stabilizerCode` is
constructed from `generatorsList` with `logicalOps : Fin 1 → LogicalQubitOps 4 stabilizerGroup`
built from T15, T16, T12. The `k = 1` case uses
`logical_commute_cross := fun ℓ ℓ' h => (h (Subsingleton.elim ℓ ℓ')).elim`.

### T18: `stabilizerCode.toStabilizerGroup.toSubgroup = Subgroup.closure generators`
**Statement.** Bridge between the bundled stabilizer-code view and the
raw `Subgroup.closure generators` view. Used by the distance proof.

### T19: every weight-1 single-qubit Pauli anticommutes with some generator
**Statement.** `∀ i : Fin 4, ∀ P ∈ {X, Y, Z}, ∃ g ∈ generators, Anticommute (weightOneAt i P) g`.

Proof outline (mirroring `FourQubit_4_2_2.lean`):
- `P = X`: anticommutes with one of the Z-stabilizers
  (`S_Z1` if `i ∈ {0,1}`, `S_Z2` if `i ∈ {2,3}`).
- `P = Y`: same (Y locally anticommutes with Z, like X does).
- `P = Z`: anticommutes with `S_X1 = XXXX`.

### T20: code distance = 2 (`HasCodeDistance stabilizerCode 2`)

**Statement.**
```
HasCodeDistance stabilizerCode 2
```
i.e. (i) distance ≥ 1 [`decide`], (ii) `logicalX = XXII` is a nontrivial
logical operator of weight exactly 2 [witness], and (iii) no weight-1
Pauli is a nontrivial logical operator [from T19, via
`no_weight_one_mem_centralizer_of_anticommute_witness`].

Method: finite enumeration (n = 4 is small); the helper
`hasCodeDistance_of` from `Framework/Core/Logical/CodeDistance.lean`
reduces the proof to T19 plus the witness `logicalX`.

Reference: distance-2 claim is from [LNCY §II] — "the code corrects for
a single amplitude damping error" (under the approximate-EC criterion;
the distance-2 detection property is the projective version of that).
The EC Zoo entry states: "Detects a single-qubit error or single erasure
as a distance-two code".

### T21: bundled `StabilizerCodeWithDistance 4 1 2`
**Statement.** Package T17 with T20 into the `StabilizerCodeWithDistance`
structure for downstream use.

## Edge cases / convention notes

1. **Qubit indexing is 0-based.** Throughout the skeleton, qubits are
   `Fin 4 = {0, 1, 2, 3}`. The LNCY paper writes
   `|n₁ n₂ n₃ n₄⟩` with 1-based indices; under our 0-based convention,
   `n₁ ↔ q₀`, `n₂ ↔ q₁`, `n₃ ↔ q₂`, `n₄ ↔ q₃`. The codeword
   strings (`0000`, `1111`, `0011`, `1100`) are identical under either
   indexing — only the *labels* change.

2. **Codeword convention is locked.** Stage-2 review must check the
   LNCY codewords (Eqs. 5–6) vs. the chosen stabilizer `(ZZII, IIZZ,
   XXXX)`. The chosen stabilizers stabilize *exactly* the LNCY
   codewords as derived above. If the reviewer prefers the EC Zoo
   "Qiskit ID 6" tableau `(XXII, IIXX, ZZZZ)`, then `logicalX` should
   be `ZIZI` or `ZZZZ`-type and `logicalZ` should be `XXII`-type — but
   this corresponds to a *different* 2-d subspace of the four-qubit
   Hilbert space. We use the LNCY codeword convention as the gold
   standard.

3. **No nontrivial phases on stabilizer generators.** All three
   generators have `phasePower = 0`. No `i`-factor or `−1`-factor
   appears.

4. **No logical Y in this skeleton.** For `k = 1` codes the optional
   `logicalY` can be derived as `i · X̄ · Z̄`, but the LNCY paper does
   not single out `logicalY`, and it is not required for any
   downstream theorem. We omit it; a Stage-4 follow-up could add it
   following the Steane7 pattern.

5. **`HasCodeDistance` vs. amplitude-damping recovery.** The paper's
   main result (Eq. 20, fidelity `1 − 5γ² + O(γ³)` under AD) uses
   *approximate* error correction criteria. Our `HasCodeDistance 2`
   captures only the projective distance-2 detection property — it does
   *not* claim approximate AD correction. The AD result would require
   a separate framework not currently in the repo (continuous-parameter
   noise channels, residue-norm bounds, etc.) and is explicitly
   out-of-scope for this skeleton.

6. **Uniqueness claim.** EC Zoo describes this as "the only qubit CSS
   code with such parameters". We do **not** formalize this
   uniqueness in this skeleton — it would require classifying all
   `[[4,1,2]]` CSS codes up to equivalence, which is a substantial
   separate theorem. The skeleton instantiates one such code and
   proves its distance; uniqueness is left as future work.
