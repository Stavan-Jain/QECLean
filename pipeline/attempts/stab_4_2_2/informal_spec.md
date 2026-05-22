# Informal spec: [[4,2,2]] Four-qubit code (C₄ / "Little Shor code")

## Summary
The [[4, 2, 2]] code, also known as C₄ or the "Little Shor code," is a four-qubit
hyperbolic self-dual CSS stabilizer code that detects any single-qubit error. It
is the smallest two-logical-qubit stabilizer code with d = 2, and is unique for
its parameters (\cite[Thm. 8]{arxiv:quant-ph/9704043}). It is widely used in
hardware demonstrations (9 distinct experimental realizations as of the EC Zoo
snapshot) and is a foundational building block in Knill's C₄/C₆ fault-tolerant
architecture.

## Parameters
- Physical qubits: n = 4
- Logical qubits: k = 2
- Distance: d = 2
- Family: CSS, self-dual (`H_X = H_Z = (1,1,1,1)`)
- Originally introduced in:
  - Vaidman, Goldenberg, Wiesner, *Error prevention scheme with four particles*,
    [arxiv:quant-ph/9603031](https://arxiv.org/abs/quant-ph/9603031), 1996.
  - Grassl, Beth, Pellizzari, *Codes for the quantum erasure channel*,
    [arxiv:quant-ph/9610042](https://arxiv.org/abs/quant-ph/9610042), 1996.

## Stabilizer generators

The code has exactly n − k = 4 − 2 = 2 stabilizer generators:

| Name | Pauli string | Description |
|------|--------------|-------------|
| Z₁ (CSS Z-check) | `ZZZZ` | Z on all four qubits |
| X₁ (CSS X-check) | `XXXX` | X on all four qubits |

This is the canonical stabilizer tableau cited in the EC Zoo entry
([preset:qiskit ID 9]). Both rows of the parity-check matrix are
`(1,1,1,1)` — the [4,3,2] single-parity-check (SPC) code dual.

Qubit indexing: **0-based** (qubits 0,1,2,3), matching the repo convention
in `Steane7.lean` and `Shor9.lean`.

## Logical operators

The standard codeword basis (from EC Zoo entry):
```
|0̄0̄⟩ = (|0000⟩ + |1111⟩) / √2
|0̄1̄⟩ = (|0011⟩ + |1100⟩) / √2
|1̄0̄⟩ = (|0101⟩ + |1010⟩) / √2
|1̄1̄⟩ = (|0110⟩ + |1001⟩) / √2
```

The logical operators consistent with this basis are:

| Logical | Pauli string | Weight |
|---------|--------------|--------|
| X̄₁ | `IXIX` | 2 |
| X̄₂ | `IIXX` | 2 |
| Z̄₁ | `IIZZ` | 2 |
| Z̄₂ | `IZIZ` | 2 |

**Verification of choices** (by direct action on the codeword basis):

- `Z̄₁ = IIZZ`: eigenvalues +1, +1, −1, −1 on `(|0̄0̄⟩, |0̄1̄⟩, |1̄0̄⟩, |1̄1̄⟩)` —
  flips the **first** logical bit measurement.
- `Z̄₂ = IZIZ`: eigenvalues +1, −1, +1, −1 — flips the **second** logical bit.
- `X̄₁ = IXIX`: maps `|0̄0̄⟩ → |1̄0̄⟩`, `|0̄1̄⟩ → |1̄1̄⟩` (verify: `IXIX·|0000⟩ = |0101⟩` and
  `IXIX·|1111⟩ = |1010⟩`, so `IXIX·|0̄0̄⟩ = (|0101⟩+|1010⟩)/√2 = |1̄0̄⟩` ✓).
- `X̄₂ = IIXX`: maps `|0̄0̄⟩ → |0̄1̄⟩`, `|1̄0̄⟩ → |1̄1̄⟩` (verify: `IIXX·|0000⟩ = |0011⟩` and
  `IIXX·|1111⟩ = |1100⟩` ✓).

**Pairwise (anti)commutation check** (by parity of overlap of {X,Y} support with {Z,Y} support):

| | Z̄₁ = IIZZ | Z̄₂ = IZIZ |
|--|-----------|-----------|
| X̄₁ = IXIX | anti (1 overlap at qubit 3) | commute (2 overlaps at qubits 1,3) |
| X̄₂ = IIXX | commute (2 overlaps at qubits 2,3) | anti (1 overlap at qubit 3) |

All four logicals commute with both stabilizers `XXXX` and `ZZZZ` (overlap is 0 or 2 on every pair).

## Codespace

The codespace is the 2² = 4-dimensional subspace of (ℂ²)^⊗4 spanned by the four
basis vectors above. As a CSS code, the codespace is the +1 eigenspace of the
joint measurement of `XXXX` and `ZZZZ`.

## Theorems to formalize

### T1: ZGenerators are Z-type
`∀ g ∈ ZGenerators, IsZTypeElement g`. The single Z-generator is `ZZZZ`, which is
trivially Z-type. [Direct from definition; CSS structure.]

### T2: XGenerators are X-type
`∀ g ∈ XGenerators, IsXTypeElement g`. The single X-generator is `XXXX`, trivially
X-type.

### T3: Z-generators commute with X-generators
The unique pair `ZZZZ * XXXX = XXXX * ZZZZ` (overlap is 4, even). This is the only
cross-commutation check. [From parity of |row_Z ∩ row_X| = 4 even.]

### T4: All generators pairwise commute (abelian stabilizer)
`∀ g h ∈ generators, g * h = h * g`. Follows from T1, T2, T3 via the existing
CSS commutation lemmas `CSSCommutationLemmas.ZType_commutes`, `XType_commutes`.

### T5: −I ∉ stabilizer subgroup
`negIdentity 4 ∉ subgroup`. Uses `CSS.negIdentity_not_mem_closure_union` from
`Core/CSSNoNegI.lean`, taking the existing CSS-decomposition shortcut.

### T6: Generator list independence (symplectic check)
`rowsLinearIndependent generatorsList`. The check matrix
```
| 0 0 0 0 | 1 1 1 1 |    (Z-row)
| 1 1 1 1 | 0 0 0 0 |    (X-row)
```
has linearly independent rows over ℤ/2 — by `decide`. Cf. Steane7 line 331.

### T7: All generators have phase power 0
`AllPhaseZero generatorsList`. Trivial: both `Z1` and `X1` were defined with
phasePower = 0.

### T8: Cross-pair anticommutation of logicals
For each ℓ ∈ {0, 1}: `Anticommute (logicalX_ℓ) (logicalZ_ℓ)`. From the table
above. Same-index pairs (X̄₁, Z̄₁) and (X̄₂, Z̄₂) anticommute (single overlap each).
[Symplectic inner product is 1 mod 2.]

### T9: Cross-pair commutation of logicals (off-diagonal)
For ℓ ≠ ℓ′ in {0, 1}: `logicalX_ℓ * logicalX_ℓ′ = logicalX_ℓ′ * logicalX_ℓ`,
`logicalX_ℓ * logicalZ_ℓ′ = logicalZ_ℓ′ * logicalX_ℓ` (cross commutes), etc.
This is the `logical_commute_cross` field of `StabilizerCode`. There are
four pairwise relations: XX, XZ, ZX, ZZ. All four pairs (X̄₁-X̄₂),
(X̄₁-Z̄₂), (X̄₂-Z̄₁), (Z̄₁-Z̄₂) involve weight-2 ops with overlap 0 or 2 ⇒ commute.

### T10: Each logical X̄_ℓ commutes with both stabilizers
`logicalX_ℓ ∈ centralizer stabilizerGroup` for ℓ ∈ {0, 1}.

- X̄₁ = IXIX vs ZZZZ: overlap (qubits 1, 3 X meet qubits 1, 3 Z) ⇒ anti at qubits 1, 3 ⇒ 2 anticommuting positions ⇒ even ⇒ commute.
- X̄₁ vs XXXX: X meets X (commute) at every position ⇒ commute.
- X̄₂ = IIXX vs ZZZZ: anti at qubits 2, 3 (count = 2) ⇒ commute.
- X̄₂ vs XXXX: commute.

### T11: Each logical Z̄_ℓ commutes with both stabilizers
Analogous to T10.

- Z̄₁ = IIZZ vs XXXX: anti at qubits 2, 3 ⇒ commute.
- Z̄₂ = IZIZ vs XXXX: anti at qubits 1, 3 ⇒ commute.
- Both commute with ZZZZ (Z-Z commute everywhere).

### T12: StabilizerCode packaging
`stabilizerCode : StabilizerCode 4 2`. Bundles T4, T5, T6, T7, T8, T9, T10, T11
into the structure.

### T13: Code distance equals 2
`HasCodeDistance stabilizerCode 2`. Requires:

1. **Witness**: `weight logicalX_1 = 2`, and `logicalX_1` is a nontrivial logical
   (from `LogicalQubitOps.xOp_nontrivial`).
2. **Lower bound**: For every weight-1 Pauli `g`, `g` is **not** a nontrivial
   logical operator.

   The argument: there are 4 × 3 = 12 weight-1 single-qubit Paulis (X, Y, or Z on
   each of 4 qubits). Each anticommutes with at least one of the two stabilizers
   `XXXX`, `ZZZZ`:
   - Weight-1 X on qubit i anticommutes with `ZZZZ`.
   - Weight-1 Z on qubit i anticommutes with `XXXX`.
   - Weight-1 Y on qubit i anticommutes with both (Y = iXZ anticommutes with X
     and with Z).
   Therefore none of the 12 weight-1 Paulis lies in the centralizer ⇒ none is a
   logical ⇒ no nontrivial logical has weight 1. Together with weight 0 (which
   means operator = I, also excluded by `weight g > 0`), we get distance ≥ 2.

   Proof method: **finite enumeration** via `decide`/`native_decide` over the
   24 (= 4 × 3 × 2) weight-1 Pauli-string + phase combinations (or 12 with
   phase 0 suffices for the operator-part check). Should be trivial for the
   solver.

## Edge cases / convention notes

- **k = 2 is the first multi-logical-qubit code in the repo.** All earlier
  codes (Repetition, Steane, Shor) have k = 1. The `StabilizerCode` structure's
  `logicalOps : Fin k → LogicalQubitOps n S` and `logical_commute_cross` fields
  are forced to be exercised non-trivially here. The Steane7 file's
  `logical_commute_cross := fun ℓ ℓ' h => (h (Subsingleton.elim ℓ ℓ')).elim`
  shortcut **does not apply** — there are genuinely off-diagonal commutation
  relations to prove.
- **Qubit indexing is 0-based** throughout; matches `Steane7.lean` /
  `Shor9.lean` conventions.
- **Phase conventions**: All stabilizer generators and standard logical
  operators use `phasePower = 0`. No `i` or `−1` factors. Logical Y can be
  defined as a derived `phaseI * X̄ℓ * Z̄ℓ`, matching the `Steane7.logicalY`
  convention; this is **not required** for the distance proof and is left
  out of the skeleton's minimum.
- **Distance = 2 means "detects 1 error but corrects 0"**, since
  ⌊(d−1)/2⌋ = 0. The EC Zoo protection text emphasizes this. We are only
  formalizing the distance claim (T13); error-correction guarantees follow
  abstractly.
- **Logical-operator choice is not unique.** The choices `X̄₁ = IXIX`,
  `X̄₂ = IIXX`, `Z̄₁ = IIZZ`, `Z̄₂ = IZIZ` are determined (up to stabilizer
  multiplication) by the codeword basis quoted in the EC Zoo entry. Other
  presentations (e.g. Aaronson-Gottesman's CHP, qiskit's `[[4,2,2]]` template)
  may use the conjugate pair `X̄₁ = XXII`, `Z̄₁ = ZIZI`, etc. **Stage 3 review
  must cross-check against the original Vaidman et al. (1996) paper to
  confirm the basis labeling matches.** The Lean formalization is internally
  consistent regardless, but T9's specific commutation pattern depends on
  this choice.
- **Self-duality.** The code is self-dual (`H_X = H_Z`), so swapping X ↔ Z
  globally yields the same code up to a Hadamard transversal. This symmetry
  is **not** formalized in the Stage-2 skeleton — left as future work.
