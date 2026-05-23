# Informal spec: \([[5,1,3]]\) Five-qubit perfect code

## Summary

The five-qubit perfect code is the smallest quantum stabilizer code that
corrects an arbitrary single-qubit error. It encodes 1 logical qubit in
5 physical qubits with distance 3, saturates the quantum Hamming bound
(hence "perfect"), and is the canonical worked example in every QEC
textbook. Its stabilizer is **non-CSS**: the four generators each mix
`X` and `Z` factors on different qubits, so the standard CSS shortcuts
(Z/X partition, `CSS.negIdentity_not_mem_closure_union`,
`IsZTypeElement` / `IsXTypeElement`) do not apply. This is the first
non-CSS instance in the repository and exercises the general n-qubit
Pauli infrastructure.

## Parameters

- **Physical qubits**: `n = 5`
- **Logical qubits**: `k = 1`
- **Distance**: `d = 3` (corrects any single-qubit error; detects any
  two-qubit error)
- **Family**: Non-CSS stabilizer code; cyclic (single-orbit) generator
  set
- **Originally introduced in**:
  - Laflamme, Miquel, Paz, Zurek, "Perfect Quantum Error Correction
    Code", *Phys. Rev. Lett.* **77** (1996) 198, `arxiv:quant-ph/9602019`
  - Bennett, DiVincenzo, Smolin, Wootters, "Mixed-state entanglement and
    quantum error correction", *Phys. Rev. A* **54** (1996) 3824,
    `arxiv:quant-ph/9604024`

The codeword tableau used here matches the EC Zoo entry
`stab_5_1_3` (which cites Qiskit's `preset:qiskit ID 21`) and
Gottesman's thesis Table 3.4.

## Stabilizer generators

The four generators are the cyclic shifts of the pattern `XZZXI`:

| Name | Pauli string | Cyclic shift |
|------|--------------|--------------|
| g₁ | `X Z Z X I` | base       |
| g₂ | `I X Z Z X` | shift 1    |
| g₃ | `X I X Z Z` | shift 2    |
| g₄ | `Z X I X Z` | shift 3    |

Count: `n − k = 5 − 1 = 4` ✓.

Phase convention: all generators have phase `+1` (i.e. `phasePower = 0`).

**Non-CSS property**: g₁ contains both `X` and `Z` factors on different
qubits, so it satisfies neither `IsZTypeElement` (which requires every
qubit to carry `I` or `Z`) nor `IsXTypeElement`. Same for g₂..g₄.
Consequently there is no `ZGenerators`/`XGenerators` partition and the
CSS commutation / `−I ∉ closure` shortcuts must be replaced by the
general parity-of-anticommutations machinery in
`PauliGroup/Commutation.lean` and a new "phase-0 + independent ⇒ no
−I" lemma (see `gap_audit.md`).

## Logical operators

Following the standard Gottesman / EC Zoo convention:

| Operator | Pauli string | Weight |
|----------|--------------|--------|
| `X̄` (`logicalX`) | `X X X X X` (all-X) | 5 |
| `Z̄` (`logicalZ`) | `Z Z Z Z Z` (all-Z) | 5 |

These are the standard "fully-supported" logicals used by Steane and
Shor as well. Both have `phasePower = 0`.

`X̄` and `Z̄` anticommute because `n = 5` is odd:
`X̄ · Z̄ = (−1)^5 · Z̄ · X̄ = −Z̄ · X̄`. This is closed by
`NQubitPauliOperator.allX_allZ_anticommute 5 (by decide)`.

Optional `Ȳ` (Stage-4 stretch): same `Ȳ = i X̄ Z̄` convention as
Steane7 / Shor9; phase-2 all-Y. Not required by the distance proof.

## Codespace

The codespace is 2-dimensional (k = 1). Explicit codeword basis (from
Laflamme et al.):

```
|0̄⟩ = (1/4) (
       |00000⟩ + |10010⟩ + |01001⟩ + |10100⟩ + |01010⟩
     − |11011⟩ − |00110⟩ − |11000⟩ − |11101⟩ − |00011⟩
     − |11110⟩ − |01111⟩ − |10001⟩ − |01100⟩ − |10111⟩
     + |00101⟩ )
|1̄⟩ = X̄|0̄⟩
```

These are referenced for context only — the formalization works at the
stabilizer level, not the codeword level (consistent with Steane7 /
Shor9 in this repo).

## Theorems to formalize

Section numbers follow the `_TEMPLATE.lean` §1–§14 structure. **Non-CSS
divergences are flagged explicitly.**

### T1: pairwise commutation of generators (replaces §4–§5)

For each unordered pair `(gᵢ, gⱼ)` with `i < j`, `i,j ∈ {1,2,3,4}`,
prove `gᵢ * gⱼ = gⱼ * gᵢ`. There are `C(4,2) = 6` pairs:
`{(g₁,g₂), (g₁,g₃), (g₁,g₄), (g₂,g₃), (g₂,g₄), (g₃,g₄)}`.

Each is closed by `pauli_comm_even_anticommutes` + explicit
anticommute-Finset computation, mirroring the per-pair
`Zᵢ_comm_Xⱼ` lemmas in `Steane7.lean`. The
anticommute-position counts (each must be even) are:

| Pair      | Per-qubit products                       | Anticommute positions | Count |
|-----------|------------------------------------------|-----------------------|-------|
| (g₁, g₂)  | X·I, Z·X, Z·Z, X·Z, I·X                  | {1, 3}                | 2     |
| (g₁, g₃)  | X·X, Z·I, Z·X, X·Z, I·Z                  | {2, 3}                | 2     |
| (g₁, g₄)  | X·Z, Z·X, Z·I, X·X, I·Z                  | {0, 1}                | 2     |
| (g₂, g₃)  | I·X, X·I, Z·X, Z·Z, X·Z                  | {2, 4}                | 2     |
| (g₂, g₄)  | I·Z, X·X, Z·I, Z·X, X·Z                  | {3, 4}                | 2     |
| (g₃, g₄)  | X·Z, I·X, X·I, Z·X, Z·Z                  | {0, 3}                | 2     |

(X·I anticommutes only when one is X/Y/Z and other is X/Y/Z and they
differ — here counting positions where the two single-qubit Paulis
anticommute, i.e. {X,Y,Z}×{X,Y,Z} with different letters.)

All six counts equal 2 (even) ⇒ pairwise commutation holds.

**`generators_commute` (the top-level statement)** packages these via
`rcases` on the unordered pair after `simp [generators]`.

### T2: `−I ∉ stabilizer`

`StabilizerGroup.negIdentity 5 ∉ Subgroup.closure generators`.

**Non-CSS divergence**: cannot use
`CSS.negIdentity_not_mem_closure_union` (no Z/X partition).
Approach: prove via the symplectic-span argument:
1. All generators have `phasePower = 0` (AllPhaseZero).
2. The check-matrix rows of `generatorsList` are linearly independent
   over `ZMod 2` (proved by `decide` / `native_decide`).
3. If `−I ∈ closure`, the standard relation argument shows `−I = ∏ gᵢ^aᵢ`
   with `aᵢ ∈ {0,1}`; the operator-part being identity forces
   `Σ aᵢ · symplectic(gᵢ) = 0`, which by independence forces all
   `aᵢ = 0`, giving `−I = 1` — contradiction with
   `negIdentity_ne_one`.

This requires the **new repo lemma**
`negIdentity_not_mem_of_independent_phase_zero` (see `gap_audit.md`).

### T3: AllPhaseZero of generators list

`NQubitPauliGroupElement.AllPhaseZero generatorsList`. Trivial:
each generator is constructed with `phasePower = 0`. Same proof shape
as Steane7's `AllPhaseZero_generatorsList`.

### T4: Generator independence

`NQubitPauliGroupElement.rowsLinearIndependent generatorsList` by
`decide` (5-qubit, 4-generator check matrix). Then
`GeneratorsIndependent_of_rowsLinearIndependent` gives
`GeneratorsIndependent 5 generatorsList`.

### T5: Logical X / logical Z anticommute

`NQubitPauliGroupElement.Anticommute logicalX logicalZ`. One-line
proof via `NQubitPauliOperator.allX_allZ_anticommute 5 (by decide)`,
identical to Steane7 (n=5 is odd ⇒ all-X / all-Z anticommute).

### T6: Logical operators in centralizer

For each generator `gᵢ`, prove `logicalX * gᵢ = gᵢ * logicalX` and
similarly for `logicalZ`. Each is `pauli_comm_even_anticommutes` with
the explicit even-count anticommute Finset.

| Generator | `logicalX = XXXXX` anti-positions     | Even? | `logicalZ = ZZZZZ` anti-positions      | Even? |
|-----------|----------------------------------------|-------|----------------------------------------|-------|
| g₁ = XZZXI | {1, 2}                                | 2 ✓   | {0, 3}                                | 2 ✓   |
| g₂ = IXZZX | {2, 3}                                | 2 ✓   | {1, 4}                                | 2 ✓   |
| g₃ = XIXZZ | {3, 4}                                | 2 ✓   | {0, 2}                                | 2 ✓   |
| g₄ = ZXIXZ | {0, 4}                                | 2 ✓   | {1, 3}                                | 2 ✓   |

Then bundle via `Subgroup.forall_comm_closure_iff` exactly as Steane7
does.

### T7: `StabilizerGroup` packaging

`stabilizerGroup : StabilizerGroup 5` via
`mkStabilizerFromGenerators 5 generatorsList ...`. Identical
boilerplate to Steane7.

### T8: `StabilizerCode 5 1` packaging

`stabilizerCode : StabilizerCode 5 1` with the eight standard fields.
`logical_commute_cross := fun ℓ ℓ' h => (h (Subsingleton.elim ℓ ℓ')).elim`
(k = 1 vacuous).

### T9: `HasCodeDistance stabilizerCode 3`

Three sub-goals via `hasCodeDistance_of`:

1. **`d ≥ 1`**: `by decide`.

2. **Witness**: there exists a non-trivial logical of weight exactly 3.
   - `logicalX = XXXXX` has weight 5, *not* 3 — cannot be the witness
     directly.
   - **Choice**: define an auxiliary element
     `logicalX_weight3 = logicalX * g₁` (which evaluates to a phase-2
     `IYYIX` if the explicit multiplication is done in the
     `NQubitPauliGroupElement` group, where phase tracking adds 2 for
     each `X·Z = −iY` and `Z·X = iY` per-qubit product). Then
     `weight logicalX_weight3 = 3`, and it is a non-trivial logical
     since it equals `X̄ · g₁` (same coset as X̄, which is non-trivial).
   - The non-triviality is proved via
     `IsNontrivialLogicalOperator_of_mul_stab` (or by directly
     verifying the three conditions: in centralizer, not in subgroup,
     `∀ s ∈ S, s.operators ≠ g.operators`).

   **Stage-3 review point**: the witness construction needs a small
   helper "non-trivial logical times stabilizer is non-trivial logical"
   lemma. The lemma probably exists in `LogicalOperators.lean` or
   `LogicalOperatorCoset.lean`; if not, it's a one-line addition.

3. **Lower bound**: every non-trivial logical of weight `w ∈ {1, 2}`
   does not exist (i.e. is NOT a non-trivial logical, equivalently:
   every weight-1 or weight-2 Pauli is NOT in the centralizer).

   - **Weight 1**: 15 cases (5 qubits × 3 non-identity Paulis). For
     each weight-1 Pauli, exhibit a generator that anticommutes with
     it. Standard pattern: weight-1 `Xᵢ` anticommutes with any
     stabilizer that has `Z` or `Y` at qubit i, etc. Closed via
     `no_weight_one_mem_centralizer_of_anticommute_witness`.

     Concrete witness table (for each qubit `i` and each `P ∈ {X,Y,Z}`,
     pick one of g₁..g₄ that anticommutes with `Pᵢ`):

     | qubit | local X anti-witness | local Y anti-witness | local Z anti-witness |
     |-------|----------------------|----------------------|----------------------|
     |   0   | g₄ (Z at 0)          | g₁ (X at 0) or g₄    | g₁ (X at 0)          |
     |   1   | g₁ (Z at 1)          | g₂ (X at 1) or g₄    | g₂ (X at 1)          |
     |   2   | g₁ (Z at 2)          | g₃ (X at 2)          | g₃ (X at 2)          |
     |   3   | g₂ (Z at 3)          | g₁ (X at 3) or g₂    | g₁ (X at 3)          |
     |   4   | g₂ (X at 4) [Z anti] | g₃ (Z at 4) or g₄    | g₂ (X at 4)          |

     (Note: at qubit 4, g₂ has X — so X-anticommutes with local Z; we
     pick g₃ which has Z at qubit 4 for local X anti-witness. Final
     table is fine-tuned during proof writing.)

   - **Weight 2**: 90 cases (C(5,2) × 9 = 10 × 9). Each weight-2 Pauli
     also fails to be in the centralizer because it anticommutes with
     at least one generator. This requires the **new repo lemma**
     `no_weight_two_mem_centralizer_of_anticommute_witness` analogous
     to the weight-1 helper (see `gap_audit.md`).

     Alternative path: `native_decide` on the full
     `HasCodeDistance stabilizerCode 3` predicate. For `n = 5`, the
     symplectic universe is `4^5 = 1024` Pauli operators (or `4 · 4^5 =
     4096` group elements including phases). The centralizer test is
     `g * s = s * g` for each `s ∈ generators` — small enough that
     `native_decide` plausibly closes it in seconds. **Stage-4 should
     try `native_decide` first** before going to the manual
     enumeration path.

## Edge cases / convention notes

1. **Phase convention for generators**: all `phasePower = 0`, matching
   the EC Zoo and Gottesman conventions. The Bennett et al. paper uses
   the same convention but writes generators as a 4×5 table without
   explicit phase symbols (phase is implicit).

2. **Qubit indexing**: 0-based throughout. The cyclic shift is `gᵢ₊₁ =
   shift_right_1(gᵢ)`, i.e. `g₂[j] = g₁[j-1 mod 5]`. (Equivalently,
   `g₂` is `IXZZX`, which is `g₁ = XZZXI` shifted right by one with
   wraparound: I goes to position 0, X to position 1, ...)

3. **Logical Y phase**: if `logicalY` is defined (optional stretch),
   use `Ȳ = i X̄ Z̄` matching Steane7's convention.

4. **Distance witness**: the witness element of weight exactly 3 is
   `logicalX * g₁`, not `logicalX` itself. This is the **central
   Stage-3 review point**: confirm
   - `(logicalX * g₁).operators = IYYIX` (one I at position 0, two Ys
     at positions 1, 2, an I at position 3, an X at position 4 — the
     specific Y positions depend on per-qubit single-qubit product
     conventions, which Stage-4 should double-check by computing
     `(logicalX * g₁).operators` explicitly).
   - `weight (logicalX * g₁) = 3` (count of non-I qubits = 3).
   - `IsNontrivialLogicalOperator (logicalX * g₁) stabilizerGroup`
     follows from `IsNontrivialLogicalOperator logicalX stabilizerGroup`
     and a "logical times stabilizer stays logical" helper.

5. **Cyclic structure**: this code is the smallest cyclic stabilizer
   code (all four generators are in a single orbit under cyclic shift).
   The formalization does *not* exploit this — each generator is
   spelled out explicitly. A future refactor could parametrize on a
   `ZMod 5` cyclic-shift action, but that's an over-engineering hazard
   at Stage 2.

6. **Non-CSS vs CSS lemma reuse**: the repo's CSS lemmas
   (`CSSCommutationLemmas.ZType_commutes`,
   `CSS.negIdentity_not_mem_closure_union`, etc.) are not used in this
   file. Instead, every step uses the underlying
   `commutes_iff_even_anticommutes` / `pauli_comm_even_anticommutes`
   tactics. This is a healthy stress test of the general-form Pauli
   infrastructure.

7. **Centralizer membership for logicals**: same `closure_induction`
   /  `Subgroup.forall_comm_closure_iff` pattern as Steane7, but the
   case-split is on the 4-element generator set (not a Z∪X union).

## References used to derive this spec

- `catalog/zoo.yaml:6559-6607` — EC Zoo entry for `stab_5_1_3`
- `https://errorcorrectionzoo.org/c/stab_5_1_3` — stabilizer tableau
  verified verbatim
- Laflamme, Miquel, Paz, Zurek `arxiv:quant-ph/9602019` (abstract
  only — PDF not parseable through WebFetch)
- Bennett, DiVincenzo, Smolin, Wootters `arxiv:quant-ph/9604024`
  (not fetched; cross-referenced via EC Zoo)
- Gottesman thesis Table 3.4 (re-derivable convention)
- `QEC/Stabilizer/Codes/Steane7.lean` — k = 1, all-X / all-Z logicals,
  the closest structural sibling
- `QEC/Stabilizer/Codes/FourQubit_4_2_2.lean` — k = 2 reference,
  source of the `weightOneAt_anticomm_*` pattern and
  `no_weight_one_mem_centralizer_of_anticommute_witness` usage
