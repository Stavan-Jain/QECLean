# Quantum Error Correction in Lean

[![Lean V4](https://img.shields.io/badge/Lean-V4-blueviolet)](https://lean-lang.org/)
[![Blueprint](https://img.shields.io/badge/blueprint-live-success)](https://stavan-jain.github.io/QECLean/)
[![Dashboard](https://img.shields.io/badge/pipeline%20dashboard-live-success)](https://stavan-jain.github.io/qec-lab/)
[![Research: qec-lab](https://img.shields.io/badge/research-qec--lab-informational)](https://github.com/Stavan-Jain/qec-lab)
[![Open in Codespaces](https://img.shields.io/badge/Codespaces-open-blue?logo=github)](https://codespaces.new/Stavan-Jain/QECLean)
[![License: Apache 2.0](https://img.shields.io/badge/License-Apache_2.0-blue.svg)](LICENSE)

This project formalizes the stabilizer formalism for quantum error correction in
the Lean 4 proof assistant, with the long-term goal of a broad formalization of
stabilizer codes.

Along the way, it develops definitions and lemmas for reasoning about qubits,
quantum states, and unitary operations, contributing toward a verified
foundation for quantum computing and fault tolerance in Lean.

## Overview

Modules are written in Lean 4 and rely on
[mathlib](https://github.com/leanprover-community/mathlib4) for linear algebra
and other foundations. Import everything via `QEC`.

### Features

- **Quantum computing foundations**: qubits, state vectors, norms, ket
  notation, single- and two-qubit gates (Paulis, Hadamard, phase, CNOT), tensor
  products, and the Clifford conjugation tableau.
- **Pauli groups**: single- and n-qubit Pauli groups, matrix representations,
  commutation theory (including tactics), and the `σ[XZZXI]` notation for
  literal Pauli strings.
- **Binary symplectic representation**: check matrices, the symplectic inner
  product, symplectic span, and the equivalence between independent generators
  and linearly independent check-matrix rows.
- **Stabilizer framework**: stabilizer groups, codespaces, centralizers,
  logical operators, logical gates, code distance, and CSS structure. Codes come
  in three layers: `StabilizerCode n k` (`Code[[n, k]]`, generators only),
  `StabilizerCodeWithLogicals n k` (`Code[[n, k]]ₗ`, adding a chosen logical
  basis), and `StabilizerCodeWithDistance n k d` (`Code[[n, k, d]]`, adding a
  distance proof).
- **Homological framework**: chain-complex (CSS) codes, the
  logical-operator-to-homology correspondence, and the bivariate-bicycle
  doubling layer (`Framework/Homological/BB*`): cover transfer, deck homotopy,
  deck towers, Bockstein rank, and small-cycle base floors.
- **CSS concatenation framework**: a parametric `[[n₁n₂, k₂, ≥ d₁d₂]]`
  concatenation construction (`Framework/Concatenation/`).
- **Concrete codes**: see the list below.

### Codes

Every distance `d` listed in the parameters below is proved.

| Code | Parameters | Where |
|---|---|---|
| Gross (bivariate bicycle) | `[[144, 12, 12]]` | `Codes/BivariateBicycle/Gross/` |
| Toric code, `L ≥ 2` | `[[2L², 2, L]]` | `Codes/Toric/` |
| Rotated surface code, odd `L ≥ 3` | `[[L², 1, L]]` | `Codes/RotatedSurface/` |
| Iceberg family, `m ≥ 2` | `[[2m, 2m − 2, 2]]` | `Codes/Iceberg/N.lean` |
| Five-qubit perfect code (non-CSS) | `[[5, 1, 3]]` | `Codes/Small/FiveQubit_5_1_3*.lean` |
| Steane code | `[[7, 1, 3]]` | `Codes/Small/Steane7*.lean` |
| `C_6` (Knill) | `[[6, 2, 2]]` | `Codes/Small/SixQubit_6_2_2*.lean` |
| `[[4, 2, 2]]` | `[[4, 2, 2]]` | `Codes/Small/FourQubit_4_2_2*.lean` |
| LNCY code | `[[4, 1, 2]]` | `Codes/Small/CSS_4_1_2*.lean` |
| 3-qubit repetition | `[[3, 1, 1]]` | `Codes/Repetition/Three*.lean` |
| n-qubit repetition, `n ≥ 2` | `[[n, 1, 1]]` | `Codes/Repetition/N*.lean` |
| Shor code | `[[9, 1, 3]]` | `Codes/Small/Shor9*.lean` |
| Quantum Hamming, `r ≥ 3` | `[[2^r − 1, 2^r − 1 − 2r]]` | `Codes/Small/QuantumHamming*.lean` |

Each code is packaged as a `StabilizerCode`. The proved obligations are
generator count, independence, pairwise commutation, and exclusion of `-I`.
Most codes also provide a `StabilizerCodeWithLogicals` (logical operators in the
centralizer, with the required anticommutation) and, where the distance is
proved, a `StabilizerCodeWithDistance`. In addition, for the Steane code,
transversal `H` and `S` are verified as the logical Hadamard and phase gates.

The single-instance and repetition codes (`Codes/Small/`, `Codes/Repetition/`)
share one layout: `<Code>.lean` runs from the generators to the distance proof
and `stabilizerCodeWithDistance`, and `<Code>Logicals.lean` adds the chosen
logical basis and `stabilizerCodeWithLogicals`. The distance proof does not
depend on the logical basis.

## Headline results

**The gross code.** IBM's `[[144,12,12]]` bivariate-bicycle code is a verified
`StabilizerCodeWithDistance 144 12 12`, along with its `[[72,12,6]]` base code.

```lean
grossStabilizerCodeWithDistance : StabilizerCodeWithDistance 144 12 12
```

See
[`Codes/BivariateBicycle/README.md`](QEC/Stabilizer/Codes/BivariateBicycle/README.md)
for the proof spine.

**The toric family.** For every `L ≥ 2`, the toric code defined on a `L × L` grid is a verified
`[[2L², 2, L]]` stabilizer code:

```lean
theorem toricCodeN_distance_eq_L (L : ℕ) [Fact (2 ≤ L)] :
    HasCodeDistance (toricStabilizerCode L) L

toricStabilizerCodeWithDistance L : StabilizerCodeWithDistance (2 * L * L) 2 L
```

The homological distance argument is mechanized:

- **Chain complex.** `∂₁ ∘ ∂₂ = 0` over `𝔽₂`.
- **Homology.** `dim(H₁) = 2` via rank-nullity on `∂₁` and `∂₂`.
- **Wrapping invariants.** `h(c)` and `v(c)` are well defined on cycles, vanish
  on boundaries, and give an isomorphism `H₁ ≅ 𝔽₂²`.
- **Distance lower bound.** Any nontrivial cycle has weight `≥ L`. One of `h`
  and `v` is `1`, which forces at least one edge in each of `L` disjoint slices.
- **CSS bridge.** `d = min(d_X, d_Z)`, and both equal `L` by symmetry.

**The rotated surface family.** For every odd `L ≥ 3`, the rotated surface code
is a verified `[[L², 1, L]]` code (`rotatedSurfaceCodeN_distance_eq_L`). It is
built on the same homological framework as the toric code.

## Project structure

```
QEC/
├── Foundations/        # Qubits, states, gates, tensor products, Clifford tableau
└── Stabilizer/
    ├── Foundations/    # Pauli groups + binary-symplectic algebra
    ├── Framework/      # Core (stabilizer / logical / CSS), Symplectic,
    │                   # Homological (incl. BB doubling), Concatenation
    ├── Geometry/       # Lattice-family-agnostic primitives
    └── Codes/          # BivariateBicycle, Toric, RotatedSurface, Iceberg,
                        # Repetition, Small
```

Lower layers never import higher ones:
`Foundations < {Geometry, Framework.Core} < Framework.{Symplectic, Homological} < Codes`.

The repo also contains these companion libraries, all outside the default
`lake build` target:

- **`QECLight`**: the library without the bivariate-bicycle family, for
  memory-constrained environments. [`Playground.lean`](Playground.lean) imports
  it.

- **`QECWidgets`**: ProofWidgets-based infoview widgets (`#pauli_strip`,
  `#toric_chain`, `#check_matrix`, and the `pauli_strip?` suggestion tactic).
  See [`QECWidgets/README.md`](QECWidgets/README.md).

The research program behind the library lives in the sibling repo
[qec-lab](https://github.com/Stavan-Jain/qec-lab). It holds the bivariate-bicycle
distance lab, the catalog-driven formalization pipeline, and the narrative
write-ups.

## Axiom policy

Everything on `main` is sorry-free and depends on exactly
mathlib's three standard axioms: `propext`, `Classical.choice`, and
`Quot.sound`. There is no `native_decide` and there are no custom `axiom`s;
finite checks go through the kernel (`decide`, `decide +kernel`, or explicit
certificates). CI enforces this over every declaration under `QEC/` with
[`scripts/AxiomCheck.lean`](scripts/AxiomCheck.lean). You can check any result
yourself with `#print axioms Your.Theorem`.

## Getting started

### Try it without installing

Open the repo in
[GitHub Codespaces](https://codespaces.new/Stavan-Jain/QECLean). The container
installs the toolchain, fetches mathlib's cache, builds `QECLight`, and opens on
[`Playground.lean`](Playground.lean). See [`deploy/README.md`](deploy/README.md)
for this setup and for self-hosting a lean4web instance.

### Prerequisites

- [Lean 4](https://lean-lang.org/) (this repo uses
  `leanprover/lean4:v4.30.0-rc2`; see `lean-toolchain`)
- [Lake](https://github.com/leanprover/lake), which ships with Lean, and
  mathlib, which Lake pulls in automatically

### Building

```bash
git clone https://github.com/Stavan-Jain/QECLean
cd QECLean
lake exe cache get   # prebuilt mathlib
lake build
```

A full build includes the gross code's kernel-checked leaves, which peak at
several GB of memory each. On a <=16 GB machine, limit parallelism (for example
`LEAN_NUM_THREADS=3 lake build`), or build `QECLight` instead.

The companion targets and checks that CI runs are:

```bash
lake build QECLight && lake build QECBlueprint && lake build QECWidgets
lake env lean Playground.lean
lake env lean scripts/AxiomCheck.lean   # axiom policy, needs a completed build
```

### Working with the code

- Open files in your Lean 4 editor (VS Code with the Lean extension, or Emacs
  with lean4-mode).
- Start with [`Playground.lean`](Playground.lean), or with
  [`QEC/Stabilizer/Codes/_TEMPLATE.lean`](QEC/Stabilizer/Codes/_TEMPLATE.lean),
  the canonical structure for a new code (including the code-file /
  logicals-file split).
- Use `#check` and `#print axioms` to explore definitions and results.

#### Claude Code users (optional)

This repo ships a project-scoped MCP configuration in `.mcp.json` that wires
up the [lean-lsp MCP server](https://github.com/oOo0oOo/lean-lsp-mcp), giving
[Claude Code](https://claude.com/claude-code) agents in-editor access to live
proof states, mathlib search (LeanSearch, Loogle, Lean Hammer), and Lean
diagnostics. Claude Code will prompt you to approve the server on first launch.

Requirements: [`uv`](https://docs.astral.sh/uv/) on `PATH` (provides `uvx`).
[`ripgrep`](https://github.com/BurntSushi/ripgrep) is recommended for the
local-search tool. See [`CLAUDE.md`](CLAUDE.md) for the agent-side workflow.

## Contributing

Contributions are welcome! If you add new modules or definitions, please:

1. **Import new modules in their umbrella file** (for example
   `QEC/Stabilizer/Codes/Small.lean`). Run `bash scripts/check-umbrellas.sh` to
   catch orphaned modules.
2. **Keep the axiom policy.** Don't use `native_decide`, `sorry`, or custom
   `axiom`s on `main`. If you need an unproven input, make it a named hypothesis
   on the theorem.
3. **Follow Lean's [style guide](https://leanprover-community.github.io/style-guide.html)**
   and the conventions in [`CLAUDE.md`](CLAUDE.md), and document key
   definitions with docstrings.
4. **Run the full check list** under "Building" above, not just `lake build`.
5. **Update this README** if you add a code family or rename top-level
   modules.

## Acknowledgments

Built using [Lean 4](https://lean-lang.org/) and
[mathlib](https://github.com/leanprover-community/mathlib4).

## License

Released under the [Apache License 2.0](LICENSE).

## Maintainer

Maintained by Stavan Jain

A project from the **University of Wisconsin–Madison**.
