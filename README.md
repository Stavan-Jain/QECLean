# Quantum Error Correction in Lean

[![Lean V4](https://img.shields.io/badge/Lean-V4-blueviolet)](https://lean-lang.org/)
[![Open in Codespaces](https://img.shields.io/badge/Codespaces-open-blue?logo=github)](https://codespaces.new/QECLean/QECLean)
[![License: Apache 2.0](https://img.shields.io/badge/License-Apache_2.0-blue.svg)](LICENSE)

QECLean is a Lean-based framework for formally specifying and verifying QEC codes. It consists of 

1. Algebraic Abstractions for specifying stabilizer codes and code families
2. Proof techniques and algorithmic infrastructure to establish $[[n, k, d]]$ code parameters for codes and code families

## Overview

Modules are written in Lean 4 and rely on
[mathlib](https://github.com/leanprover-community/mathlib4) for linear algebra
and other foundations. Import everything via `QEC`.

### Codes

Our central abstraction is the type `Code[[n, k, d]]`, which is a $[[n, k, d]]$ stabilizer code together with lean proofs that it uses $n$ physical qubit to encode $k$ logical qubits with code distance $d$. We formalize the following codes as `Code[[n, k, d]]`s:

| Code | Parameters | Where |
|---|---|---|
| Bravyi360 (downstream) | `[[360, 12, 24]]` | [bb-distance-lean](https://github.com/QECLean/bb-distance-lean) |
| Toric code, `L ≥ 2` | `[[2L², 2, L]]` | `Codes/Toric/` |
| Mitten (downstream) | `[[150, 30, 10]]` | [mitten-distance-lean](https://github.com/QECLean/mitten-distance-lean) |
| Gross (downstream) | `[[144, 12, 12]]` | [bb-distance-lean](https://github.com/QECLean/bb-distance-lean) |
| Rotated surface code, odd `L ≥ 3` | `[[L², 1, L]]` | `Codes/RotatedSurface/` |
| Triangular color code, every `r` | `[[3r(r+1) + 1, 1, 2r + 1]]` | `Codes/Color/` |
| Iceberg family, `m ≥ 2` | `[[2m, 2m − 2, 2]]` | `Codes/Iceberg/N*.lean` |
| Five-qubit perfect code (non-CSS) | `[[5, 1, 3]]` | `Codes/Small/FiveQubit_5_1_3*.lean` |
| Steane code | `[[7, 1, 3]]` | `Codes/Small/Steane7*.lean` |
| Concatenated Steane code | `[[49, 1, 9]]` | `Codes/Concat/SteaneSteane.lean` |
| `C_6` (Knill) | `[[6, 2, 2]]` | `Codes/Small/SixQubit_6_2_2*.lean` |
| `[[4, 2, 2]]` | `[[4, 2, 2]]` | `Codes/Small/FourQubit_4_2_2*.lean` |
| LNCY code | `[[4, 1, 2]]` | `Codes/Small/CSS_4_1_2*.lean` |
| 3-qubit repetition | `[[3, 1, 1]]` | `Codes/Repetition/Three*.lean` |
| n-qubit repetition, `n ≥ 2` | `[[n, 1, 1]]` | `Codes/Repetition/N*.lean` |
| Shor code | `[[9, 1, 3]]` | `Codes/Small/Shor9*.lean` |
| Quantum Hamming, `r ≥ 3` | `[[2^r − 1, 2^r − 1 − 2r, 3]]` | `Codes/Small/QuantumHamming*.lean` |

## Project structure

```
QEC/
├── Foundations/        # Qubits, states, gates, tensor products, Clifford tableau
└── Stabilizer/
    ├── Foundations/    # Pauli groups + binary-symplectic algebra
    ├── Framework/      # Core (stabilizer / logical / CSS), Symplectic,
    │                   # Homological (incl. BB doubling), Concatenation,
    │                   # FoldDouble
    ├── Geometry/       # Lattice-family-agnostic primitives
    └── Codes/          # BivariateBicycle, Toric, RotatedSurface, Color,
                        # Iceberg, Repetition, Small, Concat
```

## Axiom policy

Everything on `main` is sorry-free and depends on exactly
mathlib's three standard axioms: `propext`, `Classical.choice`, and
`Quot.sound`. There is no `native_decide` and there are no custom `axiom`s.
CI enforces this with
[`scripts/AxiomCheck.lean`](scripts/AxiomCheck.lean). You can check any result
yourself with `#print axioms Your.Theorem`.

## Getting started

### Try it without installing

Open the repo in
[GitHub Codespaces](https://codespaces.new/QECLean/QECLean). The container
installs the toolchain, fetches mathlib's cache, builds `QECLight`, and opens on
[`Playground.lean`](Playground.lean). See [`deploy/README.md`](deploy/README.md)
for this setup and for self-hosting a lean4web instance.

### Prerequisites

- [Lean 4](https://lean-lang.org/) (this repo uses
  `leanprover/lean4:v4.36.0-rc2`; see `lean-toolchain`)
- [Lake](https://github.com/leanprover/lake), which ships with Lean, and
  mathlib, which Lake pulls in automatically

### Building

```bash
git clone https://github.com/QECLean/QECLean
cd QECLean
lake exe cache get   # prebuilt mathlib
lake build
```

### Working with the code

- Open files in your Lean 4 editor (VS Code with the Lean extension, or Emacs
  with lean4-mode).
- Use `#check` and `#print axioms` to explore definitions and results.

## Contributing

Contributions are welcome! If you add new modules or definitions, please:

1. **Import new modules in their umbrella file** (for example
   `QEC/Stabilizer/Codes/Small.lean`). Run `bash scripts/check-umbrellas.sh` to
   catch orphaned modules. The library uses Lean's module system: a new file
   starts with `module`, uses `public import`, and opens with
   `@[expose] public section` (see [`CLAUDE.md`](CLAUDE.md) § "Module system").
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

## Paper

Our preprint providing an exposition to QECLean can be found here: [Specifying and Verifying Quantum Error-Correcting Codes](https://arxiv.org/abs/2611.21236)

## Maintainer

Maintained by Stavan Jain

A project from the **University of Wisconsin–Madison**.
