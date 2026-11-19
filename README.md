# QECLean: Quantum Error Correction in Lean

[![Lean V4](https://img.shields.io/badge/Lean-V4-blueviolet)](https://lean-lang.org/)
[![Open in Codespaces](https://img.shields.io/badge/Codespaces-open-blue?logo=github)](https://codespaces.new/QECLean/QECLean)
[![License: Apache 2.0](https://img.shields.io/badge/License-Apache_2.0-blue.svg)](LICENSE)
[![arXiv](https://img.shields.io/badge/arXiv-2611.21236-b31b1b.svg)](https://arxiv.org/abs/2611.21236)

QECLean is a Lean-based framework for formally specifying and verifying quantum error-correcting (QEC) codes. It consists of:

1. **Algebraic abstractions** for specifying stabilizer codes and code families, including chain complexes and check matrices.
2. **Proof techniques** and algorithmic infrastructure for establishing the $[[n, k, d]]$ parameters of codes and code families.

See our [paper](https://arxiv.org/abs/2611.21236) for technical details.

## Highlights

- **Code families**: the first mechanized distance proofs for code families, including the $[[2L^2, 2, L]]$ toric codes, rotated surface codes, and triangular color codes.
- **Gross code**: the $[[144, 12, 12]]$ gross code of [Bravyi et al.](https://doi.org/10.1038/s41586-024-07107-7)
- **$[[360, 12, 24]]$ BB code**: the first proof that this code of [Bravyi et al.](https://doi.org/10.1038/s41586-024-07107-7) has distance 24, previously known only as an upper bound.
- **Mitten code**: the $[[150, 30, 10]]$ Mitten code of [Bhardwaj et al.](https://arxiv.org/abs/2607.28795)


## Overview

Modules are written in Lean 4 and rely on
[mathlib](https://github.com/leanprover-community/mathlib4) for linear algebra
and other foundations. Import everything via `QEC`.

### Codes

Our central abstraction is the dependent type `Code[[n, k, d]]`, which is a $[[n, k, d]]$ stabilizer code together with lean proofs that it uses $n$ physical qubit to encode $k$ logical qubits with code distance $d$. We formalize the following codes as `Code[[n, k, d]]`s:

| Code | Parameters | Where |
|---|---|---|
| Bravyi360 (downstream) | `[[360, 12, 24]]` | [bb-distance-lean](https://github.com/QECLean/bb-distance-lean) |
| Toric code, `L ≥ 2` | `[[2L², 2, L]]` | `Codes/Toric/` |
| Mitten (downstream) | `[[150, 30, 10]]` | [mitten-distance-lean](https://github.com/QECLean/mitten-distance-lean) |
| Gross (downstream) | `[[144, 12, 12]]` | [bb-distance-lean](https://github.com/QECLean/bb-distance-lean) |
| Rotated surface code, odd `L ≥ 3` | `[[L², 1, L]]` | `Codes/RotatedSurface/` |
| Triangular color code, every `r` | `[[3r(r+1) + 1, 1, 2r + 1]]` | `Codes/Color/` |
| Five-qubit perfect code (non-CSS) | `[[5, 1, 3]]` | `Codes/Small/FiveQubit_5_1_3*.lean` |
| Steane code | `[[7, 1, 3]]` | `Codes/Small/Steane7*.lean` |
| Concatenated Steane code | `[[49, 1, 9]]` | `Codes/Concat/SteaneSteane.lean` |

We also formalize many more more smaller, toy codes like the $[[3, 1, 1]]$ 3-qubit repetition code.

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

### Building

```bash
git clone https://github.com/QECLean/QECLean
cd QECLean
lake exe cache get   # prebuilt mathlib
lake build
```

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

## License

Released under the [Apache License 2.0](LICENSE).

## Paper

Our preprint providing an exposition to QECLean can be found here: [Specifying and Verifying Quantum Error-Correcting Codes](https://arxiv.org/abs/2611.21236)

## Citation

If you use QECLean in your research, please cite the following paper:

```
@misc{jain2026specifyingverifyingquantum,
      title={Specifying & Verifying Quantum Error-Correcting Codes}, 
      author={Stavan Jain and Nithin Raveendran and Aws Albarghouthi},
      year={2026},
      eprint={2611.21236},
      archivePrefix={arXiv},
      primaryClass={quant-ph},
      url={https://arxiv.org/abs/2611.21236}, 
}
```

## Maintainer

Maintained by [Stavan Jain](https://stavan-jain.github.io./)

A project from the **University of Wisconsin–Madison**.
