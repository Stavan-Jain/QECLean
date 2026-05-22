# Partial value: gross

Even if the headline `d ≥ 12` proof doesn't land, here is what the
moonshot is expected to produce that has standalone value. These are
not consolation prizes — each is a meaningful contribution in its own
right.

## Lean / formalization artifacts

### 1. Group-algebra infrastructure (`Stabilizer/GroupAlgebra/`)
- `F_2[G]` for finite abelian `G`, with the modular (`char F | |G|`)
  case handled cleanly.
- CRT decomposition for `F_2[Z_n]` via factorization of `x^n - 1`
  over `F_2` (cyclotomic cosets in characteristic 2).
- Bivariate extension to `F_2[Z_ℓ × Z_m]`.

This is **not currently in mathlib** at this level of generality.
Polished, it could be upstreamed to mathlib as
`Mathlib.RingTheory.GroupAlgebra.Modular` or similar.

### 2. Camion apparent-distance formalization

- Definition of apparent distance for multivariate abelian codes.
- Proof that apparent distance ≤ minimum distance (the classical
  Camion theorem).
- Algorithmic hypermatrix-based computation à la
  Bernal-Bueno-Carreño-Simón 2014.

**Status of prior art**: no Lean formalization exists. The classical
theorem has been on the books since 1971 but unformalized.

### 3. Abelian-symmetric CSS framework
- `AbelianCSSCode` as a `HomologicalCode` carrying a commuting
  abelian-group action.
- Isotypic decomposition of `H_1` into character components.
- Per-character distance contributions.

Bridges the classical Camion machinery to the quantum CSS setting.

### 4. Concrete `BBCode` type
- `BBCode ℓ m` parametrized by `(A, B) ∈ F_2[Z_ℓ × Z_m]^2` satisfying
  `A * B = B * A`.
- `grossCode : BBCode 12 6` with `A = x^3 + y + y^2`, `B = y^3 + x + x^2`.
- Plumbing to `StabilizerCode` via the existing
  `Stabilizer/Homological/CSS` machinery.

This unlocks **all future BB-code formalization work** in the repo.
The BB72, BB90, BB108 codes from the eczoo cache become instantiations
of `BBCode`. This is genuine engineering value even if the distance
result is partial.

### 5. Numerical evidence about where Camion saturates

A computational report (Lean `#eval` over the apparent-distance
algorithm) on:
- `d_app` values for {BB5, BB72, BB90, BB108, gross} from the eczoo
  cache.
- Comparison to the eczoo-published distances.
- Saturation/looseness patterns: which exponent structures give tight
  Camion, which give loose?

This dataset alone is a contribution to the BB-code literature, even
if no theorem closes.

## Mathematical / research artifacts

### 6. Mapping: BB code parameters → consecutive-zero patterns

A clean explanation, written up in `result.md` and a possible
paper-draft seed, of how the polynomial pair `(A, B)` over
`F_2[Z_ℓ × Z_m]` projects to consecutive-zero / cyclotomic-coset
patterns. This is *the* algebraic geometry of BB codes that the IBM
2024 paper *uses implicitly* (their distance certification is
numerical) but never spells out.

### 7. Identification of the modular Maschke obstacle

A precise, Lean-verifiable statement of how `char F_2 = 2 | |G| = 72`
forces a non-semisimple decomposition, and the specific shape this
takes in terms of Jacobson radicals. Even as a negative-result
write-up, this is the kind of obstacle map that researchers in this
area would benefit from.

### 8. Honest negative-result write-up

If the Camion bound proves loose, the *reasons* are themselves
mathematically interesting. A clear write-up of "Camion bound on BB
gives `d ≥ K` because the consecutive-zero structure of `(A, B)` is
constrained by [specific exponent property]" tells future researchers
what *new idea* would be needed.

## Pipeline / infrastructure artifacts

### 9. Concrete BB code testbed

`grossCode`, even half-implemented, gives the repo a concrete
non-toric / non-surface code with non-trivial group-algebra structure.
This unblocks several deferred engineering-track moonshots: BB72
(deferred per `catalog/zoo.yaml`), other 2BGA constructions, related
self-dual BB codes (arXiv:2510.05211).

### 10. Patterns for `CLAUDE.md`

Any idioms discovered while working with `MonoidAlgebra` /
`AddMonoidAlgebra` over `ZMod 2`, modular characteristic, character
sums, CRT factorizations — all candidate `CLAUDE.md` entries for
future moonshot or engineering sessions.

### 11. Refactor footprint in `Stabilizer/Homological/` or `Core/`

If we add `AbelianCSS` cleanly to the existing framework — generic
over the symmetry group, generic over the chain complex — that
**refactor itself** is reusable: e.g. the toric code's translational
symmetry could also be presented this way, simplifying parts of
`Lattice/`.

## What is *not* a partial-value target

To stay honest, here's what we explicitly do *not* count as partial
value:

- A `sorry`-laden Lean file that "shows the structure of the proof"
  without compiling. Sketches in `daily_log.md` are fine; in committed
  Lean files they are not.
- A LaTeX-quality paper write-up with no Lean backing. The whole point
  of this pipeline is that Lean compilation is the verification floor.
- A *claimed* distance bound (e.g. "we believe `d ≥ 8` though we
  couldn't quite formalize it"). Either it compiles or it doesn't
  count.
- A complete formalization of *some other code's distance* discovered
  along the way. (That would be welcome work, but it's an unrelated
  engineering-track output, not partial value for gross.)
