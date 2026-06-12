import QEC.Stabilizer.Codes.BivariateBicycle.Defs
import QEC.Stabilizer.Codes.BivariateBicycle.CoverTransfer
import QEC.Stabilizer.Codes.BivariateBicycle.DeckHomotopy
import QEC.Stabilizer.Codes.BivariateBicycle.Witness

/-!
# Bivariate bicycle codes

Chain-level formalization of the gross `[[144, 12, 12]]` bivariate bicycle
code and its `[[72, 12, 6]]` base, related by a 2:1 covering:

- `Defs`          — groups, polynomials, chain complexes, covering data
- `CoverTransfer` — pushforward/pullback chain maps, exactness, weight identity
- `DeckHomotopy`  — the deck homotopy (R): `v + σv` bounds for every cycle `v`
- `Witness`       — the explicit weight-12 nontrivial cycle `τ(u*)`

Everything here lives at the `𝔽₂`-chain level (`HomologicalCode`); the
Pauli-group / `StabilizerCode` packaging and the conditional `d = 12`
assembly are later phases.
-/
