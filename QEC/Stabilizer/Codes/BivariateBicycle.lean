import QEC.Stabilizer.Framework.Homological

/-!
# Bivariate bicycle codes

The bivariate bicycle code of two polynomials `A`, `B` over
`ZMod ℓ × ZMod m` is defined for all parameters at once, so the whole family
lives in the framework:

- `bbChainComplex A B` is its chain complex and `bbStabilizerCode ℓ m A B` the
  stabilizer code on `2 * (ℓ * m)` qubits, with
  `2 * dim (ker A ⊓ ker B)` logical qubits (`finrank_H1_bbChainComplex`);
- the `BB*` modules of `QEC.Stabilizer.Framework.Homological` and
  `QEC.Stabilizer.Framework.FoldDouble` relate the distance of such a code to
  that of its free double covers.

This module re-exports that development under `Codes`.
-/
