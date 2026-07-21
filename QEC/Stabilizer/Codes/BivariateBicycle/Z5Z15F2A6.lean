import QEC.Stabilizer.Codes.BivariateBicycle.Z5Z15F2A6.Defs
import QEC.Stabilizer.Codes.BivariateBicycle.Z5Z15F2A6.ClassData
import QEC.Stabilizer.Codes.BivariateBicycle.Z5Z15F2A6.CertSweep
import QEC.Stabilizer.Codes.BivariateBicycle.Z5Z15F2A6.Classification
import QEC.Stabilizer.Codes.BivariateBicycle.Z5Z15F2A6.WindowEngine
import QEC.Stabilizer.Codes.BivariateBicycle.Z5Z15F2A6.KernelCert
import QEC.Stabilizer.Codes.BivariateBicycle.Z5Z15F2A6.SweepWin
import QEC.Stabilizer.Codes.BivariateBicycle.Z5Z15F2A6.DeckHomotopy
import QEC.Stabilizer.Codes.BivariateBicycle.Z5Z15F2A6.Witness
import QEC.Stabilizer.Codes.BivariateBicycle.Z5Z15F2A6.Distance

/-!
# The [[150,8,8]] → [[300,8,16]] doubling pair over `Z₅×Z₁₅ → Z₅×Z₃₀`

The first `d ≥ 7` instance of the free-ℤ₂ doubling template — the A17
docket's tightness cell `f2a6f17e1c41ff96:y` (corpus code
`bb_neigh_z5z15_f2a6f17e`, `A = 1 + y + x`, `B = xy⁶ + xy¹⁰ + x²y¹²`),
packaged as the Paper-1 **two-tier claim**: the doubling theorem and every
per-instance finite obligation are kernel-checked; the three floor inputs
enter as named hypotheses backed by solver certificates (base distance:
CaDiCaL; Smith-coset floor: CryptoMiniSat XOR-native `UNSAT@14` + parity +
orbit transport, kissat DRAT cross-proof; dangerous floor: assumption,
A11-screened).  Contrast `Z3Z6/`, where `n = 36` made all five inputs
kernel-sweepable.

- `Defs`         — groups, polynomials, complexes, the `coverData` bundle
- `DeckHomotopy` — the homotopy (R) via the Bezout witness
                   `P⋆A + Q⋆B = 1 + y¹⁵` (25 + 3 monomials)
- `Witness`      — the weight-8 `u*` (descent of the A17 cover ladder's
                   SAT witness) and its weight-16 nontrivial lift `τ(u*)`;
                   kernel-checked halves of `d(base) ≤ 8`, `d(cover) ≤ 16`
- `Distance`     — the conditional assembly `d(cover) = 16` at the chain
                   and Pauli levels (`cover300_chain_distance_eq_16`,
                   `cover300_pauli_distance_eq_16`) through the
                   logical-floor variant of the parametric layer (the
                   strong floor is false for `d = 8` bases)
-/
