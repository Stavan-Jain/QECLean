import QEC.Stabilizer.Codes.BivariateBicycle.Fractal.Polynomial
import QEC.Stabilizer.Codes.BivariateBicycle.Fractal.Defs
import QEC.Stabilizer.Codes.BivariateBicycle.Fractal.SeedAlgebra
import QEC.Stabilizer.Codes.BivariateBicycle.Fractal.Recurrence
import QEC.Stabilizer.Codes.BivariateBicycle.Fractal.Pascal
import QEC.Stabilizer.Codes.BivariateBicycle.Fractal.Truncation
import QEC.Stabilizer.Codes.BivariateBicycle.Fractal.Averaging
import QEC.Stabilizer.Codes.BivariateBicycle.Fractal.History
import QEC.Stabilizer.Codes.BivariateBicycle.Fractal.LowerBound
import QEC.Stabilizer.Codes.BivariateBicycle.Fractal.Circulant
import QEC.Stabilizer.Codes.BivariateBicycle.Fractal.Distance
import QEC.Stabilizer.Codes.BivariateBicycle.Fractal.Code
import QEC.Stabilizer.Codes.BivariateBicycle.Fractal.CheckWeight
import QEC.Stabilizer.Codes.BivariateBicycle.Fractal.DistanceGrowth
import QEC.Stabilizer.Codes.BivariateBicycle.Fractal.Family

/-!
# Weight-six fractal BB codes with unbounded figure of merit

At positive index `s`, let `q=2^s` and `N=q^2-1`. The checks
`A=1+x+x^q`, `B=1+y+y^q` on `ZMod N × ZMod N` define the exact code
`[[2*N^2, 2*q^2, d_s]]`, where `d_s` is the attained minimum of the concrete
cyclic recurrence space. The theorem `seedDistance_lower` proves
`3^s ≤ 2*s*d_s`; `seedDistance_le_period` gives `d_s ≤ N`.

`stabilizerCodeWithDistance` packages every positive-index code (its argument
is `s-1`). `growingCode t` packages the explicit subsequence `s=16*4^t`.
`growingEfficiency_strictMono` and `growingEfficiency_unbounded` prove growth
of its actual `k*d^2/n`, and `exists_weight_six_generating_set` certifies the
sparse natural generating set. No closed formula for `d_s` is assumed.

The proof passes through the recurrence quotient, a power-basis description,
a binary Pascal lower bound, dyadic truncation, translation averaging, and
the generic separable BB dimension and exact-distance theorems. All proofs
use only the standard Lean axioms.
-/
