# Obstacle diary — Approach B

## 2026-05-22: Tillich-Zémor reduces to constituent classical distances, which are themselves nontrivial to compute

**Obstacle**: Statement 12 of Lin-Pryadko gives
`d(LP[a, b]) ≥ ⌈min(d_A^⊥, d_B^⊥) / c⌉`, reducing the BB-code distance
problem to computing minimum distances of two classical F_2-linear
codes over `F_2[G]`.  These codes are sub-spaces of F_2^72 with
dimension estimated at ~12 each — small enough for explicit computation,
but minimum-weight problem for general linear codes is NP-hard.

**Attempted resolutions**:
1. Direct enumeration via `native_decide` over the kernel as a subspace
   of F_2^72: requires a Lean-level free-module decomposition of
   ker(L(a)), which is significant infrastructure.
2. Hand-construction of a low-weight element of ker(L(a)) to UPPER
   BOUND d_A^⊥: feasible for some structured codewords (e.g., products
   `f · a^{(k-1)}` where a^k = 0), but requires careful nilpotency
   analysis.
3. External SageMath / Python computation to find the minimum-weight
   element, with the result pasted as a hypothesis into Lean.  Treats
   the computation as a "trusted external oracle" — informally
   acceptable for a moonshot but degrades the formal verification
   claim.

**Status**: deferred to dimension analysis below.

## 2026-05-22: The "c" denominator (=8) crushes the Tillich-Zémor bound on the Gross polynomials

**Obstacle**: Even in the *optimistic* scenario where both classical
distances `d_A^⊥`, `d_B^⊥` are large, the Statement 12 bound is divided
by `c = |G_a ∩ G_b| = 8`.  To reach `d ≥ 12`, we'd need
`min(d_A^⊥, d_B^⊥) ≥ 96`.  Classical group-algebra codes of length 72
with distance ≥ 96 don't exist (Singleton: d ≤ n - k + 1).  The
classical code `ker(L(a))` has dimension k ≈ 12, so by Singleton
`d_A^⊥ ≤ 72 - 12 + 1 = 61`, which gives at most `⌈61/8⌉ = 8` even in
the absolute best case.

**Status**: this caps the Tillich-Zémor bound at `d ≥ 8` for the
Gross code, **regardless of any computation**.  More realistically,
`d_A^⊥` is in the range `[4, 20]`, giving the Statement 12 bound
`d ≥ 1`–`d ≥ 3`.  **Fundamental obstacle to the tight goal
`d ≥ 12`**: Tillich-Zémor's denominator-by-c structure is the wrong
shape for this code.

## 2026-05-22: Statement 5 (d ≥ d_S = d(A, B^T)) sidesteps the c denominator but introduces a different unknown

**Obstacle**: Statement 5 gives `d ≥ d_S` where `d_S` is the distance
of the block-erasure subsystem code `CSS(A, B^T)`, a `[[72, 6, d_S]]`
quantum code.  No divisor by `c`; the bound is cleaner.  But `d_S`
is itself the minimum distance of a **quantum** code on 72 qubits, k = 6
— computing it requires a CSS-distance argument on the auxiliary code,
which is the same hard problem one block-size down.

**Status**: Statement 5 changes one hard problem (n=144, k=12) for
another (n=72, k=6).  The auxiliary problem MIGHT be more tractable
(smaller exponent), but the literature doesn't give a closed-form
`d_S` for this polynomial pair either.  Tractable only with a SAT/MIP
solver — pushing us back to "trusted external oracle" territory.

## 2026-05-22: Lin-Pryadko's bounds are explicitly known-loose for IBM-engineered codes

**Obstacle**: Per the paper's Section V.A (Numerical Results),
constructed 2BGA codes show empirical distances `d = g + f n^{1/2}`
with `f ≈ 1.6`–`1.8`, matching the **lower bound from Statement 12** to
within a constant factor.  But the IBM Gross code is **not** in this
random/numerical family — it was MIP-optimized to be **above** the
generic scaling.  The Statement-12 bound is calibrated to the typical
sub-family, not the engineered tail.

**Status**: this is the same observation as Approach A's "Camion is
known-loose for engineered codes".  The literature gap is real:
**no algebraic technique known produces tight distance bounds for the
Gross polynomial pair specifically**.  The Lin-Pryadko paper itself
acknowledges this in Section IV.F (last paragraph) by appealing to
numerical sequence patterns.

## 2026-05-22: Lean formalization cost vs. payoff for the partial bound

**Obstacle**: To produce a Lean theorem of the form
`grossHomologicalCode.distance ≥ d_0` for any specific `d_0`, the
necessary infrastructure (defining `L(a)` as a matrix, the kernel as
a subspace, the classical distance, then proving Statement 12) is
heavy — estimated ~700 LoC:
- Matrix representation of `L(a)`: ~50 LoC
- Kernel as F_2-linear subspace: ~30 LoC (mathlib's `LinearMap.ker`
  works)
- Classical distance of a kernel code: ~80 LoC (minimum weight
  definition, well-defined for non-trivial kernel)
- Tillich-Zémor reduction (Statement 12 proof): ~400 LoC of the
  syndrome decoding argument
- BB code → 2BGA code instantiation bridge: ~100 LoC
- Concrete plug-in of d_0 ∈ {1, 2, 3} numerical value: ~40 LoC

For the LIKELY OUTCOME `d_0 ≤ 3`, this is a lot of Lean for a very
weak bound.

**Status**: makes the cost/benefit clearly negative for the tight
goal.  For the *parametric* theorem (any abelian 2BGA code, any
polynomial pair), the cost might be justified — but that's a
multi-session project, beyond the per-approach budget.
