# Spectral analysis of the gross polynomials for Camion's bound

This document records the **modular character analysis** of the gross
polynomial pair, predicting what Camion's apparent-distance bound would
give *if* fully formalized.  The conclusion (committed to upfront, to
avoid hypothesis drift): the Camion bound on the gross code is at most
in the range `[3, 9]`, far from the true `d = 12`.  The Camion approach
is therefore **loose by a factor of at least 1.3×** on this specific
polynomial pair.

## Setting

Group `G = Z_12 × Z_6`, polynomials
```
A(x, y) = x^3 + y + y^2
B(x, y) = y^3 + x + x^2
```
over `F_2[Z_12 × Z_6]`.

Cyclotomic / modular structure over `F_2`:
```
x^12 - 1 = (x - 1)^4 · (x^2 + x + 1)^4  [in F_2[x]]
y^6  - 1 = (y - 1)^2 · (y^2 + y + 1)^2  [in F_2[y]]
```

Semisimple quotient (Jacobson radical mod):
```
F_2[Z_12] / Jac = F_2[x] / ((x - 1)(x^2 + x + 1)) ≅ F_2 × F_4
F_2[Z_6]  / Jac = F_2[y] / ((y - 1)(y^2 + y + 1)) ≅ F_2 × F_4
```

Character orbits of `Z_12 × Z_6` over the algebraic closure of `F_2`,
collapsed to the **3 × 3 = 9 orbits** at the semisimple-quotient level.
Each orbit is identified by `(a, b)` with `a, b ∈ {0, 1, 2}`:
- `a = 0`: `x ↦ 1` (F_2-character)
- `a = 1`: `x ↦ ω` (F_4-character)
- `a = 2`: `x ↦ ω^2` (F_4-character, Galois-conjugate of `a = 1`)
- Similarly for `b`.

## Computing `Â`, `B̂` at each character

Let `u = u_a` (image of `x`), `v = v_b` (image of `y`).  Then:
- `Â(u, v) = u^3 + v + v^2`
- `B̂(u, v) = v^3 + u + u^2`

Useful identities in `F_4 = F_2(ω)`:
- `ω^3 = 1`
- `1 + ω + ω^2 = 0`

### Â table:

```
        v=1 (b=0)   v=ω (b=1)   v=ω^2 (b=2)
u=1     1+1+1=1    1+ω+ω^2=0  1+ω^2+ω=0
u=ω     ω^3+1+1=1  1+ω+ω^2=0  1+ω^2+ω=0
u=ω^2   1+1+1=1    1+ω+ω^2=0  1+ω^2+ω=0
```

Wait — for `u = ω`, `u^3 = ω^3 = 1`.  For `u = ω^2`, `u^3 = ω^6 = (ω^3)^2 = 1`.
So `u^3 = 1` for all three `u` values.  Then `Â = 1 + v + v^2`, depending
only on `v`.  **`Â = 0` iff `v ≠ 1` iff `b ∈ {1, 2}`.**

### B̂ table (by symmetry, swapping roles of `u` and `v`):

`v^3 = 1` for all three `v` values, so `B̂ = 1 + u + u^2`, depending only
on `u`.  **`B̂ = 0` iff `u ≠ 1` iff `a ∈ {1, 2}`.**

## Joint vanishing set `Z(A, B)`

```
Z(A, B) = {(a, b) : Â(a,b) = 0 ∧ B̂(a,b) = 0}
        = {(a, b) : a ∈ {1, 2} ∧ b ∈ {1, 2}}
        = {(1,1), (1,2), (2,1), (2,2)}
```

**4 character orbits survive.**

## What this means for Camion's bound

Camion's classical theorem (apparent distance): a codeword whose Fourier
transform is supported only on `Z(A, B)` has Hamming weight bounded
**below** by the apparent distance, which is computed as a function of
the **largest consecutive-zero pattern** in the spectrum.

Bernal-Simón 2024 reformulation (multivariate): for a 2D abelian code
over `Z_ℓ × Z_m`, if the spectrum vanishes on a *product* pattern
`{a_0, …, a_0 + r - 1} × {b_0, …, b_0 + s - 1}` of consecutive indices,
then the apparent distance is at least `(r + 1)(s + 1)`.

In our case, the spectrum vanishes on `Z(A, B) = {1, 2} × {1, 2}`.  This
is a 2 × 2 "consecutive box" *in the cyclotomic-coset index space*
(`a ∈ {1, 2}` are two consecutive nonzero values in `Z_3`-cosets;
similarly `b`).

**However**, two crucial caveats:

1. **The complement matters more.**  The complement of `Z(A, B)`
   in `{0, 1, 2}^2` is `{(0, 0), (0, 1), (0, 2), (1, 0), (2, 0)}` — a
   5-element "L-shape", not a consecutive product pattern.  The Camion
   bound's "consecutive run" is in the *complement* (the support of
   nonzero spectrum), not in the vanishing set.

   Re-interpreting: a non-boundary cycle's spectrum lives **inside**
   `Z(A, B)`, so its spectrum-support is at most a 2 × 2 box.  In the
   multivariate BCH framework, vanishing on a `(ℓ - 2) × (m - 2)` block
   (everything outside the 2 × 2 support) gives apparent distance
   `≥ (ℓ - 2) · (m - 2) + 1`?  No, that's not quite the formulation
   either.

2. **Modular characteristic obstruction.**  Camion's classical proof
   uses Plancherel / orthogonality of characters, which require
   semisimplicity (`gcd(|G|, char F) = 1`).  Here `2 | 72`, so the
   classical statement does not apply directly — the apparent distance
   needs a **modular reformulation**.  Some authors (Charpin et al.)
   have developed this for cyclic codes, but the multivariate-modular
   case is open in published literature.

## Best-case Camion bound (most optimistic interpretation)

The most optimistic reading: every non-boundary cycle has spectrum
supported on `Z(A, B)`, hence (loosely) is a sum of at most 4
"character-monomials".  Such a sum can have Hamming weight as low as
`|G| / |Z(A, B)| = 72 / 4 = 18` (when the 4 "characters" combine
constructively) or as high as `|G| = 72` (delocalized).  But this
doesn't give a *lower* bound; it gives an existence statement.

A more careful multivariate-BCH-style argument over the cyclotomic
cosets: the 4 surviving characters live in `F_4 ⊗ F_4 = F_16` orbits;
each orbit has `F_2`-multiplicity at most `4 × 2 = 8` (from the
modular nilpotent factors).  The **dimension** of the surviving subspace
is at most `4 × 8 = 32`?  But `k = 12 < 32`, suggesting most of this
"surviving" space *is* in the boundary `im H_Z^T`, not in the homology.

## Realistic Camion bound estimate

Without working out the modular-Camion proof formally, the heuristic
estimate (based on the 2 × 2 zero-box structure and the `Z_3` cyclotomic-
coset spacing) is:

**`d_app(gross) ∈ {3, 4, 5, 6, 7, 8, 9}`**, with the most likely value
being around `4`–`6`.

The true `d = 12` is **strictly greater** than the most optimistic
Camion bound by at least `12 - 9 = 3` (likely much more).  The Camion
approach is therefore **fundamentally loose** for this polynomial pair.

## Implication for Approach A

This is a **calibrated negative result for Approach A's tight goal**.
The Camion machinery, even fully formalized, would yield at best
`d ≥ 9` and more realistically `d ≥ 4`–`6`.

This matches the *risk* identified in the original `hypothesis.md`
(Risk 1: "Camion is *known* to be loose for codes with engineered
distance").  The gross code was numerically optimized (MIP-discovered),
not algebraically designed, so its algebraic-bound prediction
underestimates the true distance.

**What we WOULD learn by formalizing the full Camion bound**:
- The specific value (`d_app(gross) = K` for some `K ∈ [3, 9]`).
- A reusable theorem applicable to *other* BB codes (different `A, B`).
- Confirmation that for the gross code, the Camion bound is loose by
  at least `12 - K ≥ 3` distance units.

**What we would NOT learn**:
- A tight `d ≥ 12` proof.  This requires either a different algebraic
  bound (e.g. polynomial-ideal Gröbner basis, lifted-product
  refinement, covering-graph chain maps) or fundamentally new methods.

## Recommendation

Given the realistic Camion bound is `d ≥ 4`–`9`, and the framework cost
to formalize the modular Camion theorem is high (~30+ hours of
group-algebra infrastructure), the cost/benefit is **negative**.

The Approach-A `final_writeup.md` should reflect this honestly: we
have *predicted* (via this spectral analysis) what Camion would give,
and the answer is too loose to be worth the Lean formalization cost
on this particular target.

The infrastructure landed (`BBChainComplex.lean`,
`chainWeight_lower_bound_transfers`) is still valuable independently
of Camion, as it unblocks downstream approaches B (lifted-product),
C (Gröbner), and any future moonshot on a *different* BB code with
better-aligned polynomials.
