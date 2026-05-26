# T3-D — Adversarial natural constructions

Date: 2026-05-26. HANDOFF_TIER3_CV3 §4 T3-D.

## Result: 0 violations on hand-picked adversarial cases

The adversarial-sampler approach (random / annealing) was scoped out
of this session per the user's preference for small targeted tests
(HANDOFF.md §5 enumeration slowness). Instead, this battery used
hand-picked "natural constructions" within Z_6 × Z_6 (gross's G_odd
family) and rank-1 G_odd:

| label | G | A | B | wA | wB | c | in_domain | bound | d | verdict |
|---|---|---|---|---|---|---|---|---|---|---|
| D1 | Z_6×Z_6 | x³+y+y² | y³+x+x² | 3 | 3 | 3 | ✓ | 6 | 6 | tight |
| D2 | Z_6×Z_6 | 1+x+y² | 1+y+x² | 3 | 3 | 2 | ✗ | 6 | 8 | out |
| D3 | Z_6×Z_6 | 1+x+x² | 1+y+y² | 3 | 3 | 6 | ✓ | 2 | 4 | loose |
| D4 | Z_6×Z_6 | 1+x²+y⁴ | 1+y²+x⁴ | 3 | 3 | 1 | ✗ | 6 | 4 | out |
| D5 | Z_6×Z_6 | 1+x+xy | 1+y+xy | 3 | 3 | 1 | ✗ | 18 | 8 | out |
| D6 | Z_4×Z_6 | 1+y+y² | x+xy+xy² | 3 | 3 | 1 | ✗ | 4 | 2 | out |

2 in-domain cases (D1, D3), both non-violating (1 tight, 1 loose).
**0 violations.**

## Observations

D5 is interesting: `bound = 18` but `c = 1`, so it's out of domain. If
c were ≥ 3, this would be a clear violation (d = 8 < bound). The
`xy` cross-axis term creates a non-axis-separable polynomial that the
C-v1 invariant computes a much higher bound for than the actual d
warrants. Suggests that non-axis-separable polynomials are an under-
tested regime (none of the 5 Bravyi codes are non-axis-separable).

D6: rank-1 G_odd case (Z_4 × Z_6 has G_odd = Z_3). Out of domain due
to c = 1.

## Verdict on T3-D

**No violations found in this small set**, but the set is small and
biased toward Bravyi-family-style polynomials. The full adversarial
sampler (hill-climb maximization of bound − d gap) was not run; that's
a follow-up that requires more time and the L1-sampling fallback for
SAT-expensive cases.

D5 hints at a potential failure mode (non-axis-separable polynomials)
that wasn't explored systematically.

## What we DID NOT test

- Hill-climb / simulated annealing adversarial samples (HANDOFF §4 T3-D
  full target).
- Non-axis-separable polynomials with c ≥ 3 (the D5-style stress test).
- L1-sampling-based d_ub on large groups.

These remain as Tier-3-round-2 follow-up if the program continues.
