# Evidence — Tier-3 adversarial validation

Three sources of evidence: corpus sweep, Bravyi-table benchmark,
adversarial random search. All three contain falsifying instances.

## 1. Corpus sweep (T3.2)

Source: 3 894 corpus rows with `d_exact` populated, across 7 groups.

| Group   | rows | violations | tight | loose | tightness | avg gap | max gap |
|---------|-----:|-----------:|------:|------:|----------:|--------:|--------:|
| Z3xZ3   |   12 |          3 |     6 |     3 |    50.0 % |   -0.33 |       2 |
| Z3xZ4   |   73 |         12 |    20 |    41 |    27.4 % |   +0.63 |       2 |
| Z3xZ5   |  103 |         11 |    28 |    64 |    27.2 % |   +1.20 |       4 |
| Z3xZ6   |  166 |         32 |    32 |   102 |    19.3 % |   +0.63 |       4 |
| Z4xZ6   |  106 |     **48** |    58 |     0 |    54.7 % |   -2.09 |       0 |
| Z5xZ6   | 2622 |        134 |   418 |  2070 |    15.9 % |   +3.24 |       6 |
| Z6xZ6   |  812 |    **167** |   325 |   320 |    40.0 % |   -0.09 |       4 |
| **TOTAL** | **3894** | **407 (10.5%)** | **887 (22.8%)** | **2600 (66.8%)** | | **+2.17** | **+6** |

**Gap distribution** (gap = d_exact − bound; negative = violation):

| Gap  |   -22 |   -18 |   -14 |   -10 |    -8 |    -6 |    -4 |    -2 |     0 |    +2 |    +4 |    +6 |
|------|------:|------:|------:|------:|------:|------:|------:|------:|------:|------:|------:|------:|
| Count |    4 |     4 |     2 |    29 |    38 |    59 |    96 |   175 |   887 |   973 |   691 |   936 |

407 of 3 894 rows have negative gap (violation). Max single-instance
violation: gap = -22 (bound predicts d ≥ 24, actual d_exact = 2; four
such instances in Z_6 × Z_6).

**Worst violations**: codes with `A = 1 + y² + y⁴` (a "y-only" polynomial
landing in the 2-Sylow component). E.g.,

| code_id              | group  | A              | B              |   d | bound | gap |
|----------------------|--------|----------------|----------------|----:|------:|----:|
| bb_enum_Z6xZ6_624a4a1c | Z6xZ6 | `1+y²+y⁴`     | `1+y²+y⁴`     |   2 |    24 | -22 |
| bb_enum_Z5xZ6_df0763e3 | Z5xZ6 | `1+y²+y⁴`     | `1+y²+y⁴`     |   2 |    20 | -18 |
| bb_enum_Z3xZ6_d5752d61 | Z3xZ6 | `1+y²+y⁴`     | `1+y²+y⁴`     |   2 |    12 | -10 |

The pattern: A vanishes on multiple G_odd orbits with high μ (4 here,
coming from `(1+y)⁴ = 1+y⁴` in `F_2[Z_6]` whose 2-Sylow component is
`Z_2`, but the `1+y²+y⁴ = (1+y²)·(1+y²)` factorization pushes A deep
into the radical). When B has the same algebraic structure, the
purported "joint vanishing" mass is huge, but the actual minimum-weight
logical is only weight 2 — most of the joint kernel lies in `rowspan(H_X)`.

## 2. Bravyi-table benchmark (T3.3)

All five Bravyi BB codes:

| code          | group   | published d | bound | gap | verdict   |
|---------------|---------|------------:|------:|----:|-----------|
| bb_72_12_6    | Z6xZ6   |          6 |    8 |  -2 | VIOLATION |
| bb_90_8_10    | Z15xZ3  |         10 |    4 |  +6 | loose     |
| bb_108_8_10   | Z9xZ6   |         10 |    4 |  +6 | loose     |
| **gross**     | Z12xZ6  |         12 |    8 |  +4 | **loose** |
| bb_288_12_18  | Z12xZ12 |         18 |   16 |  +2 | loose     |

**`bb_72_12_6` violates the bound**: bound 8 > d 6. This is the *smallest
Bravyi instance*, and the conjecture already fails on it.

**Gross** has gap +4 (bound = 8, d = 12). NOT TIGHT, contrary to the
Tier-3 spec's claim. The spec assumes 3 joint-vanishing orbits, but
only 2 jointly vanish (verified empirically against T2.2's own
"joint vanishing" computation).

Per-orbit detail on gross (`G_odd = Z_3 × Z_3`):

| orbit (G_odd) |  size | μ(A) | μ(B) | contribution |
|---------------|------:|-----:|-----:|-------------:|
| (0,0) trivial |     1 |    0 |    0 |            0 |
| (0,1)/(0,2)   |     2 |    2 |    0 |            0 |
| (1,0)/(2,0)   |     2 |    0 |    2 |            0 |
| (1,1)/(2,2)   |     2 |    2 |    2 |            4 |
| (1,2)/(2,1)   |     2 |    2 |    2 |            4 |
| **TOTAL**     |       |      |      |        **8** |

Only the diagonal and anti-diagonal cube-root orbits are jointly
vanishing; the y-only and x-only orbits each have one of (μ_A, μ_B) = 0.

## 3. Adversarial random sampling (T3.4)

Random weight-3 polynomial pairs across three non-semisimple groups:

| Group  | samples (k ≥ 2) | violations | rate |
|--------|----------------:|-----------:|------|
| Z12xZ6 |              20 |          0 |   0% |
| Z15xZ2 |               7 |          0 |   0% |
| Z6xZ4  |               9 |          2 | 22 % |

For Z_6 × Z_4, two samples produced bound > L1_UB (where L1 is a cheap
sampling-based upper bound on d). E.g.:

```
A = y^3 + x + x^2*y    B = x*y^3 + x^3*y^3 + x^5*y^3
G = Z_6 × Z_4,  n=48,  k=8
bound = 4,  L1_UB = 2
```

L1 sampling gave an upper bound 2 on d_X, so d_X ≤ 2 < 4 = bound.
Violation.

**Edge cases** (instances with max μ ≥ 3): Z_12 × Z_6 had 74 such hits
in 200 random samples, but most had bound = 0 (because at least one of
A, B failed to vanish on the high-μ orbit). For Z_6 × Z_4, one
particularly striking edge case had max μ = 4 on both A and B, bound = 8,
L1_UB = 4 — another violation.

## Smallest documented falsifying instance

From the corpus sweep, the smallest instance violating the bound is

```
G = Z_3 × Z_4
A = 1 + x + x²
B = 1 + x + x²
n = 24, k = 16, d_exact = 2 (verified by brute-force weight-1 / weight-2
                            enumeration over 24 qubits)
bound = 8
gap = -6
```

Brute-force witness: the X-error supported on qubits 0 and 4 (in the
24-qubit indexing) commutes with all Z-stabilizers and is anticommuted
by some L_X row, so it's a nontrivial weight-2 X-logical. (Confirmed
in T3 implementation; see the test fingerprint in `T3.4_adversarial.md`.)

This is a tiny instance: G has order 12, the code has 24 qubits, and
direct kernel-dim computation shows μ_O(A) = μ_O(B) = 4 on the single
size-2 vanishing orbit, giving bound = 2 · 4 = 8. But d_X = 2 because
A = B forces a high degree of stabilizer redundancy: the would-be
"low-weight logicals" predicted by the joint-vanishing counting are
mostly in the stabilizer rowspan and project to weight-2 representatives
in the logical group.
