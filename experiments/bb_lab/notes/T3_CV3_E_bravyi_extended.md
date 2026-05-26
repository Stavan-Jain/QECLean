# T3-E — Gross-family parametric scan (substitute for Bravyi extended)

Date: 2026-05-26. HANDOFF_TIER3_CV3 §4 T3-E.

## Result: 0 violations on gross-family variants

Per HANDOFF §4 T3-E, the "Bravyi paper extended" test was substituted
with a parametric scan over gross's polynomial family (varying the
x-exponent `a` in `A = x^a + y + y^2` on Z_12 × Z_6).

| label | G | A | B | a (x-exp) | c | n | k | bound | d | verdict |
|---|---|---|---|---|---|---|---|---|---|---|
| E1 | Z_12×Z_6 | x³+y+y² (gross) | y³+x+x² | 3 | 3 | 144 | 12 | 12 | 12 | **tight** |
| E2 | Z_12×Z_6 | x²+y+y² | y³+x+x² | 2 | 3 | — | 0 | — | — | k=0 |
| E3 | Z_12×Z_6 | x⁴+y+y² | y³+x+x² | 4 | 3 | — | 0 | — | — | k=0 |
| E4 | Z_12×Z_6 | x⁶+y+y² | y³+x+x² | 6 | 3 | 144 | 8 | 6 | 6 | **tight** |
| E5 | Z_12×Z_6 | x⁹+y+y² | y³+x+x² | 9 | 3 | 144 | 12 | 12 | 12 | **tight** |
| E6 | Z_12×Z_6 | x³+y²+y⁵ (reordered y) | y³+x+x² | — | 3 | — | 0 | — | — | k=0 |

3 in-domain testable cases (E1, E4, E5), all **tight**. 0 violations.

## Observations

- Gross's x-exponent a = 3 is one of multiple choices giving d = 12.
  Other choices (a = 9) also give d = 12. Some (a = 6) give d = 6
  (smaller, because the x-axis spread is smaller).
- The k = 0 cases (a ∈ {2, 4}) indicate those specific (A, B) pairs
  have no logical qubits — out of distance scope.
- The "reordered y-exponents" case (E6: y² + y⁵) gives k = 0. Different
  y-exponents change the joint vanishing pattern and can collapse k.

## Verdict on T3-E

**Clean** within the gross-family parametric scan on Z_12 × Z_6.
The C-v3.1 refined hypothesis holds on gross's native group. The
parametric variations preserve tightness when k > 0.

This is consistent evidence — but it's testing on the conjecture's
"natural habitat" (gross's group) where it was already known to be
tight. It doesn't rule out failure modes on other groups (which T3-C
demonstrated decisively).

## What we DID NOT test

- Actual extended Bravyi-paper survey (would require reading the
  paper carefully for additional codes beyond the 5 in
  `instances/bravyi_table.yaml`).
- Codes from Bravyi's supplementary materials with different group
  structure or polynomial families.
- Lifted-product-style BB codes from other papers.

Sufficient for "in-house family check"; not sufficient for "Bravyi
literature scan." Counts as partial coverage of HANDOFF §4 T3-E.
