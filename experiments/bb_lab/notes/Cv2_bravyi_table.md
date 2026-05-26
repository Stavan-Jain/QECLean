# C-v2 — Bravyi table

Date: 2026-05-26. HANDOFF_C2 §C-v2.4.

| code | group | n | k | d | c | primary | multi-mu | verdict |
|---|---|:---:|:---:|:---:|:---:|:---:|:---:|:---:|
| bb_72_12_6 | Z₆×Z₆ | 72 | 12 | 6 | 3 | **6** | 3 | ✓ tight |
| bb_90_8_10 | Z₁₅×Z₃ | 90 | 8 | 10 | 3 | **10** | 10 | ✓ tight |
| bb_108_8_10 | Z₉×Z₆ | 108 | 8 | 10 | 3 | 12 | 12 | ✗ **VIOLATES** (12 > 10) |
| gross | Z₁₂×Z₆ | 144 | 12 | 12 | 3 | **12** | 6 | ✓ tight |
| bb_288_12_18 | Z₁₂×Z₁₂ | 288 | 12 | 18 | 3 | **18** | 5 | ✓ tight |

**4 of 5 Bravyi instances are tight (d_published exactly matches
the primary bound), and 1 violates.**

The violation on `bb_108_8_10` is decisive: this single Bravyi
instance falsifies the conjecture, independently of the corpus
sweep.

## Why bb_108_8_10 violates

bb_108_8_10 is structurally the odd-one-out among the Bravyi
instances:

| code | G_odd | G_2 | Loewy length |
|---|---|---|:---:|
| bb_72_12_6 | Z₃×Z₃ | Z₂×Z₂ | 3 |
| bb_90_8_10 | Z₁₅×Z₃ | (trivial) | 1 |
| bb_108_8_10 | **Z₉×Z₃** | Z₂ | 2 |
| gross | Z₃×Z₃ | Z₄×Z₂ | 5 |
| bb_288_12_18 | Z₃×Z₃ | Z₄×Z₄ | 7 |

- **bb_108_8_10 has G_odd = Z₉ × Z₃** (the only Bravyi instance
  with a non-elementary G_odd cube-root structure).
- The other 4 have G_odd ∈ {Z₃ × Z₃, Z₁₅ × Z₃} which lack the
  Z₉ factor.

bb_108_8_10's Frobenius orbits on Ĝ_odd = Z₉ × Z₃ partition 27
elements into orbits of sizes [1, 2, 2, 2, 2, 6, 6, 6]. The
size-6 orbits (containing characters of order 9 lifted to F_64)
support the algebraic structure that gives the genuine d = 10.

For the conjecture's RHS, only size-2 orbits contribute to the min
(w_1 = 36, evidence that these are the orbit-O isotypic kernels of
the same size as gross's). But d_actual = 10 < 12, so the
conjecture overestimates by 2.

## What this means for the conjecture

The conjecture's tightness on 4 of 5 Bravyi instances is **not
enough** to declare it correct. The single bb_108_8_10 violation
shows the conjecture is wrong: it's a coincidence on the Z₃ × Z₃
G_odd family (where bb_72, gross, bb_288 all live), not a structural
truth about BB codes.

Per HANDOFF_C2 §C-v2.6 stop conditions: this is **falsified-by-Bravyi-table**.
The Z₃ × Z₃ tightness is interesting empirical data but does not
elevate to a theorem.

## Possible follow-up shapes (not pursued in C-v2)

The conjecture might survive on a **smaller** subdomain:

- **`G_odd is elementary abelian` AND `c = 3`**: bb_72, gross, bb_288
  all satisfy this (G_odd = Z₃ × Z₃ which is elem. abelian over F_3).
  bb_108_8_10 fails the "elementary abelian" condition because
  G_odd = Z_9 × Z_3 has the 9-cycle. *Untested by corpus sweep* —
  Z₃ × Z₃ has only 12 labeled corpus rows.

- **`gcd(|G_odd|, |G_2|)` divides into G_odd's representation
  structure in a specific way**: too vague to formalize without
  additional case study.

Restricting to "G_odd elementary abelian + c=3" is a clean
mathematical condition but represents only a sliver of BB codes,
and is not what HANDOFF_C2's program is trying to bound (the goal
was a bound for **all** BB codes including bb_108_8_10).

The narrowed conjecture would still need to be proven; that's a
separate (smaller) program and is **deferred** here.
