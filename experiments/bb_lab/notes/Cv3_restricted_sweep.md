# C-v3 — restricted corpus sweep

Date: 2026-05-26. HANDOFF_C3 §C-v3.2.

Reproduce via `uv run python scripts/cv3_restricted_sweep.py`.

## 1. Setup

The C-v2 conjecture is

  `d_X(BB(G, A, B)) ≥ ⌈(1/c) · min_O min(w_1(A, O), w_1(B, O))⌉`

with `c = [G_a : G_a ∩ G_b]`. HANDOFF_C3 §2 narrows the hypothesis to
require **`G_odd` elementary abelian**.

This module's `is_g_odd_elementary_abelian` is the **loose** version:
for every prime `p | |G_odd|`, the p-primary part of G_odd is
`(Z_p)^{k_p}` (NO `Z_{p^2}` or higher). This includes bb_90's
`G_odd = Z_3 × Z_3 × Z_5` (two primes but each part squarefree) and
excludes bb_108's `G_odd = Z_9 × Z_3`.

## 2. Corpus distribution under the loose classifier

| classifier | rows | notes |
|---|:---:|---|
| Total labeled | 3 894 | |
| Loose elementary-abelian G_odd | **3 894** | All labeled rows qualify |
| Single-prime elementary-abelian (G_odd = (Z_p)^k) | 1 169 | Excludes multi-prime G_odd cases |
| Multi-prime loose-but-not-strict | 2 725 | Z_3 × Z_5, Z_5 × Z_6 (both have Z_3 × Z_5 G_odd) |

**Surprise**: every labeled corpus group has elementary-abelian G_odd
in the loose sense. The corpus does not contain any Z_9-style groups
in its labeled portion. Z_9 × Z_6 (12 488 rows) is the dominant
unlabeled group, but the SAT compute budget never produced d_exact
for any of them.

**This means**: the loose elementary-abelian restriction alone does
NOT filter out the 3 319 corpus violations seen in C-v2; the labeled
corpus is entirely in the loose-elem-ab domain. The narrowing has
to be augmented with another condition.

## 3. By `c` (the LP joint-support index)

| `c` | total | violations | tight | loose |
|:---:|:---:|:---:|:---:|:---:|
| 1 | 3 245 | **3 148** | 97 | 0 |
| 2 | 575 | 171 | 83 | 321 |
| 3 | 61 | **0** | 32 | 29 |
| 4 | 8 | 0 | 0 | 8 |
| 5 | 1 | 0 | 1 | 0 |
| 6 | 4 | 0 | 0 | 4 |

**The pattern is clean**: violations vanish at `c ≥ 3`. The narrowed
conjecture survives in the **loose-elem-ab AND `c ≥ 3`** subset (74
rows, 0 violations, 33 of 74 ≈ 44.6% tight).

## 4. By G_odd decomposition

| decomp | rows | violations | tight | tightness |
|:---|:---:|:---:|:---:|:---:|
| `(3,)` (rank-1 single-prime) | 179 | 55 | 93 | **52.0%** |
| `(3, 3)` (rank-2 single-prime, `p = 3`) | 990 | 763 | 62 | 6.3% |
| `(3, 5)` (multi-prime) | 2 725 | 2 501 | 58 | 2.1% |

The single highest tightness rate (52%) is on **rank-1 single-prime
G_odd** — the Z_4 × Z_6 and Z_3 × Z_4 family. Z_4 × Z_6 has G_odd =
Z_3, single-prime, rank-1 (see [`Cv3_z4xz6_anomaly.md`](Cv3_z4xz6_anomaly.md)).

## 5. By `c` × strict-vs-loose

| classifier | `c` | total | violations | tight |
|:---|:---:|:---:|:---:|:---:|
| Single-prime (p=3) | 1 | 840 | 743 | 97 |
| Single-prime (p=3) | 2 | 256 | 75 | 26 |
| Single-prime (p=3) | 3 | 61 | **0** | 32 |
| Single-prime (p=3) | 4 | 8 | 0 | 0 |
| Single-prime (p=3) | 5 | 0 | 0 | 0 |
| Single-prime (p=3) | 6 | 4 | 0 | 0 |
| Loose-but-not-strict | 1 | 2 405 | 2 405 | 0 |
| Loose-but-not-strict | 2 | 319 | 96 | 57 |
| Loose-but-not-strict | 5 | 1 | 0 | 1 |

The single-prime restriction would lose 13 c≥3 rows (the c=5 case in
loose-but-not-strict). The loose version retains all 74 c≥3 rows. **Both
filter versions give 0 violations at c ≥ 3, so the loose definition
is preferred** (covers more codes; includes bb_90).

## 6. The narrowed conjecture that survives

> **If `G_odd` is loosely elementary abelian (each prime-part is elementary
> abelian) AND `c ≥ 3`, then**
>
> `d_X(BB(G, A, B)) ≥ ⌈(1/c) · min_O min(w_1(A, O), w_1(B, O))⌉`.

Corpus evidence on the hypothesis domain (74 rows):
- **0 violations**.
- 33 tight (44.6%).
- 41 loose (gap > 0 from d_exact).

## 7. What happens without the c ≥ 3 condition?

At c=1: 97% violation rate, even with elementary-abelian G_odd.
At c=2: 30% violation rate.

The c condition is not optional. HANDOFF_C3 §6 risk predicted this
("the narrowing to elementary abelian *and* c≥3 might be needed"),
and the data confirms it.

## 8. Sample violations (loose elem-ab, c < 3)

All from the c ≤ 2 regime, which is excluded by the survival
hypothesis. The pattern: when A = B or A ∈ ⟨B⟩, `c = 1` and the
denominator is missing.

| instance | group | c | d | bound | A | B |
|---|---|:---:|:---:|:---:|---|---|
| 5ae76cea | Z_3×Z_5 | 1 | 2 | 8 | 1+x+x² | 1+x+x² |
| 8296ddb0 | Z_3×Z_6 | 1 | 2 | 12 | 1+y+y² | 1+y+y² |
| 7c184175 | Z_4×Z_6 | 1 | 2 | 4 | 1+y+y² | 1+y+y² |
| 50bc6d24 | Z_3×Z_6 | 2 | 2 | 3 | 1+y+y² | (some shift) |

## 9. Sample non-violations on the narrowed domain (c ≥ 3)

| instance | group | c | d | bound | verdict |
|---|---|:---:|:---:|:---:|:---:|
| gross | Z_12×Z_6 | 3 | 12 | 12 | tight |
| (sample c=3 corpus row) | Z_6×Z_6 | 3 | 4 | 2 | loose |
| (sample c=4 corpus row) | Z_6×Z_6 | 4 | 6 | 3 | loose |

## 10. Bravyi-table verification

| code | G | elem-ab | c | bound | d | hypothesis applies? | verdict |
|---|---|:---:|:---:|:---:|:---:|:---:|:---:|
| bb_72_12_6 | Z₆×Z₆ | ✓ | 3 | 6 | 6 | ✓ | tight |
| bb_90_8_10 | Z₁₅×Z₃ | ✓ | 3 | 10 | 10 | ✓ | tight |
| bb_108_8_10 | Z₉×Z₆ | ✗ | 3 | 12 | 10 | **excluded** | n/a (out of domain) |
| gross | Z₁₂×Z₆ | ✓ | 3 | 12 | 12 | ✓ | tight |
| bb_288_12_18 | Z₁₂×Z₁₂ | ✓ | 3 | 18 | 18 | ✓ | tight |

**4 of 5 Bravyi codes in domain, all tight. bb_108 is excluded by
hypothesis (NOT a counterexample).**

This is the strongest result the C-program has produced:
- Tight on 4 Bravyi instances including gross.
- 0 corpus violations on the hypothesis domain.
- The hypothesis is structurally clean (loose elem-ab G_odd ∧ c ≥ 3).
- The excluded instance (bb_108) has G_odd containing a `Z_9` factor,
  which is a structurally distinct case not covered.
