# Evidence — HT/Roos lower bound on BB code distance

Full corpus-evaluation details live in `experiments/bb_lab/notes/T2R3.4_eval.md`.
This document summarizes the structural findings supporting the verdict.

## Literature triangulation (T2R3.0)

Confirmed: Hartmann-Tzeng (1972) and Roos (1983) lower bounds for
univariate cyclic codes are textbook. Their multivariate generalizations
(Camion 1970, Sabin-Lomonaco 1992, Saints-Heegard 1995,
Bernal-Bueno-Carreño-Simón 2016) are also established.

**HT/Roos / Camion has NOT been applied to BB codes** in the surveyed
literature. The five primary BB papers (LP23 arXiv:2306.16400,
Bravyi 2024 arXiv:2308.07915, KP13 arXiv:1212.6703,
Panteleev-Kalachev 2021 arXiv:2012.04068, Wang-Pryadko 2022
arXiv:2203.17216) and recent papers (Wang-Mueller 2408.10001,
Postema-Kokkelmans 2502.17052, arXiv:2511.13560) make no mention.
LP23 §III.C explicitly notes that "the CSS bounds (31) are not very
useful" for highly-degenerate quantum LDPC codes — and `d ≥ ⌈d_A^⊥ / c⌉`
(LP23 Stmt 12) is the only published lower bound of "weight-over-weight"
shape, with `c` typically large for engineered BB codes.

Application of multivariate HT/Roos to BB codes is **novel-to-us**
(high confidence) and **plausibly novel-to-literature** (medium
confidence). See `experiments/bb_lab/notes/T2R3.0_literature_check.md`.

## Implementation (T2R3.1, T2R3.2, T2R3.3)

New module `experiments/bb_lab/src/bb_lab/ht_roos.py`:

* `defining_set(A, G)` returns `T_A ⊆ Ĝ_odd` — the zeros of A in F̄_2.
* `nonvanishing_set(A, G)` returns `Ĝ_odd \\ T_A` — the textbook
  defining set of the annihilator code `ker M_A`.
* `bch_bound(T, n)`, `ht_bound(T, n)` — classical univariate bounds.
* `mv_bch_bound(T, orders)`, `mv_ht_bound(T, orders)` — multivariate
  generalization (correct for cyclic G; conservative for non-cyclic G).
* `bb_ht_per_block_bound(A, B, G)` returns `(mv_ht(nv(A)), mv_ht(nv(B)))`.
* `bb_ht_condition(A, B, G, d_exact=...)` returns `(bool, diagnostic)`:
  gates on F_2[G] semisimple (|G| odd) AND the textbook upper bound
  being tight (d_X = min(d_A^⊥, d_B^⊥)).
* `bb_ht_bound(A, B, G, d_exact=...)` returns the candidate bound
  (`min(mv_ht_A, mv_ht_B)` if condition fires, else 1).

Test suite: `tests/test_ht_roos.py` (32 tests, all pass) covers:
* Classical BCH (Hamming dual, consecutive runs).
* Univariate HT (matches mv_ht when orders=(n,)).
* Multivariate BCH for cyclic G with full-G-generator chains.
* Non-cyclic G defensiveness (returns 1 when no full-G generator).
* Bravyi smoke tests (no crashes, all bounds ≤ |G|).
* Defining set ↔ vanishing orbits round-trip.

## Corpus evaluation (T2R3.4)

Driver `experiments/bb_lab/scripts/tier2_ht_roos_eval.py` runs the
bound on every corpus row with `d_exact` set and on all 5 Bravyi
codes from `instances/bravyi_table.yaml`.

### Bravyi table

| code | n | k | d | mv_ht(nv(A)) | mv_ht(nv(B)) | d_A^⊥ | d_B^⊥ | S(A,B)? | bound | loose by |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| bb_72_12_6 | 72 | 12 | 6 | 1 | 1 | 6 | 6 | no (G_not_semisimple) | 1 | — |
| bb_90_8_10 | 90 | 8 | 10 | 1 | 1 | 10 | 10 | yes (ok_exact) | 1 | 9 |
| bb_108_8_10 | 108 | 8 | 10 | 1 | 1 | 12 | 12 | no (G_not_semisimple) | 1 | — |
| gross | 144 | 12 | 12 | 1 | 1 | 12 | 12 | no (G_not_semisimple) | 1 | — |
| bb_288_12_18 | 288 | 12 | 18 | 1 | 1 | ? | ? | no (block_kernel_too_big) | 1 | — |

**Gross specifically**: `bb_ht_bound = 1`, far loose of the engineering
target d = 12. Two compounding obstructions:

1. **F_2[G] non-semisimple** for gross's `G = Z_12 × Z_6` (|G|=72 even).
   The Jacobson radical contributes kernel mass invisible to HT on the
   semisimple quotient.
2. **G_odd non-cyclic** (gcd(3, 3) = 3 for gross's G_odd = Z_3 × Z_3).
   No full-G_odd generator exists; our cyclic-only multivariate HT
   returns 1. The genuine multivariate Camion bound applies in principle
   but isn't implemented (and is significantly more involved than
   what we coded).

bb_90 passes obstruction 1 (|G|=45 odd, semisimple), but G_odd =
Z_15 × Z_3 has gcd(15, 3) = 3, so it also fails obstruction 2.

### Corpus sweep (3894 rows with d_exact)

| diagnostic | count |
|---|---:|
| `G_not_semisimple` | 3779 (97.0%) |
| `d_exact < min_block` (textbook bound not tight) | 96 (2.5%) |
| `ok_exact` (S(A,B) holds) | 19 (0.5%) |

* **Violations**: 0
* **Tight in S**: 13 (all on Z_3 × Z_5)
* **Loose in S but no violation**: 6 (3 on Z_3 × Z_3, 3 on others)

### Per-group breakdown

| group | total | S holds | tight | violations |
|---|---:|---:|---:|---:|
| Z_3 × Z_3 | 12 | 6 | 0 | 0 |
| Z_3 × Z_4 | 73 | 0 | 0 | 0 |
| Z_3 × Z_5 | 103 | 13 | 13 | 0 |
| Z_3 × Z_6 | 166 | 0 | 0 | 0 |
| Z_4 × Z_6 | 106 | 0 | 0 | 0 |
| Z_5 × Z_6 | 2622 | 0 | 0 | 0 |
| Z_6 × Z_6 | 812 | 0 | 0 | 0 |

Only Z_3 × Z_5 (cyclic, gcd(3,5)=1) and Z_3 × Z_3 (semisimple but
non-cyclic — bound = 1) have rows where S holds. **All other groups
have even |G| and are gated out by the semisimple check.**

## Why the bound is structurally loose on Bravyi (the §6i lesson, in HT clothing)

Per HANDOFF §6i, all 5 Bravyi codes have `[G : ⟨supp(A)⟩] = 3` — they
live in the degenerate regime where simple cyclic-code algebra fails.
The HT-specific manifestation: Bravyi engineered |G| to be even (so
F_2[G] is non-semisimple, HT only sees the G_odd quotient) AND
G_odd to be non-cyclic (so even the semisimple-quotient bound from
my impl is trivial).

The combination is no accident. Engineered BB codes with
d ≈ √n scaling rely on **mixed-block X-logicals** living in the
radical of F_2[G] (informally: cross-block correlations beyond
what character theory on G_odd can see). HT/Roos directly cannot
detect these — that's its limitation.

A bound that *does* see them needs to operate on the **full**
group algebra `F_2[G]`, not just its semisimple quotient. This is
the territory of:
* Bernal et al. 2016's apparent distance for *full* multivariate
  abelian codes (handles the non-cyclic case properly).
* Cover-graph chain-map transfer bounds (Pesah et al. 2025).
* Quantum-specific bounds incorporating the 2-block structure
  (Lin-Pryadko Statement 5's d_S, etc.).

None of these are pursued in this round.
