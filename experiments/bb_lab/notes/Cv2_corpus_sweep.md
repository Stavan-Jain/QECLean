# C-v2 — corpus sweep results

Date: 2026-05-26. HANDOFF_C2 §C-v2.3.

Reproduce via `uv run python scripts/cv2_corpus_sweep.py`.

## 1. Corpus state

3 894 labeled rows (with `d_exact`) across 8 group structures. Reflects
the bb-lab-v0 corpus DB. Rows partitioned by `c = [G_a : G_a ∩ G_b]`:

| c | row count |
|:---:|:---:|
| 1 | 3 245 |
| 2 | 575 |
| 3 | 61 |
| 4 | 8 |
| 5 | 1 |
| 6 | 4 |

The c-distribution is heavily concentrated at c = 1 (non-degenerate
BB codes, which are *not* Bravyi-style). Gross-style codes (c = 3)
are 61 of 3 894 (1.6%).

## 2. Primary conjecture result

`bound = ⌈(1/c) · min_O min(w_1(A, O), w_1(B, O))⌉` over jointly
vanishing orbits.

| metric | value |
|:---|:---:|
| Tested | 3 894 |
| Vacuous (no joint vanishing orbit) | 0 |
| **Violations** (bound > d_exact) | **3 319 (85.2%)** |
| Tight (bound == d_exact) | 213 (5.5%) |
| Loose (bound < d_exact) | 362 (9.3%) |
| Mean gap (when loose) | 0.18 |

**The primary conjecture is FALSIFIED across the corpus.**

### Per-c breakdown

| c | total | violations | tight | loose | satisfied |
|:---:|:---:|:---:|:---:|:---:|:---:|
| 1 | 3 245 | **3 148** | 97 | 0 | 97 |
| 2 | 575 | 171 | 83 | 321 | 404 |
| 3 | **61** | **0** | **32** | **29** | **61** |
| 4 | 8 | 0 | 0 | 8 | 8 |
| 5 | 1 | 0 | 1 | 0 | 1 |
| 6 | 4 | 0 | 0 | 4 | 4 |

**Striking pattern**: zero violations for `c ≥ 3`. The conjecture
**holds on the corpus subset where c ≥ 3** (74 rows, 0 violations,
33 tight, 41 loose, 44.6% tightness rate).

For `c = 1`: 97% violation rate — the bound has no denominator and
`min_O w_1` is far larger than the small `d` typical of these codes.
For `c = 2`: 30% violation rate — partial denominator, mixed.

### Sample violations

| instance | group | d_actual | bound | c | A | B |
|---|---|:---:|:---:|:---:|---|---|
| 5ae76cea | Z₃×Z₅ | 2 | 8 | 1 | 1+x+x² | 1+x+x² |
| 8296ddb0 | Z₃×Z₆ | 2 | 12 | 1 | 1+y+y² | 1+y+y² |
| fdf42d8e | Z₃×Z₆ | 4 | 12 | 1 | 1+y+y² | 1+y+x |

The pattern: when `A` and `B` generate the same subgroup (often when
`A = B` or related), `c = 1` and the bound becomes the unfiltered
`min_O w_1`, which can be far above the small `d`.

## 3. Alternative formulations (HANDOFF_C2 §5)

| formulation | violations | tight | loose |
|:---|:---:|:---:|:---:|
| primary | 3 319 | 213 | 362 |
| any-orbit | 3 319 | 213 | 362 |
| multi-mu | 3 133 | 176 | 585 |
| geometric | 3 614 | 192 | 88 |
| sum | **violates gross** | — | — |

- **any-orbit** behaves identically to primary on the labeled corpus
  (in every row, an orbit where one of A/B doesn't vanish doesn't
  produce a finite `w_1`, so the joint-vanishing constraint is
  effectively the only finite case).
- **multi-mu** is slightly tighter on average but still falsifies
  massively at `c = 1`.
- **geometric** is the worst — the geometric mean of two large
  per-orbit values rarely shrinks below `d`.
- **sum** violates on gross itself (bound = 24 > d = 12) as predicted
  in HANDOFF_C2 §5 Alt-C; excluded from corpus testing.

**None of the alternatives change the verdict.**

## 4. Conclusion

The C-v2 primary conjecture and its straightforward variants are
**falsified on the corpus**. The single positive signal — zero
violations at `c ≥ 3` — is undermined by the Bravyi table itself
(see [Cv2_bravyi_table.md](Cv2_bravyi_table.md)): the corpus's
labeled n ≤ 72 subset's `c ≥ 3` slice contains only Z₆×Z₆ and
Z₃×Z₆ instances, while the broader Bravyi family has
bb_108_8_10 in `c = 3` *with d = 10*, where the conjecture predicts
12 (violation).

## 5. Out-of-corpus violation

The corpus's c=3 subset has no Z_9×Z_6 instances at `n=108` (the
SAT budget can't label them). The Bravyi table provides the
`d_published = 10` for bb_108_8_10. The conjecture's bound on this
instance is 12, exceeding the published distance. **The c=3 subset
is therefore not safe**: the corpus-tested subset is not
representative of all c=3 instances.

This is structurally analogous to HANDOFF.md §6i's non-degeneracy
filter: a clean conditional theorem can survive on a corpus subset
yet fail on the broader engineering-target family. The C-v2
conjecture in any of its tested forms cannot be rescued by gating
on `c ≥ 3` alone.
