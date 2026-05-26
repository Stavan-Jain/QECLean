# C-v2 — tightness characterization

Date: 2026-05-26. HANDOFF_C2 §C-v2.5.

The conjecture is falsified, so this is the "what would the
structural condition `S` need to look like, if there were one"
post-mortem rather than a green-light characterization.

## 1. Tight cases (bound == d_exact)

213 corpus rows + 4 Bravyi rows.

Per-c breakdown:

| c | tight count | total | tightness rate |
|:---:|:---:|:---:|:---:|
| 1 | 97 | 3 245 | 3.0% |
| 2 | 83 | 575 | 14.4% |
| 3 | 32 | 61 | 52.5% |
| 4 | 0 | 8 | 0% |
| 5 | 1 | 1 | 100% |
| 6 | 0 | 4 | 0% |

The single c = 5 row (tightness 100%) is a small-sample artifact;
the 8 c = 4 rows are all loose. The cleanest pattern is **c = 3
gives ~50% tightness**, which is where the gross-style codes live.

Per-group breakdown of tight rows (computed from corpus sweep):

| group | total | violations | tight | loose | tightness % |
|:---|:---:|:---:|:---:|:---:|:---:|
| Z₃×Z₃ | 12 | 11 | 1 | 0 | 8.3% |
| Z₃×Z₄ | 73 | 45 | 24 | 4 | 32.9% |
| Z₃×Z₅ | 103 | 102 | 1 | 0 | 1.0% |
| Z₃×Z₆ | 166 | 145 | 2 | 19 | 1.2% |
| **Z₄×Z₆** | **106** | **10** | **69** | **27** | **65.1%** |
| Z₅×Z₆ | 2 622 | 2 399 | 57 | 166 | 2.2% |
| Z₆×Z₆ | 812 | 607 | 59 | 146 | 7.3% |

**Striking outlier**: Z₄×Z₆ has tightness rate 65.1%, dramatically
higher than any other group. This is the group with `G_2 = Z₄ × Z₂`
(same as gross) and `G_odd = Z₃`. The conjecture's "factor of c"
structure works empirically when G_2 is precisely Z₄ × Z₂ and
G_odd is one of the small cyclic odd groups.

Z_6×Z_6 (G_odd = Z_3 × Z_3, G_2 = Z_2 × Z_2) is only 7.3% tight,
suggesting that even the elementary-abelian gating + c ≥ 3 isn't
the whole story.

## 2. What distinguishes tight from loose

A decision-tree-like sketch (not run as a formal classifier — the
conjecture is falsified, so a feature-importance ranking is mostly
documentation, not a green-light condition):

- **`c ≥ 3`**: necessary for low violation rate. But not sufficient
  (bb_108 violates with c=3).
- **G_odd elementary abelian** (= product of Z_p's with distinct
  primes p): empirically present in all 4 satisfied Bravyi
  instances. Absent in bb_108_8_10 (G_odd = Z_9 × Z_3).
- **Polynomial supports are "orthogonally placed"**: `supp(A)` and
  `supp(B)` lie in *disjoint* axis subgroups of G. Gross satisfies
  this (supp(A) is `(3,0) + 0×Z_6`; supp(B) is `0 + (0,3) + Z_12×0`).

These three together would be the structural condition `S` to gate
a *narrower* conjecture on. But the conjecture as stated is
falsified, so further work would be:

1. **State a narrower conjecture** including the elementary-abelian
   gating.
2. **Re-corpus-test** in that gated domain.
3. **If survives**: attempt formal proof (would be C-v3).

This is left for a future agent.

## 3. Loose cases (bound < d_exact)

362 corpus rows + 1 Bravyi row (bb_72_12_6 if multi-mu).

The mean gap is 0.18 in primary — most loose cases are loose by
just 1 or 2. Distribution of gaps:

- Gap 0 (tight): 213 + 4
- Gap 1: ~330 corpus rows
- Gap 2: ~30 corpus rows
- Gap ≥ 3: ~2 corpus rows

The gap distribution is tight (mostly ≤ 2), suggesting the conjecture
is "almost right" when c ≥ 2, just off by small constants. This
matches the §6h footgun intuition: w_1 is the right *order of
magnitude* for some quantity related to d, but the LP-style
denominator over-corrects.

## 4. Verdict

There is no clean conditional `S` that makes the conjecture
**survive both gross AND bb_108_8_10**. The two have the same `c`
and the same support-orthogonality, but different G_odd structure
(elementary vs. cyclic-of-prime-power), and the bound only works
in the elementary case.

Restricting the conjecture's domain to "G_odd elementary abelian +
c = 3 + orthogonal supports" excludes bb_108 — and likely most of
the corpus. Not productive without re-corpus-testing in that
narrower domain.

## 5. What about `G_odd = Z_3 × Z_3` specifically?

A even more restrictive gating: G_odd = Z_3 × Z_3 (or any single
elementary-abelian shape).

- bb_72 (Z₆×Z₆): G_odd = Z_3 × Z_3. ✓
- gross (Z₁₂×Z₆): G_odd = Z_3 × Z_3. ✓
- bb_288 (Z₁₂×Z₁₂): G_odd = Z_3 × Z_3. ✓
- bb_108 (Z₉×Z₆): G_odd = Z_9 × Z_3. ✗ (excluded)

Among the Bravyi instances, this slice has 3 of 5 — all tight.
Among the corpus, the Z_3 × Z_3 G_odd family corresponds to groups
where both ℓ and m have G_2-part `2^{a_ℓ}` × `2^{a_m}` and
G_odd-part `3 × 3` (i.e., ℓ and m are of the form `3 · 2^a`).
That's Z_6, Z_12, Z_24, ... — Z_6×Z_6 (812 rows), Z_4×Z_6 (106
rows), Z_12×Z_6 (gross only), Z_12×Z_12 (bb_288 only).

The 812 + 106 = 918 corpus rows in the Z_3 × Z_3 G_odd family
might support the narrower conjecture. **Not tested** in this round
because the C-v2 verdict is already "falsified" — testing the
narrower form would be a fresh round (C-v2.5 → C-v2-narrow).

## 6. Recommendation for follow-up

If a future agent picks this up:

- State narrower conjecture: `d_X ≥ (1/c) · min_O min(w_1(A,O), w_1(B,O))`
  for BB codes with **G_odd = Z_3 × Z_3** (or more generally, a
  specific elementary-abelian structure).
- Re-corpus-test on the Z_3 × Z_3 G_odd family.
- If survives, attempt to characterize *which* structural property
  of Z_3 × Z_3 G_odd makes the bound hold (e.g., something about
  Galois orbit sizes being exactly 2, or about the characters' field
  of definition).
- Only then attempt formal proof.

This is a substantive follow-up direction but is **out of scope for
C-v2 as stated**.
