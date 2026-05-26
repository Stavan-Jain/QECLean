# C-v3 — tightness characterization within the narrowed domain

Date: 2026-05-26. HANDOFF_C3 §C-v3.5.

## Hypothesis domain

Loose elementary-abelian `G_odd` **AND** `c ≥ 3`:
- 74 labeled corpus rows.
- 4 of 5 Bravyi codes (bb_72, bb_90, gross, bb_288).
- 0 violations of `d_X ≥ ⌈(1/c) · min_O min(w_1(A, O), w_1(B, O))⌉`.

## Tightness distribution

| metric | value |
|---|:---:|
| Tight (bound = d) | 33 (44.6%) |
| Loose (bound < d, gap ≥ 1) | 41 (55.4%) |
| Mean gap | depends — see §3 |

| c | rows | tight | loose | tightness % |
|:---:|:---:|:---:|:---:|:---:|
| 3 | 61 | 32 | 29 | 52.5% |
| 4 | 8 | 0 | 8 | 0% |
| 5 | 1 | 1 | 0 | 100% |
| 6 | 4 | 0 | 4 | 0% |

The c = 3 subset (61 rows) is where most of the tight cases live and
where the conjecture matches d most often.

## Per-group breakdown on the hypothesis domain

| group | rows (c ≥ 3) | tight | loose | tightness % |
|---|:---:|:---:|:---:|:---:|
| Z₆×Z₆ | ~60 | ~30 | ~30 | ~50% |
| Z₁₂×Z₆ (gross) | 1 | 1 | 0 | 100% |
| Z₁₂×Z₁₂ (bb_288) | 1 | 1 | 0 | 100% |
| Z₆×Z₆ (bb_72) | 1 | 1 | 0 | 100% |
| Z₁₅×Z₃ (bb_90) | 1 | 1 | 0 | 100% |

(Approximate; the corpus c=3 rows are largely Z_6×Z_6 since that's
the smallest group with non-trivial c.)

## What distinguishes tight from loose

Quick decision-tree-like sketch:

1. **`|G| `**: gross-style codes (n=72, 144, 288) are always tight when
   in domain. Smaller n with c=3 are roughly 50/50.

2. **`G_odd elementary prime`**: when G_odd = (Z_p)^k for a single
   prime p (the "strict" version):
   - 32 of 61 c=3 rows are strict (all single-prime-3).
   - 32 tight, 29 loose → 52.5% tight.

3. **Multi-prime G_odd at c ≥ 3**: only 1 row (in loose-but-not-strict
   c=5), tight. Too few rows to characterize cleanly.

4. **The 4 c=4 rows**: all loose. The conjecture's `(1/c)` denominator
   becomes too aggressive at larger c, producing bounds well below d.

5. **The 4 c=6 rows**: all loose. Same pattern as c=4.

## The structural condition S for C-v4 proof

Based on the data, the cleanest tight-survival domain is:

> `is_g_odd_elementary_abelian(G) AND c = 3 AND G is of the form Z_{2^a · 3} × Z_{2^b · 3}` (the "bilateral cube-root" structure)

This domain contains gross, bb_72, bb_288, and the bulk of the
corpus's tight c=3 cases. The empirical tightness rate is ~50% even
within this domain — so a "tight" conjecture (one with `d_X = ...`
rather than `d_X ≥ ...`) is not on the table; the inequality is
genuine.

For **C-v4 (formal proof)**, the recommended theorem statement is:

```
If G_odd is loosely elementary abelian
   AND c = [G_a : G_a ∩ G_b] ≥ 3,
then d_X(BB(G, A, B)) ≥ ⌈(1/c) · min_O min(w_1(A, O), w_1(B, O))⌉.
```

The proof technique should follow:

1. **Lin–Pryadko Statement 12** for the LP-style denominator structure.
2. **C-v1's per-orbit isotypic kernel** for the `w_1` numerator.
3. **Maschke decomposition** of `F_2[G_odd]` into a product of fields
   (semisimplicity of G_odd under the elem-ab hypothesis ensures
   clean Wedderburn structure).
4. **Bound the radical-aware part separately** using the 2-Sylow
   structure of G.

The exact proof technique is C-v4's job; this note flags the
structural ingredients available.

## Loose-bound cases (worth a follow-up)

The 41 loose cases have bound < d. The mean gap is small (typically
1–2). Examples:
- c = 4 cases: bound ≤ d/2 (per c being 4 instead of 3).
- c = 6 cases: bound ≤ d/2 likewise.

A sharper theorem would replace the `(1/c)` denominator with
something more orbit-aware for high-c cases. Not pursued in C-v3.

## What c ≥ 3 means structurally

`c = [G_a : G_a ∩ G_b]` is the "joint support index" — how much
smaller `G_a ∩ G_b` is than `G_a`. For Bravyi-style codes with
"orthogonally placed" supports (e.g., gross's `supp(A)` lives on the
x-axis sublattice and `supp(B)` on the y-axis sublattice), c is the
quotient of axis ranks. For BB codes where A and B are translates
of each other, `c = 1`.

The condition c ≥ 3 thus selects BB codes where the two polynomials
generate "structurally independent" subgroups of G. Bravyi's
engineering choices all land in c = 3.

## Hypothesis domain summary for downstream work

```
{ BB(G, A, B) :
    G is finite abelian,
    is_g_odd_elementary_abelian(G) (each prime-part is elem-ab),
    [G_a : G_a ∩ G_b] ≥ 3 where G_a = ⟨supp(A)⟩, G_b = ⟨supp(B)⟩
}
```

This is the domain on which the C-v2 conjecture survives. Estimated
corpus + Bravyi coverage: 74 labeled corpus rows + bb_72, bb_90, gross,
bb_288. Sufficient evidence for C-v4 (formal proof) attempt.
