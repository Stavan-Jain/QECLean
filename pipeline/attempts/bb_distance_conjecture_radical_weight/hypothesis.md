# Hypothesis: radical-weight + LP-denominator bound

## Statement

For a BB code `BB(G, A, B)`:

```
d_X(BB(G, A, B))  ≥  ⌈(1/c) · min_O min(w_1(A, O), w_1(B, O))⌉
```

where:

- `w_1(A, O)` is the C-v1 invariant:
  `min |f|_H` over `f ∈ R_O ⊂ F_2[G]` with `f · A = 0` (the
  per-orbit isotypic kernel of multiplication by A).
- `c := [G_a : G_a ∩ G_b]`, with `G_a = ⟨supp(A)⟩` and
  `G_b = ⟨supp(B)⟩`.
- `min_O` is over Frobenius orbits `O ⊂ Ĝ_odd` where both A and B
  vanish (i.e., both `μ_O(A) > 0` and `μ_O(B) > 0`).
- If no such orbit exists, the bound is vacuous (taken to be 0).

## Where this came from

C-v1 produced the gross numerical table

| Orbit | μ_O | w_1 |
|---|---|---|
| 3 vanishing orbits (each) | 2 | **36** |
| 2 non-vanishing | 0 | ∞ |

with c = 3 for gross. The number-theoretic coincidence `36/3 = 12 =
d_gross` motivated HANDOFF_C2's primary conjecture as a "natural"
LP-Statement-12 with w_1 in place of `d_A^⊥`.

The conjecture is plausibly novel because:

- LP Statement 12 uses `d_A^⊥` (classical dual distance), not w_1.
- w_1 (C-v1) was defined to capture non-semisimple structure that
  the LP-classical numerator ignores.
- The combination "non-semisimple-aware numerator with LP-style
  denominator" is not in the literature ([Cv2_literature.md](../../experiments/bb_lab/notes/Cv2_literature.md)).

## Alternative formulations also tested (HANDOFF_C2 §5)

| name | RHS |
|---|---|
| primary | `⌈(1/c) · min_O min(w_1(A,O), w_1(B,O))⌉` (joint vanishing) |
| any-orbit | `⌈(1/c) · min_O min(w_1(A,O), w_1(B,O))⌉` (no joint requirement) |
| multi-mu | `⌈(1/c) · min_{O, μ ≤ min(μ_O(A), μ_O(B))} min(w_μ(A,O), w_μ(B,O)) / μ⌉` |
| sum | `⌈(1/c) · Σ_{O joint vanishing} min(w_1(A,O), w_1(B,O))⌉` |
| geometric | `⌈(1/c) · √(min_O w_1(A,O) · w_1(B,O))⌉` |

## Falsification target

HANDOFF_C2 §C-v2.3 corpus sweep: any single corpus violation
falsifies; HANDOFF_C2 §C-v2.4 Bravyi table check: bound > d_published
for any of the 5 Bravyi reference instances falsifies.

## Survival domain (if narrower form is to be pursued)

The proper-per-orbit-isotypic constraint plus filtration depth is a
real mathematical refinement. If the conjecture fails in its primary
shape, the "interesting" subset of BB codes where it might survive is:

- **G_odd elementary abelian** AND **c ≥ 3** AND **orthogonally-placed
  supports** (`supp(A)` and `supp(B)` live in disjoint axis
  subgroups).

This narrower form was NOT tested in this round.
