# C-v2 — alternative formulations tried

Date: 2026-05-26. HANDOFF_C2 §5.

All alternatives are implemented in `radical_weight.bb_radical_bound_alt`.

## Summary

| formulation | gross bound | bb_108 bound | corpus violations |
|---|:---:|:---:|:---:|
| primary | 12 ✓ | 12 ✗ | 3 319 / 3 894 |
| any-orbit | 12 ✓ | 12 ✗ | 3 319 |
| multi-mu | 6 (loose) | 12 ✗ | 3 133 |
| sum | 24 ✗ (gross) | — | (not tested; gross-violating) |
| geometric | 12 ✓ | 12 ✗ | 3 614 |

**Every alternative is falsified.** Either on gross itself (sum),
on bb_108_8_10 (primary, any-orbit, multi-mu, geometric), or on
the broader corpus.

## Per-alternative analysis

### Alt-A: any-orbit min (not just joint vanishing)

`bound = ⌈(1/c) · min_O min(w_1(A,O), w_1(B,O))⌉` over all orbits
where both w_1 are finite.

On the corpus, this is **identical to primary** because for `μ = 1`
in semisimple G or finite `w_1(A, O)` in non-semisimple G, the
finiteness condition is equivalent to `μ_O(A) > 0` (the standard
vanishing condition). The "any-orbit" relaxation does not change
behavior because the C-v1 implementation already returns `∞` when
the polynomial doesn't vanish on that orbit.

### Alt-B: multi-mu

`bound = ⌈(1/c) · min_{O, μ ≤ min(μ_O(A), μ_O(B))} min(w_μ(A,O), w_μ(B,O)) / μ⌉`

Intuition: deeper radical levels see "more structure" but the divisor
`μ` accounts for it. The minimum across `μ` should give a *tighter*
bound when some `μ > 1` level produces a smaller ratio.

On gross: at `μ = 1`, ratio = 36/1 = 36; at `μ = 2`, ratio = 36/2 = 18.
After (1/c) division: 18/3 = 6. So multi-mu gives **6, loose by 6**
on gross.

This makes multi-mu **less useful**, not more — it allows deeper-μ
ratios that are smaller than `w_1`, weakening the bound.

### Alt-C: sum

`bound = ⌈(1/c) · Σ_O ...⌉` over joint vanishing orbits.

On gross: 2 jointly vanishing orbits × 36 = 72. (1/3) · 72 = 24. d=12.
**Bound 24 > 12 — violates gross**, as HANDOFF_C2 §5 Alt-C predicted.
Dead-on-arrival; corpus testing skipped.

### Alt-D: geometric mean

`bound = ⌈(1/c) · √(min_O w_1(A, O) · w_1(B, O))⌉` over joint vanishing.

For each orbit, `√(36 · 36) = 36`. Min = 36. (1/3) · 36 = 12. **Tight
on gross but violates 3 614 corpus rows** (slightly more than
primary, since the geometric mean equals min when w_A = w_B but exceeds
min otherwise).

### Alt-E: reciprocal-form

Algebraically equivalent to primary. Same numerical result.

## The "what if we restrict to c ≥ 3" gating

The corpus sweep shows 0 violations on c ≥ 3 (74 rows). Bravyi's
bb_108_8_10 also has c = 3 and **violates with bound 12 > d = 10**.

So the c ≥ 3 gating is *necessary* but NOT *sufficient*. Some
deeper structural condition is needed.

Empirically, bb_108_8_10 differs from the 4 satisfied Bravyi
instances in having `G_odd` non-elementary-abelian (Z_9 × Z_3 rather
than Z_3 × Z_3 or Z_15 × Z_3). Gating on "G_odd elementary abelian"
would exclude bb_108_8_10 and produce a clean conditional theorem
on the (Z_3 × Z_3 × G_2) family — but that family is a sliver of BB
codes.

**Not pursued in C-v2.** Per HANDOFF_C2's "don't immediately shelve"
guidance, the alternatives have been exhausted. The remaining
hypothesis (gate by elementary-abelian G_odd) is a substantively
different conjecture and is documented but not tested.

## Verdict

All alternatives falsified. The C-v2 program in any straightforward
"weight-aware LP-style" form does not give a tight-on-all-Bravyi
bound. See [Cv2_corpus_sweep.md](Cv2_corpus_sweep.md) and
[Cv2_bravyi_table.md](Cv2_bravyi_table.md).
