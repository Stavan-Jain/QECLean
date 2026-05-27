# Result — Family A v2 candidate #1 (y'-spread) FALSIFIED-AS-PREDICTOR

**Verdict: FALSIFIED-AS-PREDICTOR per HANDOFF_R2.md §6 (Family A)**.

The first concrete Family A v2 candidate — using `a_O` y'-spread as a
tightness-discriminator for the C-v3 bound — fails to extend beyond the
4-instance seed observation that motivated it.

## 1. Strategic context

[HANDOFF_R2.md](../../../experiments/bb_lab/HANDOFF_R2.md) §6 names
Family A (radical-aware weight invariants) as the §6k-surviving open
direction. Round 1's C-v1 / C-v2 / C-v3 series produced `w_1`, a
weight invariant on the Jacobson-radical Loewy filtration of `F_2[G]`
— but `w_1` is invariant under R_O-unit multiplication, which is
exactly the structural blind spot that killed C-v3 (see
[`T3_CV3_H_UNIT2_attempt.md`](../../../experiments/bb_lab/notes/T3_CV3_H_UNIT2_attempt.md)
case (4,5) on Z_12 × Z_12).

The Family A v2 task: find a refinement of `w_1` that **distinguishes
R_O-unit equivalents**, plugged into the C-v3 bound shape, such that
the refined bound is tight on gross and survives Tier 3.

## 2. The candidate

`T3_CV3_H_UNIT2_attempt.md` lines 65-73 documents an empirical
observation on the 4 in-domain C-v3.1 cases on Z_12 × Z_12:

> **Empirical correlation: tight cases have 3 nonzero y'-coefficients
> in `a_O`; violator cases have 1-2.**

This motivates a candidate predicate:

```
spread_A(O) := # nonzero pure-y' Loewy-basis terms in proj_{R_O}(A)
            = #{ j > 0 : coefficient at Loewy index (0, j) is nonzero
                          in (a_O expressed in the (x+1)^i (y+1)^j basis) }
```

Candidate v2 hypothesis: **C-v3's bound is tight on rows where
`min_{O ∈ JV(A,B)} min(spread_A(O), spread_B(O)) ≥ 3`**, and
overshoots when this min is < 3.

## 3. Implementation

[`scripts/family_a_v2_seed_check.py`](../../../experiments/bb_lab/scripts/family_a_v2_seed_check.py)
implements `a_O_y_spread(A, G, orbit_rep)`:

1. Call `_project_poly_to_R_O` ([`algebraic_features.py:543`](../../../experiments/bb_lab/src/bb_lab/algebraic_features.py)) for the standard-basis `a_O ∈ R_O = F_{2^|O|}[G_2]`.
2. Change basis from monomial `x^a y^b` to Loewy `(x+1)^i (y+1)^j` via
   Pascal's-triangle-mod-2 (Lucas's theorem: `C(n,k) mod 2 = 1 iff
   (k & n) == k`).
3. Count entries with Loewy index `(0, j)` for `j > 0` and nonzero
   F_{2^|O|}-coefficient.

The basis change is essential: the H_UNIT² note's example `a_O = x' +
x'² + x'³ + ω²·y'` for case (4, 5) is the **Loewy expansion** of
`x^3 + ω + ω²·y` (since `x^3 = (1+x')^3 = 1 + x' + x'² + x'³` mod 2,
and `1 + ω + ω² = 0` over F_4 cancels the constant). My first pass
worked in the monomial basis and produced spread = 2 (wrong) for the
(1,11) case where the Loewy answer is 3 (right).

## 4. Step 2 — verification against the 4-case seed

`uv run python scripts/family_a_v2_seed_check.py` reproduces the
literature note exactly:

| case (A exponents on Z_12 × Z_12) | predicted spread | computed | verdict |
|---|---:|---:|---|
| (4, 5)   | 1 | **1** ✓ | VIOLATION (gap = -6) |
| (1, 2)   C1 | 2 | **2** ✓ | VIOLATION (gap = -6) |
| (1, 11)  | 3 | **3** ✓ | tight |
| (2, 7)   bb_288-sister | 3 | **3** ✓ | tight (expected) |

Seed-fit confirmed. Proceed to broader corpus test.

## 5. Step 3 — corpus test (FALSIFICATION)

`scripts/family_a_v2_corpus_check.py` evaluates spread across the
3,724 SAT-verified rows in non-trivial-G_2 groups (`Z6xZ6`, `Z9xZ6`,
`Z12xZ6`, `Z3xZ6`, `Z4xZ6`, `Z5xZ6` — the corpus subset where the
Loewy `y'` direction is non-trivial).

For each row, finds joint-vanishing orbits via
`algebraic_features.jacobson_radical_depth(·, orbit, G) > 0` and takes
the min spread over `{spread_A(O), spread_B(O) : O joint-vanishing}`.
Computes the C-v3 bound via `radical_weight.bb_radical_bound` and the
gap `d_exact - bound`.

**Result**:

| min_spread | rows | tight | loose (gap > 0) | violation (gap < 0) | tight rate |
|---:|---:|---:|---:|---:|---:|
| 0 | 1,691 | 92 | 328 | 1,271 | 5.4% |
| 1 | 2,033 | 99 | 34 | 1,900 | 4.9% |

**The spread is non-discriminating between tight and violator
buckets.** Across the corpus, "spread = 0" and "spread = 1" buckets
have the same tight rate (5.4% vs 4.9%), the same massive C-v3
violation count, and qualitatively the same gap distributions.

The Z_12 × Z_6 rows specifically (the only ones with Z_4-axis G_2 in
the SAT-verified set) include examples like:

- `Z12xZ6 d=8 b=8 gap=+0` (tight) with spread=0
- `Z12xZ6 d=8 b=24 gap=-16` (massive violation) with spread=0
- `Z12xZ6 d=4 b=4 gap=+0` (tight) with spread=1
- `Z12xZ6 d=6 b=3 gap=+3` (loose) with spread=1

— confirming that spread alone doesn't predict tightness even on the
Z_4-axis subset.

## 6. Why the seed didn't extend

Three honest readings:

**a. The 4-case seed was a small-sample coincidence.** Four data
points distinguish far less than they appear to. Without a derived
theoretical reason for the "spread ≥ 3 → tight" rule, the
observation is on shaky empirical ground from the start.

**b. The corpus is structurally limited where the test would matter.**
The H_UNIT² seed lives on Z_12 × Z_12 (G_2 = Z_4 × Z_4) where spread
can range over `{0, 1, 2, 3}`. The corpus has zero SAT-verified rows
on Z_12 × Z_12 (n=288 is in the "days, not hours" SAT zone) and only
18 rows on Z_12 × Z_6 (G_2 = Z_4 × Z_2, max spread = 1). The natural
test domain for the seed is empirically unreachable in the current
SAT-budget regime.

**c. Required structural restrictions aren't isolated.** The H_UNIT²
note (lines 80-96) explicitly listed three candidate fixes; this is
the most concrete (a_O y'-support cardinality), and the note already
flagged it as "suggestive empirically but unproven" and "may reduce
to a 'spread' condition on supp(A) in G". The spread-on-G hypothesis
might be the right one — but it's a different invariant.

## 7. Implication for HANDOFF_R2 §6 (Family A)

Family A's first concrete v2 candidate is shelved. The negative
result reinforces a structural observation: **`w_1` and its natural
refinements appear blind to the BB-code-distance variation among
R_O-unit-equivalent polynomials.** This is the same wall the H_UNIT²
attempt hit, now with broader empirical scope.

**Remaining within-Family-A directions** (per HANDOFF_R2 §6):
1. **Different a_O structural feature** — e.g. cross-axis x'·y' joint
   support cardinality, or weight enumerator of `a_O` viewed as an
   element of `R_O` as a code.
2. **Sharper c (joint-support-and-G_2 index)** — also flagged in
   H_UNIT² note line 94 as "no clean form proposed yet".
3. **Heroic Z_12 × Z_12 SAT push** — fills the natural test domain,
   ~days of compute. Could rescue Reading B from §5 but at high cost.

None are cheap. Family A is **expensive open theory**, consistent
with HANDOFF_R2.md §10 risk callout: "Family A might be unsolvable
in 2 days. It's open research."

## 8. What survives as contribution

- `a_O_y_spread` is a *computable* structural feature of polynomial
  pairs that wasn't built before. Documented in `scripts/family_a_v2_*`
  and available for any future Family A candidate that wants it.
- The Loewy-basis conversion (`_to_loewy_basis` in the seed-check
  script) is similarly reusable.
- The 4-case spread values now have a programmatic reproduction
  (matching the literature note), removing dependence on the manual
  table in `T3_CV3_H_UNIT2_attempt.md`.

## 9. Recommended next move

**Pivot to Family B (lifted-product algebraic)** per HANDOFF_R2.md §6.
Family B has actual published literature to mine (Panteleev–Kalachev
2022, Hastings–Haah–O'Donnell 2020, Leverrier–Zémor 2022 quantum
Tanner) and is less obstruction-bound than Family A. The Family A v2
spread candidate is the second "natural refinement" of `w_1` to be
falsified (after H_UNIT²), and the corpus data confirms it. The §6k
surviving direction may genuinely require new mathematics that exceeds
this round's budget.

## 10. Reproducibility

```bash
cd experiments/bb_lab

# Step 2 — verify against the 4-case seed.
uv run python scripts/family_a_v2_seed_check.py

# Step 3 — corpus check (~few minutes against the SAT-verified subset).
uv run python scripts/family_a_v2_corpus_check.py
```

Expected: Step 2 reproduces the literature note's 4 values exactly.
Step 3 reports the bucket counts in §5 above.
