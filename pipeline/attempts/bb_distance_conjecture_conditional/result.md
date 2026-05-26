# Result — Tier-3 round 2 verdict on the conditional Jacobson-radical BB distance bound

**Verdict: SURVIVES-WITH-CLEAN-RESIDUAL ∧ DOMAIN-EXCLUDES-BRAVYI.**

(Of the five spec-defined outcomes, this maps closest to
"survives-with-small-clean-residual" on the corpus, but it does NOT
extend to cover Bravyi — a strategically fatal qualifier that the
spec's taxonomy doesn't quite capture. Honest answer: **partial
progress, do not advance to Tier 4.**)

---

## Headline numbers

* Total corpus rows with `d_exact`: **3 894**.
* Non-degenerate rows (strict: ⟨supp(A)⟩ = G AND ⟨supp(B)⟩ = G):
  **1 937 (49.7%)**.
* Real-Jacobson-bound violations on non-degenerate subset:
  **43 (2.2%)** — identical to the proxy `d ≥ k/2` violation count
  (the bound and the proxy coincide on this subset).
* Slack distribution: all 43 violations have slack exactly -2; no
  slack ≤ -3 cases. Uniformly weight-2-logical failures.
* Tightening filter "no weight-≤2 syzygy in F_2[G]²" eliminates ALL
  43 violators → **0 / 1 796 violations** on the tightened domain.

## Bravyi-table table (the strategic finding)

Under the **strict** non-degeneracy definition (the spec's):

| code_id | non-deg? | bound | actual d | verdict |
|---|:---:|---:|---:|---|
| bb_72_12_6   | **no** | 8 | 6 | out of scope (unconditional bound violated) |
| bb_90_8_10   | **no** | 4 | 10 | out of scope (loose) |
| bb_108_8_10  | **no** | 4 | 10 | out of scope (loose) |
| gross        | **no** | 8 | 12 | out of scope (loose; gap = 4 confirms round 1) |
| bb_288_12_18 | **no** | 16 | 18 | out of scope (loose) |

**ALL 5 Bravyi instances are degenerate.** They have
`[G : ⟨supp(A)⟩] = 3` because every Bravyi polynomial uses
`x^a + y + y²` with `gcd(a, ℓ) = 3`, generating only a subgroup of
index 3 along the x-axis.

The unconditional bound on `gross` is 8 (not 12 as the round-1 spec
seed-claimed); the gap of 4 is reconfirmed. The bound on bb_72_12_6
is 8 (violating its actual d = 6) — same as round 1.

## Most informative residual cases

Two violators (chosen from the 43 to span the structural types):

1. **bb_enum_Z3xZ5_4e4eeaa5** on Z_3 × Z_5:
   * `A = y² + y³ + x`, `B = y² + y³ + x` (i.e., A = B exactly).
   * `n = 30, k = 8, d = 2, bound = 4, slack = -2`.
   * Weight-2 syzygy: `(α, β) = (1, 1)`, since `A · 1 + B · 1 = 2A = 0`
     in F_2. This is the simplest "mixed weight-2" syzygy.
   * The corresponding `(1, 1)` codeword in `F_2^{2n}` is a weight-2
     X-logical (verified by SAT giving d = 2).
2. **bb_enum_Z3xZ5_e07a228f** on Z_3 × Z_5:
   * `A = y² + y³ + x`, `B = y² + x·y² + x²·y²`.
   * `n = 30, k = 8, d = 2, bound = 4, slack = -2`.
   * Weight-2 syzygy: `(α, β) = (0, 1 + x)`, since `B = y² · (1 + x + x²)`
     and `(1 + x + x²)(1 + x) = 1 + x³ = 0` in F_2[Z_3].
   * The corresponding `(0, 1+x)` codeword is a weight-2 X-logical
     coming purely from the B-block via the `(1+x+x²)` zero-divisor.

Together, these two examples show that the 43 violators split into
"mixed weight-2" (41 cases) and "single-block weight-2 zero-divisor"
(2 cases), and both share a common abstraction: there is a weight-2
element of `ker(H_Z) \ rowspan(H_X)`.

## Tightening assessment

A clean tightener exists for the corpus subset (T3R2.5):

> **TIGHTENING** :≡ no weight-≤2 element `(α, β) ∈ F_2[G]²` with
> `αA + βB = 0`.

On the strict-non-degenerate subset:

| filter | rows | violations |
|---|---:|---:|
| non-deg only | 1937 | 43 |
| non-deg ∧ TIGHTENING | **1796** | **0** |

But the tightening **does not extend to cover bb_72_12_6** under the
joint-non-degeneracy alternative: bb_72_12_6 has
`min_wt_ker_A = min_wt_ker_B = 6` and `B ≠ unit · A`, so the
tightening filter accepts it; yet the bound (8) still exceeds d (6).
The bb_72_12_6 violation is a *deep-radical over-count* of the
orbit sum Σ|O|·min(μ_A, μ_B) over the actual joint kernel dim
(8 vs. 6) — a fundamentally different failure mode that the
weight-witness tightening cannot capture.

So the tightener is clean on the spec's domain but cannot be
extended to include Bravyi.

## Recommendation

**Declare partial-progress-and-shelve. Do not advance to Tier 4
(Lean).**

Reasoning:

1. The conditional conjecture has a strategically empty intersection
   with the Bravyi target codes under the strict non-degeneracy
   definition the spec uses. A Lean theorem about a domain that
   excludes gross / bb_72_12_6 / etc. does not help the program's
   goal of bounding d on engineered BB codes.
2. The looser joint-non-degeneracy alternative includes Bravyi, but
   bb_72_12_6 outright violates under it. The tightening filter
   doesn't help.
3. The structural finding "all non-degenerate violators of the
   Jacobson bound on the corpus admit a weight-2 syzygy" IS a
   genuine algebraic observation worth recording in the research
   log. It supports the §6h rule: the bound's failure mode is
   exactly a *weight-2 witness*, and the only clean tightener is a
   weight-2-witness filter. Future Tier-2 candidates should aim
   directly at weight-bounded structural features, not at the
   dimension-style `Σ|O|·μ_O` sum.

## What survives this round (for future Tier-2 work)

* The classifier `bb_lab.degeneracy.{supp_generates_G,
  support_subgroup_index, is_non_degenerate}` is a clean utility
  that can label any future corpus rows or generators by
  degeneracy. Cheap and well-tested.
* The empirical observation that 49.7% of the corpus is
  non-degenerate (a meaningful partition) is a useful structural
  feature for future Tier-2 conjectures targeting weight-related
  RHS.
* The realization that Bravyi codes are universally **degenerate**
  under the strict definition is itself non-obvious and useful: any
  future conjecture that wants to cover Bravyi must either (a) use
  the joint definition, (b) drop the non-degeneracy assumption
  entirely, or (c) define a stronger algebraic condition that
  Bravyi's polynomials satisfy (e.g., "support generates G after
  one rotation by a unit" — an avenue not explored here).

## Implementation status

* `experiments/bb_lab/src/bb_lab/degeneracy.py` — new module, 3
  public functions + 1 internal helper. ~120 lines.
* `experiments/bb_lab/tests/test_degeneracy.py` — 10 unit tests
  pinning the classifier on gross (degenerate, index 3), Z3xZ5
  single-axis polys, trivial poly, full-coverage polys, Lagrange
  consistency, etc.
* `experiments/bb_lab/scripts/tier3_round2_eval.py` — sweeps the
  corpus, computes `is_non_degenerate` + `jacobson_radical_bound`,
  writes parquet + summary md.
* `experiments/bb_lab/data/t3r2_nondegenerate_eval.parquet` — raw
  evaluation (gitignored). 3894 rows.
* `experiments/bb_lab/notes/T3R2.{2,3,4,5}_*.md` — full
  documentation of each task.
* No modifications to `algebraic_features.py`, `corpus.py`, or any
  other existing source file (per hard constraints).
* `uv run pytest -m "not slow" -q` → 163 passed, 2 skipped (up from
  153 at session start; +10 from `test_degeneracy.py`).
