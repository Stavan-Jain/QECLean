# Evidence — Tier-3 round 2 on the conditional Jacobson conjecture

This document collects the empirical evidence from corpus and
Bravyi-table evaluations.

---

## 1. Corpus headline (T3R2.2)

Source: `experiments/bb_lab/data/bb_instances.duckdb`, filtered to
rows with `d_exact IS NOT NULL`.

| metric | value |
|---|---:|
| Total rows with `d_exact` | 3894 |
| Non-degenerate (strict) | **1937** (49.7%) |
| Degenerate | 1957 (50.3%) |
| Non-deg violations of real Jacobson bound | **43** (2.2%) |
| Non-deg violations of proxy `d ≥ k/2` | 43 (identical set) |
| Degenerate violations of real Jacobson bound | 364 (18.6%) |

The proxy and real bound coincide on the non-degenerate subset
(both give 43 violations from the same rows). This is because on the
non-degenerate subset, the real bound's per-orbit `min(μ_A, μ_B)`
contributions sum to a value comparable to the joint kernel
dimension, which in turn equals `k/2` (Bravyi Lemma 1).

### Per-group breakdown (non-degenerate only)

| group | rows | violations | tight | loose | violation rate |
|---|---:|---:|---:|---:|---:|
| Z3xZ3 | 6 | 0 | 3 | 3 | 0.0% |
| Z3xZ4 | 43 | 0 | 13 | 30 | 0.0% |
| Z3xZ5 | 92 | 8 | 20 | 64 | 8.7% |
| Z3xZ6 | 56 | 0 | 8 | 48 | 0.0% |
| Z5xZ6 | 1604 | 28 | 170 | 1406 | 1.7% |
| Z6xZ6 | 136 | 7 | 28 | 101 | 5.1% |

### Slack distribution (non-degenerate only)

Slack = `d_exact - jacobson_bound`. Negative = violation.

| slack | count |
|---:|---:|
| -2 | 43 |
| 0 | 242 |
| 2 | 486 |
| 4 | 500 |
| 6 | 666 |

**Every violator has slack exactly -2**: a uniform under-shoot.
No slack ≤ -3 cases exist.

---

## 2. Residual characterization (T3R2.3)

All 43 non-degenerate violators have:

* `A_weight = B_weight = 3`
* `d_exact = 2, bound = 4, slack = -2, k = 8`
* Exactly one joint-vanishing orbit (size 4 or 2 depending on `G`)
  contributing the full 4 to the bound.

Distinct `A` polynomials accounting for all 43:

| `A` | group | count |
|---|---|---:|
| `1 + x*y + x^2` | Z5xZ6 | 12 |
| `y^3 + x*y + x^2` | Z5xZ6 | 16 |
| `y^2 + y^3 + x` | Z3xZ5 | 8 |
| `1 + y + x` | Z6xZ6 | 7 |

### The single structural property

**All 43 violators have a weight-≤2 syzygy in `F_2[G]²`**:
there exists `(α, β)` with total weight ≤ 2 and `αA + βB = 0`.

* 41/43: `(α, β) = (1, x^{-h})` for some `h ∈ G`; equivalently,
  `B = x^h · A` (a monomial translate / unit multiple of `A`).
* 2/43: `(α, β) = (0, 1 + x)`; here `B = y^c · (1 + x + x^2)` and
  `(1 + x + x^2)(1 + x) = 1 + x^3 = 0` in `F_2[Z_3]`.

The first 5 violators (sorted by code_id) and their certifying `(α, β)`:

| code_id | A | B | (α, β) |
|---|---|---|---|
| bb_enum_Z3xZ5_4e4eeaa5 | `y^2 + y^3 + x` | `y^2 + y^3 + x` | `(1, 1)` — `B = A` exactly |
| bb_enum_Z3xZ5_e23f912c | `y^2 + y^3 + x` | `y^3 + y^4 + x*y` | `(1, y^{-1})` — `B = y · A` |
| bb_enum_Z3xZ5_e07a228f | `y^2 + y^3 + x` | `y^2 + x*y^2 + x^2*y^2` | `(0, 1 + x)` — zero-divisor |
| bb_enum_Z3xZ5_4c4ad087 | `y^2 + y^3 + x` | `y^3 + x^2 + x^2*y` | `(1, x^{-2} y^{-1})` — `B = x^2 y · A` |
| bb_enum_Z3xZ5_d199c481 | `y^2 + y^3 + x` | `1 + y^4 + x*y^2` | `(1, ...)` — monomial translate |

---

## 3. Bravyi-table evaluation (T3R2.4)

All 5 Bravyi instances are **degenerate** under the strict definition:

| code_id | group | A | B | [G:⟨supp A⟩] | [G:⟨supp B⟩] |
|---|---|---|---|---:|---:|
| bb_72_12_6 | Z6xZ6 | `x^3 + y + y^2` | `y^3 + x + x^2` | 3 | 3 |
| bb_90_8_10 | Z15xZ3 | `x^9 + y + y^2` | `1 + x^2 + x^7` | 3 | 3 |
| bb_108_8_10 | Z9xZ6 | `x^3 + y + y^2` | `y^3 + x + x^2` | 3 | 3 |
| gross | Z12xZ6 | `x^3 + y + y^2` | `y^3 + x + x^2` | 3 | 3 |
| bb_288_12_18 | Z12xZ12 | `x^3 + y^2 + y^7` | `y^3 + x + x^2` | 3 | 3 |

Bravyi codes therefore are **out of scope** for the conditional
conjecture (strict definition). The conjecture neither holds nor
fails on them — it makes no claim.

For reference, the unconditional bound's values on the Bravyi table
(matches Tier-3 round-1's report):

| code_id | bound | d | slack |
|---|---:|---:|---:|
| bb_72_12_6 | 8 | 6 | **-2 (unconditional violation)** |
| bb_90_8_10 | 4 | 10 | +6 |
| bb_108_8_10 | 4 | 10 | +6 |
| gross | 8 | 12 | +4 |
| bb_288_12_18 | 16 | 18 | +2 |

Under the alternative **joint** non-degeneracy condition
`⟨supp(A) ∪ supp(B)⟩ = G`, all 5 Bravyi instances are non-degenerate
(see T3R2.4 §3). But bb_72_12_6 still violates with slack=-2, so the
joint-definition conditional conjecture is falsified.

---

## 4. Tightening filter (T3R2.5)

Candidate filter: "no weight-≤2 syzygy in `F_2[G]²` of `(A, B)`",
i.e., no `(α, β)` with `αA + βB = 0` and `|α| + |β| ≤ 2`.

Applied to the 1937 non-degenerate corpus rows:

| | rows in scope | violations of real Jacobson |
|---|---:|---:|
| non-deg only | 1937 | 43 |
| non-deg AND tightening | **1796** | **0** |

The filter eliminates exactly the 141 non-degenerate `d_exact = 2`
codes (43 violators + 98 tight non-violators) and keeps all
`d_exact ≥ 4` codes.

But: the tightening filter does NOT catch `bb_72_12_6` (when it's
brought into scope via the joint non-degeneracy definition):

| code_id | passes tightening | bound | d | verdict |
|---|:---:|---:|---:|---|
| bb_72_12_6 | yes | 8 | 6 | **still violates** |

The bb_72_12_6 failure mode is different: it has
`min_wt_ker_A = min_wt_ker_B = 6`, no mixed-monomial syzygy, but
the orbit-wise sum `Σ|O|·min(μ_A,μ_B)` over-counts the actual
`dim(ker M_A ∩ ker M_B) = 6`. The conjecture's RHS is wrong even
as a dimension count in the deep-radical case.

---

## 5. What does this tell us?

* On the strict-non-deg corpus, the conditional bound has a
  *structurally clean* characterization of its violators (weight-2
  syzygy) and a *cleanly empirically valid* tightened version
  ("no weight-2 syzygy" → zero violations on 1796 rows).

* The strict-non-deg condition **excludes the Bravyi target
  family**. So the clean-on-corpus conjecture has no path to
  helping the engineering goal (deriving a tight bound on gross).

* Relaxing to the joint definition includes Bravyi but reintroduces
  the bb_72_12_6 violation via a fundamentally different
  mechanism that the tightening filter cannot capture.

The conditional conjecture is therefore **incomplete in coverage**:
the version that's clean on the corpus has an empty intersection
with the Bravyi target.

---

## 6. Files

* `experiments/bb_lab/notes/T3R2.2_nondegenerate_eval.md`
* `experiments/bb_lab/notes/T3R2.3_residual_characterization.md`
* `experiments/bb_lab/notes/T3R2.4_bravyi_table.md`
* `experiments/bb_lab/notes/T3R2.5_tightening_filter.md`
* `experiments/bb_lab/data/t3r2_nondegenerate_eval.parquet` (gitignored)
* `experiments/bb_lab/scripts/tier3_round2_eval.py`
* `experiments/bb_lab/src/bb_lab/degeneracy.py`
* `experiments/bb_lab/tests/test_degeneracy.py`
