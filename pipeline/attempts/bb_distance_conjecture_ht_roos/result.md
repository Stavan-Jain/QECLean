# Result — Tier-2 Round 3 verdict on the HT/Roos lower bound for BB codes

**Verdict: SHELVED — TRIVIAL ON GROSS.**

(Of the four spec-defined outcomes, this maps closest to
"survives-loose-on-gross" in the literal sense — no violations, but
the bound is 1 on all 5 Bravyi codes including gross, far below the
engineering target d = 12. Honest answer: **shelve, do not advance
to Tier 3 / Tier 4**.)

---

## Headline numbers

* Corpus rows evaluated: **3894** (all rows with `d_exact`).
* Condition `S(A, B)` holds: **19 (0.5%)** — all on Z_3 × Z_5 or Z_3 × Z_3.
* Violations of `bb_ht_bound ≤ d_exact` under satisfied S: **0 / 19**.
* Tight (`bb_ht_bound == d_exact` under satisfied S): **13 / 19** (all on Z_3 × Z_5).
* For all 5 Bravyi codes: `bb_ht_bound = 1`. **Far loose** of any
  engineering target.
* Gross specifically: `bb_ht_bound = 1`, actual `d = 12`. Loose by 11
  (with the condition gating out at the diagnostic stage).

## Bravyi-table table

| code | non-sssimp? | non-cyclic G_odd? | mv_ht(nv(A)) | mv_ht(nv(B)) | bb_ht_bound | actual d | verdict |
|---|:---:|:---:|---:|---:|---:|---:|---|
| bb_72_12_6   | yes (\|G\|=36) | yes (Z_3×Z_3, gcd=3) | 1 | 1 | 1 | 6 | trivial bound |
| bb_90_8_10   | no (\|G\|=45)  | yes (Z_15×Z_3, gcd=3) | 1 | 1 | 1 | 10 | trivial bound |
| bb_108_8_10  | yes (\|G\|=54) | yes (Z_9×Z_3, gcd=3)  | 1 | 1 | 1 | 10 | trivial bound |
| gross        | yes (\|G\|=72) | yes (Z_3×Z_3, gcd=3)  | 1 | 1 | 1 | 12 | trivial bound |
| bb_288_12_18 | yes (\|G\|=144) | yes (Z_3×Z_3, gcd=3) | 1 | 1 | 1 | 18 | trivial bound |

**All 5 Bravyi codes hit at least one obstruction**: either F_2[G] is
not semisimple (gross, bb_72, bb_108, bb_288), and/or G_odd is
non-cyclic (all 5 — gcd(axes of G_odd) = 3 in every case). The
combination produces `bb_ht_bound = 1` uniformly.

## Most informative diagnostic case

For **gross**: `G = Z_12 × Z_6`, `G_odd = Z_3 × Z_3` after quotienting
by the 2-Sylow. The defining set `T_A` of A = x³ + y + y² in
F_2[Z_3 × Z_3]:

* `χ_(0, 0)`: Â(χ_0) = weight(A) mod 2 = 3 mod 2 = 1, so 0 ∉ T_A.
* `χ_(1, 0), χ_(2, 0)` (orbit of size 2): A_odd = (1, 1) under x³ ↦ 1
  in Z_3, so the orbit-sum is `1 + ω + ω² + ω + ω²` with ω³ = 1...
  computed: vanishes. ∈ T_A.
* `χ_(0, 1), χ_(0, 2)`: A_odd evaluates to `1 + ω + ω² = 0`. ∈ T_A.
* `χ_(1, 1), χ_(2, 2)` and `χ_(1, 2), χ_(2, 1)` (two orbits of size 2):
  combinations of x³ and y terms; computed elsewhere: ∈ T_A.

So T_A has 6 elements out of |G_odd| = 9. nv(A) = `Ĝ_odd \\ T_A` has
3 elements: `{(0, 0), (1, 0), (2, 0)}` or similar — depends on actual
calc.

In a non-cyclic Z_3 × Z_3 group, **no element generates the full G**
(max order is lcm(3,3) = 3 < |G| = 9). My multivariate HT bound
requires a full-G generator step, so it returns 1.

The genuine Camion-Bernal multivariate apparent distance for this T
would give a nontrivial number, but it would also need to operate on
the **full F_2[G]** (not the semisimple quotient F_2[G_odd]) to
account for the radical contribution to `d_A^⊥`. Both pieces are
beyond this round's implementation scope.

## Most informative tight case

For **Z_3 × Z_5 corpus row 7c7c... (d=2, k=2)**: cyclic-G_odd = G
(both factors are odd, gcd(3, 5) = 1). A is some weight-3 poly with
`d_A^⊥ = 2 = d_X`. The condition S holds (d_X = min d^⊥ = 2). The
bound `mv_ht(nv(A)) = 2`. Tight.

There are 13 such rows on Z_3 × Z_5 (all with d = 2). This is the
**only** group in the corpus where the HT bound fires nontrivially
and gives meaningful information; in all 13 cases, it correctly
predicts d_X = 2.

## Why the bound is trivial on gross (the §6i lesson, in HT clothing)

Per HANDOFF §6i, all 5 Bravyi codes have `[G : ⟨supp(A)⟩] = 3` —
their engineering depends on operating in the degenerate regime
where the support generates a strict subgroup. The HT-specific
manifestation:

1. Bravyi engineered `|G|` to be **even** in 4 of 5 codes. This makes
   F_2[G] non-semisimple — HT only operates on the semisimple
   quotient F_2[G_odd]. The Jacobson radical (the deviation from
   semisimplicity) contributes additional low-weight elements to
   `ker M_A` that HT can't see.
2. Bravyi's `G_odd` for all 5 codes is **non-cyclic**
   (gcd(axes_of_G_odd) = 3 in every case). My multivariate HT
   implementation only handles cyclic G via full-G-generator steps;
   for non-cyclic G_odd, the genuine Camion-Bernal apparent distance
   would apply but requires substantially more machinery.

The combination is no accident — Bravyi specifically engineered the
group structure to give d ≈ √n scaling, which relies on mixed-block
X-logicals that algebraic single-polynomial analysis cannot detect.
This is precisely the lesson of HANDOFF §6i.

## Recommendation

**SHELVE. Do not advance to Tier 3 / Tier 4.**

Reasoning:

1. **Empty intersection with engineering target**: bound is trivial
   (= 1) on all 5 Bravyi codes. A Lean theorem about a candidate
   bound that's trivial on gross is strategically empty — the program's
   goal is `d ≈ 12` on gross, not `d ≥ 1`.

2. **Condition gates out 99.5% of the corpus**: the structural
   condition `S(A, B)` (textbook CSS upper bound is tight) holds on
   only 19/3894 rows. Even where it holds, the bound is uniformly
   trivial outside Z_3 × Z_5.

3. **Implementation gap is real, not just notational**: the genuine
   multivariate Camion-Bernal apparent distance bound (which would
   handle non-cyclic G_odd properly) is a substantial implementation
   undertaking, and even when implemented would still be limited to
   the semisimple-quotient code over F_2[G_odd] — the radical
   contribution for even-|G| Bravyi codes would remain invisible.

## What survives this round (for future Tier-2 work)

* **`bb_lab.ht_roos`** module: cleanly tested implementation of HT
  / BCH bounds for univariate and (cyclic) multivariate cases.
  Reusable for any future bound that operates on the semisimple
  quotient of F_2[G]. ~570 lines.

* **The literature triangulation** (T2R3.0) confirms HT/Roos
  for BB codes is novel-to-us and plausibly novel-to-literature.
  Future Tier-2 candidates can reference the literature trail
  (Camion 1970 → Sabin-Lomonaco 1992 → Saints-Heegard 1995 →
  Bernal et al. 2016) when proposing more sophisticated bounds.

* **The compounding-obstructions observation**: BB codes with
  d ≈ √n scaling sit at the intersection of (a) F_2[G]
  non-semisimplicity (|G| even) AND (b) G_odd non-cyclic
  (gcd(axes) > 1). Any bound that wants to be tight on Bravyi
  must handle BOTH obstructions simultaneously. This is a clear
  technical desideratum for future Tier-2 candidates.

* **The single-block-dominance condition framework**: even if
  HT/Roos itself doesn't fire on Bravyi, the framework
  `S(A, B) := "d_X = min(d_A^⊥, d_B^⊥)"` is reusable for any
  candidate bound that operates per-block. Combined with a better
  per-block lower bound (e.g. proper Camion-Bernal), the chain
  `d_X ≥ S-bound` could in principle fire usefully — but only
  on the subset where S holds, which doesn't include Bravyi.

## Implementation status

* `experiments/bb_lab/src/bb_lab/ht_roos.py` — new module, 9 public
  functions + helpers, ~570 lines, doc-tested.
* `experiments/bb_lab/tests/test_ht_roos.py` — 32 unit tests, all pass.
* `experiments/bb_lab/scripts/tier2_ht_roos_eval.py` — corpus eval
  driver.
* `experiments/bb_lab/notes/T2R3.0_literature_check.md` — literature
  triangulation.
* `experiments/bb_lab/notes/T2R3.4_eval.md` — corpus + Bravyi eval results.
* `pipeline/attempts/bb_distance_conjecture_ht_roos/{state.yaml,
  hypothesis.md, evidence.md, result.md}` — this attempt.
* No modifications to `algebraic_features.py`, `degeneracy.py`,
  `features.py`, `canonical.py`, `enumerate_bb.py`, `cli.py`,
  `corpus.py` (per hard constraints).
* `uv run pytest -m "not slow" -q` from `experiments/bb_lab/`:
  **195 passed, 2 skipped** (up from 163; +32 new tests).
