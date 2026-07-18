# Result — Family D v3: H_2 min-weight closed-form formula (round-2 v2 session 3)
> **[Historical research record — extracted 2026-07-18 from the retired branch
> `claude/priceless-meninsky-3076ce` during branch cleanup; never previously
> merged.]** This document is from the "round-2 / round-2-v2" line (2026-05-27),
> which ran between the round-1 C-series falsification and the A-line
> (`notes/A_HANDOFF.md`, A0–A18) that later proved d(gross) = 12 in Lean by the
> h=2 cover-transfer route. The round-2 line's durable outputs are the §6l–§6n
> obstruction/identity sections in `experiments/bb_lab/HANDOFF.md` (added from
> this same branch), the (4/9)|G| H₂ min-weight identity, and the §14 open
> research questions in
> `pipeline/attempts/bb_distance_conjecture_family_d_v3_h2_minwt_formula/result.md`,
> which the A-line never picked up and which remain open as of this date.
> Section references "§6l/§6m/§6n" here mean the spectral-vacuity /
> module-invariant / (4/9)|G| entries — NOT the unmerged elementary-abelian
> "§6l" that the older HANDOFF_C3/TIER3 docs mention. This is not a live task
> list.


**Verdict: PROVED + new Tier-1 corpus feature. The (4/9)|G| pattern
observed by session 1 is the special case wt=3 of a general structural
identity, with a rigorous explicit-witness proof. Tier-1 implementation
landed as `bb_lab.h2_minwt_formula`.**

Session 1 ([family_d_v1_koszul_h2/result.md](../bb_distance_conjecture_family_d_v1_koszul_h2/result.md))
observed empirically that for all 5 Bravyi instances,
`min_wt(H_2(Koszul(A,B))) = (4/9)·|G|` exactly. Session 2
([family_d_v2_6m_obstruction/result.md](../bb_distance_conjecture_family_d_v2_6m_obstruction/result.md))
proved that no F_2[G]-module-natural invariant can lower-bound d_X
(the §6m obstruction). Session 3 (this attempt) pins the (4/9)|G|
pattern down as a **structural identity** with an explicit witness
construction, verified on 437/437 corpus instances.

## 1. Strategic context

Per session 2's recommendation §10b: "Investigate the (4/9)|G| pattern
(session 1 observation). If this is a closed-form formula
`min_wt(H_2) = ((w-1)/w)² |G|` for w-weight Bravyi codes, it's a *new
computable feature* (not a bound, just a feature) deserving its own
attempt subdirectory."

This is the intended outcome of session 3. The result is not a distance
bound (the (4/9)|G| has the wrong sign for one per §6m; it's an upper
bound on something that's already an upper bound on d_X). It IS a
clean structural identity for the joint annihilator of weight-3
polynomial pairs over Z_ℓ × Z_m.

## 2. The theorem

### 2.1. Statement

**Theorem (Family D v3 — H_2 min-weight upper bound).** Let
`G = Z_ℓ × Z_m`, and let `A, B ∈ F_2[G]` be weight-3 polynomials.
Suppose there exist group homomorphisms `φ_A, φ_B: G → Z_3` such that:

1. `φ_A(supp(A)) = {0, 1, 2}` as a multiset (each residue appears once).
2. `φ_A(supp(B))` is **constant** (all 3 elements map to the same value in Z_3).
3. `φ_B(supp(B)) = {0, 1, 2}` as a multiset.
4. `φ_B(supp(A))` is **constant**.
5. `φ_A` and `φ_B` are **linearly independent** in `Hom(G, Z_3)`.

(Conditions 5 + 1 + 3 force `9 | |G|` automatically, since
`(φ_A, φ_B): G → Z_3 × Z_3` is surjective.)

Then the element

```
e: G → F_2,   e(g) = 1  iff  φ_A(g) ≠ 2 AND φ_B(g) ≠ 2
```

(equivalently, the indicator of `G \ (φ_A^{-1}(2) ∪ φ_B^{-1}(2))`) is in
`Ann(A) ∩ Ann(B) = H_2(Koszul(A, B))`, with Hamming weight

```
wt(e) = |G| - |φ_A^{-1}(2)| - |φ_B^{-1}(2)| + |φ_A^{-1}(2) ∩ φ_B^{-1}(2)|
      = |G| - |G|/3 - |G|/3 + |G|/9
      = (4/9) · |G|.
```

Hence **`min_wt(H_2(K(A, B))) ≤ (4/9) · |G|`**.

### 2.2. Proof

For any `h ∈ G`, the value `(e · A)(h)` is the convolution:

```
(e · A)(h) = sum_{g ∈ G} e(g) · A(h − g) = sum_{a ∈ supp(A)} e(h − a).
```

For each `a ∈ supp(A)`, `e(h − a) = 1` iff
`φ_A(h − a) ≠ 2` AND `φ_B(h − a) ≠ 2`, i.e.,
`φ_A(h) − φ_A(a) ≠ 2 (mod 3)` AND `φ_B(h) − φ_B(a) ≠ 2 (mod 3)`.

By condition 4, `φ_B(a) = c_A` is constant for `a ∈ supp(A)`. So
`φ_B(h − a) = φ_B(h) − c_A` is the same value `δ` for all 3 a's. Hence
`1[φ_B(h − a) ≠ 2] = [δ ≠ 2]` is **a single bit independent of a**.

Therefore:

```
(e · A)(h) = [φ_B(h) − c_A ≠ 2] · sum_{a ∈ supp(A)} 1[φ_A(h − a) ≠ 2].
```

By condition 1, as `a` ranges over `supp(A)` (size 3),
`φ_A(a)` takes each value in `{0, 1, 2}` exactly once. So
`φ_A(h − a) = φ_A(h) − φ_A(a)` takes each value `{φ_A(h), φ_A(h)−1,
φ_A(h)−2} = {0, 1, 2}` (mod 3), one of which equals 2 and the other
two do not. Hence the inner sum = 2, mod 2 = 0.

So `(e · A)(h) = 0` for all h, i.e., `e ∈ Ann(A)`. ✓

Symmetric for B (using conditions 2 and 3). So `e ∈ Ann(A) ∩ Ann(B) = H_2`.

The weight follows from inclusion-exclusion:
`|G \ (φ_A^{-1}(2) ∪ φ_B^{-1}(2))| = |G| - 2|G|/3 + |G|/9 = (4/9)|G|`
using that `φ_A, φ_B` are independent (so the joint preimage of (2, 2)
has size `|G|/9`).

### 2.3. The closed-form formula

For weight-3 codes the bound is `(2/3)² · |G| = (4/9) · |G|`. The
pattern generalizes:

**Conjecture (untested).** For weight-w BB codes with the analogous
"refined Z_w-pair" hypothesis (each `φ` sends one polynomial's support
to all of `Z_w` and the other's support to a constant), the same
construction gives

```
min_wt(H_2) ≤ ((w-1)/w)² · |G|.
```

For w = 3, this is the proved (4/9)|G|. The general w case requires
Z_w-homomorphisms `G → Z_w`, which only exist if `w` divides the
exponent of G. The corpus is exclusively wt=3 so the conjecture is
formally untested for w ≥ 4.

## 3. Bravyi-instance verification

All 5 Bravyi-table instances satisfy the refined hypothesis with the
canonical pair `(φ_A, φ_B) = (y mod 3, x mod 3)`:

| Code | (n, k, d) | A | B | (φ_A_on_A) | (φ_A_on_B) | (φ_B_on_A) | (φ_B_on_B) | (4/9)\|G\| | actual minwt |
|---|---|---|---|---|---|---|---|---|---|
| bb_72 | [[72,12,6]] | y+y²+x³ | y³+x+x² | {0,1,2} | {0,0,0} | {0,0,0} | {0,1,2} | 16 | **16** |
| bb_90 | [[90,8,10]] | y+y²+x⁹ | 1+x²+x⁷ | {0,1,2} | {0,0,0} | {0,0,0} | {0,1,2} | 20 | **20** |
| bb_108 | [[108,8,10]] | y+y²+x³ | y³+x+x² | {0,1,2} | {0,0,0} | {0,0,0} | {0,1,2} | 24 | **24** |
| gross | [[144,12,12]] | y+y²+x³ | y³+x+x² | {0,1,2} | {0,0,0} | {0,0,0} | {0,1,2} | 32 | **32** |
| bb_288 | [[288,12,18]] | y²+y⁷+x³ | y³+x+x² | {0,1,2} | {0,0,0} | {0,0,0} | {0,1,2} | 64 | **64** |

The constructed witness achieves the bound exactly for all 5 instances.
The bound is tight for these specific instances.

## 4. Broader corpus verification

Tested on the full SAT-verified BB corpus (4,364 weight-3 BB codes):

### 4.1. Aligned subset (3 | ell AND 3 | m), |G| up to 90

- **1,419 aligned instances** total.
- **437 satisfy the refined hypothesis** (~30.8% of aligned).
- **437/437 = 100% verify**: the constructed element is in
  `Ann(A) ∩ Ann(B)` with weight exactly `(4/9)·|G|`.
- **0 violations** of the upper-bound theorem.

### 4.2. Breakdown by group structure

Some groups have 100% refined-pair coverage (`Z_21 × Z_3`, `Z_15 × Z_3`,
`Z_12 × Z_6`, `Z_3 × Z_21`); others have low coverage (`Z_6 × Z_6` has
50/812 = 6.2%). The variation reflects how "structurally favorable" the
group is for the refined-pair condition to hold:

| Group | total aligned | with refined pair | % |
|---|---|---|---|
| Z_3×Z_3 | 12 | 1 | 8% |
| Z_3×Z_6 | 166 | 12 | 7% |
| Z_3×Z_15 | 6 | 5 | 83% |
| Z_3×Z_21 | 7 | 7 | 100% |
| Z_6×Z_6 | 812 | 50 | 6% |
| Z_6×Z_15 | 54 | 10 | 19% |
| Z_12×Z_6 | 18 | 18 | 100% |
| Z_15×Z_3 | 68 | 68 | 100% |
| Z_15×Z_6 | 96 | 86 | 90% |
| Z_21×Z_3 | 180 | 180 | 100% |

### 4.3. Tightness

Of the 437 refined-pair cases (|G| ≤ 90):
- **408 = 93.4% tight** (`min_wt(H_2) = (4/9)·|G|` exactly).
- **29 = 6.6% strict** (`min_wt(H_2) < (4/9)·|G|`; theorem still holds
  as an upper bound, but isn't sharp).

For |G| ≥ 72 (114 refined-pair cases): **107 = 93.9% tight**, 7 strict.

### 4.4. Outside the refined hypothesis

When the refined hypothesis FAILS, the actual `min_wt(H_2)` is some
different value — most commonly:
- `(2/3) · |G|` (from a single Z_3-homomorphism diagonal-subgroup
  element; less restrictive condition).
- `(1/2) · |G|`, `(1/3) · |G|`, `(1/4) · |G|`, `(1/9) · |G|` for
  smaller groups with 2-torsion or degenerate polynomial structure.

These cases don't have a closed-form formula in the (4/9)|G| family;
they fall into different combinatorial categories. The (4/9)|G| identity
is a **structural** statement about a specific subfamily, not a
universal formula.

## 5. Why the bound is sometimes loose

For 29 cases in the aligned corpus (|G| ≤ 90), `min_wt(H_2)` is
strictly less than `(4/9)·|G|`. The strict-tighter elements arise from:

1. **2-torsion in G**: when `Z_2 ⊂ G`, additional non-trivial
   annihilators appear (e.g., `1_{y mod 2 = 0}` is in `Ann(A)` if
   `supp(A)` has only y-values with one residue mod 2).
2. **Degenerate polynomial structure**: if `supp(A) ⊂ Z_ℓ × {0}` (all
   y-values are 0), the H_2 decomposes by y-slice into smaller
   problems with their own min-weight elements.
3. **Combined symmetries**: when multiple independent Z_3-homs exist
   (more than one pair satisfies refinement), the intersection of all
   their "exclude residue 2" indicators gives an element of weight
   `< (4/9)|G|`.

These cases are characterized but not pinned to a clean closed form.
The (4/9)|G| bound holds in all 437 cases; tightness varies.

## 6. Implementation as Tier-1 corpus feature

Per session 2's recommendation: **the (4/9)|G| identity is implemented
as a callable structural feature**.

### 6.1. Module API

`src/bb_lab/h2_minwt_formula.py` exposes:

```python
def find_refined_z3_pair(A: Poly, B: Poly) -> Optional[tuple[..., ...]]:
    """Find (phi_A_coef, phi_B_coef) ∈ Z_3² × Z_3² satisfying the
    refined hypothesis. Returns None if no pair exists."""

def min_wt_h2_upper_bound(A, B, G) -> Optional[int]:
    """Return (4/9)·|G| if refined hypothesis holds; None otherwise."""

def construct_h2_witness(A, B, G) -> Optional[np.ndarray]:
    """Build the explicit |G|-length indicator vector witness."""

def closed_form_formula(wt: int, abs_G: int) -> float:
    """Return ((wt-1)/wt)² · |G|, the conjectured general formula."""
```

### 6.2. Tests

`tests/test_h2_minwt_formula.py` adds 14 new tests:

- 5 parameterized: each Bravyi instance hits (4/9)|G| with valid witness.
- 3 refined-pair existence cases (gross, Z_3×Z_4 negative, both-y negative).
- 2 witness-correctness cases (in Ann(A), Ann(B); weight = (4/9)|G|).
- 3 closed-form-formula sanity (wt=3, wt=4, wt=0).
- 1 corpus-sample validity check (any aligned subset works).

Full test suite: **383 passing** (was 369; +14 new).

## 7. Mechanism comparison with §6m

The (4/9)|G| identity does **not contradict** §6m's "min weight is not
a module invariant" result:

- §6m says: across F_2[G]-module-iso-class, min weight varies. The
  abstract module `H_2 = Ann(A) ∩ Ann(B)` doesn't determine its min
  weight in its canonical embedding into F_2[G].
- The (4/9)|G| identity says: for codes satisfying the refined
  hypothesis, the min weight is UPPER-BOUNDED by `(4/9)|G|` via an
  **explicit element construction** (not via module-theoretic
  inference).

The construction uses the canonical F_2-basis `{e_g}` of F_2[G],
explicitly identifying a low-weight element. This is "non-module"
data — it depends on the embedding `ι: H_2 ⊂ F_2[G]`, not just the
abstract module `H_2`.

So the (4/9)|G| identity is **compatible with §6m**: it's an
embedding-specific upper bound, not a module-iso-class invariant.

## 8. What was NOT achieved

### 8.1. Tight lower bound on d_X

The (4/9)|G| identity is an UPPER bound on `min_wt(H_2)`, which is
itself an upper bound on d_X (per session 1). So the identity provides
**two layers of upper-bounding** on d_X — useful for code analysis but
not for the moonshot goal of a distance LOWER bound.

For the Bravyi instances, the chain is:
- `d_X ≤ min_wt(H_2) = (4/9)|G|` (loose upper bound).
- bb_72: `d_X = 6 ≤ 16 = (4/9)·36`. Loose by 10.
- gross: `d_X = 12 ≤ 32 = (4/9)·72`. Loose by 20.

### 8.2. Universal weight-3 formula

The refined hypothesis is restrictive (~30% of aligned corpus). For
weight-3 BB codes that fail the hypothesis, no clean closed-form
formula was found — though we identified the "second-tier" pattern
`min_wt(H_2) ≤ (2/3)|G|` via the single-Z_3-homomorphism diagonal-
subgroup element, and noted further fragmentation into
`{(1/2), (1/3), (1/4), (1/9)}·|G|` for groups with additional 2-torsion
or degenerate polynomial structure. These are descriptive observations,
not theorems.

### 8.3. Higher-weight generalization

The conjecture `min_wt(H_2) ≤ ((wt-1)/wt)² · |G|` for arbitrary
weight `wt` is plausible but UNTESTED. The corpus is exclusively wt=3
so we have no empirical data on wt ≥ 4.

## 9. Recommendations for next session

### 9.1. Pivot to Lean formalization (recommended)

The §6h–§6m obstructions are now machine-checked in Python via
`obstructions.py`. The natural next round-2-v2 endgame is to formalize
these in Lean against `QEC/Stabilizer/Framework/Homological/BBChainComplex.lean`.

Specifically:

- **§6m as a Lean theorem.** Statement: any F_2[G]-module-iso-class
  invariant ψ fails to lower-bound d_X. Witness: H_0(K_gross) ≅
  H_2(K_gross) with min weights differing by 32×.
- **§6h, §6j, §6k, §6l as Lean lemmas** with their specific witnesses.
- **(4/9)|G| identity as a separate Lean theorem** (in a `Syzygy.lean`
  or `H2MinWeight.lean` sister file): given the refined hypothesis,
  construct the explicit witness and prove its weight is (4/9)|G|.

The (4/9) theorem's proof is elementary (a few lines of group-theory +
modular arithmetic). It should be ~50-100 lines of Lean if the BB
homological infrastructure supports it. The §6m theorem is harder —
needs Frobenius duality and might require new abstractions.

**Estimate: 1-3 sessions for §6h/§6j/§6k/§6l (mechanical from the
witnesses); 2-4 sessions for §6m; 1-2 sessions for the (4/9)|G|
identity.**

### 9.2. Higher-weight generalization

Test the conjecture `min_wt(H_2) ≤ ((wt-1)/wt)² · |G|` on weight-4
and weight-5 BB codes (would require new corpus generation). If the
pattern generalizes, that's a stronger structural identity.

### 9.3. Tightness characterization

For the 7% of refined-pair cases where the bound isn't tight,
characterize the "tighter element" structurally. This might reveal a
secondary identity for the actual min-weight in those cases.

### 9.4. Open problem: is (4/9)|G| ALWAYS the min for Bravyi instances?

We verified it numerically. A rigorous proof of TIGHTNESS (not just
upper-bound) for the Bravyi family would be a stronger structural
result. This requires showing that no H_2 element has weight strictly
less than (4/9)|G| in the Bravyi codes. Group-theory plus dim H_2 = k/2
calculations should suffice — but it's separate work.

## 10. Files committed this session

| File | Type | Purpose |
|---|---|---|
| `src/bb_lab/h2_minwt_formula.py` | Module | `find_refined_z3_pair`, `min_wt_h2_upper_bound`, `construct_h2_witness`, `closed_form_formula` |
| `tests/test_h2_minwt_formula.py` | Tests | 14 new tests, all passing |
| `scripts/family_d_v3_h2_minwt_formula.py` | Script | Sample corpus probe |
| `scripts/family_d_v3_h2_minwt_aligned.py` | Script | Aligned-group breakdown |
| `scripts/family_d_v3_h2_minwt_full_analysis.py` | Script | Multi-category classifier |
| `pipeline/attempts/.../result.md` | Documentation | This file |

## 11. Reproducibility

```bash
cd experiments/bb_lab
uv sync --extra dev

# Run the new tests:
uv run pytest tests/test_h2_minwt_formula.py -v

# Run the (4/9)|G| theorem verification on the corpus:
uv run python scripts/family_d_v3_h2_minwt_formula.py --limit 200

# Detail on aligned-group breakdown:
uv run python scripts/family_d_v3_h2_minwt_aligned.py --limit 300

# Multi-category classification:
uv run python scripts/family_d_v3_h2_minwt_full_analysis.py --limit 500

# Quick sanity-check on the Bravyi 5 (session 1 reproduction):
uv run python scripts/family_d_v1_koszul_h2.py

# Iso-witness for §6m (session 2):
uv run python scripts/family_d_v1_koszul_h2_iso_witness.py
```

## 12. Honest framing

This session **succeeded** in its stated goal: the (4/9)|G| pattern
from session 1 is now a rigorously-proven structural identity, not just
an empirical curiosity. The proof is elementary (group-theoretic +
modular arithmetic + an explicit indicator-function witness) and the
identity is implemented as a callable Tier-1 corpus feature.

The result is **not a distance bound** — per §6m, it can't be — but
it is a clean structural observation that survives as a useful
diagnostic for analyzing BB codes. It complements the §6h-§6m
obstruction registry as a "positive structural feature" of weight-3
BB codes.

**This session's contribution to the moonshot is a clean
positive identity** (the (4/9)|G| theorem), backed by a Tier-1
implementation, on top of session 2's clean negative identity (§6m).
Together they sharpen the structural understanding of BB codes: we
know precisely what kinds of "module-theoretic" arguments can't work
(§6h-§6m) AND we have explicit weight identities for the cases where
the structure cooperates ((4/9)|G|).

Time spent: ~3.5 hours (corpus exploration, hypothesis refinement,
proof, implementation, tests, documentation).

## 13. Connection to the moonshot's central question

The moonshot was: "Can we find a closed-form distance lower bound for
BB codes tight on gross?"

**§6h-§6m** (sessions 0-2) closed the door on classical algebraic
families: no closed-form bound tight on gross exists within
F_2[G]-module-iso-class invariants, character theory, chain maps,
or spectral gaps.

**Session 3's (4/9)|G| identity** gives a partial answer: it's an
explicit structural identity for a specific family of weight-3 BB
codes, but it's an **upper** bound on `min_wt(H_2)` — and since
`min_wt(H_2)` is itself an upper bound on `d_X`, the (4/9)|G|
identity tells us NOTHING about lower-bounding `d_X`.

The honest verdict is the §6m-style closure: classical algebraic
techniques cannot tightly bound `d_X` from below for the gross codes.
The (4/9)|G| identity is a **structural identity** for BB codes that
deserves its own niche in the lab's vocabulary, but it doesn't move the
distance-lower-bound needle.

The natural next session pivot: **Lean formalization of §6h-§6m and
the (4/9)|G| identity** — turning the round-2-v2 negative result into
a Lean-verified structural-impossibility theorem with explicit
positive-identity witness.

## 14. Open research questions

Critical-reading of §6n raises several follow-up questions a BB-code
researcher would want answered before declaring the result complete.
Ordered by ROI / importance.

### 14.1. Highest-ROI: are any of the 403 non-Bravyi tight codes BETTER than Bravyi?

Of the 408 tight cases on `|G| ≤ 90`, only 5 are Bravyi-table
instances. The other 403 are weight-3 BB codes satisfying the
refined Z_3-pair hypothesis with `min_wt(H_2) = (4/9)|G|` exactly.
Their `d_exact` values are in the corpus (most are SAT-verified).

Concrete question: **does any non-Bravyi tight code have higher `d/n`
than the Bravyi instances?**

- If yes → publishable: new BB codes that the Bravyi polynomial
  search missed.
- If no → also publishable: Bravyi's search was effectively exhaustive
  within the structural family `(4/9)|G|` identifies.

This is a 1-hour SQL query on the corpus. The fact that it's not in
the result.md is the most glaring gap. **Should be answered next.**

### 14.2. Does the conjectured `((w-1)/w)² · |G|` generalize?

§2.3 conjectures the formula for arbitrary weight w. The proof
structure suggests:

- For weight-w, hypothesis = "refined Z_w-pair" (each `φ` permutes
  one polynomial's support onto Z_w and is constant on the other's).
- Witness = `e(g) = 1[φ_A(g) ≠ w-1 ∧ φ_B(g) ≠ w-1]`, support
  `((w-1)/w)² · |G|`.

**Parity obstruction**: For the inner sum to vanish mod 2, we need
`w-1 ≡ 0 (mod 2)`, i.e., **w must be odd**. For even w, the witness
construction fails — sum is `w-1 ≡ 1 (mod 2)`, so `(e · A) ≠ 0`.

So the conjecture as stated is only plausible for **odd weights**.
A truly general formula would need to handle even w differently (or
not at all). The corpus is exclusively wt=3, so this is untested.
**Worth investigating analytically** before claiming the formula
generalizes.

### 14.3. Algebraic taxonomy of the 29 strict cases

§5 identifies three mechanisms (2-torsion, axis-degenerate supports,
extra Z_3-homs) but doesn't pin them down case-by-case. A complete
classification would:

1. For each of the 29 strict cases, identify which structural feature
   causes strictness.
2. For each structural feature, derive the **exact** `min_wt(H_2)`
   (not just "less than (4/9)|G|").
3. Produce a decision-tree closed form: given `(A, B, G)`, classify
   into a structural category, then output `min_wt(H_2)` exactly.

This converts the result from "(4/9)|G| is tight in the generic case"
to "complete closed-form formula for ALL refined Z_3-pair codes,
across structural categories." Real theorem with multiple cases,
~few days of work.

### 14.4. Can the cellular witness yield a `d_X` LOWER bound (dodging §6m)?

§6m blocks F_2[G]-module-iso-class lower bounds on `d_X`. The (4/9)|G|
witness `e(g) = 1[φ_A(g) ≠ 2 ∧ φ_B(g) ≠ 2]` uses **non-module data**:
the F_2-basis vectors of F_2[G] indexed by group elements. It's
embedding-specific. **In principle this dodges §6m.**

Concrete next question: the witness `e` is a Z-codeword (annihilates
both A and B). Is it a *logical* Z-codeword or a *stabilizer*?

- If it's always a stabilizer for some structural reason, the witness
  doesn't bound `d_Z`. It tells us only that small stabilizers exist.
- If it's a logical, `d_Z ≤ wt(e) = (4/9)|G|` — the upper-bound
  conclusion we already have.
- If we can characterize WHEN it's stabilizer vs logical structurally
  (some algebraic condition on `(A, B, G)`), we might find a subfamily
  where the witness IS a stabilizer, meaning no logical of weight
  `(4/9)|G|` exists. **That would lower-bound `d_Z` from below**
  using non-module data — exactly what §6m permits.

This is the moonshot's primary question viewed through the cellular
lens. Worth ~2-3 sessions of focused work; high uncertainty but
high payoff if it lands.

### 14.5. Make the "base × fiber" decomposition rigorous

The refined Z_3-pair gives a quotient `G ↠ Z_3 × Z_3` with kernel
`fiber ⊂ G`. For gross, fiber = `4Z_12 × 2Z_6` of order 8 = G_2.
The fiber's structure (specifically G_2 = Z_4 × Z_2 for gross)
seems to control `d_X` — but §6n does not explain how.

Can we prove a theorem of the form

```
d_X(BB(G, A, B))  =  f(base structure) · g(fiber structure)
```

or even an inequality

```
d_X(BB(G, A, B))  ≥  f(base) · g(fiber)
```

for refined Z_3-pair codes? Concretely: derive a lower-bound formula
parametric in the cellular structure (base) and the lift (fiber).
This is the natural connection to Panteleev-Kalachev's lifted-product
theory; their asymptotic `d = Ω(N)` might admit a quantitative
refinement in the refined-Z_3-pair setting.

Research-grade work, ~weeks. Could yield the first quantitative
lifted-product distance bound for engineered BB codes.

### 14.6. Decoder implications

The cellular decomposition `G → Z_3 × Z_3 × fiber` suggests a
hierarchical decoder: first correct on the 9 cells, then refine within
each fiber. Compare to surface code's local-then-global decoding.

Concrete experiments:
- Run BP / OSD on Bravyi codes WITH and WITHOUT cellular-aware
  initialization. Compare convergence and threshold.
- Build a custom decoder that explicitly leverages the Z_3-cellular
  structure. Does it beat generic BP / OSD on the same codes?

If yes → BB codes might decode faster / with better thresholds than
expected, and §6n becomes practically relevant. If no → §6n is
mathematically elegant but practically irrelevant.

This is harder to answer cleanly (simulation + threshold analysis),
but it determines whether the cellular structure matters for
fault-tolerant quantum computing.

### 14.7. The "complement" structure

The witness has support `(4/9)|G|`. The complement has support
`(5/9)|G|`. Is the complement also in `Ann(A) ∩ Ann(B)`?

By symmetry of `Ann(A) ∩ Ann(B)` under "flip the witness": no, since
`e + 1_G = (complement indicator)` is in `Ann(A) ∩ Ann(B)` iff
`1_G ∈ Ann(A) ∩ Ann(B)`, iff `A · 1 = 0` and `B · 1 = 0`, iff
`|supp(A)| ≡ 0 (mod 2)` and `|supp(B)| ≡ 0 (mod 2)`. For weight-3
polynomials, weights are odd, so `A · 1 ≠ 0` and the complement is
NOT in `Ann(A) ∩ Ann(B)`.

So the (4/9)|G| witness is "asymmetric in the complement direction" —
it's not the case that both half-spaces give witnesses. This is a
small observation but worth noting in any future paper.

### 14.8. What I'd actually do first

Given limited time, the priority ordering (highest first):

1. **§14.1** (1 hour SQL query) — could find new codes immediately
2. **§14.2** (1 day analytical) — fixes the formula's generalization claim
3. **§14.3** (few days) — completes the theorem statement
4. **§14.4** (2-3 sessions, risky) — the moonshot's primary question revisited
5. **§14.5** (research-grade) — quantitative lifted-product theory
6. **§14.6** (simulation-heavy) — practical relevance test

The first three (§14.1-§14.3) are *cheap and important* — completing
the §6n picture. They should land before declaring the result
complete. §14.4-§14.6 are bigger investments with higher uncertainty
but potentially much bigger payoffs.

**The single most important question** is §14.1. The 403 non-Bravyi
tight codes are sitting in the corpus, waiting to be queried.
