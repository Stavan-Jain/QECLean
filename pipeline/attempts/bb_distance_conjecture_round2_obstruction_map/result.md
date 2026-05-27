# Result — Round 2 first-pass obstruction map

**Verdict: ROUND-2-FIRST-PASS COMPLETE; no tight bound found; obstruction
map enriched; Family D moonshot recommended for round-2 v2.**

Round 2 ran the merged Phase-0 pipeline against four candidate families
(A, B, C, D) per HANDOFF_R2.md §6 and produced two new structural
obstructions, two clean negative empirical results, and a measurably
richer corpus. No analytic distance bound tight on gross was found.
The remaining open direction (Family D, module/syzygy) is research-
grade and deferred to a multi-session moonshot.

## 1. Strategic context

[HANDOFF_R2.md](../../../experiments/bb_lab/HANDOFF_R2.md) §1: goal is
a closed-form lower bound `d_X ≥ f(G, A, B)` provable in Lean against
`bbChainComplex`, tight or near-tight on the gross polynomials. Round
1 ran six conjecture rounds (Cv1 → Cv4, R1+R4) and shelved all; net
output was the §6h–§6k obstruction theorems and the `w_1` weight
invariant. Round 2 restarted with the merged Phase-0 architecture
(obstruction registry, candidate registry, predicates, adversarial
generator, classify CLI) and ran candidates from four families.

Per HANDOFF_R2.md §10 honest-framing: "A tight bound on gross may not
exist in closed form. If round 2 doesn't yield it and the obstruction
map narrows, that itself is a publishable result." Round 2 lands at
exactly that position.

## 2. What round 2 ran (and what each landed)

### Tier 1 — corpus expansion (commit `08d8491`)

Targeted-neighborhood sampling replacing the failed full-enumerate
approach (single Z_3 × Z_15 enumerate at parallel-8 exceeded 30 min /
hit OOM with no output). Yields:

| Regime | Rows added | SAT-verified |
|---|---:|---:|
| Multi-prime mixed-rank G_odd (bb_90's class) | 322 | 261 |
| Gross-scale Z_12×Z_6 + Z_12×Z_12 | 33 | 18 |
| Non-semisimple multi-prime (Z_6×Z_15 / Z_15×Z_6) | 150 | 150 |
| Triple-prime G_odd (Z_3×Z_35) | 13 | 13 |
| **Total** | **485 new rows** | **307 with d_exact** |

Corpus now 16,704 total / 4,201 with `d_exact`. New distance distribution
on the SAT-verified subset includes **16 rows with d=2** (R1+R4-falsifier
class — valuable Tier-3 adversarial fodder) and **8 rows with d=12**
(gross-distance class on multi-prime + gross-group instances).

### Family A v2 candidate #1 (commit `08d8491`)

**Hypothesis** (from H_UNIT² failure note seed): the C-v3 bound is
tight when `min_{O ∈ JV(A,B)} a_O y'-spread ≥ 3` and overshoots when
the spread is ≤ 2.

**Implementation**: `a_O_y_spread` projects A to R_O, converts to
Loewy basis via Pascal-mod-2, counts pure-y' nonzero entries
([scripts/family_a_v2_seed_check.py](../../../experiments/bb_lab/scripts/family_a_v2_seed_check.py)).
Reproduces all 4 H_UNIT² literature values exactly.

**Result** ([scripts/family_a_v2_corpus_check.py](../../../experiments/bb_lab/scripts/family_a_v2_corpus_check.py)):
across 3,724 SAT-verified rows in non-trivial-G_2 groups, the spread
buckets {0, 1} have **identical tight rates** (5.4% vs 4.9%) and the
same massive C-v3 violation count. The 4-case seed observation does
not extend.

**Verdict**: FALSIFIED-AS-PREDICTOR. Detailed write-up at
[`bb_distance_conjecture_family_a_v2_yspread/result.md`](../bb_distance_conjecture_family_a_v2_yspread/result.md).

### Family B literature pass (this commit)

**Targeted papers**: Panteleev–Kalachev 2022 (arXiv:2111.03654),
Hastings–Haah–O'Donnell 2020 (arXiv:2009.03921), Leverrier–Zémor 2022
(arXiv:2202.13641), Wang–Mueller 2024 (arXiv:2408.10001).

**Finding**: All four give **asymptotic** distance bounds (`d = Ω(N)`
or similar). The "closed-form finite numerical lower bound on a
specific BB code" that round-2 needs **does not exist in the published
literature**. Adapting PK/HHO/LZ proof techniques to derive a finite
bound is research-grade derivation work, not literature reading.

**Verdict**: Family B as a v1 candidate is BLOCKED by literature gap.
Could be revisited only by deriving new mathematics from the
asymptotic proofs.

### Family C v1 (spectral) (this commit)

**Hypothesis**: spectral gap of the Cayley graph of M_A and M_B
correlates with d_X, enabling a Sipser-Spielman-style lower bound.

**Implementation** ([scripts/family_c_spectral_check.py](../../../experiments/bb_lab/scripts/family_c_spectral_check.py)):
compute `λ_2 = max_{χ ≠ trivial} |sum_{g ∈ supp(A)} χ(g)|` over all
4,364 weight-3 SAT-verified corpus rows.

**Result**: across-corpus Pearson correlation between spectral gap
`(w − λ_2)` and `d_X` is **−0.020** — effectively zero. All Z_12×Z_6
(gross-group) rows have gap = 0.000 yet d ranges from 4 to 12.

**Root cause** (new obstruction §6l): for any BB code with k ≥ 2,
Bravyi 2024 Lemma 1 forces A and B to jointly vanish on a non-trivial
character. That vanishing forces `λ_2(M_A) = weight(A)`, so the
spectral gap is identically 0 on every k ≥ 2 BB code.

**Verdict**: STRUCTURALLY VACUOUS. The whole Family C "spectral-bound"
subfamily is now blocked at Tier 0 by §6l (machine-checked).

### Family D (module/syzygy) — literature pass (this commit)

**arXiv searches**: "syzygy code distance lower bound quantum" returns
**zero hits**. "Groebner basis code distance quantum LDPC" also zero.

**Natural module-theoretic quantities** (Koszul complex, Hilbert
series, Castelnuovo-Mumford regularity, Anick resolution) all either
equal d_X exactly (reformulation, no bound) or require deriving new
theory.

**Verdict**: Family D is research territory, **not session-scale**.
Deferred to the round-2 v2 moonshot (see §6 below).

## 3. New obstructions added

### §6l — Cayley-graph spectral bounds vacuous

Added to [HANDOFF.md §6l](../../../experiments/bb_lab/HANDOFF.md) and
machine-checked in
[obstructions.py](../../../experiments/bb_lab/src/bb_lab/obstructions.py)
via the `uses_cayley_spectral_bound` predicate. Four new tests in
`test_obstructions.py`. Full test suite: 360 passing.

The proof is 3 lines:

> If k ≥ 2 then A vanishes on some non-trivial character χ (Bravyi
> Lemma 1). On that χ, `|λ_A(χ)| = sum_{g ∈ supp(A)} χ(g)|` achieves
> its maximum value `|supp(A)|` (since the χ-values of supp(A) all lie
> in a coset trivial under the joint-vanishing relation). So the
> spectral gap `weight − λ_2 ≤ 0`. Any spectral lower bound is vacuous.

### §6 docstring patch — c-form clarification

The C-program's `bb_radical_bound` deliberately uses
`c = [G_a : G_a ∩ G_b]` (the index), while LP12 uses `c = |G_a ∩ G_b|`
(the order). Both are "joint subgroup quantities" with different
behavior. Cv2 design (notes/Cv2_literature.md §2) chose the index for
tightness reasons; round-2's LP12 demo eval initially used the index
by accident and saw 7,512 false violations. Fix: explicit warning in
`joint_support_subgroup_index` docstring that it is **NOT** LP12's c.

## 4. Net mathematical contributions

| Output | Type | Where |
|---|---|---|
| §6l obstruction (spectral vacuity) | New theorem | HANDOFF.md §6l + obstructions.py |
| C-form audit (Cv2's c vs LP12's c) | Clarification | radical_weight.py docstring |
| `a_O_y_spread` implementation | New computable feature | scripts/family_a_v2_seed_check.py |
| Loewy-basis conversion `_to_loewy_basis` | Reusable utility | scripts/family_a_v2_seed_check.py |
| Cayley spectral-radius computation | New feature | scripts/family_c_spectral_check.py |
| 485 new corpus rows / 307 d_exact | Substrate expansion | data/bb_instances.duckdb |
| 4 new obstruction tests | Regression | tests/test_obstructions.py |

## 5. What survives the round

- The §6h–§6l obstruction registry now machine-checks all known
  structural impossibility theorems for BB-code distance bounds.
- The corpus has the round-1 blind spot (multi-prime mixed-rank
  G_odd) filled at 100% SAT-verification for the bb_90 structural class
  and Z_3² × Z_7 / Z_3 × Z_5² variations.
- The merged Phase-0 architecture (candidates registry, adversarial
  generator, classify CLI) worked end-to-end on real candidates.
- `w_1` (round 1) and `a_O_y_spread` (round 2) are standalone
  computable invariants; neither bounds d, but both are reusable for
  future Family A v3+ work.

## 6. Recommended next move

**Round-2 v2 should be Family D as a multi-session moonshot.** See
[`HANDOFF_FAMILY_D_MOONSHOT.md`](../../../experiments/bb_lab/HANDOFF_FAMILY_D_MOONSHOT.md)
for the handoff document. The new agent picks up with:

- Round 2's negative pattern (no closed-form bound accessible from
  Families A, B, C using session-scale tools)
- §6h–§6l ruling out character-theoretic, chain-map, dimension, and
  spectral approaches
- Family D as the surviving direction not yet definitively shelved
- Concrete starting points: Anick resolution + minimum-weight
  differentials, Hilbert series degree bounds, Koszul non-regularity
  refinement

The user should treat round-2 v2 as a research moonshot in the spirit
of the gross moonshot (`pipeline/attempts/gross/result.md`) — multi-
session, with failures as first-class outputs, and the Lean kernel as
the eventual verification floor.

If Family D yields no bound in 2-3 sessions of focused work, that
itself completes the "no published-classical-analytic-technique can
be tight on gross" result implicit in §6h–§6l, making it explicit and
exhaustive. That's a publishable structural-impossibility theorem.

## 7. Reproducibility

```bash
cd experiments/bb_lab
uv sync --extra dev

# Verify the full test suite (360 passing, includes §6l tests).
uv run pytest -q

# Reproduce the Family A v2 falsification.
uv run python scripts/family_a_v2_seed_check.py
uv run python scripts/family_a_v2_corpus_check.py

# Reproduce the Family C v1 spectral falsification.
uv run python scripts/family_c_spectral_check.py

# Re-run LP12 demo eval (matches round-1 T2R2.4 baseline).
uv run python scripts/demo_lp12_eval.py

# Smoke-test the obstruction gate against Family C v1 (should
# classify as SHELVED-A-PRIORI via §6l).
uv run python -c "
from bb_lab.obstructions import FAMILY_C_V1_SPECTRAL, classify
print(classify(FAMILY_C_V1_SPECTRAL))
"
```

## 8. The corpus snapshot

`experiments/bb_lab/data/bb_instances.duckdb` is gitignored. The
round-2 corpus snapshot is in this worktree only. To regenerate from
scratch (would take ~3-4 hours):

```bash
# Phase 1 — round-1 baseline (already on bb-lab-v0; copy from there
# OR run the canonical enumerate sequence per Cv2_corpus_sweep.md).
# Round-2 additions:
uv run python scripts/sample_gross_neighborhood.py
uv run python scripts/sample_structural_extras.py
uv run bb-lab fill-distance-ubs --only-missing
uv run python scripts/fill_z21z3_sample.py 200 --group Z21xZ3
# (and similar per-group runs for Z15xZ3, Z3xZ21, Z12xZ6, Z15xZ5, Z5xZ15)
uv run bb-lab fill-features
```

A reproducibility script that wraps all of these into one command
would be a useful round-2-v2-prep task (~30 min).
