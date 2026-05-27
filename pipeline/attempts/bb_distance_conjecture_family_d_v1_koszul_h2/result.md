# Result — Family D v1: Koszul H_2 cheap probe

**Verdict: FALSIFIED-AS-LOWER-BOUND; CONFIRMED-AS-UPPER-BOUND; §6m
candidate identified (weight ≠ module invariant).**

Round-2 v2 first session investigated handoff §4d (the cheapest Family D
candidate). Empirical finding: `min_weight(H_2(Koszul of (A, B))) ≥ d_X`
on 5/5 Bravyi instances and 200/200 sampled SAT-verified corpus rows.
The relation holds with the **wrong sign for a lower bound**: it is an
UPPER bound on d_X (and a loose one for engineered codes). The
mechanism is now understood, and the result generalizes into a §6m
candidate ruling out a class of "natural" module-theoretic lower bound
attempts.

## 1. Strategic context

Round-2 v2 picks up where v1 left off:
[`bb_distance_conjecture_round2_obstruction_map/result.md`](../bb_distance_conjecture_round2_obstruction_map/result.md).
Five §6h-§6l obstructions are now machine-checked, ruling out
character-theoretic, chain-map, dimension-RHS, spectral, and
non-degenerate-only directions. Family D (module/syzygy/Anick/Koszul)
is the surviving major direction.

This attempt is the **first concrete Family D candidate** following the
handoff document
[`HANDOFF_FAMILY_D_MOONSHOT.md`](../../../experiments/bb_lab/HANDOFF_FAMILY_D_MOONSHOT.md)
§4d (Koszul non-regularity refinement / cheap probe).

## 2. Hypothesis and rationale

**Hypothesis (4d)**: For BB codes, the minimum Hamming weight in
`H_2(K(A, B)) = Ann(A) ∩ Ann(B)` gives a non-trivial lower bound on
`d_X`. Equivalently:

    d_X ≥ min weight in (ker M_A ∩ ker M_B) \ {0}

**Why this might work**: H_2 ≠ 0 for BB codes (since k > 0 forces
non-regular (A, B) sequences). The joint annihilator is a structurally
rich submodule of F_2[G]. If its minimum non-zero weight is a clean
F_2[G]-module invariant ≥ d_X, this would be a Family D lower bound
formalizable in Lean against `bbChainComplex`.

**Why it might fail**: H_2 is a quotient/sub of dimension `k/2`, with no
a-priori control over its weight distribution. Min weight is a
non-module-theoretic property — F_2[G]-module isomorphisms don't
preserve Hamming weight in general. So even though dim H_2 is module-
invariant, min wt H_2 might bear no relation to d_X.

## 3. Implementation

`experiments/bb_lab/scripts/family_d_v1_koszul_h2.py` (seed: 5 Bravyi
instances) and `family_d_v1_koszul_h2_corpus.py` (corpus extension).

The computation:

1. Build `M_A, M_B` circulant matrices via `bb_lab.checks.circulant`.
2. Stack vertically: `[M_A; M_B]` of shape `(2|G|, |G|)`.
3. Compute `nullspace_f2([M_A; M_B])` — this is the F_2-basis of `H_2`.
4. Brute-force enumerate `2^dim_H_2 - 1` non-zero linear combinations
   to find the min Hamming weight in F_2[G] = F_2^|G|.
5. Compare with the known `d_X`.

For BB codes with k ≤ 12 (Bravyi table), `dim H_2 = k/2 ≤ 6`, so brute
force is trivially fast (2^6 = 64 enumerations per instance).
Throughout the broader corpus, dim H_2 stays ≤ 16 in our 200-row
sample, so full enumeration is tractable.

## 4. Empirical results

### Bravyi-table instances

```
code_id                (n,k,d)      dim ann_A dim ann_B  dim H_2  minW(H_2)   d_X   gap  ratio
─────────────────────────────────────────────────────────────────────────────────────────────────
bb_72_12_6             [[72,12,6]]         12        12        6         16     6   -10   2.67
bb_90_8_10             [[90,8,10]]          6         6        4         20    10   -10   2.00
bb_108_8_10            [[108,8,10]]         6         6        4         24    10   -14   2.40
gross                  [[144,12,12]]       12        12        6         32    12   -20   2.67
bb_288_12_18           [[288,12,18]]       24        24        6         64    18   -46   3.56
```

Key observations:

- `dim H_2 = k/2` exactly in every case (matches the predicted Koszul
  identity via Bravyi-Cross).
- `min_wt(H_2)` is **always ≥ d_X**, with ratios 2.0 to 3.6.
- **`min_wt(H_2)` does NOT lower-bound d_X — it UPPER-bounds it.**
- The ratios scale: `bb_72: 2.67`, `gross: 2.67` (gross is the h=2
  cover of bb_72). Consistent doubling of the absolute value.

### Striking algebraic pattern on Bravyi table

For the 5 Bravyi instances:

| Code      | min_wt(H_2) | |G|  | min_wt / |G| |
|-----------|------------:|-----:|-------------:|
| bb_72     |          16 |   36 | 0.444 = 4/9  |
| bb_90     |          20 |   45 | 0.444 = 4/9  |
| bb_108    |          24 |   54 | 0.444 = 4/9  |
| gross     |          32 |   72 | 0.444 = 4/9  |
| bb_288    |          64 |  144 | 0.444 = 4/9  |

**EXACT pattern**: `min_wt(H_2) = (4/9) |G|` for all 5 Bravyi codes.
This is `((w-1)/w)² · |G|` for `w = wt(A) = wt(B) = 3`. Suggests the
formula `min_wt(H_2) = ((wt(A)-1)/wt(A))² |G|` for the
particular Bravyi family. **(Not confirmed for general weight.)**

### Corpus check

`scripts/family_d_v1_koszul_h2_corpus.py` random-sampled 200
SAT-verified rows (n ≤ 72):

- **0 / 200 rows** have `min_wt(H_2) < d_X` (i.e., the upper-bound
  hypothesis holds everywhere).
- **1 / 200 rows** has `min_wt(H_2) = d_X` (tight; n=60, d=2 minor
  instance).
- **199 / 200 rows** have `min_wt(H_2) > d_X` (strictly above).
- Worst (smallest) ratio: 1.0 (the tight case).

So `min_wt(H_2) ≥ d_X` looks like a **robust upper-bound inequality**,
not just a Bravyi-table coincidence.

## 5. Mechanism (why the direction is wrong)

The inequality `min_wt(H_2) ≥ d_X` is structural and now understood:

**Lemma**: For any `γ ∈ H_2(K(A, B)) = Ann(A) ∩ Ann(B)`, the pair
`(γ, 0) ∈ F_2[G]^2` is in `ker(H_X)`:

```
H_X · (γ; 0) = M_A · γ + M_B · 0 = 0
```

(since γ ∈ Ann(M_A) = Ann(A)). So `(γ, 0)` is a candidate Z-codeword.
It is non-trivial (i.e., not in `row(H_Z)`) **provided** `γ ∉ B · Ann(A)`,
which holds generically. Symmetrically, `(0, γ)` is also a candidate
Z-codeword via the Ann(B) inclusion. Both pairs have weight `wt(γ)`.

Therefore:

    d_Z ≤ min_wt(H_2 \ trivial)  ≤  min_wt(H_2)

For BB codes, d_X = d_Z by polynomial symmetry, so:

    d_X ≤ min_wt(H_2)

**This is the WRONG direction for a Family D lower bound.** The
construction `γ ↦ (γ, 0)` UPPER-bounds d_X via explicit weight-`wt(γ)`
Z-codewords from H_2 elements. To LOWER-bound d_X via H_2 would require
an embedding `ker(H_X) ↪ (something involving H_2)` that's weight-
preserving in the *reverse* direction — and no such embedding is
suggested by the module structure.

## 6. Why "natural" module-theoretic invariants fall this way

This negative result generalizes. **F_2[G]-module structure controls
DIMENSIONS, not WEIGHTS**, and Hamming weight is a property of the
chosen F_2-basis (the standard `{e_g : g ∈ G}` basis), NOT a module
invariant.

Concretely: F_2[G]-modules `M`, `M'` can be isomorphic (as modules) but
have *very different* minimum Hamming weights in their natural
realizations as subspaces of `F_2[G]^d`. For example, this attempt
established:

- `H_0(K) = F_2[G]/(A,B)` and `H_2(K) = Ann(A) ∩ Ann(B)` are
  **F_2[G]-module isomorphic via Frobenius duality** (since F_2[G] is
  Frobenius for G finite, the duality
  `Hom_{F_2[G]}(F_2[G]/I, F_2[G]) ≅ Ann(I)` is module-natural).
- Yet `min_wt(H_0) = 1` (for gross — any e_i ∉ (A,B) gives a
  weight-1 coset rep), while `min_wt(H_2) = 32`.

So **module isomorphisms can scale min-weight by factor 32×** in this
example. Any candidate lower bound on d_X using only F_2[G]-module
structure of (A, B) faces this obstacle.

This is the seed of a §6m obstruction (proposed; not yet formalized):

> **§6m (proposed)**: Any F_2[G]-module-theoretic invariant of (A, B)
> that is preserved under F_2[G]-module isomorphism is necessarily a
> dimension-class quantity (and thus subject to §6h category error) or
> a non-numerical invariant (e.g., the isomorphism class itself). Min
> Hamming weight of a submodule is not such an invariant: Frobenius-
> dual isomorphic modules can differ in min weight by O(|G|) factors.
> Therefore, no closed-form lower bound `d_X ≥ f(A, B, G)` exists where
> f is computable from the F_2[G]-module structure of (A, B) alone.

This is stronger than §6h (which only rules out dimension-RHS): it
rules out *any* module-theoretic LHS as well.

The escape route would be: a bound `d_X ≥ f(A, B, G, ι)` where ι is
some *non-module-theoretic* extra data (e.g., a specific F_2-basis, a
covering or chain-map structure, a metric). Bounds in Families B-C
(BCH, lifted-product, Cayley) use such extra data — but they're
already blocked by §6j, §6k, §6l. Lifted-product (Family B) has the
most potential surviving structure but no closed-form bound exists in
the literature (round-2 v1 §2 finding).

## 7. What survives from this attempt

| Output | Type | Where |
|---|---|---|
| `family_d_v1_koszul_h2.py` (5-instance probe) | Implementation | `scripts/` |
| `family_d_v1_koszul_h2_corpus.py` (corpus extension) | Implementation | `scripts/` |
| The `(4/9)|G|` Bravyi-family pattern | Empirical observation | `result.md` §4 |
| Mechanism for `min_wt(H_2) ≥ d_X` | Lemma (informal) | `result.md` §5 |
| §6m candidate (weight ≠ module invariant) | Proposed obstruction | `result.md` §6 |

The `(4/9)|G|` pattern is striking enough to warrant follow-up: it
suggests a clean closed-form expression for `min_wt(H_2)` as a
function of `(wt(A), wt(B), G)`. Even if it doesn't bound d_X, it's a
new computable feature of BB codes, in the spirit of `w_1` (round 1)
and `a_O_y_spread` (round 2 v1) — neither of which bound d but both
of which are reusable invariants. Documented for future v3+ work.

## 8. Recommendations for next session

### Top recommendation: pivot to §6m write-up

The 4d direction was a "cheap probe" — and it ruled itself out cleanly.
More importantly, the **mechanism** of failure (weight ≠ module
invariant) suggests an obstruction that may apply to **all of Family
D** (4a Hilbert series, 4b regularity, 4c Anick), not just 4d.

Specifically:
- 4a (Hilbert series of `syz(A, B)`) gives DIMENSIONS at each graded
  piece, not weights. Even under the "augmentation grading"
  (Hamming weight as filtration), the Hilbert function of the filtered
  module is a dimension count, not a min-weight quantity. Same §6m
  obstruction applies.
- 4b (Castelnuovo-Mumford regularity) bounds DEGREES of generators in
  a minimal free resolution; degree is module-natural, but the
  translation degree-to-Hamming-weight is exactly the §6m problem.
- 4c (Anick resolution) provides differentials whose ENTRIES live in
  F_2[G]; min Hamming weight of an entry is not module-natural.

**Suggested next session**: write up §6m formally, with the F_2[G]-
module-isomorphism argument as a proof sketch. Add to
[obstructions.py](../../../experiments/bb_lab/src/bb_lab/obstructions.py)
as `_fires_6m(c, i)` predicate (true when `c.family == MODULE_THEORETIC
or SYZYGY` and `c.rhs_type == WEIGHT` without `c.uses_non_module_data`).

If §6m formalizes cleanly, this combined with §6h-§6l would constitute
a **publishable structural-impossibility theorem**: "No closed-form
distance lower bound for BB codes exists in any of the natural algebraic
families." That would be the moonshot deliverable.

### Lower-priority alternatives

- 4a (Hilbert series under augmentation): try once for completeness,
  even though §6m likely fires. If the Hilbert series of `syz(A,B)`
  under the radical filtration shows an unexpected weight bound, this
  attempt would be falsified — but expect it to hit the same wall.
- 4c (Anick resolution): implement, but expect §6m to fire similarly.
  The Anick resolution provides MODULE structure, not weight structure.
- 4e (Brouwer-Zimmermann / probabilistic): not strictly Family D but
  module-aware. Might give a tighter UPPER bound than current
  baseline. Useful for the corpus but doesn't help with the headline
  lower-bound goal.

### Probabilistic bound territory

A genuinely fresh direction: BB codes have **non-trivial automorphism
groups** (G acts on F_2[G] by translation, and stabilizes (A, B) for
some specific automorphism subgroup). The Aut-group-induced WEIGHT
ENUMERATOR of the code IS a non-module-theoretic invariant. Could
this give a structural lower bound? Not yet investigated; needs a
separate hypothesis.

## 9. Honest framing

This first session of round-2 v2 closed direction 4d cleanly as a
negative result. The cheap-probe expectation (1 session) was met
exactly: hypothesis formulated, implemented, tested empirically on
both small (5-instance) and large (200-instance) datasets, mechanism
understood, generalization to §6m identified.

The negative result is **first-class output** per the moonshot framing
(handoff §1). Specifically:

- The §6m candidate is the strongest result: it potentially closes the
  entire Family D direction in a single structural argument.
- The `(4/9)|G|` pattern is a new computable feature that survives,
  even though it doesn't bound d.
- The mechanism (Frobenius-dual modules with different min weights) is
  a precise statement that could be the proof core of §6m.

Time spent: ~3 hours (literature reread, hypothesis, two probes,
mechanism, write-up).

## 10. Reproducibility

```bash
cd experiments/bb_lab
uv sync --extra dev

# Reproduce the Bravyi-table probe.
uv run python scripts/family_d_v1_koszul_h2.py

# Reproduce the 200-row corpus check (requires bb_instances.duckdb).
uv run python scripts/family_d_v1_koszul_h2_corpus.py

# Verify the §6 obstruction registry still classifies syzygy-family
# weight-RHS candidates as PROCEED (i.e., §6m hasn't been added yet):
uv run bb-lab classify --family syzygy --rhs weight \
    --name "Koszul H_2 minweight" --bound "d_X ≥ min weight in H_2"
```

## 11. Lean target (deferred to round-2 v3)

If a future direction produces a real lower bound, the Lean target
remains
[`QEC/Stabilizer/Framework/Homological/BBChainComplex.lean`](../../../QEC/Stabilizer/Framework/Homological/BBChainComplex.lean).
A `Syzygy.lean` sister file would house Family D bounds. No Lean was
written for this attempt — the result is empirical / negative, not yet
ripe for formalization.
