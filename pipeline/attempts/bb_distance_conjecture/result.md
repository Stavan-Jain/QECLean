# Result — Tier-3 verdict on the Jacobson-radical BB-distance conjecture

**Verdict: FALSIFIED.**

The conjecture

```
d_X(BB(G, A, B)) ≥ Σ_{O ∈ V_A ∩ V_B} |O| · min(μ_O(A), μ_O(B))
```

does not survive adversarial testing. The bound exceeds `d_exact` on
**407 of 3 894** corpus rows (10.5%) and on the smallest Bravyi instance
(`[[72, 12, 6]]`). It is not tight on the gross code, contrary to the
Tier-3 spec's seed claim.

## What the spec got wrong

The Tier-3 spec asserted that the bound on gross is `3 · 2 · min(2,2) = 12`,
based on a count of 3 jointly vanishing orbits. This is incorrect:
- gross has 3 orbits where `A` vanishes (y-axis nontrivial cube-roots)
- gross has 3 orbits where `B` vanishes (x-axis nontrivial cube-roots)
- the intersection is only **2 orbits** (the "diagonal" and "anti-diagonal"
  cube-root characters where BOTH α ≠ 0 AND β ≠ 0)

So the conjecture's bound on gross is `2·min(2,2) + 2·min(2,2) = 8`,
giving a gap of 4 to actual d=12 — not tight. T2.2 itself explicitly
identified the joint vanishing as 2 orbits ("the 2 orbits {(1,1), (2,2)}
and {(1,2), (2,1)} — the 'diagonal' and 'anti-diagonal' cube-root
characters"), so this was a counting error in the Tier-3 spec, not a
property of T2.2's empirical observation.

## Why the conjecture fails

Two structural reasons.

### Reason 1: It overcounts in CSS quotient

`d_X = minwt(ker(H_Z) \ rowspan(H_X))`, a **quotient** of `ker(H_Z)` by
the X-stabilizer rowspan. The conjecture's sum `Σ |O| · min(μ_A, μ_B)`
counts dimensions of `ker M_A ∩ ker M_B` in the **semisimple-quotient**
sense, but does not subtract the part of that intersection killed by
`rowspan(H_X)`. When A and B are algebraically close (especially `A = B`),
most of `ker M_A ∩ ker M_B` lies in the stabilizer rowspan and contributes
nothing to nontrivial logicals.

Worst case: `G = Z_6 × Z_6, A = B = 1 + y² + y⁴`. The bound says d ≥ 24,
actual d = 2. Gap = -22. Four such "y-only" instances exist in the
corpus.

### Reason 2: Mu can exceed real weight contributions

For weight-w polynomials A landing deep in the 2-Sylow radical (e.g.
`(1+y)^k` factors), μ can grow without limit in `|G_2|`. The bound is
then |O| times this large μ, but a low-weight logical from these
"deep-radical" elements remains low-weight because the radical filtration
is on dimensions, not on Hamming weights. There's no direct mechanism
in the conjecture's statement that ties μ to Hamming weight.

## What survives

The **operational invariant** μ_O(A) is well-defined and computable:
it equals the F_{2^|O|}-dimension of the kernel of multiplication by
the projected polynomial in the local component. This invariant satisfies
the consistency identity

```
dim_{F_2} ker M_A  =  Σ_O |O| · μ_O(A)
```

which is a CSS-relevant linear-algebra fact, not a conjecture. The code
in `experiments/bb_lab/src/bb_lab/algebraic_features.py` computes μ_O
correctly (18 unit tests, including direct verification of `dim ker M_A`
sum-formulas on Z_3, Z_4, Z_3×Z_3, Z_3×Z_5, Z_4×Z_3, Z_4×Z_6, Z_6×Z_6
groups).

This μ-invariant is still a useful **feature** for the corpus — codes
within the same group_struct with the same vanishing signature but
different μ-signatures are algebraically distinct, and this may yet
predict distance via a *different* functional form than the falsified
linear-sum one.

## What's next

**Do not formalize this conjecture in Lean (Tier 4).** It is false; a
Lean proof would necessarily fail, and a counterexample-Lean proof
isn't an interesting deliverable.

**For Tier 2 / 3 refiners**:

1. **Quotient-aware refinement**. Replace `Σ |O| · min(μ_A, μ_B)` with
   `dim_{F_2} (ker M_A ∩ ker M_B) − dim_{F_2}(rowspan(H_X) ∩ ker M_A ∩ ker M_B)`.
   This is `k_quasi` — the dimension of the logical-X coset space, which
   IS related to d_X via `d_X ≤ minwt(coset reps)` — still an upper
   bound, not a lower bound. So the direction of the conjecture is
   wrong anyway: a dimension count gives ceilings (upper bounds), not
   floors (lower bounds), on minimum weight.

2. **Hamming-weight-aware refinement**. The conjecture as stated mixes
   "dimensions" (`Σ |O| · μ`) with "weights" (`d_X`). To get a lower
   bound on d_X, one needs to argue that **every** low-weight logical
   must use ≥ k qubits — a dual to the dimension count, not the dimension
   count itself. The natural shape is a Singleton-type or BCH-type
   bound: "if A vanishes on an orbit with character order d, then any
   logical's BB-block weight is ≥ some function of d". The Camion BCH
   analog and the Kovalev–Pryadko Tillich–Zémor bound are the existing
   members of this family — both *provably loose* on engineered BB codes
   (see `pipeline/attempts/gross/result.md`).

3. **Better seed observation**. T2.2's correct empirical observation —
   that the kernel dimension factors as `Σ |O| · μ_O` — describes
   how the *k* of the code relates to algebraic structure (since
   `k = 2 · dim(ker M_A ∩ ker M_B)`). It does NOT describe the *d*
   of the code. Future Tier-2 conjectures should aim at d-relevant
   invariants (e.g. per-orbit dual-classical distance, weight-enumerator
   structure, Newton-polytope diameter) rather than purely dimension-
   counting invariants.

## Most informative finding

For a future Tier-2 refiner or Tier-4 Lean agent: **the conjecture's
direction is wrong**. Dimension counts give upper bounds on coset
sizes, hence indirect upper bounds on logical operator count, but
they don't directly give lower bounds on weight. A real lower bound
on d_X must be a "every nonzero logical has weight ≥ something" argument
that goes via the structure of the *symplectic / dual-code* layer, not
the algebraic projection layer. The cleanest open direction in the
surveyed literature is closing the gap

```
⌈d_A^⊥ / c⌉ ≤ d_X ≤ d_A^⊥
```

(Lin–Pryadko Stmt 12) for `c = |G_a ∩ G_b| > 1`, which is the gross
regime. **None** of the surveyed papers give a deterministic lower
bound tight on engineered BB codes.

## Implementation status

- `algebraic_features.jacobson_radical_depth(poly, orbit, G)` — operationally
  defined, mathematically clean. 18 unit tests pass.
- `algebraic_features.jacobson_radical_bound(A, B, G)` — implements
  the conjecture exactly as stated. 130 corpus + Bravyi + adversarial
  results confirm the bound is invalid.
- No modifications to `features.py`, `canonical.py`, `enumerate_bb.py`,
  `cli.py`, or `scripts/tier2_explore.py` (per hard constraints).
- Full test suite passes: `uv run pytest -m "not slow" -q` → 130 passed,
  2 skipped, 3 deselected (up from 112 before T3.1).

## Files

- `experiments/bb_lab/src/bb_lab/algebraic_features.py` — added
  `jacobson_radical_depth`, `jacobson_radical_bound`,
  `g_odd_frobenius_orbits`, helpers.
- `experiments/bb_lab/tests/test_jacobson.py` — 18 tests.
- `experiments/bb_lab/scripts/tier3_corpus_sweep.py` — corpus sweep
  driver.
- `experiments/bb_lab/scripts/tier3_bravyi_benchmark.py` — Bravyi table.
- `experiments/bb_lab/scripts/tier3_adversarial.py` — adversarial
  random search.
- `experiments/bb_lab/notes/T3.2_corpus_sweep.md` — corpus sweep
  results.
- `experiments/bb_lab/notes/T3.3_bravyi_benchmark.md` — Bravyi-table
  results.
- `experiments/bb_lab/notes/T3.4_adversarial.md` — adversarial results.
- `pipeline/attempts/bb_distance_conjecture/{state.yaml, hypothesis.md,
  evidence.md, result.md}` — this attempt.
