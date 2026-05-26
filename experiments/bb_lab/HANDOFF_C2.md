# bb_lab Handoff C-v2 — propose a distance bound using w_μ

C-v1 landed cleanly: `radical_weight.py` defines a weight-refined
Jacobson-radical invariant `w_μ(A, O)` satisfying (W1)–(W4) of
`HANDOFF_C.md`. **You are now extending it into a distance bound.**

This document is the second in the C-series. Required reading
order: `HANDOFF.md` → `HANDOFF_C.md` → C-v1 deliverable notes
(`notes/Cv1_{literature,design,results}.md`) → this document.

---

## 1. Where C-v1 left things

The relevant numerical takeaways from the C-v1 deliverable:

**Gross numbers**:

| Orbit | μ_O | w_1 | w_2 | w_3 | w_4 | w_5 |
|---|---|---|---|---|---|---|
| 3 vanishing orbits (each) | 2 | **36** | 36 | 36 | 36 | 48 |
| 2 non-vanishing | 0 | ∞ | ∞ | ∞ | ∞ | ∞ |

By the (x↔y) symmetry, the same table holds for `grossA` and `grossB`.

**The number-theoretic coincidence**: gross has `d = 12`, and
`36 / 3 = 12`. The factor of `3` matches **exactly** the
Lin–Pryadko `c = [G_a : N]` index from the gross moonshot (where
`G_a = ⟨supp(grossA)⟩ = Z_4 × Z_6`, `G_b = ⟨supp(grossB)⟩ = Z_12 × Z_2`,
`N = G_a ∩ G_b = Z_4 × Z_2`, so `[G_a : N] = [G_b : N] = 3`).

This is **not yet** a tested conjecture — it's a single-instance
coincidence that needs falsification. That's your job.

---

## 2. The candidate conjecture (your falsification target)

For a BB code `BB(G, A, B)`:

$$d_X(\mathrm{BB}(G,A,B)) \;\geq\; \frac{1}{c(A,B)} \cdot \min_O\;\min\!\bigl(w_1(A, O),\; w_1(B, O)\bigr)$$

where:

- The outer `min_O` ranges over **all Frobenius orbits `O ⊂ Ĝ`**
  for which both `w_1(A, O)` and `w_1(B, O)` are finite (i.e., both
  polynomials vanish on `O`). If no such orbit exists, the bound is
  vacuous (or take the value to be `0`).
- `w_1(A, O)` is C-v1's invariant at radical level 1, restricted
  to the orbit-`O` local-ring component.
- `c(A, B) := [G_a : G_a ∩ G_b]` is the LP `c`. Note `c(A,B) =
  c(B,A)` by `[G_b : G_a ∩ G_b] = [G_a : G_a ∩ G_b]` when the BB
  code is non-degenerate as a *pair* (jointly).

Plug-in for gross: `w_1 = 36`, `c = 3`, bound = `36/3 = 12 = d`.
**Tight.**

This is the **primary candidate**. If it falsifies, try the
alternatives in §6 below before declaring the direction dead.

---

## 3. Why this is plausibly novel

The conjecture has the **shape** of Lin-Pryadko Statement 12
(`d ≥ d_A^⊥ / c`), but the numerator is the C-v1 radical-aware
quantity, not the semisimple `d_A^⊥`. The LP Statement 12 numerator
for gross is `d_A^⊥ = 6`, giving bound `6 / 3 = 2` — loose by 10.
The C-v1 numerator for gross is `w_1 = 36`, giving bound `36 / 3 = 12`
— tight.

**The hypothesis**: substituting C-v1's `w_1` for LP's `d_A^⊥`
"unlocks" the non-semisimple structure of gross. This dodges the
§6j wall by construction — `w_1` is defined exactly on the
Jacobson-radical filtration that the character-theoretic family
ignores.

If the conjecture survives corpus testing, this is plausibly a new
result. **Do the literature check first** (per §6a discipline):
search "Loewy weight quantum code distance lower bound" and
"radical filtration cyclic code minimum distance". Document in
`notes/Cv2_literature.md`. The most likely "almost-this-already" is
the Andriatahiny ([arXiv:1601.07633](https://arxiv.org/abs/1601.07633))
line that C-v1's literature check already surveyed — recheck
specifically whether their rad^μ bounds compose with an LP-style
denominator in any prior work.

---

## 4. Your specific tasks

### T C-v2.1 — Pre-implementation literature check

~half-day. As above.

### T C-v2.2 — Implement `bb_radical_bound(A, B, G)`

Add to `src/bb_lab/radical_weight.py` (extending C-v1's module, not
modifying it destructively — add new functions). New functions:

- `joint_support_subgroup_index(A: Poly, B: Poly, G) -> int` —
  computes `c = [G_a : G_a ∩ G_b]`. Uses `degeneracy.supp_generates_G`
  machinery already in place.
- `bb_radical_bound(A: Poly, B: Poly, G) -> int` — returns the
  conjectured lower bound. Returns `0` if the bound is vacuous
  (no jointly-vanishing orbit).
- `bb_radical_bound_alt(A, B, G, formulation: str)` — provides the
  alternatives in §6 below for easy A/B testing.

Add tests in `tests/test_radical_weight.py` (extending C-v1's
tests):

- Gross: `bb_radical_bound(grossA, grossB, Z_12×Z_6) == 12` exactly.
- Smaller Bravyi instances: bound is non-trivial.
- An obvious "should-be-loose" case (e.g., random BB pair where
  Lin-Pryadko Stmt 12 is known to be tight) — bound is consistent.

### T C-v2.3 — Corpus sweep

Write `scripts/cv2_corpus_sweep.py`. For every labeled row in the
corpus:

1. Compute `bb_radical_bound(A, B, G)`.
2. Check whether `d_exact ≥ bound`. **A single violation falsifies
   the conjecture.** Report violations, including row id,
   polynomials, computed bound, actual d.
3. Tightness statistics: tight count, mean looseness, per-group
   breakdown.

**Critical**: the corpus has rows where `c = 1` (non-degenerate).
For these, the bound reduces to `min w_1` (no denominator). Make
sure your implementation handles this edge case.

Save to `notes/Cv2_corpus_sweep.md`.

### T C-v2.4 — Bravyi table

Compute the bound for all five Bravyi instances. The *required*
result on gross is `bound == 12`. The other four must satisfy
`bound ≤ d_published` to be consistent. Document tightness:

| code | actual d | C-v2 bound | gap | verdict |
|---|---|---|---|---|

Save to `notes/Cv2_bravyi_table.md`.

### T C-v2.5 — Tightness characterization

For corpus rows where the bound is tight: what's structurally
distinct? Decision-tree on features (use the T2.1 classifier
script as template). If you find a clean characterization, that's
the **structural condition `S`** the Tier 3 skeptic will gate on,
and the C-v3 proof will assume.

Save to `notes/Cv2_tightness.md`.

### T C-v2.6 — Verdict + artifact

Create `pipeline/attempts/bb_distance_conjecture_radical_weight/`
with `state.yaml`, `hypothesis.md`, `evidence.md`, `result.md`.

Possible verdicts (in order of desirability):

- **survives-tight-on-gross**: zero corpus violations,
  `bound(gross) == 12`. → C-v3 (formal proof attempt).
- **survives-near-tight**: zero corpus violations, `bound(gross) ∈
  {8, 9, 10, 11}`. Partial win; document gap, try alternatives
  from §6, iterate. Still progress.
- **falsified-by-corpus**: some row violates. Document concretely.
  Try alternative formulations from §6 before declaring the
  direction dead.
- **survives-but-loose-on-gross**: zero violations, `bound(gross)
  ≤ 8` (same as previous rounds). Document and shelve.
- **inconclusive**: implementation bug or definitional ambiguity
  encountered. Document and ask.

---

## 5. The alternative formulations (try if primary falsifies)

If primary `(1/c) · min_O min(w_1(A,O), w_1(B,O))` falsifies on
some corpus row, **don't immediately shelve**. Try in order:

**Alt-A. Restrict to joint vanishing**:

$$d_X \;\geq\; \frac{1}{c} \cdot \min_{O \in V_A \cap V_B} \min(w_1(A,O), w_1(B,O))$$

Same as primary but only sum over orbits where *both* A and B
vanish. Smaller orbit set → potentially smaller bound but stronger
constraint.

**Alt-B. Multi-level via μ**:

$$d_X \;\geq\; \frac{1}{c} \cdot \min_{O, \mu \leq \min(\mu_O(A), \mu_O(B))} \frac{\min(w_\mu(A,O), w_\mu(B,O))}{\mu}$$

The intuition: deeper radical levels see "more structure" but the
divisor `μ` accounts for it. For gross at `μ=1`, this gives
`36 / 3 / 1 = 12`; at `μ=2`, `36 / 3 / 2 = 6`. The min would be
the smaller, so this is potentially looser.

**Alt-C. Sum across vanishing orbits**:

$$d_X \;\geq\; \frac{1}{c} \cdot \sum_{O \in V_A \cap V_B} \min(w_1(A,O), w_1(B,O))$$

Risky — sums can grow large. For gross: `(1/3) · 3 · 36 = 36`,
**violates** `d = 12`. So this one's dead-on-arrival; included as
a sanity check that you understand which variants are violating.

**Alt-D. Symmetric weight**:

$$d_X \;\geq\; \frac{1}{c} \cdot \sqrt{\min_O w_1(A,O) \cdot w_1(B,O)}$$

Geometric mean instead of min. Less common in coding theory but
worth a check.

**Alt-E. Reciprocal-form**:

$$\frac{1}{d_X} \;\leq\; c \cdot \max_O \frac{1}{\min(w_1(A,O), w_1(B,O))}$$

Equivalent rewrite of primary in case the iteration is cleaner.

Document which alternatives you try in `notes/Cv2_alternatives.md`.

---

## 6. Side-quest: investigate the `per_orbit_dual_distance` bug

C-v1 surfaced an interesting observation: `weight_invariants.per_orbit_dual_distance`
(from T2R2) uses G_2-fiber-summed character constraints, while C-v1's
`w_1` uses proper per-fiber. For gross, `per_orbit_dual_distance ==
12` while `w_1 == 36` — a factor of 3 difference, suspiciously equal
to gross's `c`.

**The fiber-summing in T2R2's implementation may have been
implicitly dividing by `c`.** If so:

- T2R2's `per_orbit_dual_distance` is actually `w_1 / c_orbit` in
  disguise — a quantity that's *already shape-correct* for the
  conjecture.
- The T2R2 round didn't see this because `per_orbit_dual_distance`
  on gross gives 12, and `(1/c_joint) · 12 = 4` (loose by 8), so it
  didn't surface as tight.
- But if you reinterpret `per_orbit_dual_distance` as `w_1 / c`,
  then `d_X ≥ per_orbit_dual_distance` directly would imply
  `d ≥ 12` on gross — the right answer.

**This may be the most important investigation in C-v2.** Either:

- (a) Confirm the fiber-summing-as-division interpretation. If
  correct, then T2R2 actually had the bound already, just
  misinterpreted it. Document, and the C-v2 conjecture becomes
  *exactly* `d_X ≥ per_orbit_dual_distance` (post-bugfix).
- (b) Show the interpretation is wrong. Then `per_orbit_dual_distance`
  is genuinely buggy and should be fixed as part of C-v2's
  deliverable. The C-v2 conjecture using `w_1` stands as the
  novel quantity.

Either outcome is informative. Save to `notes/Cv2_perodual_investigation.md`.

---

## 7. Hard constraints

- Read-only on `data/bb_instances.duckdb` via `Corpus(read_only=True)`.
- **Don't modify** any file outside `src/bb_lab/radical_weight.py`
  (extending only), `src/bb_lab/weight_invariants.py` (if and only
  if the per_orbit_dual_distance investigation produces a clear
  fix), and new files under `scripts/`, `notes/`, `tests/`, and
  `pipeline/attempts/bb_distance_conjecture_radical_weight/`.
  Especially **don't touch** `algebraic_features.py`,
  `degeneracy.py`, `ht_roos.py`, `homological_bounds.py`.
- **§6h–§6k still apply.** The proposed conjecture's RHS is a
  weight invariant (good), and the conjecture's domain is *all*
  BB codes (not gated by non-degeneracy or semisimplicity), so it
  dodges §6i/§6j/§6k. **But verify this every time you propose an
  alternative.**
- Tests must pass: `uv run pytest -m 'not slow' -q` from
  `experiments/bb_lab/` (~247+ tests). Your additions should grow
  the count.
- **Don't commit** unless explicitly asked. The C-v1 agent followed
  this discipline (HANDOFF_C didn't request commit); you should too
  unless asked.

---

## 8. Risks

- **The primary conjecture might be a single-instance coincidence**:
  the gross factor-of-3 might not generalize. Possible: corpus has
  many rows where the conjecture violates badly. Run §3 corpus
  sweep early and report numbers in the first day of work.
- **Joint vanishing orbits may be empty** for many rows. If so,
  the primary conjecture is vacuous on those rows. Alt-A or Alt-C
  may have non-vacuous behavior.
- **`c` may not be well-defined or computable** when one of
  `supp(A)`, `supp(B)` doesn't generate a full sub-product. The
  C-v1 `degeneracy.py` machinery handles the "generates G" case;
  for proper subgroup intersections, you may need to extend.
- **The Lean formalization (eventually C-v3) requires `c`'s
  invariance** under the BB equivalence group. C-v1 already
  dropped F₂[G]-unit invariance, but the conjecture you're testing
  uses `c` which IS unit-invariant (it's a subgroup invariant).
  If the proof you eventually attempt requires combining the two,
  the equivalence-group story will need to be unified.

---

## 9. Out-of-scope for C-v2

- C-v3 (formal proof). C-v2's deliverable is "the conjecture
  survives or falsifies, with a structural condition if needed."
- C-v4 (tighten to exact d). C-v2 just needs *some* tight-on-gross
  result; closing the remaining gap is for later.
- Lean implementation. This is downstream of C-v3.
- Anything that requires modifying `algebraic_features.py`,
  `degeneracy.py`, etc. (per §7 above).
- Re-doing C-v1's literature work — extend it, don't repeat it.

---

## 10. First-day checklist

1. Read `HANDOFF.md` (§6h–§6k especially).
2. Read `HANDOFF_C.md`.
3. Read your own C-v1 outputs: `notes/Cv1_{literature,design,results}.md`.
4. Read this document end-to-end.
5. `cd experiments/bb_lab && uv sync --extra dev && uv run pytest -m 'not slow' -q` — confirm 247+ passing.
6. Skim `radical_weight.py` to refresh the `w_μ(A, O)` API.
7. Reproduce the gross table from `scripts/cv1_gross_table.py` —
   make sure `w_1 = 36` is what you actually get.
8. Manually compute `c(grossA, grossB, Z_12 × Z_6) = 3`. Verify.
9. Then implement T C-v2.2.

---

## 11. Expected timeline + variance

- **First survivable result**: 2–4 days. The primary conjecture
  is concrete enough to test quickly. If it survives the corpus
  sweep, the §C-v2.4 / .5 / .6 work follows in days.
- **First falsification**: also 2–4 days, if it comes early.
  If it does, you'd cycle through the alternatives in §5, each
  taking another day of corpus testing.
- **C-v2.6 verdict**: 1–2 weeks total under honest effort.

Risk-weighted: ~40% probability the primary conjecture survives
the corpus (zero violations). ~25% probability it's *tight on
gross AND survives corpus*. The remaining mass is split between
"falsified by corpus" (~30%) and "survives but loose on gross"
(~5%).

These are subjective priors. If the actual evidence is much
stronger or weaker than these numbers suggest, that's itself
informative.

---

## 12. Pointer to the broader program

After C-v2 lands (in whatever form):

- **survives-tight-on-gross** → C-v3 handoff (`HANDOFF_C3.md`) for
  the formal proof attempt against the structural condition `S`
  identified in §C-v2.5.
- **falsified-by-corpus** → if alternatives in §5 don't survive
  either, document the obstruction in HANDOFF.md as §6l, and
  decide whether to attempt C-v2 round 2 with a different
  conjecture shape or shelve.
- **survives-but-loose** → document, shelve, and consider whether
  the per_orbit_dual_distance side-quest (§6) yields a separate
  contribution.

Good luck. The C-v1 gross numbers are the most promising signal
of the program so far. The factor of 3 might be real.
