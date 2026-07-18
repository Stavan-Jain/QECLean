# bb_lab Handoff C — Option C-v1: weight-aware Jacobson-radical filtration
> **[Historical research record — extracted 2026-07-18 from the retired
> orchestration branch `bb-lab-v0` during branch cleanup; never previously
> merged.]** This is an original proposal/handoff document (2026-05-26) for one
> phase of the round-1 C-series (weight-aware Jacobson-radical filtration). The
> executed deliverables have long been on main — `notes/Cv1_*.md`,
> `notes/Cv2_*.md`, `notes/Cv3_*.md`, `notes/T3_CV3_*.md`,
> `notes/Cv4_R4_falsified.md`, and
> `pipeline/attempts/bb_distance_conjecture_radical_weight{,_narrow,_narrow_tier3}/`
> — and cite this document by section throughout; it is extracted to repair
> those references and preserve the proposal-side record (priors, stop
> conditions, alternative formulations). The conjecture line it proposes was
> ultimately **falsified** (C-v2 by corpus/Bravyi sweep; C-v3-as-tight by
> Tier-3 batteries; R1+R4 by the Z₃×Z₁₅ adversary). Note: references here to
> "HANDOFF.md §6l" mean an elementary-abelian-G_odd write-up that was never
> merged; that content lives in
> `pipeline/attempts/bb_distance_conjecture_radical_weight/result.md`, while
> main's actual `HANDOFF.md` §6l (from the later round-2 line) is a different
> obstruction (Cayley-spectral vacuity). Nothing here is a live task.


You are continuing a research program documented at length in
`HANDOFF.md`. Read that document **before** this one — it carries the
overall 4-tier architecture, the corpus + tooling, and §§6h–6k which
record five rounds of elimination work. **This document narrows the
focus to one specific open mathematical direction.**

## 1. What's settled by prior work — don't repeat any of it

Five rounds of structured elimination have exhausted the classical
toolkit. The current state, in increasing structural specificity, is
recorded in `HANDOFF.md`:

- **§6h**: dimension counts on the RHS of `d ≥ …` are wrong-typed
  (they bound `k`, not `d`). **Round 1 Jacobson conjecture
  falsified** at 10.5% corpus violations.
- **§6i**: every Bravyi instance has `[G:⟨supp(A)⟩] = 3` — they
  are degenerate. Filtering on non-degeneracy excludes the
  engineering target. **Round 2.5 conditional Jacobson shelved.**
- **§6j**: every published character-theoretic distance bound for
  abelian codes (Camion, Sabin–Lomonaco, Saints–Heegard, BBCS 2016,
  BG-S 2017) requires F₂[G] **semisimple**. Gross has `|G|=72`
  (even) so F₂[G] is non-semisimple. **The entire family is
  structurally blind to gross.** Jitman–Ling 2013 is the
  load-bearing citation.
- **§6k**: cover-graph chain-map bounds (Symons–Rajput–Browne 2025,
  the homological family) require `gcd(h, char F) = 1` where `h` is
  cover degree. Gross is the h=2 cover of `[[72,12,6]]` over F₂, so
  chain-map injectivity fails. **Categorically different framework,
  same number-theoretic 2-divisibility blocker as §6j.**

**The recurring pattern**: `char F = 2` divides a critical integer
parameter of gross's construction in every approach tried so far,
either through `|G|` (Fourier family) or through cover degree `h`
(chain-map family). Bravyi's `|G|=72=2³·3²` over F₂ appears
deliberately adversarial against bounds that hinge on 2-coprimality.

**This narrows the surviving research directions.** The one
mathematical object that bypasses the 2-divisibility wall by
construction — and which is also absent from the literature — is
the **Jacobson radical of F₂[G] itself, refined by Hamming weight
rather than by F₂-dimension**. That is option C-v1. You are
attempting it.

---

## 2. The specific mathematical goal

For a finite abelian group `G` with `2 | |G|` (so F₂[G] is
non-semisimple), the Jacobson radical `J = rad(F₂[G])` is non-trivial.
The decreasing filtration

  `F₂[G] = J⁰ ⊃ J¹ ⊃ J² ⊃ … ⊃ J^t = 0`

is a chain of two-sided ideals. The dimension-graded refinement is
classical: it gives the **Loewy length** and the
dimension-weighted Jacobson depth `μ_O(A)` used in Round 1's
falsified conjecture (`Σ_O |O| · μ_O(A) = dim_F₂ ker M_A`).

**Goal of C-v1**: define a **Hamming-weight refinement** of this
filtration. Concretely:

> For each Frobenius orbit `O ⊂ Ĝ` (equivalently, each minimal
> primitive central idempotent `e_O` in the semisimple quotient
> F₂[G_odd]) and each filtration level `μ ∈ {1, …, depth(O)}`,
> define a weight invariant
>
>   `w_μ(A, O) ∈ ℤ_{≥0} ∪ {∞}`
>
> such that:
>
> (W1) `w_μ(A, O)` depends only on the BB-code equivalence class of
>     `(G, A)` (invariant under G-translation, `Aut(G)`, and
>     `F₂[G]`-unit multiplication).
>
> (W2) `w_μ(A, O)` is "weight-shaped" in the §6h sense — it is the
>     minimum Hamming weight of some nonzero element of an
>     equivalence-class-of-elements derived from `A` and the
>     filtration. Specifically: `w_μ(A, O) ∈ ℤ_{≥0}` should be the
>     **minimum |·|_H** of a nonzero element of some F₂-subspace of
>     F₂[G] determined by `(A, O, μ)`, not the **dim** of such a
>     subspace.
>
> (W3) `w_μ(A, O)` is computable from `(A, G)` in polynomial time
>     (or at least, in the same complexity class as `min_wt_ker_A`,
>     which is exponential in `dim ker(A)` brute-force but tractable
>     in our corpus's regime).
>
> (W4) `w_μ(A, O)` reduces to the right textbook quantity in known
>     limits — e.g., for `μ = 1` and semisimple `F₂[G]`, it should
>     match the classical cyclic-code dual distance `d^⊥_O(A)`
>     restricted to the orbit-O isotypical component.

**That is the entire deliverable for C-v1.** Whether `w_μ` yields
a distance bound (C-v2), whether it can be proved (C-v3), whether
it is tight on gross (C-v4) are downstream concerns; do not let
them constrain the C-v1 definition. C-v1 is its own publishable
contribution if (W1)-(W4) are satisfied with a clean definition.

---

## 3. Why this is a real mathematical question, not engineering

You will not find `w_μ` in the literature. The classical theory:

- **Modular representation theory** (Brauer characters, projective
  covers, Auslander–Reiten quivers) studies the structure of
  non-semisimple group algebras over fields of positive
  characteristic. It is **dimension-graded** throughout.
- **Coding theory's weight enumerators** study Hamming weight
  distributions of codes. They are typically applied to
  **semisimple** quotients.

The intersection — a weight-refinement of the modular-representation-
theoretic filtration — is exactly the open territory. **Plausibly**
there are related notions in:

- **Strong apparent distance** (Bernal–Bueno-Carreño–Simón 2017
  follow-up, arXiv:1704.03761) — defined on the semisimple part, but
  the *idea* of a layered weight invariant is there.
- **Projective resolution weights** of representations of F₂[G] —
  not, to my knowledge, applied to distance theory.

Two structural references to study before defining `w_μ`:

- Curtis & Reiner, "Methods of Representation Theory" — for the
  general theory of group algebras over non-semisimple base.
- Webb, "A Course in Finite Group Representation Theory" — for
  Loewy filtrations and the Jacobson radical of `kG` when
  `char k | |G|`.

---

## 4. What "satisfy (W1)–(W4)" looks like in practice

The C-v1 deliverable is a paper-quality definition plus an
implementation. A reasonable sketch of the work:

1. **Choose a candidate definition**. Multiple candidates:
   - `w_μ(A, O) := min_{f ∈ J^μ \ J^{μ+1}, f|_O · A = 0} |f|_H`
   - `w_μ(A, O) := min_{f ∈ J^{μ-1}, f · A ≡ 0 (mod J^μ)} |f|_H`
   - `w_μ(A, O) := min |f|_H over a basis of (rad R_O)^μ · A`
   
   Each captures something different about how `A` interacts with
   the radical. Pick one (or define a family parameterized by the
   choice) and commit to a specific candidate.

2. **Prove (W1) — invariance** under the BB-code equivalence group.
   Standard machinery: G-translation acts by multiplication by a
   group element (a unit in F₂[G], so it preserves `J^μ`);
   `Aut(G)` acts by ring automorphisms of F₂[G] (so it preserves
   `J^μ` and `|·|_H`); F₂[G]-units preserve `J^μ` and (up to a
   permutation of basis elements) preserve `|·|_H`. The first two
   are clean; the third is more subtle (multiplication by a unit
   is *not* in general weight-preserving — `(1+x) · 1 = 1+x` has
   weight 2 vs. `1` has weight 1).
   
   **If (W1) cannot be made true under F₂[G]-units, restrict to
   the weaker equivalence group** (drop units; just shifts +
   `Aut(G)` + swap). That's still meaningful — the corpus is
   organized under exactly that equivalence (see `canonical.py`).

3. **Prove (W2) by construction** — your definition should literally
   take the form `min |f|_H` over some F₂-subspace.

4. **Implement (W3)**. Add `bb_lab/radical_weight.py` (NEW module)
   with:
   - `jacobson_filtration(G) -> list[set]` returning the
     `J^0, J^1, …, J^t` (or a basis of each) as F₂-subspaces of
     `F₂[G]`.
   - `w_mu(A, O, mu, G) -> int` returning your invariant.
   
   For computability in the corpus regime: `|G| ≤ 144` means
   `F₂[G]` has dimension up to 144. F₂-subspace operations are
   tractable. Minimum-Hamming-weight in a `dim ≤ 22` subspace is
   doable by Gray-code traversal (already in `features.py:min_weight_in_kernel`).
   
   Test (W3) on:
   - `G = Z_4`: F₂[Z_4] ≅ F₂[x]/(x⁴ + 1) = F₂[x]/(x+1)⁴. Single
     orbit, Loewy length 4. `J^k = (x+1)^k F₂[Z_4]`. Pick `A = 1+x`
     (= `(x+1) · 1`); then `A ∈ J¹ \ J²`. Compute `w_μ` and verify
     against hand calculation.
   - `G = Z_12 × Z_6` (gross's group): compute `w_μ(grossA, O, μ)`
     for the 3 vanishing orbits.

5. **Prove (W4)** — semisimple-limit recovery. When `J = 0`
   (semisimple), `J^0/J^1 = F₂[G]` and there's nothing higher to
   filter. Show `w_1(A, O)` recovers the per-orbit dual distance
   `d^⊥_O(A)` from `weight_invariants.per_orbit_dual_distance` (T2R2).

6. **Compute the gross-code vector `(w_μ(grossA, O), w_μ(grossB, O))`**
   for every orbit O and every level μ ≤ 2. This is the numerical
   evidence that C-v1 has captured a real new invariant about gross.
   The expected gross numbers: at least one (orbit, μ) entry should
   give a value `≥ 6` to be even potentially useful for the
   downstream C-v2/v3/v4 work (recall gross's actual `d = 12`).

**Stop conditions for C-v1**:

- (a) Clean definition satisfying (W1)–(W4) + tests + a gross-numerics
  table → C-v1 done, output ready for review.
- (b) Definition is forced to drop F₂[G]-unit invariance to be
  well-defined → still acceptable; document the restriction.
- (c) After honest effort, no candidate definition can simultaneously
  satisfy (W2) and (W3) (e.g., the weight-minimum is uncomputable or
  not well-defined modulo the equivalence) → that's a publishable
  obstruction. Document and stop.

---

## 5. What's already there for you

- `experiments/bb_lab/src/bb_lab/algebraic_features.py` —
  Frobenius orbits, vanishing patterns, the (now-known-wrong)
  Jacobson-radical depth `μ_O(A)`. The orbit machinery is sound.
- `experiments/bb_lab/src/bb_lab/weight_invariants.py` —
  `per_orbit_dual_distance(A, G)` from T2R2. This is the
  semisimple-limit target for (W4).
- `experiments/bb_lab/src/bb_lab/features.py:min_weight_in_kernel(M)`
  — Gray-code minimum-weight computation in F₂-subspaces of
  dimension ≤ 22. Reuse for `w_μ` implementation.
- 222 passing tests across the lab. Your new module should add
  unit tests and not regress existing ones.

---

## 6. Hard constraints

- **Don't claim novelty without literature check** (HANDOFF §6a).
  Before writing the definition, search at least:
  - "Loewy structure weight Hamming code"
  - "modular representation theory minimum distance"
  - "Brauer character weight enumerator"
  - "abelian code radical weight"
  Document what you find in `notes/Cv1_literature.md` before
  implementing.
- **§6h rule absolutely applies.** Your `w_μ(A, O)` must be `min |f|_H`
  over some subspace, not `dim` of some subspace. If you find yourself
  writing `dim(...)` on the RHS of a definition, you've reintroduced
  the §6h footgun.
- **Read-only on the corpus DB.** `Corpus(read_only=True)` if you
  need to evaluate `w_μ` over corpus instances for sanity checks.
- **Don't modify**: any existing source file in `src/bb_lab/`. Add
  `src/bb_lab/radical_weight.py` and `tests/test_radical_weight.py`
  only. New scripts go under `scripts/`. New notes under `notes/`.
- **Don't advance to C-v2** (proposing a distance bound) until C-v1's
  (W1)–(W4) are all green and have unit tests. That's a separate
  follow-up handoff.

## 7. Risks specific to this direction

- **The definition might force weight-incompatible group action.**
  Multiplication by `(1+x) ∈ F₂[Z_n]` changes Hamming weight.
  Your weight invariant cannot be unit-invariant in general. Plan
  to document a *restricted* equivalence group (just shifts +
  `Aut(G)` + swap; drop F₂[G]-unit multiplication). This makes the
  invariant a function of more variables than the "canonical
  representative" (which dedups by all four equivalences); that's
  fine for theory but means the corpus's canonical-form-deduped
  rows may need to be re-decanonicalized for testing.

- **Loewy length is small.** For F₂[Z_2^a · m] with m odd, Loewy
  length is `a+1` (the nilpotency index of the augmentation ideal
  in `F₂[Z_2^a]`). For gross, `|G|=72=2³·3²`, so Loewy length is 4.
  Your `w_μ` has only 4 nontrivial values per orbit. This may be
  enough for a useful bound, or it may be too coarse — you'll find
  out empirically.

- **The eventual distance bound (C-v2) may still fail.** Even with
  a clean `w_μ`, the connection to BB-code distance might not work
  out. C-v1 *defines an object*; C-v2 *uses the object to bound
  distance*. The C-v1 deliverable should be evaluated on its own
  merit (a new mathematical invariant), not by whether C-v2 succeeds.

## 8. Out of scope for C-v1

- The distance-bound conjecture itself (C-v2).
- Lean formalization (C-v3 / Tier 4).
- Tightness on gross (C-v4).
- Anything in the §6h–§6k shelved regions.
- Modifying any existing module.
- Cover-graph / homological / character-theoretic frameworks
  (already eliminated by §6j and §6k).

## 9. First-day checklist for the new agent

1. Read `HANDOFF.md` end-to-end, especially §6h–§6k.
2. Read this document.
3. Run `cd experiments/bb_lab && uv sync --extra dev && uv run pytest -m "not slow" -q` — should be 222 passed.
4. Skim `src/bb_lab/algebraic_features.py` and the Jacobson section of `tests/test_jacobson.py` to absorb how the dimension-graded `μ_O` is currently computed.
5. Do the literature check (§6 above) and write `notes/Cv1_literature.md`.
6. Then start designing `w_μ`.

Expected time to a clean C-v1 deliverable, with honest effort and a
literate research agent: **2–6 weeks**, with risk-weighted variance.
The literature check alone may take a week if done seriously.

## 10. Pointer to the broader program

This handoff is for one specific direction in a much larger 4-tier
investigation. After C-v1 lands (in any of forms (a)–(c) from §4),
the next steps would be:

- C-v2: propose a distance bound `d_X ≥ F(w_μ values)`.
- C-v3: prove it on a structural sub-family.
- C-v4: tighten to gross.

Each is its own multi-week project. The 4-tier handoff structure
(`HANDOFF.md` → this document → future C-v2 handoff → …) keeps each
phase scoped.

Good luck. Even a clean (c) outcome is a real contribution.
