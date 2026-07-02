# A13 — The Bockstein equality (A12 OQ2): plan + candidate proof

**Status: session-0 (2026-07-02) — plan, a candidate half-page proof of the
full conjecture, and a 167k-pair validation sweep (all clean). Red-team of
the proof (W0) and the stratified exhaustive sweep (W1) are the next
actions; nothing below is "theorem" until W0 passes.**
Branch: `claude/a13-bockstein-equality` (off PR #53, includes A12).
Prereq reading: `A12_deck_homotopy_R.md` §1 (notation), §3 (theorem), §4
(the conjecture), §8 OQ2 (the question as posed).
Script: [`a13_bockstein_stratified_sweep.py`](../scripts/a13_bockstein_stratified_sweep.py).

## 0. The question, three equivalent ways

Notation as in A12 §1: `R̃ = F₂[G̃]`, deck `σ` of order 2, `ε = 1+σ`
(`ε² = 0`), `D = F₂[ε]/(ε²)`, Koszul complex
`K̃ : R̃ →^{(B,A)} R̃² →^{(A,B)} R̃`, base `K̄ = K̃/εK̃`, transfer LES with
connecting maps `δ₂ : H₂(K̄) → H₁(K̄)` and `δ₁ : H₁(K̄) → H₀(K̄)`,
`k = dim H₁(base)`, `k̃ = dim H₁(cover)`, `E = dim εH₁(cover)`,
`g = dim ((ε)+(A,B))/(A,B)` (so `k̃ − k = 2g`, A12 Lemma 1).

- **Q-rank.** Is `E = k̃ − k` always? (Theorem A12 gives `≥`.)
- **Q-comp.** Is `δ₁∘δ₂ = 0 : H₂(base) → H₀(base)`?
- **Q-elem.** Whenever `Az, Bz ∈ εR̃`, is
  `W := A·ε⁻¹(Bz) + B·ε⁻¹(Az) ∈ ε(A,B)`?

**Defect identity (new, sharpens the A12 `≥` into an equality).** The LES
bookkeeping of A12 §3 gives not just `E ≥ k̃−k` but

```
E − (k̃ − k) = rank(δ₁∘δ₂).
```

*(Proof: `E = dim ker δ₁ − dim(ker δ₁ ∩ im δ₂)` and
`k̃−k = dim ker δ₁ − dim im δ₂`; subtract and use
`dim im δ₂ − dim(ker δ₁ ∩ im δ₂) = dim δ₁(im δ₂)`.)* So Q-rank ⟺ Q-comp,
quantitatively: the deviation *is* the composite's rank. Q-comp ⟺ Q-elem by
unwinding the two connecting maps (A12 §4 formula; the ambiguity in the
choices of lift and `ε⁻¹` moves `W` exactly within `ε(A,B)`, and the
`z`-lift ambiguity `z ↦ z+εu` cancels: `W ↦ W + 2ABu = W`).

**Payoff if true.** `H₁(cover) ≅ D^{k̃−k} ⊕ F₂^{2k−k̃}` as a deck module —
the complete representation type from the two ranks the screens already
compute. Theorem A12 ((R) ⟺ `k̃ = k` ⟺ Bezout) becomes the `a = 0` slice of
a full structure theorem.

## 1. The headline finding: the structural route collapses to a lift trick

A12 §4 correctly observed that `δ² = 0` is **not formal**: for the deck
extension `0 → F₂ → D → F₂ → 0`, `Ext_D(F₂,F₂) = F₂[e]` with `e² ≠ 0`.
Session-0 sharpens that with an explicit witness *at the complex level*:

**Toy obstruction.** Over `R̃ = D` itself take the 3-term complex of free
`D`-modules `D →^{·ε} D →^{·ε} D`. Its transfer SES has
`δ₂, δ₁ : F₂ → F₂` both isomorphisms, so `δ₁δ₂ ≠ 0` — and the complex is
even *self-dual* under the Frobenius pairing. Consequences: (i) any proof
must use more than "free D-modules + transfer LES + self-duality of the
complex" — **the OQ2 structural route as originally scoped (extend-by-ε
LES + Frobenius self-duality) cannot succeed on those hypotheses alone**;
(ii) the toy also violates `k̃ ≥ k`, locating it firmly outside the Koszul
world (A12 Lemma 1 is Koszul-specific).

What the classical `β² = 0` proofs actually use is not formality but an
**integral lift**: the singular chain complex exists over `ℤ/4` (indeed
`ℤ`), not just `ℤ/2`. The BB analogue exists canonically — **the 4-fold
cover along the same axis** — and that is the entire proof:

**Candidate Theorem (tower lift).** *Let `G̃` be a finite abelian group,
`σ ∈ G̃` of order 2, `R̃ = F₂[G̃]`, `ε = 1+σ`, and `A, B ∈ R̃` arbitrary.
Then `δ₁∘δ₂ = 0`. Hence `E = k̃ − k` and
`H₁(cover) ≅ D^{k̃−k} ⊕ F₂^{2k−k̃}`.*

Note the scope: arbitrary order-2 `σ` — free-ℤ₂ axis doublings
(`σ = x^ℓ`), *twisted* decks (`σ = x^a y^b`), any block `S[P]` with any
order-2 `s` (coefficients `S = F_{2^d}` change nothing).

*Construction (Frattini lift).* There is a finite abelian `Ĝ` with
`Ĝ ↠ G̃`, kernel `⟨σ̂²⟩` of order 2, where `σ̂ ↦ σ` has **order 4**:
decompose `G̃ = ∏ Z_{n_t}`, pick a coordinate where `σ` has nonzero
component (`= n_t/2`), and double that factor's order, keeping all
exponents. For the standard free-ℤ₂ BB cover this is literally the next
rung of the doubling tower: `Ĝ = Z_{4ℓ}×Z_m`, `σ̂ = x^ℓ`. Write
`R̂ = F₂[Ĝ]`, `ε̂ = 1+σ̂`. Three facts, all from `R̂` being **free over
`F₂[⟨σ̂⟩] = F₂[ε̂]/(ε̂⁴)`** (group algebra over a subgroup algebra):

1. `ε̂² = 1+σ̂²`, so `R̂/ε̂²R̂ ≅ R̃` (and `ε̂ ↦ ε`);
2. `ker(R̂ → R) = ε̂R̂` (the ℤ/4-augmentation ideal is principal on `ε̂`:
   `1+σ̂² = ε̂²`, `1+σ̂³ = ε̂ + σ̂ε̂²`);
3. `Ann_{R̂}(ε̂) = ε̂³R̂` (and `Ann_{R̃}(ε) = εR̃`).

*Proof of Q-comp.* Let `z̄ ∈ H₂(base)`, i.e. `Āz̄ = B̄z̄ = 0` in `R`. Lift
`z̄` all the way to `ẑ ∈ R̂`, and lift `A, B` to `Â, B̂ ∈ R̂` (canonical
same-exponent lifts). By fact 2, `Âẑ = ε̂â` and `B̂ẑ = ε̂b̂` for some
`â, b̂ ∈ R̂`. Reduce mod `ε̂²`: `z := ẑ mod`, `a := â mod`, `b := b̂ mod`
are then *valid choices* in the two connecting-map recipes
(`εa = Az`, `εb = Bz` in `R̃`). The composite's representative is
`W = A·b + B·a ∈ R̃`, which lifts to `Ŵ = Â·b̂ + B̂·â`, and

```
ε̂·Ŵ = Â(ε̂b̂) + B̂(ε̂â) = ÂB̂ẑ + B̂Âẑ = 2ÂB̂ẑ = 0        (char 2),
```

so `Ŵ ∈ Ann_{R̂}(ε̂) = ε̂³R̂ ⊆ ε̂²R̂` (fact 3), i.e. **`W = 0` in `R̃`** —
not merely in `ε(A,B)`. Since the connecting maps are well-defined on
homology, computing the composite along one valid chain of choices
suffices: `δ₁δ₂(z̄) = [ε⁻¹(0)] = 0` (the mult-`ε` iso `R ≅ εR̃` sends only
`0̄` to `0`). ∎ For *arbitrary* (non-tower-compatible) choices, `W` moves
exactly by `ε(A,B)` (§0), giving Q-elem in the stated form. ∎

Two reframings worth recording:

- **Spectral-sequence view.** This is `d₁² = 0` of the `ε̂`-adic filtration
  of the 4-fold-cover complex `K̂` (each adjacent-quotient SES of the
  filtration is isomorphic to the transfer SES, using fact 3 for the
  graded identifications). That is exactly the "length-`2^r` Bockstein
  spectral sequence" route that OQ1 anticipated — OQ2 is its first-page
  shadow, one rung up the tower. The element-level proof above is the
  unwound version and is what Lean should formalize (no SS machinery).
- **Why the toy escapes.** The toy complex `(D, ·ε, ·ε)` admits *no* lift
  to a complex of free `F₂[ℤ/4]`-modules (`d̂² = ε̂²·unit ≠ 0` for any lift
  `d̂ ≡ ·ε mod ε̂²`), while the Koszul differentials lift for free because
  their *matrix entries* are ring elements that lift. Liftability is the
  real content; Koszul-ness is just the cheapest way to certify it.

## 2. Red-team checklist (W0 gate — mandatory before "theorem")

This program has had confident claims overturned twice (methodology
red-team; A9 stored-form artifacts). The argument above is suspiciously
short; an independent verifier pass must check, at minimum:

- (a) The connecting-map recipes match the actual SES orientation and
  conventions (`∂₂ = (B,A)`, `∂₁ = (A,B)`; `δ` well-defined; the sub-term
  identification `R ≅ εR̃` uses `Ann_{R̃}(ε) = εR̃`).
- (b) Fact 2 (`ker(R̂ → R) = ε̂R̂`) — check the ℤ/4-augmentation-ideal
  computation.
- (c) Fact 3 (`Ann_{R̂}(ε̂) = ε̂³R̂`) — the freeness argument, including
  coefficient fields `S ≠ F₂` and non-cyclic `Ĝ`.
- (d) Choice-independence: each `δ` is well-defined on homology *before*
  any choices are made, so one valid chain of choices computes the
  composite. (This is where a subtle error would hide: verify the chosen
  `(z, a, b)` are simultaneously valid for the two recipes as composed,
  i.e. `δ₁` is evaluated on the class `[(b̄, ā)]` and `(b, a)` is a
  legitimate lift of it.)
- (e) The Frattini-lift construction for *every* order-2 `σ` (including
  `σ ∈ 2G̃`, e.g. `σ = (1,2) ∈ Z₂×Z₄`): the doubled coordinate gives
  `2σ̂ ≠ 0`, order exactly 4, and `Ĝ/⟨σ̂²⟩ ≅ G̃`.
- (f) Nothing uses `A, B` beyond commutativity and liftability — state the
  general lemma at the right altitude (any complex of free `D`-modules
  that lifts to a complex of free `F₂[ℤ/4]`-modules has `δ₁δ₂ = 0`; the
  toy shows the lift hypothesis is not removable).
- (g) Numerical: §3 evidence + W1's exhaustive strata.

## 3. Session-0 validation (this branch, quick mode, all clean)

`a13_bockstein_stratified_sweep.py` extends the A12 block sweep with F₈
coefficients, biased deep-ideal sampling, twisted decks, a per-pair
**element-form direct check** (solve `εa = Az`, `εb = Bz` on a basis of
`Z = {z : Az, Bz ∈ εR̃}` and test `W ∈ ε(A,B)` — independent of the
`E = 2g` bookkeeping route), and a per-block **tower-lift pillar check**
(build the ℤ/4-lift, assert `rank(ε̂) = 3n/4`, `rank(ε̂³) = n/4`, which
with `ε̂⁴ = 0` force fact 3).

Totals: **167,698 pairs, 74,804 in the `g > 0` stratum, 39,611 live**
(`g > 0` with both `A, B ∉ εR̃` — the only stratum where both `δ`'s can be
nonzero, i.e. where the conjecture has content), **4,518 element-form
direct checks, 0 violations of any kind**; A12's CE1/CE2 regression rows
reproduce (`E = 2g` = 12, 8). Strata: `F₂[P]`, `|P| = 16`
(`Z₁₆, Z₈×Z₂, Z₄×Z₄`, all decks); `F₈[Z₂]` exhaustive; `F₈[Z₄]`,
`F₈[Z₂²]`, `F₄[Z₈]`, `F₄[Z₄×Z₂]` sampled ×4 strategies; global
`F₂[Z₆×Z₃]`; global `F₂[Z₆×Z₆]` including the **twisted deck
`s = x³y³`** (never exercised by any A12 sweep). Log:
session transcript; re-run is ~2 min (`--full` for W1 sizes).

Structural observation, confirming the W2 lemma's expected shape: on
**chain** blocks (`Z₁₆`, `F₄[Z₈]`, `F₈[Z₄]`) the live count is *zero* in
all 167k pairs — `g > 0` forces both valuations past `N/2`, killing both
base images, so `δ₂ = 0` and the equality holds with no content. The
two-generator blocks (`Z₈×Z₂`, `Z₄×Z₄`, `Z₄×Z₂`) carry all the live
cases — exactly OQ2's predicted danger zone, now heavily sampled clean.

## 4. Workstreams

**W0 — red-team + write-up (first; ~0.5 day).** Independent adversarial
pass over §1 against the §2 checklist (fresh session or subagent, given
the overturn history). If it passes: upgrade OQ2 to a theorem in a
self-contained `A13_result.md` (statement at the §2(f) altitude), update
A12 §4/§8 and the research-log entry, and record the "structural route as
scoped is insufficient" finding (§1 toy) alongside.
*Kill criterion:* any checklist item fails → demote to conjecture, record
the flaw precisely, W1 reverts to falsification framing, and the fallback
structural attack is via the intersection form (`δ₁ = δ₂^*` up to
antipode; `δ₁δ₂ = 0 ⟺ im δ₂` isotropic — but note the toy already bounds
how far duality alone can go).

**W1 — stratified exhaustive sweep (~0.5–1 day, parallel with W0; the
user-requested "cheapest falsification path", now doubling as theorem
verification).**
- `--full` run of the session-0 script (4× samples; minutes).
- True *exhaustive* `F₂[P]`, `|P| = 16`: enumerate `A` up to unit orbit
  (orbit ⟺ principal ideal; BFS from a seed through unit multiplications,
  or canonical forms by annihilator profile), `B` exhaustive over the
  maximal ideal; expected cost `#orbits (10²–10³) × 2^15 ×` sub-ms ≈
  hours, embarrassingly parallel. Same treatment for `F₄[P]`, `|P| = 8`;
  `F₈[P]`, `|P| = 4` exhaustive (`4096²` pairs ≈ 1.7·10⁷, overnight or
  bit-batched).
- Report per stratum: pairs, `g>0`, live, `max defect E − 2g` (expected
  ≡ 0). Any violation → run the element-form checker to extract the
  failing `z` (it localizes the bug in proof or code — with W0 passed, a
  violation means exactly one of them is wrong, and the witness decides).

**W2 — chain-ring case lemma, written out (~0.5 day; optional but cheap,
and independently valuable).** On a chain block `S[Z_{2^r}]` (`= S[t]/t^N`,
`ε ~ t^{N/2}`) everything is valuations: write the closed forms for
`k, k̃, g, E` as functions of `(val A, val B, N)`, prove `E = 2g` by the
finite case analysis, and note the structural corollary the sweep
confirmed (`g > 0 ⟹` both vals `> N/2 ⟹ δ₂ = 0`). Corollary, independent
of W0: **the equality is a theorem for every cover whose undoubled
coordinate has odd order** (all blocks chain). Side payoff: closed-form
per-block `k̃` predictions from base data — a screen ingredient A9-style
hunts can use without building covers.

**W3 — Lean formalization (staged; scope after W0 passes).**
- **L1 (the A13 target): the element-level theorem via the lift.** The
  proof is finite and constructive — no LES, no SS. Natural statement at
  the §2(f) altitude over `MonoidAlgebra F₂ Ĝ`, or concretely over the
  `BBDoubling` layer's convolution algebra with `Ĝ = Z_{4ℓ}×Z_m` (where
  facts 1–3 are finite linear algebra, potentially `decide`-able per
  instance and provable parametrically with the layer's existing
  machinery). Risk to scout: mathlib's support for "group algebra is free
  over subgroup algebra" (coset-basis argument may need hand-rolling).
- **L2 (paper-grade rank corollary): `E = k̃ − k`.** Needs the transfer-LES
  bookkeeping in finite-dimensional F₂ linear algebra — the "genuine
  formalization project" A12's scope note already flagged for its own
  clause (iii); size it only if Paper 1 states the structure theorem at
  full strength.
- **L3: instances — nothing to do.** Gross/pair72 sit at `k̃ = k` where
  `deckTrivial_of_bezout` already gives `E = 0`.
- A12's Lean target (i) (`membership ⟺ k̃ = k`) remains the best first
  formalization payoff overall; L1 here is the A13 addition, sized
  similarly.

**W4 — bookkeeping (~0.5 hr).** Research-log entry (done session-0), A12
forward pointers (done), memory note; on completion fold the structure
theorem into the Paper-1 deck-module section (with A12 as the `a = 0`
slice) and open **A14 = OQ1 with the same weapon**: the lift trick plus
the now-available `d₁² = 0` makes the length-`2^r` Bockstein SS concrete;
the tower question ("`σ_* = id` on top ⟹ `k` constant along the tower",
equivalently the `d₂, d₃, …` obstructions and whether `H₁` over
`F₂[Z_{2^r}]` is determined by the rank ladder `k, k̃, k̂, …`) is the
family-paper theorem and is *not* answered by A13 (the module category of
`F₂[Z_{2^r}]`, `r ≥ 2`, has `2^r` indecomposables — two ranks can't pin
it; new obstructions are expected to be genuinely open).

## 5. Decision tree and cost

```
W0 red-team ──pass──► A13_result.md (theorem) ──► W1 confirms exhaustively
   │                        │                        │ violation? → witness
   │                        ├─► W2 corollaries       │   decides proof-vs-code
   │                        └─► W3.L1 Lean target    ▼
   │                                              Paper-1 fold-in + open A14
   └─fail (checklist item) ─► record flaw; conjecture reopens;
        W1 = falsification (stratified exhaustive, F₈, twisted decks);
        fallback structural route = intersection-form isotropy of im δ₂
        (bounded by the §1 toy: duality alone provably insufficient)
```

Cost to theorem-grade with exhaustive verification: **~2 days** (W0 + W1 +
W2). L1 Lean: ~1–2 days after that; L2 sized separately. Program note:
A12 already established OQ2 is not load-bearing for the doubling engine
(which operates at `k̃ = k`); this is a mathematical-core + paper item,
priced accordingly — but at the current price it is the cheapest open
problem on the A-series board.
