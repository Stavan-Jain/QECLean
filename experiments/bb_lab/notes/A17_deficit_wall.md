# A17 — The deficit wall: theorem, mechanism, and a measurement correction

**Status: theorem package PROVED and machine-validated (final battery
25/25 green; the first run's two "failures" were the §8 discoveries);
the A14 §16 OQ is answered in a corrected form.** The wall *value* is a
theorem: under (R)
and odd polynomial weights, `d_safe` is even and `d_safe = 2d` is
equivalent to safe-half viability, so **`2d − 2` is the unique maximal
SF-failing value** — nothing between `2d − 1` and viability is
achievable. The wall *mechanism* is the pushforward: under (R) the
projection of any cover logical with surviving class is itself a
safe-sector base logical (`im p₁ = im δ₂`), so a cover that fails to
double through its safe sector hands the safe floor a witness at no
weight cost (`d_safe ≤ d̃_safe`). The empirical sharpening "the orbit
maximum stalls at *exactly* `2d − 2`" is **retracted as a measurement
artifact**: the §15/§16 "ceiling 18" readings were first-found SAT
witness weights, not certified minima; exact ladders (this session) put
the stored bb108-y cell at `d_safe = 14 = 2d − 6` — certified on both
sides of the cover, with the T2 coupling tight at `14 = 14` — and every
ladder-sampled orbit finalist at `≤ 12`; the corrected table is in §8.
This note is **phase P3 of the A17 d≥7 doubling-hunt plan**
(`A17_d7plus_doubling_hunt_plan.md`, drafted in a sibling worktree; the
plan's "2(d−1) shadow hypothesis" is settled here — refuted as stated,
replaced by the pushforward mechanism — and its P1 corpus battery
should report S4 weights as "≤" bounds per §8).
Branch: `claude/charming-euler-ef6879` (off `main` after PR #55).
Script: [`a17_deficit_wall_checks.py`](../scripts/a17_deficit_wall_checks.py);
data: `data/a17/deficit_wall_checks.json`.

## 0. The question (A14 §16, verbatim)

> **The recurring shape — a "deficit wall" just below 2d.** In every
> probed direction, the orbit-maximum safe floor stalls a hair under the
> target: bb_108 at 18 vs 20 (both decompositions, hundreds of
> presentations), bb_288 at 32–34 vs 36 (strongest sampled cells). [...]
> Candidate new OQ: is there a parity/duality mechanism pinning `max over
> presentations of the safe-floor minimum` to `2d − 2` for non-doubling
> BB codes? (Note `2d − 2 = 2(d − 1)` — suggestive of a
> weight-(d−1)-ish base object whose double-cover shadow lands in the
> safe sector; connects to the overlap-rescue math and the
> closed-form-S0 residue.)

Answer, in three parts. **(a) Yes — parity pins the value**, and it is a
one-line theorem (L1 below): with weight-3 polynomials every 1-cycle has
even weight, so an SF-failing cell can sit at `2d − 2` and no higher.
**(b) The mechanism is a pushforward, not a base object**: the
weight-`(2d−2)`-ish object whose "double-cover shadow lands in the safe
sector" is really a *cover* logical whose *base shadow* is the safe
element (T2 below); the natural base-side guess (two overlapping
translates of a minimal logical — the difference-class mechanism T1) is
provably available only under an index condition and is *measurably
silent* on bb_108 (§7). **(c) The sharp empirical premise was an
artifact**: the recorded 18s and 34s were solver witness weights (upper
bounds), not minima; the corrected picture is in §8. What survives of
the recurrence is exactly what the theorem forces: even values `≤ 2d−2`
for every failing cell, `= 2d` for every viable one.

## 1. Setting and the object

Conventions of A12 §1 / A14 §1, with the doubled axis canonicalized to
x: base `G = Z_ℓ × Z_m`, `R = F₂[G]`; `A, B ∈ R`; base Koszul complex

```
K̄ :  R --∂₂--> R² --∂₁--> R,   ∂₂ f = (Af, Bf),   ∂₁(u,v) = Bu + Av,
```

`H₁ = ker ∂₁ / im ∂₂`, `k = dim H₁`, `d = min{|w| : w ∈ ker ∂₁ \ im ∂₂}`.
Cover `G̃ = Z_{2ℓ} × Z_m` with the same-exponent lifts `Ã, B̃`; complex
`K`; `ε = 1 + x^ℓ`; transfer `τ = ε·lift : K̄ → K` and pushforward
`p = mod-ε : K → K̄` give the SES `0 → K̄ →^τ K →^p K̄ → 0` and its LES.
**(R)**: `ε ∈ (Ã, B̃)` ⟺ `k̃ = k` (A12). Under (R), Prop A14.1 gives
`p₂ = 0`, `δ₂` injective, `dim im δ₂ = k/2`, `im p₁ = im δ₂`, and the
seam-carry representatives `seamC ζ` for `δ₂[ζ]`.

**Definition (safe sector, safe distance).** The safe sector is
`S := im δ₂ ⊆ H₁(K̄)` and

```
d_safe := min{ |w| : w ∈ ker ∂₁,  [w] ∈ S \ 0 }.
```

By A14.1(3)+(5) this is exactly the quantity the lab measures (the
minimum over `ζ ∈ ker ∂₂ \ 0` of the coset minima
`min_f |seamC ζ + ∂₂ f|`), A14 §3's "imΔ-distance". The safe half of the
doubling template is `SF ⟺ SeamCosetFloor (2d) ⟺ d_safe ≥ 2d`.

Throughout, "the parity hypothesis" means `|A|` and `|B|` are both odd
(all Bravyi-corpus BB pairs have weight 3+3).

## 2. Lemma L0 (the safe sector is the transfer kernel)

**Lemma.** `S = ker(τ₁ : H₁(K̄) → H₁(K))`. Concretely: a base logical
class is safe **iff its transfer to the cover is a cover boundary** —
`[w] ∈ S ⟺ ε·w̃ ∈ im ∂̃₂` for any lift `w̃`. (No hypothesis beyond the
SES; under (R) the common dimension is `k/2`.)

*Proof.* LES exactness at the `H₁(K̄)` slot between `δ₂` and `τ₁`:
`im δ₂ = ker τ₁`. The chain-level transfer `τ(w) = ε·w̃` is independent
of the lift (two lifts differ by an element of `ker p = εR̃`, killed by
`ε` since `ε² = 0` on the free cover), and `τ₁[w] = [ε·w̃]`, which
vanishes iff `ε·w̃ ∈ im ∂̃₂`. ∎

This is the reframing everything below uses: **the safe floor is the
minimum weight of a logical that dies in the double cover.** The battery
check `L0/*` verifies span equality `im δ₂ = ker τ₁` (not just
dimensions) on nine covers including both bb_288 presentations and the
Z₁₈×Z₃ re-decomposition of bb_108.

## 3. Lemma L1 (parity) — the wall value

**Lemma.** Under the parity hypothesis, every 1-cycle of `K̄` *and* of
`K` has even weight. Consequently `d`, `d̃ = d(cover)`, `d_safe`, and
every safe-class coset minimum are even.

*Proof.* The augmentation `η : F₂[H] → F₂`, `η(f) = |f| mod 2`, is a
ring homomorphism for any finite abelian `H`. If `∂₁(u,v) = Bu + Av = 0`
then `Bu = Av`, so `η(B)η(u) = η(A)η(v)`; with `η(A) = η(B) = 1` this
gives `|u| ≡ |v| (mod 2)`, hence `|(u,v)| = |u| + |v|` even. The lifts
have the same weights, so the same argument runs in `K`. ∎

(The same augmentation step appears in A8 §4.2 to kill odd-weight
stabilizers; the observation here is that it applies to *all cycles* of
both complexes at once. The hypothesis is load-bearing: toric-type pairs
with `|A| = |B| = 2` have odd-weight cycles — the vertical loop on an
odd-`L` torus — and their freeze values can be odd.)

**Corollary (the wall value).** Under (R) + parity, for every
presentation cell exactly one of:

- `d_safe = 2d` — but see §5's converse: this *is* safe-half viability
  and forces the cover's safe sector to clear `2d`; or
- `d_safe ≤ 2d − 2` — SF fails, and the failure value is even.

There is no failing value in `{2d − 1}` and none above `2d` matters for
the template, so **`2d − 2` is the unique maximal SF-failing value: the
deficit wall.** (Values `> 2d` are not excluded by parity alone, but
`d_safe > 2d` never occurs on any measured instance — the doublers all
sit at exactly `2d` — and §5's T2 explains why: the cover's own
tightness witnesses push down onto safe classes of weight ≤ 2d whenever
the safe sector is achieved upstairs, which the battery verifies on
every doubler tested.)

## 4. Lemma L2 + Theorem T1 (collision subgroups and difference classes)

For a base 1-cycle `z` put

```
Stab₀(z) = {g ∈ G : [gz] = [z]},     K_z = {g ∈ G : (1+g)[z] ∈ S}.
```

**Lemma L2.** `H₁` is an `R`-module and `S` an `R`-submodule;
`Stab₀(z) ⊆ K_z` are subgroups of `G`; the map
`gK_z ↦ [gz] + S` is a well-defined injection `G/K_z ↪ H₁/S`; and under
(R), `[G : K_z] ≤ 2^{k/2}`.

*Proof.* `S = ker τ₁` is a submodule because `τ₁` is `R`-linear:
`τ₁(r·α) = r̃·τ₁(α)` for any lift `r̃` (well-defined — two lifts differ
in `(ε)`, and `ε` kills `im τ₁`). Subgroup closure of `K_z`:
`(1+gh)[z] = (1+g)[z] + g·((1+h)[z]) ∈ S + g·S = S`, and
`(1+g⁻¹)[z] = g⁻¹·((1+g)[z]) ∈ S`; `Stab₀ ⊆ K_z` since `0 ∈ S`.
Injectivity and well-definedness: `[gz] ≡ [g′z] (mod S)` ⟺
`g·(1 + g⁻¹g′)[z] ∈ S` ⟺ `g⁻¹g′ ∈ K_z` (unit action preserves the
submodule). The index bound: `G/K_z` injects into `H₁/S`, which has
`2^{k − dim S} = 2^{k/2}` elements under (R). ∎

**Theorem T1 (difference-class bound).** (R); `z` a minimum-weight
logical. If `K_z ⊋ Stab₀(z)` — in particular whenever
`[G : Stab₀(z)] > 2^{k/2}`, by the index bound — then for any
`h ∈ K_z \ Stab₀(z)`,

```
0 ≠ (1+h)[z] ∈ S   and   d_safe ≤ |z + hz| = 2d − 2·|supp z ∩ supp hz| ≤ 2d.
```

*Proof.* Immediate from L2 and inclusion–exclusion on supports; the "in
particular" holds because `[G:K_z] ≤ 2^{k/2} < [G:Stab₀]` forces the
proper containment. ∎

**Measured status (battery `L2/*`, `T1/*`).** The subgroup structure and
index bound hold on every tested instance. But the mechanism *fires*
only where `K_z ⊋ Stab₀`: on bb90-y (`|K_z| ∈ {15,45} ⊋ |Stab₀| = 5`,
difference bound `U = 10`, tight at the freeze value) — while on
pair72-x, gross-x, hit3-y, and **bb108-y the census gives `K_z = Stab₀`
exactly for every minimum-weight logical** (18, 84, 84, 54 of them,
exhaustively enumerated). So the natural base-side guess for the wall
witness — two overlapping translates of a minimal logical, the
`2(d−1)`-shaped object A14 §16 hypothesized — is **provably absent** on
the very code that motivated the OQ. The wall needs T2.

## 5. Theorem T2 (the pushforward mechanism)

Write `d̃_safe := min{ |ṽ| : ṽ a cover logical with p₁[ṽ] ≠ 0 }` — the
cover's **safe-sector minimum** (A8 §4's "safe sector" of the cover; its
complement, `p₁[ṽ] = 0`, is the dangerous/diagonal sector handled by the
template's other half).

**Theorem T2.** Under (R): if `ṽ` is a cover 1-cycle with
`p₁[ṽ] ≠ 0` and `|ṽ| ≤ W`, then `p(ṽ)` is a base logical with
`[p(ṽ)] ∈ S \ 0` and `|p(ṽ)| ≤ |ṽ| ≤ W`. Hence

```
d_safe ≤ d̃_safe .
```

*Proof.* `p₁[ṽ] = [p(ṽ)] ∈ im p₁ = im δ₂ = S` by A14.1(2) (this is
where (R) enters), and it is nonzero by hypothesis, so `p(ṽ)` is a
cycle not in `im ∂₂`. The sheet inequality `|p(ṽ)| ≤ |ṽ|` is
fiberwise: `p(ṽ) = ṽ₀ + ṽ₁` with `|ṽ₀ + ṽ₁| ≤ |ṽ₀| + |ṽ₁| = |ṽ|`. ∎

**Corollary W (the wall, cell level).** (R) + parity.

1. If the cover fails to double *through its safe sector*
   (`d̃_safe < 2d`), then `d_safe ≤ d̃_safe ≤ 2d − 2`, with explicit
   witness `p(ṽ)`: **the safe floor inherits the cover's failure at no
   weight cost.**
2. Conversely, if `d_safe ≥ 2d` (SF holds) then *every* cover logical
   with surviving class weighs `≥ 2d`: `|ṽ| ≥ |p(ṽ)| ≥ d_safe ≥ 2d`.
   So an SF-viable cell can only fail to double in the dangerous sector
   (`p₁[ṽ] = 0`) — which is precisely the sector the template's
   witness/(M) half floors. **SF + (M) ⟹ doubling** is the template,
   re-derived; and "SF-true ⟹ doubles" (A11's empirical 111/111)
   holds exactly when the dangerous sector never under-runs `2d` alone
   (the (M)-robustness conjecture, §9).

*Proof.* (1) T2 at `W = d̃_safe`; `d̃_safe` is even by L1 (its
minimizers are cover cycles), so `< 2d` means `≤ 2d − 2`. (2) is the
displayed inequality: the middle term is a representative of a nonzero
class of `S`. ∎

**Measured status (battery `T2/*`).** On the failing cells the safe
sector is achieved upstairs at the wall: bb108-y has a weight-18 cover
logical with `p₁ ≠ 0` pushing to a weight-18 safe base logical (3.2 s
SAT; overlap-free, `|p(ṽ)| = |ṽ|`); bb90-y the same at weight 10 = d
(the freeze, seen from above: the cover's light safe-sector logical *is*
the undoubled-direction logical of A14 §13, and its shadow is the safe
class); bb90-x at 18 → 12 (three overlapping fiber pairs); the
re-decomposed bb108-u18 at 16 → 16. On the doublers the probe is SAT at
exactly `2d` with `|p(ṽ)| = 2d` and safe (pair72-x 8→8, gross-x 12→12,
hit3-y 12→12): their tight `d_safe = 2d` classes lift overlap-free, so
`d̃_safe = 2d = d_safe` — **the coupling `d_safe ≤ d̃_safe` is tight in
every measured instance, doublers and failers alike.**

## 6. The deficit-wall theorem, assembled

**Theorem (deficit wall).** Let `(A, B)` be a BB pair with `|A|, |B|`
odd, `d = d(base) ≥ 2`, and consider any literal-lift `Z₂` cover
satisfying (R). Then:

1. `d_safe` is even, and `d_safe ≥ 2d ⟺ SF` (safe-half viability).
2. If SF fails, `d_safe ≤ 2d − 2`: **the wall value `2d − 2` is the
   unique maximal SF-failing value.**
3. `d_safe ≤ d̃_safe` (pushforward); in particular a cell whose cover
   has any light safe-sector logical fails SF at that weight or less,
   and an SF-viable cell forces the cover's entire safe sector to
   `≥ 2d`.
4. Where `K_z ⊋ Stab₀(z)` for a minimum-weight `z` (guaranteed if
   `[G : Stab₀(z)] > 2^{k/2}`), additionally
   `d_safe ≤ 2d − 2·max{|supp z ∩ supp hz| : h ∈ K_z \ Stab₀}`.
5. **Orbit form.** For a code none of whose presentation cells is
   SF-viable, the orbit maximum of `d_safe` is an even number
   `≤ 2d − 2`. Its exact value is a code-level invariant *not* pinned
   by this theorem; §8 records the corrected measurements (the
   previously reported "exactly `2d − 2`" readings were witness-weight
   artifacts).

All parts are proved above (1: L1+definition; 2: L1; 3: T2/W; 4: T1;
5: 1–2 applied cell-wise).

## 7. Validation battery

`uv run python scripts/a17_deficit_wall_checks.py` (~minutes;
SAT-witness ladders plus bounded UNSAT attempts; `--expensive`
reproduces the 5-h cover certificate). The battery ran twice in this
fork: the *first* run scored 23/25 with its two "failures" being the
exactness pins written for the old "ceiling = 18" reading — they
correctly refused to certify it (SAT@17 returned weight-16 witnesses;
one finalist at 12), which is how §8's correction was discovered. The
committed battery asserts the corrected claims and is green.

| check | covers | result |
|---|---|---|
| L0 span equality `im δ₂ = ker τ₁`, dim `k/2` | pair72-x, gross-x, hit3-y, bb90-x/y, bb108-y, bb108-u18 (Z₁₈×Z₃), bb288-y, bb288-c48b | 9/9 PASS |
| L1 parity (200 random cycles/complex + seams) | 6 covers | PASS (all seam weights even) |
| L2 `K_z` subgroup + index ≤ `2^{k/2}` | 5 covers, exhaustive min-logical enumerations (18/84/84/≥100/54) | PASS |
| T1 census | bb90-y fires (`U = 10`); pair72/gross/hit3/bb108-y: `K_z = Stab₀`, silent | as stated |
| T2 gating | bb108-y @18 (18→18), bb90-y @10 (10→10) | PASS |
| T2 probes | bb90-x 18→12; bb108-u18 16→16; pair72 8→8; gross 12→12; hit3 12→12 (all safe, all SAT) | recorded |
| W ladders | bb90-y: `d_safe = 10 = d` **certified** (UNSAT@9 all reps + seam@10); bb108-y: descent lands < 18 (14 with the §8 certificates); 4-finalist sample: all even, ≤ 12 | PASS |

Independent corroborations along the way: gross's 84 weight-6 logicals
are exhaustively re-enumerated and none is safe (matches A_HANDOFF's
"imΔ-distance 12 while d = 6"); hit3-y matches gross's `K_z` structure
exactly (they share a base up to presentation); bb108-x's stored
condition-2 death and the u-axis's zero k-gate failures reproduce §14/§16.

## 8. The measurement correction (exact ladders)

The §15/§16 sweep protocol recorded, per refuted cell, the weight of the
*first extracted SAT certificate* at the query bound (`floor − 1` or
similar). Those are upper bounds on `d_safe`, not minima — CaDiCaL
returns any model under the cardinality bound, and nothing in the
pipeline pressed below it. The A17 exactness pins exposed this
(`SAT@17` on the stored bb108-y cell returned a weight-**16** witness
where "18" had been recorded, and likewise on all eight scanned orbit
finalists — one of them at **12**). Descending ladders (SAT at `w` ⟹
retry at `w_found − 2`, by parity; terminate at UNSAT) give the
corrected values:

| cell | historical reading | corrected (this session) | grade |
|---|---|---|---|
| bb90-y stored (freeze) | raw seam 10 | **d_safe = 10 = d exactly** | UNSAT@9 all reps, certified |
| bb108-y stored | "light class at 18" (§14) | **d_safe = 14 = 2d − 6 exactly** | base: UNSAT@12 on all orbit reps (20M-conflict budget, ≈69 min); cover: `d̃_safe = 14` **exactly** (SAT@14 pushing 14→14 overlap-free; UNSAT@12, ≈5 h CaDiCaL at n=216) — the T2 coupling is tight at 14 = 14 |
| bb108 v1 x-finalists | "S4-refuted at 12–18", ceiling 18 | first witnesses ≤ 16 (one 12) on 8 cells; **full ladders descend all four sampled cells to ≤ 12 = 2d − 8** | witness-grade; every value even, `< 18` — the cells whose *cheap tiers* stalled at 20 have true minima at 12 |
| bb108-u18 stored (Z₁₈×Z₃) | "16/18 again" (§16) | **≤ 16** (cover T2 witness 16→16) | witness-grade |
| bb288-y stored | "witness weight 34" | **≤ 34**, exact unmeasured | n=288 base / n=576 cover UNSAT priced out (the 5-h n=216 certificate calibrates the wall-region hardness) |
| gross-x / hit3/4/6-y / pair72-x (doublers) | floors tight at 2d | **= 2d exactly**, and the cover safe sector is achieved at 2d with overlap-free lifts (`d̃_safe = 2d = d_safe`) | Lean/MIm + a14 S4 + this battery |

Corrected empirical picture:

- **No measured instance attains the wall.** The theorem allows
  SF-failing cells anywhere in `{even ≤ 2d − 2}`; the historical
  readings suggested the maximum `2d − 2` recurred across codes; the
  exact values show bb_108's stored-y cell at `14 = 2d − 6` (certified
  both sides) — currently the *largest* certified value anywhere in the
  orbit — and every ladder-sampled finalist at `≤ 12 = 2d − 8`. The
  "recurrence at exactly `2d − 2`" was the query bound reflecting back
  through first-found witnesses.
- **The freeze value is exact where the freeze mechanism runs** (bb90-y
  `= 10 = d`): when a minimum-weight class is itself safe, the ladder
  bottoms out at `d` immediately — T1's difference classes and T2's
  pushforward agree on it from both sides.
- **The doubling side is rigid**: every viable cell measured sits at
  exactly `2d`, with the coupling `d_safe = d̃_safe` tight in both
  directions. Nothing observed contradicts `d_safe ≤ 2d`
  unconditionally, but the theorem as proved needs the safe sector
  achieved upstairs (T2) or a firing collision subgroup (T1) to force
  it; the corner where both mechanisms are silent remains open (§9).
- **Solver-hardness clusters at the wall region.** UNSAT certificates
  two below the true minimum are seconds on 54-cell frames but hours at
  n = 216 (and out of reach at n ≥ 288) — the same "value-carrying
  lightness" OQ4 predicted, now with a measured hardness profile. The
  practical protocol: witness ladders always; UNSAT pins only where the
  frame is small or the claim is load-bearing.

## 9. Consequences and residue

- **OQ status (A14 §16).** Answered as corrected: the wall *value* is a
  theorem (§3, §6.2), the *mechanism* is the pushforward (§5), the
  "exactly `2d − 2` across codes" recurrence was a witness-weight
  artifact (§8). What recurs for real is: every failing cell at an even
  value `≤ 2d − 2`, every viable cell at exactly `2d`, and the tight
  coupling `d_safe = d̃_safe` in all measurements.
- **The (M)-robustness conjecture (new, sharp).** On the T1 corpus every
  k-preserving short is SF-false (465/465) — no cover ever failed
  *only* dangerously. Conjecture: for corpus-class BB pairs the
  dangerous sector never under-runs `min(2d, d̃_safe)`. With §5.2 this
  would make **SF ⟺ doubles** on k-preserving literal lifts a theorem,
  and the wall statement unconditional. (A8 §4.2's data is consistent:
  all `b ≠ 0` rungs clear the floor with margin, the binding rung is
  the diagonal `b = 0`.)
- **The attainment question, reopened correctly.** The code-level
  invariant `maxSF(code) := max over orbit cells of d_safe` satisfies
  `maxSF ∈ {2d} ∪ {even ≤ 2d − 2}`; bb_108's measured value is ≤ 16 on
  every sampled cell (both decompositions' stored cells and 20/192 v1
  finalists), i.e. the wall is not attained there and the pre-A17
  "orbit ceiling 18" overstated the orbit by 2. What structural feature
  sets `maxSF` (16-vs-18 for bb_108; the true value for bb_288) is the
  honest residue of the deficit-wall OQ — now with the right definition
  and tooling (`certify_dsafe` + descending ladders) to measure it.
- **Hunt guidance.** The battery's screens are unaffected (screens only
  ever claimed upper bounds — "necessity by construction" — and every
  S0/S1/S2 rejection stands). But *reported refutation weights* from S4
  should never be read as floors; `a14_s4_ladder.coset_query` callers
  that log `weight` now have a documented descending-ladder recipe for
  exact values.
- **Lean package: LANDED (same session), axiom-clean.**
  `QEC/Stabilizer/Framework/Homological/BBDeficitWall.lean` (new module,
  wired into the `Homological` umbrella; builds green with zero
  warnings; flagship theorems check to the standard three axioms — no
  `sorry`, no `native_decide`):
  - **L1**: `sum_conv` (the augmentation is multiplicative on
    convolutions), `cycle_support_even` (generic: odd-weight `A, B` ⟹
    every 1-cycle has even support), instantiated as
    `base_cycle_weight_even` / `cover_cycle_weight_even` (the cover
    hypotheses *descend* through `push_A`/`push_B` — only the base
    sums are assumed).
  - **L0**: `pull1_seamC` (`τ(seamC ζ) = liftStab ζ`) and
    `pull1_mem_boundaries_iff_seamCoset` — a base 1-chain pulls back
    to a cover boundary **iff** it lies in a seam coset; the forward
    chase descends the boundary witness through `liftC2_decomp` and
    takes `sheet1`.  This is the connecting-map slot `im δ₂ = ker τ₁`
    at chain level, sibling to `BBTransferH1.ker_pushH1_eq_range_pullH1`.
  - **T2**: `push1_mem_seamCoset_of_deckTrivial` (under
    `DeckTrivialOnH1`, i.e. from any `deckTrivial_of_bezout` witness,
    every cover cycle's pushforward lies in a seam coset — proof:
    `τ(p v) = v + σv` is a boundary) and
    `not_seamCosetFloor_of_light_cover_cycle` (a cover cycle of weight
    `< m` with non-boundary pushforward refutes `SeamCosetFloor m`) —
    `d_safe ≤ d̃_safe` in the repo's own predicates, the converse
    direction to `safeFloor_of_seamCosetFloor`.
  - **The wall**: `seamCosetFloor_of_even_of_pred` and
    `safeFloor_of_even_of_pred` — for even `m`, the floors at `m − 1`
    upgrade to `m` for free, so **the unique maximal failing value of
    an even target is `m − 2`**.
  Not formalized (follow-up if ever needed): L2/T1 collision
  subgroups (the mechanism is measurably silent on the codes that
  matter), and A14.1(2)'s dimension count (T2 deliberately routes
  around it via deck-triviality).
