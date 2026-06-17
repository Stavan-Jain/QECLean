# The d=12 doubling mechanism extends beyond gross: a [[336,12,12]] BB code over Z₃×Z₇

> **STATUS.** The distance value `d=12` (both covers) is **SAT-exact** (computational,
> load-bearing). The *mechanism* — why the cover doubles — is given a partial **analytic
> account**: the cover-split and the (R) null-homotopy transfer; the dangerous sector is
> `≥ 12` binding at `b = 0`, with the `b=0`/hexagon/D-pair (M) lower bounds transferring
> analytically from gross (the *achieved* minima, and the new weight-8 rung, are
> SAT-confirmed only). The Smith-class domain matches gross in *dimension* but not
> structure; the confinement transfers only as a char-2 skeleton. The **safe-sector
> confined floor** over Z₃×Z₇ is the main piece still developed only computationally. This
> is NOT "fully analytic d=12" (the A4 §0 bar) — it is "verified value + a partial analytic
> mechanism." See §6 for the exact open list. *(This draft was hardened by an adversarial
> review that corrected an earlier overclaim — the dangerous rungs reach 16/20/≥24, not 12;
> only `b=0` binds.)*

Source session artifacts: tool `scripts/a5_cover_cascade.py` (commit `73008c9`),
memory `bb-cover-cascade`. Companion: `A4_writeup.md` (the gross proof this extends),
`A5_goal2_log.md` (the goal-2 class program this grew out of).

---

## 0. Results

**Theorem (computational).** There is a bivariate-bicycle code
`[[168,12,6]]` over `G = Z₆ × Z₁₄`, with

    A = 1 + y + x³y³,    B = 1 + x + x²y⁷

(canonical representative up to full BB-equivalence; `d(base) = 6` SAT-exact), whose
free-ℤ₂ cover in the x-direction — the BB code over `Z₁₂ × Z₁₄` with the same `A, B` —
is **`[[336,12,12]]`**: its distance is exactly

    d(x-cover) = 12 = 2 · d(base),

verified by exact SAT (UNSAT through weight 11, SAT at 12). The **y-cover** over
`Z₆ × Z₂₈` (same `A, B`, deck `y ↦ y+14`) is **also `[[336,12,12]]` with `d = 12`**
(SAT-exact, UNSAT through 11). So **both** free-ℤ₂ covers of the base double — and both
carry the (R) null-homotopy (§4.1).

**Why it matters.** This is the **first** evidence that the gross "confined-frame
collapse" doubling (A4: `d(gross) = 2·d(base) = 12`) is **not specific to gross's
group**. Gross lives over `Z₆ × Z₆`, whose odd part `Z₃ × Z₃` gives a *uniform*
component ring `F₂[Z₂²] × F₄[Z₂²]⁴`. The new code's odd part `Z₃ × Z₇` gives a
*heterogeneous* ring `F₂[Z₂²] × F₄[Z₂²] × F₈[Z₂²]² × F₆₄[Z₂²]²`, where gross's
F₄-specific "co-point rigidity" engine does **not** apply — yet the doubling still
holds. The mechanism is more robust than the gross machinery that proves it.

**Analytic status, sector by sector** (the body of this note):
- The cover-split, the (R) null-homotopy, and the ρ-link confinement *skeleton* all
  **transfer**. The Smith-class domain has the same *dimension* (6) but a different internal
  structure; the one-sided floor is stronger on the A-side only.
- The **dangerous sector** `≥ 12` holds, **binding uniquely at `b = 0`** (every nonzero
  stabilizer clears 12 with margin — hexagon 16, D-pair 20, weight-8 ≥24). The `b=0`,
  hexagon, and D-pair lower bounds transfer analytically from gross; the lone gap is a
  presentation-free `m(weight-8) ≥ 2` (the new class is global, so gross's local argument
  fails — but it is far from binding, so off the critical path).
- The **safe-sector confined floor** `≥ 12` over `Z₃ × Z₇` is the main open piece.

**Conjecture.** Every Z₂²-frame *anchorable* BB base (in the sense of A5: floor-bearing
frame + multiplicity-free disjoint difference sets + mirrored projections) with
`dim ker ∂₂ = 6` and the squaring identity `(1+x²)B² = 1+x⁶` has a free-ℤ₂ x-cover with
`d = 2·d(base)`. The new code is the first instance beyond gross; `Z₆ × Z₁₈` (which has
further k=12 anchorable codes) is the next test.

---

## 1. Discovery: the cover-cascade

The code was not hand-picked. It was surfaced by a **gate cascade** that turns "can the
gross technique apply to BB code C?" into checkable predicates run on C's *base
quotient* (`scripts/a5_cover_cascade.py`). The relevant mode is `--hunt-direct`:
enumerate every Z₂×Z₂-frame group up to a cardinality cap (not just the ones in the
corpus, which for this frame is only `Z₆×Z₆`), and for each list the anchorable bases.

Two lessons from the hunt, recorded here because they are reusable traps:
1. **Structural anchorability (the A5 hypotheses (i)+(ii)+(iii)) does NOT enforce k>0.**
   The raw hunt produced 151,668 "anchorable" hits over `Z₆×Z₁₀, Z₆×Z₁₄, Z₆×Z₁₈,
   Z₁₀×Z₁₀`; under the `k>0` filter, `Z₆×Z₁₀` and `Z₁₀×Z₁₀` are **entirely degenerate**
   (k=0, not codes). Always validate a structural hit with `code_params(.).k > 0` AND an
   exact-SAT distance before calling it a base.
2. **`Z₆×Z₁₄` is real.** It yields 216 origin-anchored hits that collapse to **exactly
   one** genuinely-new `[[168,12,6]]` code up to full BB-equivalence (Aut × A↔B swap ×
   independent monomial translation; the dedup is validated by `Z₆×Z₆`'s 36 hits
   collapsing to the single gross base). All sampled members are SAT-exact `d = 6`.

---

## 2. The base code and its CRT structure

`base = [[168,12,6]]` over `G = Z₆ × Z₁₄`, `A = 1 + y + x³y³`, `B = 1 + x + x²y⁷`.
- `k = 12`, frame `Z₂ × Z₂` (2-part of each axis is exactly `Z₂`), `d = 6` (SAT-exact).
- Mirrored projection (iii): `A` is monomial in x (`π_x(A) = {x³}`), `B` monomial in y
  (`π_y(B) = {y⁷}`) — the gross §4.4 shape.
- Difference sets `dA, dB` multiplicity-free with `dA ∩ dB = ∅` (gate (ii)).

**The CRT frame.** `F₂[Z₆×Z₁₄] = F₂[Z₂²] ⊗ F₂[Z₃×Z₇]`. The odd part `Z₃ × Z₇ ≅ Z₂₁`
splits over F₂ by Frobenius orbits of its character group under `χ ↦ χ²`:

    Z₃ × Z₇  →  F₂ × F₄ × F₈ × F₈ × F₆₄ × F₆₄     (6 orbits)

versus gross's `Z₃ × Z₃ → F₂ × F₄ × F₄ × F₄ × F₄` (5 orbits, all nontrivial parts F₄).
The component multipliers `Â_j, B̂_j` are units or radicals in `F_q[Z₂²]`:

    Â_j over (F₂,F₄,F₈,F₈,F₆₄,F₆₄):  U,  U, R*,  U,  U, R*
    B̂_j over (F₂,F₄,F₈,F₈,F₆₄,F₆₄):  U, R*,  U,  U, R*, R*

This is the crux of why the doubling is non-obvious: gross's engine lemma relies on the
"co-point rigidity" of a radical multiplier `D` over `F₄[Z₂²]` — its value vector over
the four Z₂² layers has *one zero and three pairwise-distinct nonzero values*, which
works because F₄ has exactly three nonzero elements. Over `F₈` (7 nonzero) and `F₆₄`
(63 nonzero) this rigidity is simply false. So the gross floor machinery cannot be
quoted; the doubling, if true, must rest on the *robust* part of the mechanism.

---

## 3. The main result

The x-cover is the BB code over `G' = Z₁₂ × Z₁₄` with the same `A, B` (the free-ℤ₂ cover
with deck transformation `σ: x ↦ x + 6`). `k = 12`, `n = 336`. Exact SAT (pysat
in-process, no proofs) on `d_X` (= `d_Z` by the BB inversion duality):

    w ≤ 5  UNSAT (0.6s)   w ≤ 8  UNSAT (16s)
    w ≤ 6  UNSAT (2.5s)   w ≤ 11 UNSAT
    w ≤ 7  UNSAT (5.6s)   w = 12 SAT     ⟹  d(x-cover) = 12.

So `d(x-cover) = 2·d(base)`, the gross value, over a different group. The **y-cover**
(over `Z₆ × Z₂₈`, deck `y ↦ y+14`) is exact `d = 12` as well (UNSAT through 11, SAT at
12; the w≤11 UNSAT took ~43 min, the longest single call). So both free-ℤ₂ cover
directions double. (The earlier worry that the [[336]] UNSAT direction would hang was
unfounded — the in-process pysat path resolves each weight in seconds to ~tens of
minutes.)

---

## 4. Analytic account: why it doubles

The gross proof (A4 §§5–13) forces **both** homological sectors of `H₁(cover)` to
`2·d(base)`. Write `p` for the sheet-sum projection `cover → base`; `|v| ≥ |p(v)|`.
- **Dangerous sector** `[p(v)] = 0 ∈ H₁(base)`: `|v| = |b| + 2m(b)` with
  `b = p(v) ∈ Stab_Z(base)`; the *factor-2 lemma* `(M): |b| + 2m(b) ≥ 12` follows from
  the **light-stabilizer classification** + the m-rung bounds.
- **Safe sector** `[p(v)] ≠ 0`: by **(R)** the projection lands in the nonzero Smith
  classes `im Δ ∖ 0`, and the **confined floor (M-im)** forces every base 1-cycle in a
  nonzero Smith class to weight `≥ 12`.

### 4.1 What transfers (the skeleton + the target)

| Ingredient | Gross (Z₃²) | New (Z₃×Z₇) | Transfer |
|---|---|---|---|
| Cover-split `\|v\|≥\|p(v)\|`, diagonal doubling | generic | generic | verbatim |
| (R) null-homotopy `(1+x²)B² = 1+x⁶` | via `y⁶=1` | via `y¹⁴=1` | **verbatim** |
| Smith domain `dim ker ∂₂ = dim(Ann A ∩ Ann B)` | 6 (63 classes) | **6 (63 classes)** | **dimension only** (†) |
| Confinement `ρ² = 0` | radical of F₄[Z₂²] | radical of F_q[Z₂²], any q | **field-independent** (‡) |
| One-sided floor `μ(Ann A)` | 6 | **12** | stronger on the A-side only (§) |
| Target value | 12 | 12 (SAT) | — |

(†) **Only the dimension (6) and class count (63) match — the *structure* does NOT.**
The new code's nonzero `ker ∂₂` elements have weight multiset **{32:21, 48:42}** in **3
translation orbits of size 21**, versus gross's **{16:9, 18:48, 24:6}** in **5 orbits**
(sizes 9,12,36,3,3). The weights are roughly doubled but not cleanly (no 36-analogue, no
18-analogue). So the safe-sector *domain* has the same dimension to analyze, but a different
internal structure — consistent with the confined-floor dictionary being different (§4.3).

(‡) Correct but only the *skeleton*: `ρ²=0` is a formal char-2 fact and transfers to any
F_q, but the confined floor also needs the *value-rigidity* of the components, which IS
field-specific (F₄'s "one zero + three distinct values" fails over F₈/F₆₄). `ρ²=0` alone
does not reach 12; it is necessary, not sufficient.

(§) Asymmetric: `μ(Ann A) = 12` but `μ(Ann B) = 6` (same as gross's 6). The safe-sector
floor uses the A-side, so "stronger" holds where it's used, but the one-sided floor is not
uniformly stronger.

Two of these deserve a line of proof.

**The (R) null-homotopy transfers for BOTH covers.** *x-cover:*
`B² = (1+x+x²y⁷)² = 1 + x² + x⁴y¹⁴ = 1 + x² + x⁴` because `y¹⁴ = 1` (the y-axis has order
14 in base and x-cover). Then `(1+x²)·B² = (1+x²)(1+x²+x⁴) = 1 + x⁶` as a polynomial; in
the cover ring (x of order 12, `x⁶ ≠ 1`) this is the null-homotopy generator
`z = (1+x²)·B·v_L` with `∂₂ z = v + σv`, giving `σ_* = id` and `im p_* ⊆ ker τ_* = im Δ`.
Gross uses the identical identity via `y⁶ = 1`. *y-cover:* by the x↔y symmetry, `A` is the
relevant polynomial — `A² = (1+y+x³y³)² = 1 + y² + x⁶y⁶ = 1 + y² + y⁶` (x-free, since
`x⁶ = 1` on the Z₆ x-axis) — and `1 + y¹⁴` factors as `(1+y²+y⁴+y⁸)·A²` (a weight-4
multiplier rather than the x-cover's weight-2 `1+x²`, but a genuine factorization). So the
y-cover carries the same (R) reduction; its safe sector also sees only the Smith classes.

**The confinement is field-independent.** The radical of `F_q[Z₂²] = F_q[X,Y]/(X²,Y²)`
is `(X,Y)`, and for any `D ∈ (X,Y)`, `D² = 0` in characteristic 2 regardless of `q`
(every term carries `X²`, `Y²`, or `XY·(X or Y)`). So the ρ-links `ρ_i = B̂_i Â_i⁻¹`
that drive the confined floor satisfy `ρ_i² = 0` over `F₈`/`F₆₄` exactly as over `F₄`.
The radical *skeleton* of the confined frame transfers; only the value-rigidity (used by
the weight dictionary) is F₄-specific.

### 4.2 The dangerous sector — ≥ 12, binding only at `b = 0`

The light-stabilizer classification, verified computationally complete through weight 11
(SAT-enumerate `rowspan(H_Z)` via `v = x·H_Z`; parity kills odd weights), is

    84 hexagons (wt 6, μ_Z = 6)  +  21 weight-8 (one orbit, NEW)  +  504 D-pairs (wt 10)

with nothing else at weight ≤ 11. The factor-2 lemma `(M)` needs `|b|+2m(b) ≥ 12` for every
`b`. Two columns must NOT be conflated — the (M) *lower bound* that proves ≥12, and the
*achieved* dangerous minimum (the actual min-weight dangerous logical projecting to `b`,
from constrained cover-SAT; an earlier draft of this note wrongly reported the lower bound
as the achieved value):

| Class | count | (M) lower bound | **achieved** `\|b\|+2m` (SAT) |
|---|---|---|---|
| `b = 0` (diagonal) | — | `m ≥ 6` → ≥12 | **12** ← the UNIQUE binding rung |
| hexagon (wt 6) | 84 | `m ≥ 3` → ≥12 | 16 (`m = 5`) |
| D-pair (wt 10) | 504 | `m ≥ 1` → ≥12 | 20 (`m = 5`) |
| weight-8 | 21 (1 orbit) | `m ≥ 2` → ≥12 | ≥24 (`m ≥ 8`) |
| `\|b\| ≥ 12` | — | `m ≥ 0` → ≥12 | ≥12 |

So the dangerous-sector minimum is **exactly 12, achieved uniquely at `b = 0`** — the
diagonal `τ(u*)` of a weight-6 base logical `u*`, i.e. the doubling tightness witness. Every
*nonzero* stabilizer clears 12 with large margin (16 / 20 / ≥24). This mirrors gross, whose
own `b≠0` dangerous minimum is **14**, not 12 (A4 Appendix A): the hexagon/D-pair rungs are
*not* binding in either code.

- **What's analytic.** The (M) lower bounds `m(hexagon) ≥ 3`, `m(D-pair) ≥ 1`, `m(0) ≥ 6`
  are the gross coset-counting arguments; they depend on Theorem A (`d(base)=6` ⟹ no base
  cycle of weight ≤5) plus the *geometry* `|hexagon| = 6`, `|D-pair union| = 11`, which is
  identical in the new code. These **transfer** (not *purely* "given Theorem A" — they also
  use the support shapes, which happen to match). Together they prove dangerous ≥ 12.
- **The new class is non-binding, but its rung is the one analytic gap.** `dA ∩ dB = ∅`
  forces pairwise hexagon sums to weight 10 or 12, never 8, so the 21 weight-8 stabilizers
  (one orbit) are **global**: minimum decomposition **36 hexagons**, hexagon-union `U = 110`
  of 168 cells. The gross *local* coset m-rung (which needs `U ≤ 9`) is hopeless for them,
  so there is no clean analytic `m(weight-8) ≥ 2`. Computationally it is far from binding
  (achieved `m ≥ 8`, contribution ≥24) — the very globalness that defeats the local argument
  forces `m` large — so it is off the critical path for the ≥12 bound, but a presentation-
  free `m(weight-8) ≥ 2` remains open (§6).
- **Reproduction caveat (a documentation defect this review caught).** Measuring the
  achieved minima by constrained cover-SAT requires applying the BB inversion duality `Φ`
  (Lemma 2.1) to carry the stabilizer `b` into `ker(H_Z)` *before* fixing `p(v) = b`. A
  same-side reading is structurally UNSAT for every `b ≠ 0` (a `Z`-stabilizer `b` lives in
  `ker H_X`, while `p(v)` always lands in `ker H_Z`); the `b=0` control is satisfiable either
  way and returns 12, which is what validates the encoding.

Net: the dangerous sector `≥ 12` is binding only at `b = 0` (the diagonal, analytic via
Theorem A); the hexagon/D-pair lower bounds transfer from gross and clear 12 with margin;
the one genuinely new feature (weight-8) is confirmed off the critical path but lacks a
clean analytic lower bound.

### 4.3 The safe sector — the open core

The safe-sector setup transfers completely (4.1): the (R) reduction puts every safe
cover logical's projection into a nonzero Smith class, and there are the same 63 of them
(`dim ker ∂₂ = 6`). What remains is the **confined floor (M-im)**: every base 1-cycle in
a nonzero Smith class has weight `≥ 12`. In gross this is the §§10–13 program — the slot
frame, the slot-cost rules built from the layer weight dictionary `d₃`, and the
118-achiever ρ-link kill. The one ingredient that does **not** transfer is the
**dictionary**: over `Z₃ × Z₇` the per-orbit minimum layer weights are

    single nontrivial orbit:  8, 12, 14   (vs gross's flat 6)

reflecting the F₄/F₈/F₆₄ split. The slot-cost minimization and the achiever-kill must be
re-derived with these heterogeneous values. The SAT-confirmed `d = 12` fixes the target,
so the effort is justified rather than speculative — but it is genuinely undeveloped
mathematics, and it is the reason this note's headline is "value + mechanism," not "fully
analytic."

---

## 5. What this says about the technique

- The doubling is the **same mechanism** as gross, not a coincidence: it rests on the
  cover-split, a 6-dimensional Smith domain, the squaring identity, and a nilpotent-
  radical confinement — all of which are present here. Gross's uniform-F₄ engine is
  *incidental*.
- The right conjecture-level invariant is therefore structural (`dim ker ∂₂ = 6` + the
  squaring identity), **not** "monomial-equivalent to gross." The cover-cascade's
  DOUBLE_CANDIDATE gate (single ℤ₂ cover of a Z₂²-anchorable base) is the screen; this
  code is the first hit outside the gross class to survive distance verification.
- But "very similar" is not "the same proof": both sectors carry genuinely new content
  (dangerous: a new global weight-8 stabilizer class; safe: a heterogeneous dictionary).
  The technique transfers as an *architecture*; the quantitative cores are code-specific.

---

## 6. Status and next steps

**Established:** `d(base) = 6` and `d(both covers) = 12` (SAT-exact); the cover-split and the
(R) homotopy (analytic); the dangerous sector `≥ 12` binding at `b = 0` (the `b=0`/hexagon/
D-pair (M) lower bounds transfer analytically from gross; the achieved minima 12/16/20/≥24
are SAT-confirmed).

**Open:**
1. The safe-sector confined floor over `Z₃ × Z₇` — re-derive the slot-cost walk and the
   achiever-kill with the heterogeneous dictionary (8/12/14). The main missing piece
   of a full analytic `d(cover) = 12` (applies to both cover directions).
2. **Test the conjecture on the `Z₆ × Z₁₈` k=12 anchorable codes.** The adversarial review
   found **324** Z₆×Z₁₈ codes satisfying *all* hypotheses (k=12, dim ker∂₂=6, the squaring
   identity with B's y-exponent = 9) but did not finish SAT-ing their covers — this is the
   live falsification probe (if any such cover has a weight-≤6 logical, the conjecture dies).
3. A presentation-free analytic argument for `m(weight-8) ≥ 2` (off the critical path,
   since the class is non-binding — SAT gives `m ≥ 8` — but it is the lone dangerous-sector
   rung without a clean analytic lower bound, because the class is global).

**Resolved since first draft:** the y-cover `Z₆ × Z₂₈` is exact `d = 12` (both cover
directions double), and its (R) homotopy transfers (§4.1).

---

## Appendix. Verification map (reproduction)

All checks use `experiments/bb_lab/scripts/a5_cover_cascade.py` (commit `73008c9`) and
`bb_lab` (`checks.bb_check_matrices`, `codeparams.code_params`, `sat_distance.x_distance`,
`sat_distance._xor_chain`, `linalg.nullspace_f2`). Data artifacts (`data/a5/*.jsonl`) are
gitignored and regenerate on demand.

| claim | check |
|---|---|
| discovery of the code; tiers; k=0 lesson | `a5_cover_cascade.py --hunt-direct --max-card 120` |
| dedup: 216 hits = 1 code; gross's 36 = 1 code | Aut(G)×swap×translation canonical form (validated on Z₆×Z₆ → 1) |
| `k=12`, frame `Z₂²`, mirrored projections | `code_params`, `crt_frame`, `projection_report` |
| `d(base) = 6` | `x_distance(base, weight_upper_bound=7)` (= 6) |
| `d(x-cover) = 12` | `x_distance(cover Z₁₂×Z₁₄, weight_upper_bound=13, verbose)` (UNSAT≤11, SAT 12) |
| CRT split `F₂·F₄·F₈²·F₆₄²` | `orbit_fields((3,7))` field sizes |
| (R) identity `(1+x²)B² = 1+x⁶` via `y¹⁴=1` | polynomial multiply, `B²=1+x²+x⁴` |
| `dim ker ∂₂ = 6` | `nullspace_f2([M_B; M_A]).shape[0]` |
| `μ(Ann A) = 12` | `nullspace_f2(M_A)` + min-weight-in-basis |
| light-stab classification (84 hex + 504 D-pair + 21 wt-8) | SAT-enumerate `rowspan H_Z` at each even weight ≤ 10 |
| weight-8 globalness `r=36, U=110`, 1 orbit | GF(2) solve `x·H_Z=b` over the 64-coset; translation orbits |
| Smith-domain structure {32:21, 48:42}, 3 orbits | weights + translation orbits of nonzero `ker ∂₂` |
| achieved dangerous minima (b=0→12, hex→16, D-pair→20, wt8→≥24) | constrained cover-SAT with the duality fix below |
| dictionary `8/12/14` over Z₃×Z₇ | `layer_dictionary((3,7), orbit_fields((3,7)))` |

**The constrained cover-SAT (corrected encoding).** To find the min-weight dangerous logical
projecting to a stabilizer `b`: constrain a cover `X`-logical `v` (`H_Z^cov v = 0`, nontrivial
against `find_logical_z`), and fix `p(v) = Φ(b)` where `Φ` is the BB inversion duality
(Lemma 2.1, `g ↦ −g`, swapping the L/R blocks) that carries the `Z`-stabilizer `b` (which
lives in `ker H_X`) into `ker H_Z` so that `p(v)` can equal it. **Without `Φ` the constraint
`p(v) = b` is UNSAT for every `b ≠ 0`** (type mismatch) — a defect in an earlier draft of
this appendix that the adversarial review caught; the `b = 0` control is satisfiable either
way and must return 12. Projection (x-double): cover qubit `(blk, x', y')` ↦ base
`(blk, x' mod 6, y')`; the two cover preimages of base `(blk, x, y)` are `(x, y)` and
`(x+6, y)` in the same block; `p(v) = Φ(b)` is encoded as 168 constraints
`XOR(v[p₀], v[p₁]) = Φ(b)[q]`.
