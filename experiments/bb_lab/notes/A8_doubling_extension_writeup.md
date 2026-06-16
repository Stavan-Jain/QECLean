# The d=12 doubling mechanism extends beyond gross: a [[336,12,12]] BB code over Z₃×Z₇

> **STATUS.** The distance value `d=12` is **SAT-exact** (computational, load-bearing).
> The *mechanism* — why the cover doubles — is given an **analytic account**: the
> cover-split skeleton, the (R) null-homotopy, the Smith-class domain, the
> confinement, and the entire **dangerous sector** transfer from / re-derive over the
> new group; the **safe-sector confined floor** is the single piece still developed
> only computationally. This note is the honest write-up of that state. It is NOT a
> claim of "fully analytic d=12" for this code (the A4 §0 bar) — it is "verified value
> + analytic mechanism modulo one sector."

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

verified by exact SAT (UNSAT through weight 11, SAT at 12). The y-cover over `Z₆ × Z₂₈`
likewise has `d ≥ 7` (a doubling effect; exact value not pushed).

**Why it matters.** This is the **first** evidence that the gross "confined-frame
collapse" doubling (A4: `d(gross) = 2·d(base) = 12`) is **not specific to gross's
group**. Gross lives over `Z₆ × Z₆`, whose odd part `Z₃ × Z₃` gives a *uniform*
component ring `F₂[Z₂²] × F₄[Z₂²]⁴`. The new code's odd part `Z₃ × Z₇` gives a
*heterogeneous* ring `F₂[Z₂²] × F₄[Z₂²] × F₈[Z₂²]² × F₆₄[Z₂²]²`, where gross's
F₄-specific "co-point rigidity" engine does **not** apply — yet the doubling still
holds. The mechanism is more robust than the gross machinery that proves it.

**Analytic status, sector by sector** (the body of this note):
- The cover-split, the (R) null-homotopy, the 6-dimensional Smith-class domain, and the
  ρ-link confinement all **transfer** (some verbatim, some by a field-independent
  argument). The one-sided floor is *stronger* than gross's.
- The **dangerous sector** `≥ 12` is **closed** (its binding rungs transfer; the one new
  stabilizer class is shown non-binding).
- The **safe-sector confined floor** `≥ 12` over `Z₃ × Z₇` is the single open piece.

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

So `d(x-cover) = 2·d(base)`, the gross value, over a different group. (The earlier
worry that the [[336]] UNSAT direction would hang was unfounded — the in-process pysat
path resolves each weight in seconds to a few minutes.)

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
| Smith domain `dim ker ∂₂ = dim(Ann A ∩ Ann B)` | 6 (63 classes) | **6 (63 classes)** | **identical** |
| Confinement `ρ² = 0` | radical of F₄[Z₂²] | radical of F_q[Z₂²], any q | **field-independent** |
| One-sided floor `μ(Ann A)` | 6 | **12** | stronger |
| Target value | 12 | 12 (SAT) | — |

Two of these deserve a line of proof.

**The (R) null-homotopy is verbatim.** `B² = (1+x+x²y⁷)² = 1 + x² + x⁴y¹⁴ = 1 + x² + x⁴`
because `y¹⁴ = 1` (the y-axis has order 14 in both base and cover). Then
`(1+x²)·B² = (1+x²)(1+x²+x⁴) = 1 + x⁶` as a polynomial. In the cover ring (x of order
12, `x⁶ ≠ 1`) this is the nontrivial null-homotopy generator `z = (1+x²)·B·v_L` with
`∂₂ z = v + σv`, giving `σ_* = id` and hence `im p_* ⊆ ker τ_* = im Δ` — the safe sector
sees only the Smith classes. Gross uses the identical identity via `y⁶ = 1`.

**The confinement is field-independent.** The radical of `F_q[Z₂²] = F_q[X,Y]/(X²,Y²)`
is `(X,Y)`, and for any `D ∈ (X,Y)`, `D² = 0` in characteristic 2 regardless of `q`
(every term carries `X²`, `Y²`, or `XY·(X or Y)`). So the ρ-links `ρ_i = B̂_i Â_i⁻¹`
that drive the confined floor satisfy `ρ_i² = 0` over `F₈`/`F₆₄` exactly as over `F₄`.
The radical *skeleton* of the confined frame transfers; only the value-rigidity (used by
the weight dictionary) is F₄-specific.

### 4.2 The dangerous sector — closed

The light-stabilizer classification, verified computationally complete through weight 11
(SAT-enumerate `rowspan(H_Z)` via `v = x·H_Z`; parity kills odd weights):

| Class | count | structure | m-rung | `\|b\|+2m` |
|---|---|---|---|---|
| `b = 0` | — | — | `m ≥ 6` | 12 |
| hexagon (wt 6) | 84 | `∂₂δ_g`, **local** | `m ≥ 3` | **12** |
| D-pair (wt 10) | 504 | `∂₂(δ_g+δ_{g+d})`, **local** | `m ≥ 1` | **12** |
| weight-8 | 21 (1 orbit) | **global** (NEW) | `m ≥ 3` | 14 |
| `\|b\| ≥ 12` | — | — | `m ≥ 0` | ≥12 |

- `μ_Z = 6`; the 84 weight-6 stabilizers are exactly the hexagons, the 504 weight-10
  exactly the D-pairs — the **binding** rungs, both giving exactly 12. They are *local*
  (hexagon support 6, D-pair support/union 11), so the gross m-rung bounds
  (`m(hexagon) ≥ 3`, `m(D-pair) ≥ 1`) — which are the generic coset-counting arguments
  depending only on Theorem A (`d(base) = 6` ⟹ no base cycle of weight ≤ 5) — **transfer
  verbatim**.
- **The new class.** `dA ∩ dB = ∅` forces every *pairwise* hexagon sum to weight 10 or
  12, never 8. So the 21 weight-8 stabilizers (one translation orbit) are **not** local
  pairwise objects: each has minimum decomposition **36 hexagons** with hexagon-union
  `U = 110` of 168 cells. The gross local coset m-rung (which needs `U ≤ 9`) is therefore
  hopeless for them. **But** a constrained cover-SAT — the minimum-weight dangerous
  logical `v` with `p(v) = b` — returns `|v| > 12`, i.e. `m(weight-8) ≥ 3` and a
  contribution `8 + 2·3 = 14 > 12`. The resolution is structural: the very *globalness*
  that breaks the local argument is exactly why `m` is large — a dangerous logical
  projecting to a spread-out stabilizer must itself be heavy. The weight-8 class is
  **non-binding** and harmless. (By the single orbit + seam-transport covariance, `m ≥ 3`
  for all 21.)

Net: the dangerous sector `≥ 12` rests on the binding hexagon/D-pair rungs, which
transfer from gross; the one genuinely new feature is confirmed off the critical path.

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

**Established:** `d(base) = 6` and `d(x-cover) = 12` (SAT-exact); the cover-split, (R),
Smith domain, confinement, one-sided floor (analytic / structural); the dangerous sector
`≥ 12` (binding rungs transfer analytically; the new weight-8 class verified non-binding).

**Open:**
1. The safe-sector confined floor over `Z₃ × Z₇` — re-derive the slot-cost walk and the
   achiever-kill with the heterogeneous dictionary (8/12/14). The single missing piece
   of a full analytic `d(x-cover) = 12`.
2. The y-cover `Z₆ × Z₂₈` exact distance (only `≥ 7` checked).
3. Test the conjecture on the `Z₆ × Z₁₈` k=12 anchorable codes (SAT their covers).
4. A presentation-free analytic argument for `m(weight-8) ≥ 2` (off the critical path,
   since the class is non-binding, but it would make the dangerous-sector write-up
   self-contained without the constrained SAT).

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
| `m(weight-8) ≥ 3` (`\|v\|>12`) | constrained cover-SAT: cover cycle, nontrivial, `p(v)=b`, min weight |
| dictionary `8/12/14` over Z₃×Z₇ | `layer_dictionary((3,7), orbit_fields((3,7)))` |

The cover-SAT projection map (x-double): cover qubit `(blk, x', y')` ↦ base
`(blk, x' mod 6, y')`; the two cover preimages of base `(blk, x, y)` are `(x, y)` and
`(x+6, y)` in the same block; `p(v) = b` is encoded as 168 constraints
`XOR(v[p₀], v[p₁]) = b[q]`.
