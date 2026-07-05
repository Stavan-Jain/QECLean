# A14 — OQ4: a safe-floor criterion (necessary screens for condition 3)

**Status: Phases 0–2 and 4 COMPLETE (§§9–12), plus the rung-2 tower
battery (§13). Battery power 86% cheap-tier / 100% with S4 on decidable
frames, zero false rejects throughout; hit3/4/6-y safe floors
SAT-CERTIFIED (5 orbit reps each, ~25 s); bb_288 SF-refuted on BOTH
axes; gross safe floor independently SAT-cross-checked. Tower result
(§13): every proven rung-1 double, re-doubled on the same axis,
**freezes at its rung-1 distance** (all five rung-2 safe floors refuted
with weight-`d(rung-1)` light classes; SAT confirms `d_X ≤ d(rung-1)`
on all) — the toric same-axis bottleneck, now certified. Write-up
shipped. Remaining (optional): Phase 3 — the Lean lemma package for
Prop A14.1(1)–(2) in `BBDoubling.lean`, coordinated with A13-L2b's
exactness chase (`push0_surjective`).**
Branch: `claude/a14-safe-floor-criterion` (off `claude/a13-bockstein-equality`,
which carries PR #53's parametric cover layer and the A13 Lean modules).
Scripts: [`a14_seam_formula_check.py`](../scripts/a14_seam_formula_check.py)
(Phase 0 gate).

## 0. The question (A12 §8, OQ4)

> **OQ4 — A safe-floor criterion (the next rung of the template).** With
> condition 2 now free given the k-check, the doubling separation lives
> provably in condition 3's safe floor (cross-session corroborated: same
> (R)/R1 rates on doubles and failures; separation visible only in
> safe-class coset minima). Open: any ideal/character-theoretic *necessary*
> condition for `safe floor ≥ 2d(base)` — e.g. a Smith-heavy-class
> reformulation of `im p_*` — that is cover-class-generic? Honest
> expectation: the floor is value-carrying (engine/SAT territory; the
> [[288,12,18]] anti-instance shows it genuinely fails off-frame), so aim
> for cheap necessary screens to sharpen A9-style hunts, not a full
> criterion.

**Scope discipline (fixed up front).** Two facts from A11 bound what this
fork can honestly claim:

1. The safe floor is *sufficient* for doubling (C-safe: 0/465 violations)
   but **not necessary** — 41 of the 152 T1 doublers are overlap-rescued
   (`|v| = |p(v)| + 2·overlap` clears `2d` even though the projected coset
   dips below). Every claim in this fork is pinned to **SF** (the safe
   floor itself, the template's provability bottleneck), never to
   "doubling".
2. SF is **presentation-sensitive** (equivalent presentations re-route
   `im p_*` through different base classes — hit3's stored x-cover d = 6
   vs its anchorable presentation's d = 12). All screens are evaluated on
   the pinned presentation; the only symmetry we exploit below is
   G-translation, which fixes the presentation. Aut(G)-orbits do **not**.

Deliverable shape (per OQ4's own framing): a battery of *necessary* screens
with (a) one-paragraph necessity proofs, (b) measured rejection power on
the known SF-failure corpus, (c) integration into the A9 hunt, plus (d) a
small structural proposition (§2) that makes the safe sector canonical —
the "Smith-heavy-class reformulation of `im p_*`" OQ4 names.

## 1. The object, pinned down

Fix the free ℤ₂ BB cover conventions of A12 §1: cover group
`G̃ = Z_{2ℓ} × Z_m`, base `G = Z_ℓ × Z_m`, same polynomials (canonical
same-exponent lift), deck `s = x^ℓ`, `ε = 1 + s`, `R̃ = F₂[G̃]`,
`R = F₂[G] = R̃/(ε)`. Chain complexes are the Koszul complexes; **this
note uses the repo's block order** (`BBChainComplex.lean`):
`∂₂(f) = (A·f, B·f)` (block 0 = A, block 1 = B) and
`∂₁(u,v) = B·u + A·v`. (The A12 note writes the blocks swapped,
`∂₂ = (B,A)`; all statements are symmetric under the swap.)

The template's condition 3, safe half, is the Lean predicate
`SeamCosetFloor m` (`BBDoubling.lean`):

```
∀ ζ : H → ZMod 2, ∂₂ ζ = 0 → ∀ f : H → ZMod 2,
  seamC ζ + ∂₂ f ∉ boundaries → m ≤ chainWeight (seamC ζ + ∂₂ f)
```

with `seamC ζ = sheet1 (∂₂^cover (liftC2 ζ))` (`BBCover.lean`, the
chain-level Smith connecting map). `safeFloor_of_seamCosetFloor` turns this
into `SafeFloor m` (every cover cycle with non-boundary pushforward weighs
≥ m) via (R) plus the sheet inequality `|v| ≥ |p(v)|`. So:

**SF(A, B, ℓ) := SeamCosetFloor (2·d(base))** — a statement purely about
the *base* code and the seam classes. Gross discharges it with the CRT/F₄
MIm engine (63 classes); pair72 with three `2¹⁸` kernel sweeps; nothing
else discharges it today.

## 2. Proposition A14.1 — under (R) the safe sector is canonical

Everything below assumes the cover satisfies **(R)**, which by Theorem A12
is equivalent to `k̃ = k` and to the Bezout membership `ε ∈ (A,B) ⊆ R̃`.
Write the transfer LES of the SES `0 → K̄ →^τ K →^p K̄ → 0`
(`τ = ε·lift`, `p = mod-ε`):

```
H₂K̄ →^{τ₂} H₂K →^{p₂} H₂K̄ →^{δ₂} H₁K̄ →^{τ₁} H₁K →^{p₁} H₁K̄ →^{δ₁} H₀K̄ → ⋯
```

Recall from A12 Lemma 0 (base version): `k = 2·dim R/(A,B)`,
`dim H₂(K̄) = dim ann_R(A,B) = dim R/(A,B) = k/2 = dim H₀(K̄)`.

**Proposition A14.1.**

1. **(p₂ vanishes; Δ = δ₂ is injective.)** `p₂ = 0`, hence
   `ker δ₂ = im p₂ = 0` and `dim im δ₂ = k/2`.
2. **(The safe sector is exactly `im Δ`, and the §3-doc "observations"
   are theorems.)** `im p₁ = ker τ₁ = im δ₂` (each of dimension `k/2`),
   `ker p₁ = im τ₁` (dimension `k/2`), `ker δ₁ = im δ₂` — in particular
   the Bockstein composite `δ₁∘δ₂` vanishes **automatically at `k̃ = k`**
   (OQ2's content lives entirely off the doubling regime) — and `δ₁` is
   surjective, so `p₀ : H₀(K) ≅ H₀(K̄)`.
3. **(Explicit representatives: the seam-carry formula.)** For a base
   2-cycle `ζ ∈ ker ∂₂ = ann_R(A,B)`, `δ₂[ζ] = [seamC ζ]`, and with the
   canonical (x-degree < ℓ) lifts,

   `seamC(ζ)(q, 0) = (Ã·ζ̃)(q_x + ℓ, q_y)`, `seamC(ζ)(q, 1) = (B̃·ζ̃)(q_x + ℓ, q_y)`

   for `q = (q_x, q_y) ∈ G`, `q_x < ℓ` — i.e. the **x-carry masks** of the
   lifted stabilizer products: the sum of monomial products whose x-degrees
   sum past `ℓ`, re-read at degree − ℓ. A closed polynomial formula; no
   division, no SAT.
4. **(G-orbit transport.)** `δ₂` is `R`-linear, so `δ₂[g·ζ] = g·δ₂[ζ]`
   for `g ∈ G`; multiplication by `g` permutes each C₁ block and fixes
   `im ∂₂`; hence **coset minima are constant on G-translation orbits of
   `ker ∂₂ \ 0`**. (At chain level `seamC(g·ζ)` and `g·seamC(ζ)` may
   differ by a boundary when the x-translation re-wraps the section —
   equality holds at class level, which is all the minima see. Pure
   y-translations commute with the sheet split, recovering gross's
   13-y-orbit MIm transport as the chain-level special case.)
5. **(SF, reformulated.)** Under (R),

   `SF ⟺ ∀ ζ over G-orbit representatives of ker ∂₂(base) \ 0 : min_{f ∈ C₂(base)} |seamC ζ + ∂₂ f| ≥ 2d(base).`

   No class-nonvanishing side condition is needed (injectivity of `δ₂`
   makes every `ζ ≠ 0` a genuinely nonzero class; `ζ = 0` is vacuous).

*Proofs.*

(1) Since `C₃ = 0`, `H₂(K) = ker ∂̃₂ = ann_{R̃}(A,B)`. If
`z ∈ ann_{R̃}(A,B)` then `z·(A,B) = 0`, and (R) gives `ε ∈ (A,B)`, so
`εz = 0`, so `z ∈ ann(ε) = εR̃` (freeness of the cover). Hence
`p(z) = z mod ε = 0`; as `H₂(K̄)` has no boundaries to quotient by,
`p₂[z] = 0` on the nose. Exactness at the second `H₂(K̄)` gives
`ker δ₂ = im p₂ = 0`, and `dim im δ₂ = dim H₂(K̄) = k/2`. ∎

(2) `ker τ₁ = im δ₂` and `ker p₁ = im τ₁` are LES exactness (no
hypothesis). So `rank τ₁ = k − k/2 = k/2 = dim ker p₁`, and
`rank p₁ = k̃ − k/2 = k/2` using `k̃ = k`. The linchpin (A12: chain
identity `τ∘p = 1+σ` plus (R)) gives `τ₁∘p₁ = ε_* = 0`, i.e.
`im p₁ ⊆ ker τ₁ = im δ₂`; equal dimensions force equality. Exactness at
the third slot gives `ker δ₁ = im p₁ = im δ₂` (so `δ₁∘δ₂ = 0`), whence
`rank δ₁ = k − k/2 = k/2 = dim H₀(K̄)`: `δ₁` surjective, `τ₀ = 0`, and
`p₀` is an isomorphism (consistently, `dim H₀(K) = k̃/2 = k/2`). ∎

(3) The connecting-map recipe: lift `ζ` to `ζ̃` (canonical section), take
`∂̃₂ ζ̃ ∈ C̃₁`; its pushforward is `∂₂ ζ = 0`, so `∂̃₂ ζ̃ ∈ ker p = im τ`,
and `δ₂[ζ] = [τ⁻¹(∂̃₂ ζ̃)]`. For `w = εu ∈ im τ` the two sheets of `w`
agree as base chains (`(εu)_{sheet0} = ū₀ + ū₁ = (εu)_{sheet1}` after
degree reduction) and `τ⁻¹(w)` *is* that common sheet — which for
`∂̃₂ ζ̃ = (Ã ζ̃, B̃ ζ̃)` is exactly the sheet-1 (x-degree ≥ ℓ) part, the
carry masks as displayed. This is literally `BBCover.seamC`
(`sheet1 ∘ liftStab`), so the Lean predicate and the formula coincide
definitionally. ∎

(4) `τ` and `p` are maps of `R̃`-module complexes (`τ(r·v̄) = r·τ(v̄)`
since the lift ambiguity dies in `ε²  = 0`), so the connecting map is
`R̃`-linear, hence `R`-linear (`ε` kills both sides). Multiplication by a
group element is a coordinate permutation on each block preserving
`im ∂₂` and Hamming weight, so it maps the coset of `δ₂[ζ]` bijectively
onto the coset of `δ₂[g·ζ]` preserving weights. ∎

(5) Immediate from (1), (3), (4) and the definition of
`SeamCosetFloor`. ∎

**Remarks.** (i) The proof of (1) is ideal-theoretic — exactly the OQ4
flavor: the Bezout witness that certifies (R) *also* pins the safe
sector's size. (ii) Statement (2) upgrades the extensibility-doc §3
bullets ("`im Δ` and `ker p_*` are each exactly half of `k`",
"`im τ_* = ker p_*`") from per-instance observations to theorems, and
shows the observed instance values (`rank p_* = 2` for pair72, 6 for
gross; 3 resp. 63 Smith classes) are forced. (iii) `ker ∂₂ = ann_R(A,B)`
gives the safe classes a *module* structure — (4) is its cheapest
consequence; the character/ideal decomposition of `ann(A,B)` is where
tier S2 (§4) digs.

## 3. Corollary: what a necessary screen is

By §2(5), SF is a conjunction of per-orbit-representative coset-minimum
bounds. Hence **any procedure that produces (or certifies the existence
of) a coset element of weight < 2d for some `ζ ≠ 0` refutes SF** — and
every screen below is such a producer. Necessity proofs are one-line by
construction; the design question is only *power per unit cost*, measured
on the corpus of §5.

Two corroborating gross data points (A_HANDOFF cheat-sheet, discovery
grade): the base's 84 weight-6 logicals all lie **outside** `im Δ`
(`imΔ-distance = 12` while `d(base) = 6`) — gross passes SF precisely
because the light locus misses the safe sector (screen S3's picture) —
and `ker ∂₂` min weight is 16 (the sparse-2-cycle inputs to S0 are
themselves heavy).

## 4. The screen battery

Ordered by cost. All are frame-agnostic (no `Z₃²`/elementary-abelian
assumption); all run base-side only (no cover SAT anywhere).

- **S0 — raw seam weights** (closed form, ~free).
  Reject if `|seamC(ζ)| < 2d` for some orbit rep `ζ`. Cost:
  `(2^{k/2}−1)/orbit` products of the two cover polynomials with lifted
  kernel elements. Necessity: `seamC(ζ)` is the `f = 0` coset element.

- **S1 — budgeted boundary descent** (cheap).
  From `seamC(ζ)`, greedily add `∂₂(monomial)` while weight decreases
  (bounded rounds; also the one-shot sweep over all `|G|` single-monomial
  `f`). Reject on any dip below `2d`. Necessity: the reached element is
  exhibited.

- **S2 — unit-sector reduction** (the ideal/character-theoretic tier;
  the research content).
  CRT-split `R` over the odd part: `R = ⊕_χ T_χ`, `T_χ = S[P]` local.
  Wherever the seam's `χ`-component lies in `(A_χ, B_χ)T_χ` (in
  particular wherever some combination of `A_χ, B_χ` is a unit), cancel
  it *exactly*; assemble the per-block `f_χ` through CRT into one global
  `f` — a genuine coset element supported on the singular sectors, plus a
  pinned-spectrum report saying which classes even need SAT. Char-2
  algebraic identities (the Frobenius-square family that produced the
  base-floor counterexample) re-enter here with the correct polarity, as
  lightness-certificate generators. Necessity: the assembled `f` is
  explicit.

- **S3 — light-class database** (amortized linear algebra).
  Per base code, accumulate every H₁ class ever *observed* light
  (weight-< 2d logicals from any SAT/ladder/census run, on any
  presentation of that base). Reject a cover candidate if
  `δ₂(H₂) ∩ lightTable ≠ 0` (rank computations). This is the amortized
  form of A11's presentation-sensitivity: same base, different
  presentation ⟹ different `im Δ` tested against one shared table.
  Necessity: the table stores witnesses.

- **S4 — budgeted witness-SAT** (the strongest; still cheap-side only).
  A11's base-side coset ladder (`a11_s3_diagnose.py safefloor` shape),
  capped at weight `2d − 1` and time-boxed, per orbit rep. A witness
  rejects with certificate; a timeout is *no verdict* (never claim the
  floor from a timeout — that is the expensive UNSAT side, exactly what
  screens exist to avoid).

**Positive-side byproduct (not a screen).** S2's sector analysis plus
§2(4)'s transport is the first half of the gross MIm engine stated
generically; whatever survives the screens on the hit3/4/6 targets is
also the start of the engine re-instantiation their `d = 12` proofs need.

## 5. Validation corpus and metrics

| Set | Size | Role |
|---|---|---|
| SF-true doublers (A11 T1 stream) | 111 | **Soundness** — a necessary screen must reject none |
| gross + pair72 + A8-anchorable cells | 2 + 7 | Soundness (proof-grade floors) |
| SF-fail rows (A11) | 322 | **Power** — % rejected, per screen, at what cost |
| Overlap-rescued doublers | 41 | SF-false: rejection is *correct* here (they are not SF-certifiable); sanity only |
| A10 hard-negative bases (492 orbit cells) | 13 | Must-catch negatives |
| [[288,12,18]] → [[576]] anti-instance | 1 | Headline off-frame test (`d_safe ≤ 24 < 36`) |
| hit3/4/6, Z₆×Z₁₄, Z₆×Z₁₈ | 5+ | The live targets to re-rank |

Metrics: per screen — false-reject count on the soundness set (must be
0), rejection rate on the power set, marginal rejections over the cheaper
tiers, wall-clock per candidate. Output: ranked battery + recommended
column order for `a9_lean_target_screen.py`.

## 6. Phases and gates

- **Phase 0 — structure + conventions (this session).** Prop A14.1 on
  paper (§2); `a14_seam_formula_check.py` reproduces the three
  `SeamTables.lean` literals **bit-for-bit** from the carry formula,
  re-derives the pair72 floors (8/8/8) by direct `2¹⁸` sweep, checks
  `p₂ = 0` / `Δ` injective / `im p₁ = im δ₂` on pair72 *and* gross,
  computes gross's 63 raw seam weights (all must be ≥ 12 — consistency
  with the proven MIm floor) and its orbit structure, and runs the CE2
  negative control ((R) fails ⟹ the linchpin and (1) genuinely break).
  *Gate: all checks green; any seam mismatch = convention bug, stop.*
- **Phase 1 — harness + cheap screens (1 session).** S0/S1/S3 over the
  §5 corpus; soundness gate; first power table. *Decision: if S0+S1
  already reject ≳ 80% of the 322, S2 becomes optional polish.*
- **Phase 2 — sector tier + integration (1–2 sessions).** S2, S4;
  necessity proofs written out; battery ranked; new columns wired into
  the A9 screen; re-rank hit3/4/6 and the T1 pool (the concrete payoff:
  choose where the engine re-instantiation goes).
- **Phase 3 — Lean package (1 session, optional).** Prop A14.1(1)–(2) in
  `BBDoubling.lean`, sharing the exactness diagram chase
  (`push0_surjective` etc.) that A13-L2b Phase 1 needs anyway — land it
  once, consume twice. Optionally `seamCosetFloor_of_classTable` (floor
  leaves reusable across covers of one base).
- **Phase 4 — write-up (½ session).** Results appended here; extensibility
  doc §3 (observed → theorem) and §7 (A9 integration); `research_log.md`;
  OQ4 status line in A12 §8.

**Out of scope, queued as follow-on:** the overlap-term necessity half
(`min |p(v)| + 2|v₀ ∧ v₁| ≥ 2d` on light reachable classes; model system
Z₃×Z₄:y per A11) — that upgrades SF-screens to *doubling*-screens; and
the rung-wise family version along `Z_{2^r}` towers (tour-de-gross), where
A13's tower theorem supplies the k-row and SF must be screened per rung.

## 7. What this consumes from A12/A13 (and what it doesn't)

- **From PR #53 (on this branch):** the formal object (`SeamCosetFloor`,
  `safeFloor_of_seamCosetFloor`, `seamC`), the pair72 ground truth
  (`SeamTables.lean`, floors 8/8/8), and the A9 hunt this sharpens.
- **From A12:** the (R) ⟺ `k̃ = k` ⟺ Bezout theorem (used in A14.1(1)),
  the linchpin-iff, and the LES bookkeeping.
- **From A13:** `BBBocksteinRank.lean`'s exactness/diagram-chase core =
  the same instantiation Phase 3 needs; `BBEpsFree` as the clean language
  for `ann(ε) = (ε)` steps. **Non-dependency:** the deck-module structure
  theorem is vacuous at `k̃ = k` (trivial deck action) — OQ4 does *not*
  wait on the `Module.Free F₂[⟨σ⟩] F₂[G]` gap. Conversely A14.1(2) shows
  `δ₁∘δ₂ = 0` is automatic on the doubling regime, sharpening where OQ2's
  remaining content lives (only `k̃ > k`).
- **From A11/A10/A9:** the corpus, the C-safe baseline, the
  presentation-sensitivity rule, and the ladder tooling S4 reuses.

## 8. Risks / claim discipline

- **Low marginal power** beyond S0/S3 is a live possibility (the floor is
  value-carrying). That outcome is still the OQ4 answer — "no shallow
  structure separates light from heavy safe classes" — and S4's
  witness-side remains a real hunt accelerator. The plan does not bet on
  S2 being strong.
- **Never** claim necessity-for-doubling (41 overlap rescues), never read
  a screen timeout as a floor, never orbit-maximize before screening
  (Aut-orbits change the presentation; only G-translations are safe).
- **Convention drift** between lab and repo (block order, section, sheet)
  is killed at the Phase-0 gate by the bit-for-bit SeamTables comparison.

## 9. Phase 0 log (2026-07-04) — gate GREEN, 30/30

`uv run python scripts/a14_seam_formula_check.py` — all checks pass on
first run (pure numpy, seconds). Conventions locked: repo block order
(block 0 = A, block 1 = B), canonical section `x < ℓ`, sheet-1 read at
`x + ℓ`, block-major C₁ layout, row-major cells.

**pair72 (16 checks).** The carry formula reproduces all three
`SeamTables.lean` literals **bit-for-bit** on the `MaskDefs` kernel basis
(each weight 12); the three classes are non-boundary; the direct `2¹⁸`
sweeps give coset minima **8/8/8** (144 minimizing chains each) — the
Lean floors re-derived independently. Prop A14.1 numerics: `p₂ = 0`,
`dim im δ₂ = 2` (injective), `im p₁ = im δ₂` (union rank 2), and the
class-level G-transport `[seamC(g·ζ)] = g·[seamC(ζ)]` holds for **all**
18 translations × 3 classes.

**gross base (9 checks).** `k = k̃ = 12`; `dim ker ∂₂ = 6`; `p₂ = 0`;
`δ₂` injective (dim 6); `im p₁ = im δ₂`. **S0 data: all 63 raw seam
weights ≥ 12, histogram `{12: 18, 14: 12, 16: 15, 18: 12, 20: 6}`.**
Two findings beyond the gate:

- **S0 is tight on gross**: the 18 classes with raw seam weight 12 have
  coset minimum *exactly* 12 (raw seam is a coset element; the proven MIm
  floor gives ≥ 12). The MIm engine only ever needed `≥`; the raw-seam
  table pins those 18 exactly, for free.
- **Full-G transport beats the engine's y-transport**: the 63 classes
  fall into **13 y-orbits** (exactly the MIm `T_y`-transport count —
  independent corroboration) but only **5 full-G orbits**. A14.1(4)'s
  class-level x-transport is thus worth a further 2.6× reduction: a
  gross-shaped safe floor needs only **5** per-orbit-rep floors, not 13.
  Directly relevant to the hit3/4/6 engine re-instantiation.

**CE2 negative control (5 checks).** `k` jumps 8 → 16; `p₂ ≠ 0`;
`δ₂ = 0` (against `dim H₂(base) = 4`); `im p₁` (dim 8) ⊄ `im δ₂` — every
conclusion of Prop A14.1 fails without (R), and the `δ₂ = 0` value is the
one forced by the A12 bookkeeping at the `k̃ = 2k` boundary
(`k̃ − k = dim ker δ₁ − dim im δ₂` with `ker δ₁ ≤ k`). The hypothesis is
load-bearing, not decorative.

**Gate verdict:** seam formula and Prop A14.1 are safe to build Phase 1
on; no convention drift between lab and repo.

## 10. Phase 1 log (2026-07-04) — gate GREEN

`uv run python scripts/a14_safe_floor_screens.py` (57 s). Outputs:
`data/a14/t1_screens.jsonl` (all 638 rows: recomputed exact minima +
screen verdicts), `data/a14/anchors_screens.jsonl`,
`data/a14/phase2_gap_rows.jsonl`.

**Ground truth recomputed for every row.** All T1 frames have ≤ 24 base
cells, so the per-class coset minima are *exact* (direct enumeration of
`im ∂₂`, float32-GEMM chunked). Cross-validation: **0/152 mismatches**
against the A9 profiles' `safe_class_minima`/`safe_floor_ok` — two
independent code paths agree on every doubler. 617 rows scoped
(21 `k_changed` rows excluded — out of SF scope, as (R) fails).

**Corpus census (recomputed):**

| set | n | SF-true | SF-false |
|---|---|---|---|
| DOUBLES | 152 | 111 (= A11) | 41 overlap-rescued (= A11) |
| shorts | 465 | **0** | **465** |

Every single k-preserving short fails the safe floor. Combined with the
doubler column: **on the T1 direct-sweep frames, SF-true ⟹ doubles with
no exceptions (111/111)** — the safe floor alone, no tight-witness
conjunct needed, is empirically sufficient here; it remains non-necessary
(the 41 rescues). (A11's "322" figure was the light-floor count over the
13 hard-negative bases' 492 orbit cells, not over the 465 shorts —
denominator clarified, no conflict.)

**Soundness: 0 false rejections** on the 111 SF-true rows, for both S0
and S1 (theorem-guaranteed for S0; empirically confirms the
implementation), and on the proof-grade anchors (pair72: S1 descends
12 → 8 = the exact floor, does not dip below; gross: raw and descended
minima sit at exactly 12 — greedy cannot cross the proven MIm floor).

**Power on the 506 SF-false rows (465 shorts + 41 rescued):**

| screen | rejects | rate |
|---|---|---|
| S0 (raw seam < 2d) | 288 | 57% |
| S0 + S1 (greedy descent) | 378 | **75%** |

Per frame:axis (SF-false, caught): Z3xZ3 6/6, Z3xZ4:x 21/30,
Z3xZ4:y 24/41, Z3xZ5:x 50/62, Z3xZ5:y 50/67, **Z3xZ6:x 84/84**,
Z3xZ6:y 60/92, Z4xZ6:x 63/91, Z4xZ6:y 20/33.

**bb_288 anti-instance: S0 alone catches it.** The [[288,12,18]]
x-double's raw seam minimum is **24** — below the floor 36, and exactly
the known `d_safe ≤ 24` bound that previously took a SAT run. The
headline off-frame failure needs no solver. The y-double passes S0/S1
(raw min 48 ≥ 36): its SF status is genuinely open — first concrete S4
target.

**Residual gap: 128 rows** (105 shorts + 23 rescued doublers), by frame:
Z3xZ6:y 32, Z4xZ6:x 28, Z3xZ4:y 17, Z3xZ5:y 17, Z4xZ6:y 13, Z3xZ5:x 12,
Z3xZ4:x 9. Structure of the miss: S1 reaches the exact minimum on 65% of
all classes (61% of light ones); on the gap rows the light classes sit
only **2–4 below the floor** (deficit histogram {2: 201, 4: 231, 6: 3})
while greedy stalls 2–8 above — the missing weight drops need
*coordinated multi-monomial* cancellation, precisely the S2
(sector-exact division) / S4 (budgeted ladder) design point. A cheap
S1 upgrade to try first in Phase 2: pair-monomial moves (≤ |G|²
candidates per round — still trivial at these sizes).

**Phase-2 decision (per §6 gate):** 75% < the ~80% bar, so S2 is
justified, prioritized on the gap frames above; S4 on whatever survives
S2, plus the bb_288-y question.

## 11. Phase 2 log (2026-07-04) — S1+/S2/S4, gate GREEN

Scripts: `a14_phase2_screens.py` (S1+ pair descent + S2 CRT-block
kills; 3 s over the 128 gap rows + 6 targets),
`a14_s4_ladder.py` (budgeted per-class coset SAT; ~3 min total).
Outputs: `data/a14/{phase2_screens,phase2_targets}.jsonl`,
`data/a14/s4_results.json`.

**S1+ / S2 on the 128 Phase-1 gap rows: 57 caught (45%), 0 soundness
violations** → cumulative cheap-tier power **435/506 = 86%** (past the
§6 80% bar). Marginal split: S1+ pair-moves alone catch 44; the S2
kill-combos (+polish) add 13. S2's implementation: per-coordinate
cyclic idempotents from the hardcoded `x^q − 1` factor table
(q ∈ {1,3,5,7,9}, verified at import), tensored to an orthogonal block
decomposition; per block, linear solves inside `e_χR` for f killing the
A-side, B-side, or both components of the seam; ≤ 4^B combos
enumerated, best few S1+-polished. Every element is explicitly
`seam + ∂₂f` — necessity by construction, and the soundness invariant
(screen value ≥ exact minimum) held on all 1000+ class evaluations.
Residual 71 rows (Z4xZ6:x 20, Z3xZ6:y 18, Z3xZ5:y 12, Z3xZ4:y 10,
Z3xZ5:x 8, Z3xZ4:x 3) — light classes needing genuinely deep
cancellation; on hunt-scale frames S4 decides them trivially (see
validation below), so the battery is complete in practice.

**S4 (SAT per orbit rep, A14.1(4) transport).** Encoding: f-vars +
XOR-chained output cells + `seqcounter` cardinality, CaDiCaL,
conflict-budgeted; every SAT answer re-verified as a genuine coset
element before acceptance. Validation on 12 gap rows (36 queries
against exact ground truth): PASS.

| target | orbit reps | result | cost |
|---|---|---|---|
| gross-x (floor 12) | 5 | **SF-CERTIFIED** (all UNSAT @ 11) | 24 s |
| hit3-y (floor 12) | 5 | **SF-CERTIFIED** | 26 s |
| hit4-y (floor 12) | 5 | **SF-CERTIFIED** | 32 s |
| hit6-y (floor 12) | 5 | **SF-CERTIFIED** | 21 s |
| bb288-y (floor 36) | 5 | **SF-REFUTED** (rep 1 SAT, weight 34) | 60 s |

Readings:

- **gross**: the entire safe floor, proven in Lean by the MIm engine
  (Γ-membership + 13-rep y-transport + 64-case dispatch), is
  independently reproduced by a 24-second solver run over the 5
  full-G orbit reps — solver-grade vs kernel-grade, but as a
  *targeting* instrument the A14.1(4)-transported S4 makes the engine
  frame cheap.
- **hit3/4/6 re-rank (the Phase-2 deliverable):** all three pass every
  cheap tier with their floors *exactly tight* (min raw seam = 12 =
  floor on every one, the gross pattern), and S4 certifies
  `SeamCosetFloor 12` outright. None is overlap-rescued; the engine
  re-instantiation can choose any of the three on safe-floor grounds.
- **bb288 is now dead on both axes, with certificates**: x-axis raw
  seam weight 24 (S0, no solver), y-axis SAT witness at weight 34
  (raw 48, S1+ stalls at 40 — genuinely S4-deep). The "off-frame ⟹
  light safe classes" picture is certificate-backed in both
  directions of the doubling.

**Battery, final shape (cost-ordered, all necessity-by-construction):**
S0 raw seams (free, 57%) → S1/S1+ descent (≈free, 75%) → S2 sector
kills (cheap linear algebra, 86%) → S4 budgeted SAT (seconds per orbit
rep on hunt-scale frames; decides everything the cheap tiers leave).
A9-hunt wiring: `screen_row` / `screen_row_phase2` are importable
per-candidate calls (`(A, B, ℓ, m, axis, d) → columns`); folding them
into `a9_lean_target_screen.py`'s row loop is a mechanical follow-up
(Phase 4).

## 12. Phase 4 log (2026-07-04) — write-up shipped

- **Extensibility doc** (`docs/gross-distance-extensibility.md`): §3
  gains the A14 update block (the "observed in both instances"
  structural features are theorems; safe sector canonical; seam-carry
  representatives; 63 → 13 → 5 orbit transport; `δ₁∘δ₂ = 0` automatic
  at `k̃ = k`); §7's engine-target paragraph gains the A14 update (the
  battery, the hit3/4/6-y SAT certifications, bb_288 dead both axes,
  and the scope caveat — the battery settles *which* codes deserve the
  engine, not the engine work itself).
- **`pipeline/research_log.md`**: A14 entry added (top of the list),
  status *success* in OQ4's own terms — cheap necessary screens plus
  target decisions, full criterion explicitly out of scope.
- **A9 profiler wiring**: `a14_columns(A, B, ℓ, m, axis, d)` in
  `a14_phase2_screens.py` (cheap tiers only, k-gate included), called
  advisorily from `profile_pair` in `a9_lean_target_screen.py` — new
  columns `a14_s0_raw_min`, `a14_cheap_min`, `a14_screen_reject`
  (or `a14_skip`/`a14_screen_error`). Semantics: on small frames the
  columns sit alongside A9's exact `safe_class_minima` (a cheap-tier
  non-reject with `safe_floor_ok = false` marks an S4-deep row); on
  36-cell+ frames they are the only safe-floor signal available.
  Verified on a corpus doubler and on hit3-y.
- **Remaining (the only open item):** Phase 3 — Prop A14.1(1)–(2) as
  Lean lemmas in `BBDoubling.lean`, sharing the homology exactness
  chase (`push0_surjective`, `ker p_* = im τ_*`) with A13-L2b Phase 1
  so it lands once and is consumed twice.

## 13. Tower battery (2026-07-05) — rung-2 safe floors all refuted; towers freeze

The five proven rung-1 doubles are themselves BB codes; re-doubling the
same axis is the next rung of each `Z_{2^r}` tower (the tour-de-gross
shape). A13 already proved the k-row (deck-trivial towers keep k, so
condition 2 survives every rung); the only open input at rung 2 is the
value-carrying safe floor, `SeamCosetFloor (2·d(rung-1))`. The battery
decides it. Scripts: `a14_tower_battery.py` (k-gate → cheap tiers → S4),
`a14_tower_distance_probe.py` (exact SAT distance ladder). Outputs:
`data/a14/{tower_battery,tower_distance_probe}.json`.

| tower (re-double axis) | rung-2 | floor | safe floor | `d_X` (SAT) |
|---|---|---|---|---|
| gross-x  `[[144,12,12]] →x` | `Z₂₄×Z₆` | 24 | **REFUTED** (light class wt 12) | **≤ 12** (SAT@12) |
| pair72-x `[[72,4,8]] →x`    | `Z₁₂×Z₆` | 16 | **REFUTED** (light class wt 8)  | **8** (UNSAT ≤7, SAT@8) |
| hit3-y   `[[144,12,12]] →y` | `Z₆×Z₂₄` | 24 | **REFUTED** (light class wt 12) | **≤ 12** (SAT@12) |
| hit4-y   `[[144,12,12]] →y` | `Z₆×Z₂₄` | 24 | **REFUTED** (light class wt 12) | — |
| hit6-y   `[[144,12,12]] →y` | `Z₆×Z₂₄` | 24 | **REFUTED** (light class wt 12) | — |

Every rung-2 safe floor is refuted **by the free tier S0 alone**: the
raw seam minimum equals `d(rung-1)` exactly (12, resp. 8) — half the
doubling target. The distance probe confirms the consequence at the
logical level: pair72-x re-double is a clean full ladder to
**`d_X = 8`** (UNSAT ≤ 7, SAT at 8), and both `n = 288` towers have a
weight-12 logical (SAT at 12), so `d_X ≤ 12`. (The `n = 288` UNSAT
tail ≤ 11 is the memory-documented CaDiCaL-intractable regime and was
not run — irrelevant to the verdict: `12 < 24` already kills the
double, and in fact the tower is *flat*, `d(rung-2) = d(rung-1)`.)

**Mechanism — this is the toric caution, certified.** Re-doubling the
axis you already doubled leaves the *other* axis as the bottleneck: the
minimal rung-2 logical routes through the still-cheap undoubled
direction, so `min(long doubled loop, short other loop) = short loop =
d(rung-1)`. The extensibility-doc §3 caution ("doubling x leaves the
y-loop as the bottleneck, `min(2L, L) = L`") was stated for the plain
toric code; the battery shows the gross lineage obeys it identically,
and the safe floor is exactly the instrument that *sees* it — the light
safe class at weight `d(rung-1)` is the undoubled-direction logical,
lifted. So:

- **Naive same-axis re-doubling is a dead end for growing distance** —
  it produces `[[2ⁿ⁺¹·…, k, d]]` with `d` pinned at the rung-1 value,
  strictly worse rate at the same distance.
- This is *consistent with*, not contradicted by, the IBM
  tour-de-gross family reaching `[[288,12,18]]`: that member is a
  **different** cover (`Z₁₂×Z₁₂`, a mixed/cleverer lift), not the
  `Z₂₄×Z₆` same-axis re-double probed here. The family grows by
  changing the lift, not by iterating one axis.
- **Program consequence:** distance `> 12` does **not** come from
  towers over the current instances. It must come from (a) a
  larger-`d` *base* (the `d ≥ 7` hunt — bb_90/bb_108 at `d = 10` are
  the first targets), or (b) a mixed / non-same-axis cover in the
  tour-de-gross direction (screen the `Z₁₂×Z₁₂` [[288,12,18]]
  presentation orbit — A14's battery makes that nearly free per
  presentation). Both are cheap next hunts; the tower direction is now
  closed with certificates.
