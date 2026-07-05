# A12 — Is the homotopy (R) automatic? (RESOLVED: no in general; iff k is preserved)

**Status: theorem proven on paper + machine-verified on 157 covers and
exhaustive block sweeps (2026-07-02). Remaining open: only the quantitative
Bockstein refinement (§4) — now attacked as A13
(`A13_bockstein_equality_plan.md`, branch `claude/a13-bockstein-equality`:
candidate tower-lift proof + 167k-pair clean sweep, red-team pending).**
Branch: `claude/admiring-curran-3a5e2a` (off PR #53). Scripts:
[`a12_deck_r_probe.py`](../scripts/a12_deck_r_probe.py) (first
counterexamples), [`a12_deck_r_survey.py`](../scripts/a12_deck_r_survey.py)
(157-cover survey),
[`a12_bockstein_block_sweep.py`](../scripts/a12_bockstein_block_sweep.py)
(block-level sweep),
[`a12_weight3_class_sweep.py`](../scripts/a12_weight3_class_sweep.py)
(Phase-C class sweep).

## 0. The question

For a free ℤ₂ BB cover (cover group `G̃ = Z_{2ℓ} × Z_m`, base `G = Z_ℓ × Z_m`,
same polynomials `A, B`, deck `σ = ·x^ℓ`): does **(R)**, `σ_* = id` on
`H₁(cover)`, hold *always*, or is there a counterexample? It held in every
instance ever checked (gross, the §5 pair `[[36,4,4]]→[[72,4,8]]`, all 152 A9
doubles, the Z₆×Z₁₄ covers in both directions).

**Resolved in passing (recorded here, from the prompt that opened A12):
semantic (R) is equivalent to solvability of the layer's level-1 certificate**
`1 + σ = ∂₂∘C + E∘∂₁` with `C : C₁ → C₂`, `E : C₀ → C₁` **F₂-additive** (the
form `deckTrivial_of_homotopy_certificate` in
`QEC/Stabilizer/Framework/Homological/BBDoubling.lean` takes). Proof of the
nontrivial direction ((R) ⟹ certificate): split `C₁ = ker ∂₁ ⊕ W`. On a basis
of `ker ∂₁`, (R) gives `(1+σ)z ∈ im ∂₂`; choose `∂₂`-preimages and extend
linearly — that defines `C` on `ker ∂₁`; set `C|_W = 0`. `∂₁|_W` is injective,
so define `E` on `∂₁(W) = im ∂₁` by `E(∂₁w) := (1+σ)w` and `E := 0` on a
complement of `im ∂₁`. On `ker ∂₁`: `∂₂Cz = (1+σ)z`, `E∂₁z = 0` ✓; on `W`:
`∂₂Cw = 0`, `E∂₁w = (1+σ)w` ✓. So **the certificate route loses nothing**.

## 1. Reformulations (all elementary; used throughout)

Write `R̃ = F₂[G̃]`, `s = x^ℓ`, `ε = 1 + s` (so `ε² = 0`), `D = F₂[⟨σ⟩] ≅
F₂[ε]/(ε²)`. The BB complex is the **Koszul complex** of the pair `(A,B)` over
`R̃`: `C₂ = R̃ →^{(B,A)} C₁ = R̃² →^{(A,B)} C₀ = R̃`, and `σ` acts as
multiplication by the group element `s` (central), so it commutes with `∂` for
free.

- **(D-module form)** `H₁(cover)` is a finite `D`-module `≅ D^a ⊕ F₂^b`;
  (R) ⟺ `ε·H₁ = 0` ⟺ `a = 0` ⟺ H₁ has no free deck-summand. `(σ_* − id)² = 0`
  is automatic; the question is only whether the unipotent part is trivial.
- **(Transfer LES form)** `0 → εK → K → K/εK → 0` with `K/εK ≅ εK ≅` base
  complex `K̄` gives

  ```
  H₂(K̄) --δ₂--> H₁(K̄) --τ₁--> H₁(K) --p₁--> H₁(K̄) --δ₁--> H₀(K̄)
  ```

  with `ε_* = τ₁∘p₁` on `H₁(K)`; `τ` is the transfer (`τ(x̄) = x + σx`), `p`
  the pushforward (mod-ε reduction), `δ` the connecting map = the **Bockstein**
  of the deck extension `0 → F₂ → D → F₂ → 0`. Hence
  **(R) ⟺ `im p_* ⊆ ker τ_* = im δ₂` — the §3 "linchpin" of the doubling
  template is an *iff*, not merely a consequence** (`Δ` *is* the connecting
  map).
- **(CRT-block form)** Splitting by characters of the odd part of `G̃`,
  `R̃ = ⊕_χ T_χ` with `T_χ = S[P]`, `S = F_{2^d}`, `P` = 2-part of `G̃`
  (always ∋ `s`; `P = Z_{2^a}×Z_{2^b}` since BB groups have two cyclic
  factors); each `T_χ` is local Frobenius. `H₁`, (R), and all quantities
  below decompose block-wise.

## 2. Headline answer: NO — (R) is not automatic

**Counterexample construction (dead blocks).** If some character kills *every
sector component* of both `A` and `B` (i.e. `A_χ = B_χ = 0` in `T_χ`), the
block contributes `T_χ²` to `H₁` — a free `D`-module — and `ε` acts
nontrivially. Concretely, on `G̃ = Z₆×Z₃` (free ℤ₂ cover of `Z₃×Z₃` doubling
x, deck `s = x³`), with `χ(x²) = χ(y) = ω` (`ω` a primitive cube root):

| case | A | B | k(cover) | k(base) | dim (1+σ)H₁ | (R) | `1+s ∈ (A,B)` |
|---|---|---|---|---|---|---|---|
| toric-ish control | `1+x` | `1+y` | 2 | 2 | 0 | HOLDS | yes |
| gross `Z₁₂×Z₆` | `x³+y+y²` | `y³+x+x²` | 12 | 12 | 0 | HOLDS | yes |
| pair72 `Z₆×Z₆` | `x²+y+y³` | `1+x+y²` | 4 | 4 | 0 | HOLDS | yes |
| **CE1** `Z₆×Z₃` | `1+y+y²` | `x²(1+y+y²)` | 24 | 12 | **12** | **FAILS** | no |
| **CE2** `Z₆×Z₃` | `1+y+y²` | `1+x²+x⁴` | 16 | 8 | **8** | **FAILS** | no |

(Machine-verified; both CEs are weight-3 pairs, `k > 0` — legitimate members
of the broad BB/2BGA class, though degenerate: CE1 has a common factor
(`B = x²·A`), CE2 is direction-decoupled (`Φ₃(y)`, `Φ₃(x²)`). Whether the
*strict IBM shape* with positive exponents admits failures is the Phase-C
sweep question — answer in §6: yes.)

**Lift-dependence.** (R) is a property of the **cover pair**, not the base
pair: different lifts of the same base polynomials give different covers
that can disagree on (R). Example: base `Z₃×Z₃`, `A = 1+y+y²`,
`B = 1+x+x²`. The canonical lift of `B` to `Z₆×Z₃` mixes deck sectors
(`x⁰, x¹, x²` have x-parities 0,1,0; a lone odd-sector monomial can never
be killed by a character), so that cover satisfies (R); the sector-pure
lift `B̃ = 1+x²+x⁴` gives CE2, which violates it. Any statement "this base
pair doubles safely" must fix the lift convention (the doubling pipeline
always uses the canonical same-exponent lift).

## 3. The theorem: (R) ⟺ k preserved ⟺ Bezout membership

**Theorem A12.** For every free ℤ₂ BB cover:

1. `k(cover) ≥ k(base)`, with equality **iff** `1+x^ℓ ∈ (A,B) ⊆ F₂[G̃]`.
2. `dim_F₂ (1+σ)·H₁(cover) ≥ k(cover) − k(base)`.
3. Consequently the following are **equivalent**:
   (R); `k(cover) = k(base)`; `1+x^ℓ ∈ (A, B)`. In the membership case the
   homotopy certificate is explicit (Lemma 2 below), so (R) additionally
   comes with a finite, `native_decide`-checkable witness.

*Proof.*

**Lemma 0 (k-formula, self-contained).** `im ∂₁ = (A,B)` as an F₂-space, so
`rank ∂₁ = dim (A,B)`; `im ∂₂ ≅ R̃/ann(A,B)`, and Frobenius duality of the
group algebra (`dim ann I = |G̃| − dim I`) gives `rank ∂₂ = dim (A,B)` too.
Hence `k = dim H₁ = 2|G̃| − 2·dim (A,B) = 2·dim R̃/(A,B)`.

**Lemma 1 (counting).** `R̃/(ε, A, B) ≅ R/(A,B)` (reduction mod ε is exactly
the base), so
`k(cover) − k(base) = 2·dim ((ε) + (A,B))/(A,B) ≥ 0`, with equality iff
`ε ∈ (A,B)`. This proves 1.

**LES bookkeeping (proves 2).** In the transfer LES (§1), exactness gives
`im p₁ = ker δ₁` and `ker τ₁ = im δ₂`, so

- `dim εH₁ = dim τ₁(p₁(H₁)) = dim ker δ₁ − dim(ker δ₁ ∩ im δ₂)`,
- `k̃ = dim im τ₁ + dim im p₁ = (k − dim im δ₂) + (k − dim im δ₁)`, i.e.
  `k̃ − k = dim ker δ₁ − dim im δ₂`.

Since `dim(ker δ₁ ∩ im δ₂) ≤ dim im δ₂`, subtracting gives
`dim εH₁ ≥ k̃ − k`. ∎(2)

**Lemma 2 (membership ⟹ (R), constructively).** If `1+s = P·A + Q·B` then
`C(f,g) := Q⋆f + P⋆g`, `E(h) := (P⋆h, Q⋆h)` are module maps with
`(1+σ) = ∂₂∘C + E∘∂₁` on all of `C₁` (two-line check using commutativity;
this is "Koszul homology is annihilated by its ideal", made explicit).
**Both existing instance certificates are the special case `P = 0`**:
gross's `(1+x²)·B² = 1+x⁶` (`Q = (1+x²)B`) and pair72's `p·B = 1+x³`
(`Q = p`).

**Equivalences (3).** (R) ⟹ `0 = dim εH₁ ≥ k̃ − k ≥ 0` ⟹ `k̃ = k` ⟹
(Lemma 1) membership ⟹ (Lemma 2) (R). ∎

**Why every checked instance held.** Machine survey
(`a12_deck_r_survey.py`, 157 covers: gross x- and y-doubling, pair72, the
Z₆×Z₁₄ `[[168,12,6]]` base doubled both ways, all 152 A9 pairs): **all 157
are k-preserving, all satisfy membership, (R) holds on all** — as the
theorem forces. The observed universality was never evidence about the
general class; every historical check sat in the k̃ = k regime, where no
counterexample is possible. Mystery dissolved.

## 4. The remaining open mathematics: the Bockstein refinement

**Conjecture (quantitative).**
`dim_F₂ (1+σ)·H₁(cover) = k(cover) − k(base)` exactly (the theorem gives ≥).

By the LES bookkeeping above, equality holds **iff `im δ₂ ⊆ ker δ₁`, i.e.
iff the Bockstein composite `δ₁∘δ₂ : H₂(base) → H₀(base)` vanishes.** This
is *not* formal: for the deck extension `0 → F₂ → D → F₂ → 0`,
`Ext_D(F₂,F₂) ≅ F₂[e]` is polynomial with `e² ≠ 0` (the minimal resolution
of `F₂` over `D` has the Bockstein an isomorphism in every degree), so
`δ² = 0` must come from the specific structure of the length-2 self-dual
Koszul complex, if it is true at all. Concretely, on a base 2-cycle `z̄`
(so `Az = εa`, `Bz = εb` for a lift `z`):
`δ₁δ₂(z̄) = [ε⁻¹(A·b + B·a)] ∈ H₀(base)` — a Massey-product-style
obstruction, well-defined mod `(Ā,B̄)`.

Evidence:
- exact (`dim εH₁ = k̃ − k`) on **all 157 surveyed covers** and on all five
  probe rows including both counterexamples (12 = 12, 8 = 8);
- exact on **every pair of every local block swept exhaustively**
  (`a12_bockstein_block_sweep.py`: all `(A,B)` pairs over `F₂[P]` for
  `P ∈ {Z₂, Z₄, Z₂², Z₈, Z₄×Z₂}` and `F₄[P]` for `P ∈ {Z₂, Z₄, Z₂²}`, every
  order-2 deck `s`; ~10⁶ pairs) **and on all sampled pairs** for
  `F₂[P]`, `|P| = 16` (`Z₁₆, Z₈×Z₂, Z₄×Z₄`) and `F₄[P]`, `|P| = 8`
  (30k random pairs per (P, s));
- hand-proved on `P = Z₂` blocks (failure ⟺ dead block, count matches) and
  on chain-ring blocks `S[Z_{2^r}]` (failure ⟺ `min-valuation > N/2`,
  count matches).

Status: **open in general** (a proof needs the self-duality of the Koszul
complex or an explicit chain-level contraction of `δ₁δ₂`; a counterexample
needs a block escaping the swept range, i.e. `|P| ≥ 16` exotic pairs or
`S ≥ F₈`). Not load-bearing for the doubling program: the program operates
at `k̃ = k`, where the theorem already gives everything, and the theorem's
≥ direction alone pins (R) exactly.

Literature (B6): the containment questions between Koszul-homology
annihilators and the ideal are a studied stream (Corso–Huneke–Katz–
Vasconcelos, "annihilators of Koszul homology"); no off-the-shelf theorem
gives `ann H₁ ∩ soc-directions ⊆ (A,B)` for Frobenius group algebras, and
the classical Bockstein-vanishing arguments (`β = Sq¹`, `β² = 0`) do not
apply — the deck extension `0 → F₂ → F₂[Z₂] → F₂ → 0` has
`Ext_D(F₂,F₂) = F₂[e]`, `e² ≠ 0`. The conjecture appears genuinely new.

## 5. Plan and execution status

**Phase A — re-mine existing data. ✅ DONE** (157/157 clean; see §3).

**Phase B — settle R★.**
- B0 (theorem write-up): ✅ DONE — §3 above; R★ upgraded from conjecture to
  theorem by the LES inequality.
- B4 (block sweep): ✅ DONE — see §4 evidence.
- B3 (Bockstein δ² = 0 in general): OPEN, downgraded to "nice-to-have"
  (§4); candidate routes recorded there.
- B6 (literature): pending — Koszul-annihilator / Bockstein-for-2-groups
  literature check.

**Phase C — sharpest safe class. ✅ DONE** — cover-side sweep
(`a12_weight3_class_sweep.py`, ~1.04M weight-3 cover pairs + strict-IBM
grid): results in §6. Headline: the IBM shape is *not* structurally safe;
subtle (non-dead-block) failures dominate; the only safe criterion is the
k-check itself (cheap, and equivalent to (R) by the theorem).

**Phase D — Lean payoff. ✅ DONE (D1 + D3).**
- D1: `deckTrivial_of_bezout` in `BBDoubling.lean` — hypotheses `P, Q` with
  `conv P Ac + conv Q Bc = deckPoly` (`deckPoly = 1 + x^{deckS}`); proof =
  Lemma 2's module maps (`bezoutC v = P⋆v_L + Q⋆v_R`,
  `bezoutE h = (Q⋆h | P⋆h)`) through `deckTrivial_of_homotopy_certificate`,
  with the block computations in `bezout_blockL/R`. Builds warning-free.
- D3: pair72's `Z3Z6/DeckHomotopy.lean` retrofitted onto the Bezout route:
  `homotopyR = deckTrivial_of_bezout 0 pPoly` with the 36-point identity
  `pPoly_bezout` closed by kernel **`decide`** (previously a 72-basis
  `native_decide` sweep) — the (R) leg of pair72 is now native-free.
- D4: `docs/gross-distance-extensibility.md` §2 tier table + §3 update
  block rewritten to theorem status. ✅

**Phase E — write-up: ✅** research_log entry added; Paper-1 fold-in
(template condition 2 stops being a per-instance certificate hunt: it is
*equivalent* to the k-check the screen already performs).

## 6. Phase C results (cover-side sweep, `a12_weight3_class_sweep.py`)

**General weight-3 class** (all unit-normalized unordered cover pairs on a
grid of 19 cover groups `Z_L×Z_m`, `L ∈ {2,4,6,8,10,12}`; 1,040,472
pairs): **11,307 (R)-failures**. Mechanism × axis-class:

| | dead-block | SUBTLE (no dead character) |
|---|---|---|
| mixing (neither poly axis-locked) | 1,476 | **8,730** |
| one-sided | 192 | 861 |
| single-var / decoupled | 27 | 21 |

Three headline facts:

1. **Subtle failures dominate** (9,612 of 11,307): the `(δ, εδ)`-type
   non-dead-block mechanism (§4) is the *common* failure mode at weight 3,
   not an exotic block artifact. Verified by hand on a sample: `Z₂×Z₆`,
   `A = 1+y+y²`, `B = 1+y+y⁵` — at `χ(u) = ω` the block pair is
   `(ωδ_t, δ_t)`, ideal `(δ_t) ∌ ε_x`, and no character kills either
   polynomial outright.
2. **Failures need small odd-part character relations**: zero failures on
   any group whose odd part is `{1, 5}`-only (`Z₄×Z₄`, `Z₈×Z₄`, `Z₈×Z₅`,
   `Z₅×Z₅`, …) — a weight-3 polynomial dies at a character only through a
   3-term relation among roots of unity, first available at order 3
   (`1+ω+ω² = 0` in `F₄`) and order 7 (`1+η+η³ = 0` in `F₈`). `Z₈×Z₃` has
   exactly 1 failure (chain-ring block); `Z₆×Z₆` has 9,562.
3. **The strict IBM shape is NOT safe** (210,920 IBM-shaped cover pairs,
   `A = x^a+y^b+y^c`, `B = y^d+x^e+x^f`, all exponents ≥ 1): **1,769
   failures** — 1,728 dead-block, all on `Z₁₄×Z₇` (the `F₈` relation), and
   **41 subtle, all on `Z₆×Z₆`** — e.g. `A = x+y+y³`, `B = y+x+x³`, an
   innocent-looking pair on the gross base group. Parity protects many
   real codes (a lone monomial in a deck-parity sector blocks dead
   characters — e.g. gross's own `A = x³+y+y²` for x-doubling), but parity
   alone does not block subtle failures.

**Conclusion (sharpest safe class):** there is no useful syntactic safe
class — the operative criterion **is** the theorem's: check
`k(cover) = k(base)` (one rank computation, already emitted by the A9
screen), equivalently find a Bezout witness. Nothing weaker (shape,
parity, mixing) suffices; nothing more is needed.

## 6b. Cross-session corroboration (A11 literal-lift session, 2026-07-02)

The A11 literal-lift-criterion session (branch
`claude/a8-literal-lift-criterion`, note `A11_literal_lift_criterion.md`
Entry 1, commit `68da34c`) independently audited **1164 cells** — all six
anchorable Z₆×Z₆ classes × both axes × {stored form + all 96 anchorable
presentations} — plus the full 638-row A9 hunt stream: **(R), the
linchpin, and membership (their "R1") hold on every cell**, including all
non-doubling ones, and their S2 matrix has (R) at 100% of both doubles
and failures. Three read-throughs against this note:

- By Theorem A12 (§3) this is exactly what must happen on k-preserving
  frames: (R) is *equivalent* to `k̃ = k`, so within a k-gated family it
  can never discriminate doubles from non-doubles — consistent with their
  diagnosis that the doubling separation lives entirely in the safe floor
  (template condition 3; their base-side coset probes: hit3-stored-x
  safe-class minima `{6:12, 8:45, ≥12:6}` vs the flipped presentation
  `{≥12:63}`).
- Their "(R) is ~free for weight-3 literal lifts" is a *frame* fact, not
  a class fact: §6's sweep contains canonical-lift weight-3 failures off
  those frames (all k-jumping, as the theorem forces).
- Their **R0** observation (`1+δ` in each *principal* ideal `(A)`, `(B)`
  separately, on the whole frame) is strictly stronger than membership
  and matches the `P = 0` shape of both proven instance witnesses. Their
  on-cycles certificate form — for a cycle, `(1+σ)v = ∂₂(C v)` directly,
  no `E` needed — is the cycle restriction of `bezout_chain_identity`
  (the `E∘∂₁` correction matters only off-cycles, which is what lets
  `deckTrivial_of_bezout` route through the all-chains certificate
  lemma).

## 7. Risks / notes

- **Probe conventions**: `∂₂ = (B,A)`, `∂₁ = (A,B)` — the statements are
  symmetric under the swap; internal consistency assertions ran green on
  all rows; the survey's k-values match the A9 table's `[[n,k,d]]` columns
  row-by-row (independent cross-check).
- **Class definition**: the headline "not automatic" is for the broad
  weight-3 2BGA/BB class; the strict-IBM-shape subclass is Phase C's
  question. State the class explicitly in any external claim.
- **Public/private split**: this note lives in `experiments/bb_lab/notes/`
  (slated private-side); the Lean lemma D1 and the doc §3 correction are
  public-side.

## 8. Open problems, sharpened (2026-07-02)

Ordered by program value. Two unconditional facts from the LES bookkeeping
frame all of them: `k(base) ≤ k(cover) ≤ 2·k(base)` (the upper bound —
`k̃ = 2k − dim im δ₁ − dim im δ₂` — was implicit in §3 and deserves its own
line; CE1 sits exactly at the `2k` boundary), and for **odd**-order decks
the whole question trivializes (`F₂[Z_p]` is semisimple for odd `p`, so
Maschke gives (R) ⟺ `k̃ = k` for free) — `p = 2` is the modular case, and
Theorem A12 says the modular answer *matches* the semisimple one.

**OQ1 — Tower/deck generalization (highest program value).** For a free
`Z_{2^r}` cover tower `G̃ → G̃/⟨σ^{2^{r-1}}⟩ → ⋯ → G` (iterated doubling —
the tour-de-gross family route), does `σ_* = id` on `H₁(top)` force
`k(top) = k(base)`?
*Known:* ⟸ holds in full generality — for any finite abelian deck `Δ`,
`k(top) = k(base)` ⟺ `I_Δ ⊆ (A,B)` (augmentation ideal; counting lemma
verbatim) ⟹ deck acts trivially (Koszul annihilation, same two lines). And
`σ_* = id` does give `k(top) = k(mid)` by A12 applied to the top `Z₂`-step
(deck `σ^{2^{r-1}}`).
*The gap:* does `σ_* = id` on `H₁(top)` force the induced `σ̄_* = id` on
`H₁(mid)`? Not obvious — `p_* : H₁(top) → H₁(mid)` need not be surjective.
*Route:* the ε-adic filtration is now length `2^r`, so the two-step LES
becomes a Bockstein spectral sequence; the A12 inequality should be its
first-page shadow. A clean statement here ("deck trivial ⟺ k constant
along the tower") is the theorem the family paper wants.
*Status (2026-07-02): **RESOLVED — YES**, fork **A13**
([`A13_deck_tower_plan.md`](A13_deck_tower_plan.md) §0★).* `σ_* = id` on
`H₁(top)` **does** force `k(top) = k(base)` for every free `ℤ_{2^r}` tower
(`r ≥ 2`; `r = 1` is this note). Proof: A12 on the top `ℤ₂`-step gives the
entry `ε^{N/2} ∈ (A,B)`, then a **descent** — apply (R) to the canonical
cycle `ε^{N-t}(f,g)`; the boundary coefficient `z` satisfies `ε^t z = 0`,
so ε-freeness divides it (`z = ε^{N-t}u`), yielding
`ε ∈ (A,B) + ε^{N-t}S` — plus a ring-algebra iteration eliminating the
tail. Simpler than the planned route: no spectral sequence, no `Ob`-class,
no induction on `r`. The core descent is Lean-formalized axiom-clean
(`BBDeckTower.lean`, `eps_mem_of_deckTrivial`); screens exhaustive to deck
order 8. The compressed "divided class `ε̄φ`" picture (planning-grade
below) was correct but unnecessary — the direct descent bypasses it.

**OQ2 — The Bockstein equality (mathematical core).** Is
`dim (1+σ)H₁ = k̃ − k` always? Equivalent forms: `δ₁∘δ₂ = 0`;
`im δ₂ ⊆ im p_*`; element form — whenever `Az, Bz ∈ εR̃`, must
`A·ε⁻¹(Bz) + B·ε⁻¹(Az) ∈ ε(A,B)` (well-defined mod `ε(A,B)`)?
*If true:* `H₁(cover) ≅ D^{k̃−k} ⊕ F₂^{2k−k̃}` as a deck module — the
complete representation type from two ranks (uses `k̃ ≤ 2k`).
*Verified frontier:* every instance; exhaustive `F₂[P]` `|P| ≤ 8`, `F₄[P]`
`|P| ≤ 4`; chain-ring blocks (`P` cyclic ⟸ `m` odd) reducible to a finite
`(val A, val B, N)` case lemma — worth writing out, since it would make the
equality a *theorem for every cover with odd undoubled coordinate*.
*Cheapest falsification path:* the `g > 0` stratum of `Z₈×Z₂` / `Z₄×Z₄`
blocks was only randomly sampled — a stratified exhaustive sweep there
(enumerate ideals containing neither `ε` nor a unit) is an afternoon;
`S = F₈` blocks are untouched.
*Structural route:* the extend-by-ε Koszul LES
`0 → H₁/εH₁ → H₁(A,B,ε) → ann_{H₀}(ε) → 0` plus Frobenius self-duality of
the complex.
*Follow-up (2026-07-02, A13):* session-0 found a candidate half-page proof
via the ℤ/4 **Frattini lift** (the 4-fold cover is the "integral lift"
behind the classical `β² = 0`), a toy showing the self-duality route as
stated above is provably insufficient, and a 167k-pair clean sweep
covering F₈ blocks and twisted decks — see
`A13_bockstein_equality_plan.md` (red-team pending).

**OQ3 — Arithmetic classification of the failure locus.** Conjecture: for
weight-3 cover pairs, (R)-violations exist on `Z_L×Z_m` iff the char-2
unit equation `x + y = 1` is solvable in the relevant roots of unity —
i.e. iff the odd part admits a 3-term vanishing sum (available at order 3:
`1+ω+ω²`; order 7: `1+η+η³`; generally governed by which pairs of odd
orders `(ord x, ord (x+1))` occur in `F̄₂` — a finite-field table), with
the sector/parity constraints layered on top.
*Evidence:* the §6 table exactly — zero failures on every
`{1,5}`-odd-part group, failures precisely where `μ₃` or the `F₈` relation
is available; even the lone `Z₈×Z₃` (chain-block) failure needs the `μ₃`
cancellation to reach socle depth.
*Two halves:* dead blocks = elementary (pure unit-equation + sector
parity); subtle blocks need the ideal-theoretic criterion (`ε ∉ (A_χ,B_χ)`
with both nonzero) — characterize which weight-3 sector images can
generate such an ideal.
*Payoff:* a-priori (R)-safety certificates for whole group families, and
with it lift-robustness statements (which base pairs are safe under
*every* lift vs only the canonical one).

**OQ4 — A safe-floor criterion (the next rung of the template).** With
condition 2 now free given the k-check, the doubling separation lives
provably in condition 3's safe floor (cross-session corroborated: same
(R)/R1 rates on doubles and failures; separation visible only in
safe-class coset minima). Open: any ideal/character-theoretic *necessary*
condition for `safe floor ≥ 2d(base)` — e.g. a Smith-heavy-class
reformulation of `im p_*` — that is cover-class-generic? Honest
expectation: the floor is value-carrying (engine/SAT territory; the
[[288,12,18]] anti-instance shows it genuinely fails off-frame), so aim
for cheap necessary screens to sharpen A9-style hunts, not a full
criterion.
*Status (2026-07-04): **ATTACKED as A14**
([`A14_safe_floor_criterion_plan.md`](A14_safe_floor_criterion_plan.md),
branch `claude/a14-safe-floor-criterion`). Phase 0 done: under (R) the
safe sector is canonical — `p₂ = 0`, `Δ = δ₂` injective,
`im p_* = im Δ = Δ(ann_R(A,B))` of dim `k/2`, explicit seam-carry
representatives (= `BBCover.seamC`, matched bit-for-bit against
`SeamTables.lean`), coset minima constant on G-translation orbits
(gross: 63 classes → 13 y-orbits = the MIm transport count → **5**
full-G orbits), and `δ₁∘δ₂ = 0` automatic at `k̃ = k` (sharpening where
OQ2's remaining content lives). Screen battery S0–S4 designed,
necessity-by-construction. Gate: `a14_seam_formula_check.py` (30/30).
Phase 1 done (`a14_safe_floor_screens.py`, exact ground truth on all
638 T1 rows, 0 false rejects, A9-profile cross-validation 0/152
mismatches): **S0+S1 reject 75% of the 506 SF-false rows at zero cost;
every k-preserving short is SF-false (so SF-true ⟹ doubles, 111/111,
on the T1 frames); and the [[288,12,18]] x-double anti-instance is
caught by S0 alone — raw seam weight 24 = the previously-SAT-derived
`d_safe ≤ 24`.* 128 gap rows (light classes 2–4 below floor, needing
multi-monomial cancellation) queue for the S2/S4 tier.*

**OQ5 — R0 structure (cheap, tidy).** The literal-lift session observed
`1+δ ∈ (A)` and `∈ (B)` *separately* (R0) across their whole frame. By the
single-generator counting lemma, R0 ⟺ each circulant factor preserves its
own `dim R̃/(A)` under descent. Questions: (a) construct/count
R1-but-not-R0 covers among k-preserving weight-3 pairs (minutes of sweep);
(b) R0 forces one-sided witnesses (`Q⋆B = 1+s`) — half-size Lean
certificates, which is what both proven instances happened to use. Is R0
generic on engine frames or an artifact of small ones?

**Formalization scope note.** The natural Lean targets, in order:
(i) `membership ⟺ k̃ = k` (finite linear algebra, no homotopy);
(ii) the chain-ring case lemma of OQ2; (iii) the full (R) ⟺ k iff — only
if the paper states it at theorem level (needs H₁ dimension counting +
the LES, a genuine formalization project).
