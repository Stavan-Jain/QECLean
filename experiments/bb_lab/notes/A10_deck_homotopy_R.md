# A10 — Is the homotopy (R) automatic? (plan + first results)

**Status: OPEN — plan with decisive first results (2026-07-02).**
Branch: `claude/admiring-curran-3a5e2a` (off PR #53,
`claude/wizardly-tereshkova-a7c840`). Probe:
[`scripts/a10_deck_r_probe.py`](../scripts/a10_deck_r_probe.py).

## 0. The question

For a free ℤ₂ BB cover (cover group `G̃ = Z_{2ℓ} × Z_m`, base `G = Z_ℓ × Z_m`,
same polynomials `A, B`, deck `σ = ·x^ℓ`): does **(R)**, `σ_* = id` on
`H₁(cover)`, hold *always*, or is there a counterexample? It held in every
instance ever checked (gross, the §5 pair `[[36,4,4]]→[[72,4,8]]`, all 152 A9
doubles, the Z₆×Z₁₄ covers in both directions).

**Resolved in passing (recorded here, from the prompt that opened A10):
semantic (R) is equivalent to solvability of the layer's level-1 certificate**
`1 + σ = ∂₂∘C + E∘∂₁` with `C : C₁ → C₂`, `E : C₀ → C₁` **F₂-additive** (the
form `deckTrivial_of_homotopy_certificate` in
`QEC/Stabilizer/Framework/Homological/BBDoubling.lean` takes). Proof of the
nontrivial direction ((R) ⟹ certificate): split `C₁ = ker ∂₁ ⊕ W`. On a basis
of `ker ∂₁`, (R) gives `(1+σ)z ∈ im ∂₂`; choose `∂₂`-preimages and extend
linearly — that defines `C` on `ker ∂₁`; set `C|_W = 0`. `∂₁|_W` is injective,
so define `E` on `∂₁(W) = im ∂₁` by `E(∂₁w) := (1+σ)w` and `E := 0` on a
complement of `im ∂₁`. On `ker ∂₁`: `∂₂Cz = (1+σ)z`, `E∂₁z = 0` ✓; on `W`:
`∂₂Cw = 0`, `E∂₁w = (1+σ)w` ✓. So **the certificate route loses nothing**; the
only open part was whether (R) itself can fail. It can — see §2.

## 1. Reformulations (all elementary; used throughout)

Write `R̃ = F₂[G̃]`, `s = x^ℓ`, `ε = 1 + s` (so `ε² = 0`), `D = F₂[⟨σ⟩] ≅
F₂[ε]/(ε²)`. The BB complex is the **Koszul complex** of the pair `(A,B)` over
`R̃`: `C₂ = R̃ →^{(B,A)} C₁ = R̃² →^{(A,B)} C₀ = R̃`, and `σ` acts as
multiplication by the group element `s` (central), so it commutes with `∂` for
free.

- **(D-module form)** `H₁(cover)` is a finite `D`-module `≅ D^a ⊕ F₂^b`;
  (R) ⟺ `ε·H₁ = 0` ⟺ `a = 0` ⟺ H₁ has no free deck-summand. `(σ_* − id)² = 0`
  is automatic; the question is only whether the unipotent part is trivial.
- **(Transfer LES form)** `0 → εC ↪ C → C/εC → 0` with `C/εC ≅ εC ≅` base
  complex gives `⋯ → H_i(base) →^{τ_*} H_i(cover) →^{p_*} H_i(base) →^{δ}
  H_{i−1}(base) → ⋯`, and `ε` on `H₁(cover)` is `τ_* ∘ p_*`. Hence
  **(R) ⟺ `im p_* ⊆ ker τ_* = im δ` — the §3 "linchpin" of the doubling
  template is an *iff*, not merely a consequence** (worth a one-line doc
  correction: `Δ` *is* the connecting map).
- **(CRT-block form)** Splitting by characters of the odd part of `G̃`,
  `R̃ = ⊕_χ T_χ` with `T_χ = S[P]`, `S = F_{2^d}`, `P` = 2-part of `G̃`
  (always ∋ `s`); each `T_χ` is local. `H₁` and (R) decompose block-wise;
  blocks where `A_χ` or `B_χ` is a unit contribute 0.

## 2. Headline answer: NO — (R) is not automatic

**Counterexample construction (dead blocks).** If some character kills *every
sector component* of both `A` and `B` (i.e. `A_χ = B_χ = 0` as elements of
`T_χ`), the block contributes `T_χ²` to `H₁` — a free `D`-module — and `ε`
acts nontrivially. Concretely, on `G̃ = Z₆×Z₃` (free ℤ₂ cover of `Z₃×Z₃`
doubling x, deck `s = x³`), with `ω` a primitive cube root and
`χ(x²) = χ(y) = ω`:

| case | A | B | k(cover) | k(base) | dim (1+σ)H₁ | (R) | `1+s ∈ (A,B)` |
|---|---|---|---|---|---|---|---|
| toric-ish control | `1+x` | `1+y` | 2 | 2 | 0 | HOLDS | yes |
| gross `Z₁₂×Z₆` | `x³+y+y²` | `y³+x+x²` | 12 | 12 | 0 | HOLDS | yes |
| pair72 `Z₆×Z₆` | `x²+y+y³` | `1+x+y²` | 4 | 4 | 0 | HOLDS | yes |
| **CE1** `Z₆×Z₃` | `1+y+y²` | `x²(1+y+y²)` | 24 | 12 | **12** | **FAILS** | no |
| **CE2** `Z₆×Z₃` | `1+y+y²` | `1+x²+x⁴` | 16 | 8 | **8** | **FAILS** | no |

(Machine-verified by the probe script; the table is its verbatim output. Both
CEs are weight-3 pairs, `k > 0` — legitimate members of the broad BB/2BGA
class.)

**Caveats on the class.** CE1/CE2 are *degenerate*: CE1 has
`gcd`-type common factor (`B = x²·A`), CE2 is direction-decoupled (`A` pure-y,
`B` pure-x, i.e. `Φ₃(y)`, `Φ₃(x²)`). Under the strict IBM monomial shape
(`A = x^a + y^b + y^c`, `B = y^d + x^e + x^f`) the sector-cancellation
constraints are much tighter (a single monomial in a sector can never be
killed by a character) — a hand analysis suggests only edge cases like
`a = d = 0` survive; whether an (R)-violating pair exists with all exponents
positive is a Phase-C sweep question.

## 3. Two lemmas (proofs in hand; Lean pending) and why history was 100%

**Lemma 0 (k-formula, self-contained).** `im ∂₁ = (A,B)` as an F₂-space, so
`rank ∂₁ = dim (A,B)`; `im ∂₂ ≅ R̃/ann(A,B)`, and Frobenius duality of the
group algebra (`dim ann I = |G̃| − dim I`) gives `rank ∂₂ = dim (A,B)` too.
Hence `k = dim H₁ = 2|G̃| − 2·dim (A,B) = 2·dim R̃/(A,B)`.

**Lemma 1 (counting).** `R̃/(ε, A, B) ≅ R/(A,B)` (reduction mod ε is exactly
the base). So
`k(cover) − k(base) = 2·dim ((ε) + (A,B))/(A,B)`. In particular
**`k(cover) ≥ k(base)` always, with equality iff `1+s ∈ (A,B)`.**

**Lemma 2 (membership ⟹ (R), constructively).** If `1+s = P·A + Q·B` then
`C(f,g) := Q⋆f + P⋆g`, `E(h) := (P⋆h, Q⋆h)` are module maps with
`(1+σ) = ∂₂∘C + E∘∂₁` on all of `C₁` (two-line check using commutativity).
This is the standard "Koszul homology is annihilated by its ideal" fact, made
explicit. **Both existing instance certificates are the special case `P = 0`**:
gross's `(1+x²)·B² = 1+x⁶` (`Q = (1+x²)B`) and pair72's `p·B = 1+x³`
(`Q = p`). Corollary (with Lemma 1): **k preserved ⟹ (R)**.

**Why every checked instance held.** Gross (12→12), pair72 (4→4), the Z₆×Z₁₄
covers (12→12), and (to be re-mined in Phase A, expected) all 152 A9 doubles
are k-preserving — and in the k-preserving regime (R) is a *theorem* (Lemmas
1+2). The observed universality was never evidence about the general class;
it was the k̃ = k class, where no counterexample is possible. Mystery
dissolved, modulo the Phase-A re-mine.

## 4. The remaining open mathematics

**Conjecture A10 (quantitative R★):**
`dim_F₂ (1+σ)·H₁(cover) = k(cover) − k(base)`
(equivalently `= 2·dim ((ε)+(A,B))/(A,B)`; the free-summand count `a` of §1
equals half the k-jump… note `k̃ − k = 2·gap` and the conjecture says
`dim εH₁ = k̃ − k`, i.e. `a = 2·gap`). Consequences: **(R) ⟺ k(cover) =
k(base) ⟺ `1+s ∈ (A,B)`** — a complete, cheaply decidable characterization,
and both directions of the empirical correlation.

Evidence so far:
- exact on all five probe rows (0/0/0 and 12/12, 8/8);
- exact on the nastiest hand-analyzed local block: `T = S[Z₂×Z₂]`,
  `(A,B) = (δ, εδ)` where `δ = 1+t`: there `dim εH₁ = 2 = 2·dim
  ((ε)+(δ))/(δ)` — a block where (R) fails with `(A,B) ≠ (0,0)`, showing
  failures are *not* only dead blocks, yet the count still matches;
- block-level hand proofs of the ⟸-of-R★ boundary cases: for `P = Z₂` blocks
  (R) fails iff the block is dead; for chain-ring blocks `S[Z_{2^r}]`
  (`T = S[v]/(v^N)`, pairs `(v^a·u₁, v^b·u₂)`), (R) ⟺ `min(a,b) ≤ N/2` ⟺
  `ε = v^{N/2} ∈ (A,B)` (e.g. `a = b = 3`, `N = 4` fails).

Proof strategy (B-phase): the Koszul long exact sequence for extending the
pair `(A,B)` by the element `ε` — `0 → H₁(A,B)/εH₁(A,B) → H₁(A,B,ε) →
ann_{H₀(A,B)}(ε) → 0` — plus Frobenius/Gorenstein duality of `T_χ` (the
complex is self-dual; `ann_{R̃}(ε) = εR̃`). Everything reduces to a
dimension count among `H₀`-type quantities, which Lemma 0/1 machinery
already handles. Fallback: exhaustive block sweep (§5, B4).

If R★ is *false*, the failure is a block where `ε·H₁ = 0` but
`ε ∉ (A,B)` — i.e. `ann H₁(Koszul) ⊋ (A,B)` in the ε-direction. That is
interesting in its own right (Koszul-annihilator gap over a symmetric
algebra) and would mean (R) is strictly finer than k-preservation; the
doubling program is unaffected either way (it lives at k̃ = k).

## 5. Plan

**Phase A — re-mine existing data (½ day).**
`a10_deck_r_survey.py`: for gross, pair72, Z₆×Z₁₄ both directions, gross
y-cover, and all 152 A9 pairs (from the A9 store/notes; `bb_lab` primitives
`checks.bb_check_matrices` + `codeparams.code_params`, with the probe's
independent linear algebra as cross-check): record
`(k_base, k_cover, dim εH₁, membership)`. Expected: every row k-preserving
with `εH₁ = 0` and membership ✓ (per Lemmas 1–2 there is no other
possibility if (R) held). Any deviation is immediately decisive: a
k-jump-with-(R) row refutes R★'s ⟹ direction on real data.

**Phase B — settle R★ (1–3 days, the math core).**
B1. Write up the CRT-block reduction rigorously (odd/2-part split, Galois
pairing, `ε` block-local).
B2. Polish Lemmas 0–2 to publishable form (they are also §6-doc corrections).
B3. Attack Conjecture A10 via the Koszul-LES + duality route above.
B4. Fallback/completeness: exhaustive block sweep — `P ∈ {Z₂, Z₄, Z₂², Z₈,
Z₄×Z₂, Z₂³}`, `S ∈ {F₂, F₄, F₈}`, pairs `(A,B)` up to `GL₂(T)`-equivalence
and unit scaling (Koszul homology is a `GL₂`-invariant of the pair);
tabulate `dim εH₁` vs `2·dim ((ε)+(A,B))/(A,B)`. Either R★ verified on all
blocks relevant to any bounded cover size (with B1 this proves it there), or
an explicit gap block feeds B5.
B5. If a gap block exists: realizability search — lift it to a genuine
weight-3 pair on a small cover group (sector-cancellation constraints as in
§2), or prove unrealizable.
B6. Literature pass (WebSearch): annihilators of Koszul homology over
artinian Gorenstein / symmetric algebras (uniform annihilators, Wiebe-type
results) — R★ may be a known statement in disguise.

**Phase C — sharpest safe class (1 day).**
Sweep small groups × weight-3 pairs for `k̃ > k` (equivalently membership
failure): confirm/refute that all failures are "degenerate" (common-factor
or decoupled), and specifically whether any strict-IBM-shape pair (all
exponents positive) can fail (R). Outcome: a precise statement of the class
on which (R) is automatic, referencing which A9/T1 gate enforces it.

**Phase D — Lean payoff (1 day).**
D1. `deckTrivial_of_bezout` in `BBDoubling.lean`: hypotheses `P, Q` with
`P⋆A + Q⋆B = 1 + x^ℓ` (a `Finsupp`/function-level polynomial identity,
`decide`-able per instance); proof = Lemma 2's `C, E` through the existing
`deckTrivial_of_homotopy_certificate`. Subsumes both instance certificates.
D2 (after B): if R★ proven, the k-preservation form
(`hk : k_cover = k_base → DeckTrivialOnH1`) — optional, D1 already covers
practice.
D3 (optional cleanup): retrofit gross + pair72 DeckHomotopy files onto D1.
D4. Doc updates in `docs/gross-distance-extensibility.md` §3: condition 2's
status becomes "⟺ `k` preserved (Lemma; conjecturally also necessary)";
merge the "k is preserved" observed-feature bullet into it; note the
linchpin-iff; record the certificate-completeness remark of §0.

**Phase E — write-up (½ day).**
`research_log.md` entry; fold into Paper-1 positioning (template condition 2
stops being a per-instance certificate hunt: it is *free* given the k-check
the screen already performs).

## 6. Risks / notes

- **Probe conventions**: `∂₂ = (B,A)`, `∂₁ = (A,B)` — the (R)/k statements
  are symmetric under the swap, and internal consistency assertions (T1, C1)
  ran green on all rows; Phase A cross-validates against `bb_lab` and A9
  data anyway.
- **Class definition**: the headline "not automatic" is for the broad
  weight-3 2BGA/BB class; the IBM-shape subclass may be safe (Phase C
  decides). State the class explicitly in any external claim.
- **Block sweep size**: `GL₂(T)`-orbit enumeration for `|T| = 4096+` needs
  the orbit-reduction to be implemented well (unit group is large); start
  with `P ∈ {Z₂, Z₄, Z₂²}` where full enumeration is trivial.
- **Public/private split**: this note lives in `experiments/bb_lab/notes/`
  (slated private-side per the split decision); the Lean lemma D1 and the
  doc §3 correction are public-side.
