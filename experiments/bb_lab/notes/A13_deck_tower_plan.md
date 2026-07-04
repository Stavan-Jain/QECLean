# A13 — Deck-trivial ⟺ k constant along ℤ_{2^r} doubling towers (OQ1)

**Status: RESOLVED — YES (2026-07-02).** `σ_* = id` on `H₁(top)` forces
`k(top) = k(base)` for every free `ℤ_{2^r}` doubling tower (`r ≥ 2`; `r = 1`
is A12). The hard direction is a completed elementary proof (§0★), its core
descent is **formalized in Lean, axiom-clean** (`eps_mem_of_deckTrivial` in
`QEC/Stabilizer/Framework/Homological/BBDeckTower.lean`), and the statement
+ mechanism + every intermediate identity pass exhaustive/sampled screens
(§0★). The clean family statement **deck-trivial ⟺ k constant along the
tower** now holds.
Branch: `claude/a13-deck-trivial-tower` (off PR #53 head).
Predecessor: [`A12_deck_homotopy_R.md`](A12_deck_homotopy_R.md) — this is
its §8 **OQ1**, promoted to its own fork. The plan below (§1–§8) is retained
as written; §0★ records the resolution.

## 0★. Resolution (2026-07-02)

**Theorem A13 (Q(r), answered).** For a free `ℤ_{2^r}` BB cover
(`ε = 1+σ`, deck order `N = 2^r`, `ε^N = 0`, `S = 𝔽₂[G]` free over
`Λ = 𝔽₂[⟨σ⟩]`), the following are equivalent:
`σ_* = id` on `H₁(top)`  ⟺  `ε ∈ (A,B)`  ⟺  `k(top) = k(base)`  ⟺  the
whole deck acts trivially at every level of the tower.

**The proof that closed it (the §3 gap, filled).** Running the S3/S7
mechanism forced the missing step. Under (R_r): A12 on the top `ℤ₂`-step
gives the entry `ε^{N/2} ∈ (A,B)` (`(σ^{N/2})_* = (σ_*)^{N/2} = id`). Then
the **descent** — apply (R_r) to the *canonical cycle* `ε^{N-t}(f,g)` where
`ε^t = fA+gB`:

1. the returned boundary coefficient `z` satisfies `ε^t z = 0` (two-line
   char-2 cancellation using the witness), **so `EpsFree` divides it:
   `z = ε^{N-t}u`** — this is the step §3 was missing;
2. back-substitution gives `εf = ε^t p + Bu`, `εg = ε^t q + Au`, hence
   `ε^{t+1} = ε^t(pA+qB)`, so `ε^t(ε + pA + qB) = 0`;
3. `EpsFree` again: `ε = pA + qB + ε^{N-t}v`, i.e. `ε ∈ (A,B) + ε^{N-t}S`.

Entry `t = N/2` (needs `N ≥ 4`, `r ≥ 2`) feeds the **iteration**: `boost`
grows the tail exponent (`ε ∈ (A,B) + ε^m S ⟹ ∈ (A,B) + ε^{2m-1}S`, pure
ring algebra) until it passes `N` and `ε^m = 0`, leaving `ε ∈ (A,B)`. ∎

This subsumes the planning-grade R2–R5 (§3) and is *stronger and simpler*:
no spectral sequence, no `Ob`-class bookkeeping, no induction on `r` — one
deck application on one cycle, then a ring-algebra iteration. R3/R6/(★) are
now corollaries or unused; the Bockstein-SS frame (Attack A) and Frobenius
pairing (Attack B) were not needed.

**Lean (public-side, axiom-clean).**
`QEC/Stabilizer/Framework/Homological/BBDeckTower.lean` (builds in 1.4 s,
axioms = `propext, Classical.choice, Quot.sound` only). Contents:
- `EpsFree ε N`, `DeckTrivial ε A B` — the two geometric inputs as abstract
  char-2-ring predicates (see the file header for the `𝔽₂[G]` model);
- `descent` — steps 1–3 above (axioms `propext, Quot.sound`);
- `boost`, `iterate_aux`, `iterate` — the tail-elimination (char-independent);
- `eps_mem_of_deckTrivial` — the headline ⟹, entry `ε^m ∈ (A,B)` (`2 ≤ m ≤
  N-2`) taken as hypothesis (= A12 top-step).
Pairs with the existing `BB.deckTrivial_of_bezout` (the ⟸) to give the full
iff at the ring level.

**Scope / what is NOT yet formalized (honest).** The Lean theorem is the
*ring-theoretic core*. Two bridges remain paper-level: (i) `DeckTrivial` and
`EpsFree` are the abstract predicates, not yet derived from the concrete
`bbChainComplex` deck action and `𝔽₂[G]`-freeness (freeness over the
subgroup algebra `𝔽₂[⟨σ⟩]`); (ii) the entry `ε^m ∈ (A,B)` is imported as
A12's top-step result rather than re-proved. Both are the same
`H₁`-dictionary work flagged as plan item L1 (a genuine formalization
project); neither is a mathematical gap. `k(top)=k(base) ⟺ ε∈(A,B)` is the
counting lemma (A12 Lemma 0/1), paper-level here.

**Screens (refutation-first, all clean).**
- [`a13_deck_tower_block_sweep.py`](../scripts/a13_deck_tower_block_sweep.py):
  the endpoint `(R) ⟺ ε∈(A,B)` (S1), the canonical-violator mechanism (S3),
  divided-class liveness (S7), A12 top-step regression (S4), and the R3/S6/S8
  structural identities — **exhaustive** on `𝔽₂[Z₄]`, `𝔽₂[Z₈]` (`N=4,8`),
  `𝔽₄[Z₄]`, `𝔽₂[Z₄×Z₂]` (both deck classes); **sampled** (uniform + a
  targeted `ε²∈I` stratum) on `𝔽₂[Z₈×Z₂]`, `𝔽₂[Z₄×Z₄]`, `𝔽₄[Z₄×Z₂]`.
  Zero S1 mismatches anywhere; S3/S7 fire on every `2≤t*≤N-2` pair.
- [`a13_gross_ladder.py`](../scripts/a13_gross_ladder.py): the gross x-tower
  `Z_{6·2^j}×Z₆`, `j=0..3` (up to `[[576,12,·]]`) — `k≡12` and full
  deck-triviality at every level from the single level-free witness
  `(1+x²)B² = 1+x⁶` (**T3/P0 confirmed**); plus the full battery on genuine
  weight-3 `Z₁₂×Z₃` cover pairs (0 mismatches, S3/S7/S4 firing).
  `𝔽₈` blocks remain out of scope (same residual as the A12 sweep).

**Implications for the family paper.** Template condition 2 is now a clean
equivalence at every tower level, not a per-instance certificate hunt: it
*is* the k-check. The k-row of the tour-de-gross family is a theorem (T1–T3
+ A13). What A13 does **not** touch — and where growing distance must come
from — is the value-carrying safe floor (condition 3); see the caveats in
the parent conversation (BT cross-section cap on the pure x-tower;
growing-`d` needs the 2D/twisted route, where each free-`ℤ₂` sub-step reuses
this same equivalence).

## 0. The question, and what is already a theorem

For a free `Z_{2^r}` BB cover tower `G_r → G_{r-1} → ⋯ → G_0` (iterated
x-doubling, same polynomials `A, B` at every level — the tour-de-gross
family route), with `σ = ·x^ℓ` generating the full deck `Δ ≅ Z_{2^r}`:

> **Q(r).** Does `σ_* = id` on `H₁(top)` force `k(top) = k(base)`?

`Q(1)` is Theorem A12. The target statement for the family paper is
"deck trivial ⟺ k constant along the tower".

**Theorem inventory — what needs no new mathematics** (write-up items
only; each is a short corollary of A12 + the counting lemma):

- **T1 (counting along the tower).** `k_j = 2·dim S/((A,B) + (ε^{2^j}))`
  (Lemma 0 of A12 at each level), and the ideals `(ε^{2^j})` shrink as
  `j` grows, so `k_0 ≤ k_1 ≤ ⋯ ≤ k_r`: *k is monotone up the tower*, and
  "k constant along the tower" ⟺ the single equality `k_r = k_0` ⟺
  `ε ∈ (A,B)` (counting lemma with `I_Δ = (ε)`; `I_Δ` is principal for
  cyclic decks).
- **T2 (per-level deck-triviality ⟺ k constant).** "`σ̄_* = id` on
  `H₁(S_j)` for **every** level `j`" ⟺ `k` constant. ⟸: membership +
  Koszul annihilation at each level. ⟹: each consecutive pair
  `S_{j+1}/S_j` is a free ℤ₂ BB cover whose deck generator is a power of
  `σ̄`, so Theorem A12 applies stepwise and `k_{j+1} = k_j` for all `j`.
  **So the entire content of Q(r) is weakening "every level" to "top
  level only".**
- **T3 (the gross tower is certified uniformly in r — see §4).**

**The precise gap** (OQ1's phrasing): does `σ_* = id` upstairs force the
induced `σ̄_* = id` on `H₁(mid)`? Not obvious — `p_*` need not be
surjective. §3 turns this into the vanishing of one canonical class.

## 1. Notation (fixed for the whole fork)

- `G_j = Z_{2^j ℓ} × Z_m`, `S_j = F₂[G_j]`; `S := S_r` (top), base `S_0`.
  Everything is stated for x-towers; the y-axis case is the transpose.
- `σ = ·x^ℓ ∈ S`, `ε = 1 + σ`. Char-2 Frobenius: `1 + σ^{2^j} = ε^{2^j}`.
  Hence `S_j ≅ S/ε^{2^j}S`, and the deck of `S` over `S_j` is
  `⟨σ^{2^j}⟩ ≅ Z_{2^{r-j}}` with augmentation ideal `(ε^{2^j})`.
- `Λ = F₂[Δ] = F₂[ε]/(ε^{2^r})` — local chain ring; `S` is **Λ-free**
  (group algebra over a subgroup algebra), so `Ann_S(ε^t) = ε^{2^r-t}S`.
- `K = K(A,B;S)`: the Koszul/BB complex `S →^{(B,A)} S² →^{(A,B)} S`
  (A12 §1 conventions). `k_j = dim H₁(A,B;S_j) = 2·dim S_j/(A,B)`.
- **(R_r)**: `σ_* = id` on `H₁(top)` ⟺ `ε·H₁(A,B;S) = 0` (char 2:
  `σ_* − id` acts as multiplication by `ε`).
- `t* := min { t ≥ 0 : ε^t ∈ (A,B) ⊆ S }` — the **critical level**.
  `Q(r)`'s conclusion ⟺ `t* ≤ 1`.

## 2. Imported facts (provenance: A12, verbatim or with `I_Δ` swapped)

- **K1 (counting, any finite abelian deck).** `k(top) − k(base) =
  2·dim (I_Δ + (A,B))/(A,B) ≥ 0`, equality iff `I_Δ ⊆ (A,B)`. [A12
  Lemma 0 + Lemma 1; OQ1 "Known" block.]
- **K2 (Koszul annihilation).** `(A,B)` annihilates `H_*(K)`; so
  membership ⟹ deck-trivial, at every level, on `H₁` and (via the
  antipode, which sends `ε` to the unit multiple `σ⁻¹ε`) on `H¹`.
- **K3 (Theorem A12, per step).** For every free ℤ₂ BB cover:
  (R) ⟺ `k̃ = k` ⟺ deck-poly membership, with a constructive
  certificate (`deckTrivial_of_bezout`).
- **K4 (CRT blocks).** `S = ⊕_χ T_χ`, `T_χ = F_{2^d}[P]`, `P` = 2-part
  of `G_r` — local Frobenius, σ-stable, Λ-free. (R_r), memberships,
  `H₁`, and everything in §3 decompose block-wise. `P` is cyclic ⟺ the
  undoubled coordinate `m` is odd.

## 3. Planning-grade derivations (W1: verify adversarially, then promote)

Derived at planning time (2026-07-02); each looks elementary but none is
checked beyond hand-derivation. **W1 = re-derive on paper, then
machine-check R3/R4/R5 shapes inside the §5 screens before anything
leans on them.**

- **R2 (top step).** (R_r) ⟹ `(σ^{2^{r-1}})_* = id` ⟹ [K3 on the top
  ℤ₂-step, whose deck poly is `1 + x^{2^{r-1}ℓ} = ε^{2^{r-1}} =: μ`]
  `k_r = k_{r-1}` and `μ = fA + gB` for some `f, g ∈ S`. In particular
  `t* ≤ 2^{r-1}`.
- **R3 (divided class generates coker p_*).** Let `t ≥ 1` with
  `ε^t = fA + gB`, and `S/ε^t` the level-`t` quotient (a group algebra
  iff `t` is a power of 2 — R3 does not care). Then
  `φ := [(f̄, ḡ)] ∈ H₁(A,B; S/ε^t)` is a cycle class, and **every**
  1-cycle `y` over `S/ε^t` satisfies `y = p(z) + c̄·(f̄,ḡ)` for a top
  cycle `z`: lift `y`, write `y₁A + y₂B = ε^t c = c(fA+gB)`, and
  `z := (y₁+cf, y₂+cg)` is an honest cycle over `S`. So
  `H₁(S/ε^t) = p_*H₁(S) + (S/ε^t)·φ` — **coker p_* is cyclic, generated
  by the divided class**. (Needs only the membership witness, not (R_r).)
- **R4 (one obstruction class).** Under (R_r):
  `ε̄·p_*H₁(S) = p_*(ε·H₁(S)) = 0`, so by R3
  `ε̄·H₁(S/ε^t) = (S/ε^t)·(ε̄φ)`. Hence deck-triviality one level down
  is the vanishing of the single class `Ob_t := ε̄φ = [ε(f,g) mod ε^t]`.
  Witness-independence under (R_r): two witnesses differ by a top cycle
  `w`, and `ε̄(φ − φ′) = p_*(ε[w]) = 0`. Element form (Massey-style,
  parallel to OQ2's): `Ob_t = 0` ⟺ ∃`s`: `εf ≡ sB` and `εg ≡ sA`
  (mod `ε^t S`).
- **R5 (liveness bootstrap — unconditional).** Suppose
  `ε^t = fA + gB` with `2 ≤ t ≤ 2^r − 2` and `Ob_t = 0` for **some**
  witness: `εf = sB + ε^t h₁`, `εg = sA + ε^t h₂`. Then
  `ε^{t+1} = (εf)A + (εg)B = ε^t(h₁A + h₂B)` (the `s`-terms cancel), so
  `ε^t(ε + h₁A + h₂B) = 0`, and Λ-freeness gives
  `ε = h₁A + h₂B + ε^q w` with `q = 2^r − t ≥ 2`. Iterating the
  congruence `ε ≡ ε^q w (mod (A,B))` gives
  `ε ≡ ε^{1+k(q-1)} w^k → 0`, i.e. **`ε ∈ (A,B)`**. Contrapositive
  (the useful reading): **if `t* ≥ 2`, then `ε̄φ ≠ 0` at level `t*`,
  for every witness — the divided class is ε-alive at the critical
  level unless the tower is already trivial.** (Note: no (R_r), no
  induction on r, no spectral sequence.)
- **(★) The compressed question.** Combining R3–R5: under (R_r),
  `ε̄H₁(A,B; S/ε^{t*}) = span(ε̄φ)`, which is nonzero iff `t* ≥ 2`. So

  > **Q(r) ⟺ [(R_r) forces `ε̄·H₁(A,B; S/ε^{t*}S) = 0`]** — does
  > deck-triviality upstairs descend to the critical level?

  This is exactly OQ1's "precise gap", with `mid` sharpened to the
  critical level and the failure locus compressed to one canonical
  class. A counterexample must exhibit (R_r) together with `t* ≥ 2`
  (equivalently `Ob_{t*} ≠ 0`); by K1 it then automatically has
  `k_r > k_0`. Conversely a proof only ever needs to kill `ε̄φ`.
- **R6 (chain blocks are done — modulo write-up).** On a block
  `T = F_q[P]` with `P` cyclic: `T ≅ F_q[t]/(t^N)` (separable odd part),
  Λ-freeness pins `v(ε) = N/2^r` (rank count: `dim εT = rank·(2^r−1)`),
  and every element is `unit·t^v`. With `a = v(A) ≤ b = v(B)` (∞ for 0):
  `dim H₁ = 2a`, and the generating cycle `(t^{b-a}, 1)` has
  `ε·(t^{b-a},1) ∈ B₁ ⟺ a ≤ v(ε) ⟺ ε ∈ (A,B)`. Degenerate strata
  agree (dead block `A=B=0`: `H₁ = T²`, ε acts nontrivially, (R_r)
  fails; unit block: `H₁ = 0`, membership trivial). **So Q(r) holds for
  every r on chain blocks; by K4, Q(r) holds outright whenever the
  undoubled coordinate is odd.** This is the same finite
  `(val A, val B, N)` case lemma A12's OQ2 wants — one write-up serves
  both. The hard core is non-cyclic `P` (gross family: `m = 6`), i.e.
  blocks `F_q[t,u]`-type with a second nilpotent direction.

## 4. P0 — the gross tower is certified today (instance payoff)

The gross witness is **level-free**: with `B = y³ + x + x²`,

```
(1 + x²)·B² = (1+x²)(y⁶ + x² + x⁴) = (1+x²)(1 + x² + x⁴) = 1 + x⁶
```

is an identity in `F₂[x,y]/(y⁶−1)` — it uses only `y⁶ = 1` and char 2,
never the x-order. At every gross-tower level `G_j = Z_{6·2^j} × Z₆`
the deck of level `j` over the `[[72,12,6]]` base is `⟨x⁶⟩ ≅ Z_{2^j}`
with `I_Δ = (1+x⁶)`, so `1+x⁶ ∈ (B) ⊆ (A,B)` **uniformly in j**. By K1
+ K2:

> **T3.** Along the whole tour-de-gross x-ladder, `k ≡ 12` and the full
> deck acts trivially on every `H₁(level j)` — one witness, every `r`.

(Consistency: level 2 is the known `[[288,12,18]]` — `k = 12` ✓. The
witness is R0-shaped — principal in `(B)` — matching A12 §6b.)
Consequence for sequencing: **the family paper's k-row does not wait on
Q(r)**; Q(r) upgrades the mechanism from per-instance certificates to a
clean equivalence. P0 also pins what a Lean certificate looks like (§6).

## 5. Attacks

### Attack A — Bockstein spectral sequence (the conceptual frame)

The ε-adic filtration `K ⊇ εK ⊇ ⋯ ⊇ ε^{2^r-1}K ⊇ 0` has length `2^r`;
Λ-freeness makes every graded piece the base complex, `E₁ = ⊕_{i<2^r}
H_*(base)`, and `d₁` is A12's connecting map δ — A12's inequality is
the first-page shadow, as OQ1 predicted. But R3–R5 show the *working*
route is elementary: the only higher-page content Q(r) needs is the
single class `ε̄φ`, whose page-climb is the gap between the relations
(R_r) provides at filtration `2^{r-1}+1` — e.g. on the auxiliary top
cycles `μs·(f,g)` (cycles since `μ² = 0`) — and the target congruence at
filtration 1 mod `ε^{t*}`. Work items: (a) set the SS up carefully once
(finite, multiplicative, degenerate cases); (b) express `Ob` and the
(R_r)-relations in page terms and look for the forcing pattern; (c) keep
the OQ2 composite `δ₁δ₂` in view — same toolbox, and any structure
proved here (e.g. self-duality constraints on the pages) feeds OQ2.

### Attack B — Frobenius duality / the perfect pairing (shortest path if
it works)

`K` is a self-dual DG algebra over the Frobenius `S`: expected perfect
pairing `⟨z, w⟩ = λ(z₁w₂ + z₂w₁)` on `H₁` (multiplication to `H₂ =
Ann(A,B)·e₁e₂`, then the Frobenius form λ), with ε self-adjoint.
[Verify or source the perfectness — Gorenstein duality for Koszul
homology; CHKV "annihilators of Koszul homology" is the adjacent
literature per A12 §4.] Then:

- membership target: `ε ∈ (A,B) ⟺ λ(ε·Ann(A,B)) = 0` (Frobenius
  ann-duality);
- hypothesis: (R_r) ⟺ `λ(ε(z₁w₂ + z₂w₁)) = 0` for **all** cycle pairs;
- candidate cycles to feed in: `v·(f,g)` for `v ∈ Ann(A,B)` (cycles
  since `vμ = 0`), the auxiliary `μs·(f,g)`, and Frobenius-square cycles
  `(C,0)` when `A = C²` (the A8-counterexample mechanism — likely where
  a counterexample hides if one exists).
- **Known trap (found at planning time):** pairing `ε·v(f,g)` against a
  generic cycle `y` and substituting `εy = s_y(B,A)` collapses to
  `λ(v·s_y·μ) = 0` automatically — that pairing route detects nothing.
  The needed identity must pair the coker-`p_*` direction against
  something *not* in the ε-image. Concrete sub-task: on the §5C screens,
  compute Gram matrices of the pairing on `H₁(S/ε^{t*})` and locate
  which classes detect `λ(εv) ≠ 0`; reverse-engineer the identity from
  the data.

### Attack C — screens (refutation-first; lab discipline: exhaustive
where possible, sampling only with an exact confirmatory follow-up)

Extend `a12_bockstein_block_sweep.py` / `a12_deck_r_survey.py` to deck
order `2^r ≥ 4`. For every pair record: `t*`, memberships `ε, ε², μ`,
`εH₁ =? 0` (full (R_r), not just the top-step generator), witness
`(f,g)`, `Ob` at levels `t*` and `2^{r-1}`, the k-profile `k_0 … k_r`,
and pairing diagnostics.

- **C0 (verify §3 before trusting it).** On every swept pair with
  `μ ∈ (A,B)`: machine-check R3 (`H₁(S/ε^t) = p_*H₁ + span φ`), R4
  (`ε̄H₁ = span ε̄φ` under (R_r)), R5 (no pair with `t* ≥ 2` and
  `Ob_{t*} = 0`). Any violation = a bug in §3, found cheap.
- **C1 (exhaustive blocks, r = 2).** `F₂[Z₄]`, `F₂[Z₈]`, `F₄[Z₄]`
  (chain controls for R6 — expect zero hits); **`F₂[Z₄×Z₂]`** (first
  hard block, 65,536 pairs, all order-4 decks `s` up to automorphism).
  Next tier (`|T| = 2^16`: `F₂[Z₈×Z₂]` r∈{2,3}, `F₂[Z₄×Z₄]`,
  `F₄[Z₄×Z₂]`, `F₈[Z₄]`): unit-normalized + translation-orbit
  exhaustive if feasible, else stratified by ideal type + heavy
  sampling — **log coverage honestly, no silent caps.** A hit =
  `(R_r) ∧ t* ≥ 2` = counterexample to Q(2); then check
  block-realizability in an actual weight-constrained BB cover pair
  (A12 CE machinery) and against the canonical-lift convention.
- **C2 (cover-level, r = 2, weight-3, canonical lifts).** Small grid
  mirroring `a12_weight3_class_sweep`: `Z₁₂×Z₃` (tower over `Z₃×Z₃`),
  `Z₁₂×Z₆` (tower over `Z₃×Z₆`), `Z₈×Z₂`, `Z₈×Z₆`, `Z₂₄×Z₃`; strict-IBM
  stratum flagged. Failure geography: how often does (R_r) fail vs
  `Ob ≠ 0` under partial hypotheses — maps where the theorem could
  break.
- **C3 (the real ladders).** Gross x-tower `j = 0..3` (up to
  `Z₄₈×Z₆`, 576 qubits — rank computations only): verify P0
  numerically end-to-end. The six anchorable Z₆×Z₆ classes × both axes
  (A11): extract per-level witnesses, test whether each has a
  **level-free witness** like P0 (conjecture: yes on engine frames,
  R0-shaped). Uniform witnesses found here go straight into §6's Lean
  targets and the paper's instance table.

## 6. Lean staging (public-side payoff)

In order; (i)–(ii) are unconditional on Q(r)'s fate:

- **L0 (gross-tower certificates).** Fixed small `r`: the witness
  identity `(1+x²)·B² = 1+x⁶` at level `r` is a finite kernel-`decide`
  identity (pair72 precedent: 36-point `pPoly_bezout`; level 2 = 144
  points). Route deck-triviality per level through the existing
  `deckTrivial_of_bezout` / `deckTrivial_of_homotopy_certificate`
  (`Framework/Homological/BBDoubling.lean`) — each tower level is an
  `XDoubleCoverData` instance over the previous one, so **no new deck
  machinery is needed for iterated statements**.
- **L1 (T1/T2 write-ups).** Paper-level first; the Lean form of the
  counting lemma (`membership ⟺ k̃ = k`, finite linear algebra) is
  A12's noted target (i) and would make T2 formal via stepwise
  composition. Genuine but bounded project; schedule after M4.
- **L2 (descent lemma R3, chain level).** Constructive, no homology
  quotients: "given a witness and a mid 1-cycle, produce the top cycle
  and coefficient" — a good parametric lemma over `XDoubleCoverData` +
  witness hypotheses, matching the layer's chain-function style.
- **L3 (outcome-dependent).** If Q(r) is proven: the liveness bootstrap
  R5 is first-order ring algebra (`Ann_S(ε^t) = ε^{2^r−t}S` + a finite
  congruence iteration) — surprisingly Lean-friendly. If refuted: the
  counterexample block as a `decide`-checked anti-instance, A10-style.

## 7. Milestones, sequencing, kill criteria

- **M0** (this session): plan committed; A12 §8 OQ1 gets a pointer.
- **M1 = W1** (first work session, ~half day): adversarially verify
  R2–R6 on paper; promote §3 to theorem-grade prose in this note or
  demote what breaks. Includes the two soft spots: the A12-on-top-step
  application (free ℤ₂ BB cover with the *same* `A,B`, base = level
  `r−1` — check A12's hypotheses list verbatim) and the Λ-freeness
  annihilator fact.
- **M2** (~1 day): C0 + C1 core + C3 gross ladder. Decisive either way.
- **M3** (branch point): hit ⟹ counterexample write-up + salvage
  statement for the paper (T1 + T2 + T3 stand regardless; state Q(r) as
  answered-negative with the failure stratum). No hit ⟹ M4.
- **M4** (≤ 2 focused sessions — hard kill criterion): prove `(★)`.
  Attack B first (one identity away if the pairing is perfect), Attack
  A as fallback bookkeeping. If neither closes: **park** — record the
  Ob-formalism as the sharpest known reduction in A12 §8/OQ1, ship
  T1/T2/T3 for the paper, demote Q(r) to a stated open problem. Do not
  let the general question block the family write-up.
- **M5**: Lean L0 (+L2 if M4 succeeded); L1 as capacity allows.
- **M6**: research_log entry (result-grade only), A12 §8 status update,
  `gross-distance-extensibility.md` fold-in, paper text for
  T1/T2/T3 (+T4 if it exists).

## 8. Risks / notes

- **Lift convention.** (R) is lift-sensitive (A12 §2). The tower uses
  the canonical same-polynomial lift at every level — state this in
  every external claim; C2 flags non-canonical strata separately.
- **Hypothesis strength.** (R_r) is triviality of the *full-deck
  generator* upstairs. The weaker "top-step generator only"
  (`(σ^{2^{r-1}})_* = id`) gives R2 but not R4's
  `ε̄·p_* = 0` — don't conflate them in statements or screens.
- **X vs Z side.** All statements transpose via the antipode
  (`ε ↦ σ⁻¹ε`, a unit multiple), so memberships and (R) agree on `H₁`
  and `H¹`; one side suffices. Verify once in C0.
- **Mixed towers.** The IBM family also moves the y-coordinate
  (`d = 6(2r+b−1)` bookkeeping). K1/T1 cover any finite abelian deck;
  the Ob-machinery is cyclic-2-specific. Scope A13 to the pure
  x-doubling axis; note the abelian-product generalization as a
  follow-up only if the paper needs it.
- **OQ2 synergy.** C1 doubles as OQ2's "cheapest falsification path"
  (the `g > 0` strata of `Z₈×Z₂`/`Z₄×Z₄` blocks, now swept at deck
  order 4 too); R6's chain-block lemma is OQ2's wanted case lemma. Keep
  the two ledgers separate but share the harness.
- **Public/private split.** This note is lab-side (slated private);
  T1–T3 statements, the Lean layer additions, and the extensibility-doc
  updates are public-side.
