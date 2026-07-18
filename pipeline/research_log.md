# Research log

Index of moonshot attempts (novel-math research track). Each entry links to
`attempts/<name>/result.md`. **Failures are first-class outputs** — document
what was tried and why it didn't work.

## Format

```
- YYYY-MM-DD — <name> — <status: success | partial | failed> —
  <one-line summary>. [details](attempts/<name>/result.md)
```

## Entries

- 2026-07-07 — class-small-cycle-theorem (A15/A16, goal 2) — success —
  **The A5 goal-2 target statement is an unconditional theorem: every
  weight-3 BB instance with Sidon disjoint difference sets (D1 ∧ D2),
  mirrored projections (iii), Ann ≠ 0, and a floor-bearing frame
  (4∤ℓ, 4∤m) has no nonzero 1-cycle of weight ≤ 5 — d ≥ 6, with every
  free-Z₂ cover inheriting the floor.** Mechanism: a field-generic
  widened engine for the one-sided floor (the F₄ co-point dichotomy
  is support-generic; only value-rigidity is F₄-locked); the (1,3)
  kill via char-2 chirality identities (the weight-3 triangle image
  IS the Frobenius square B² + c, and (iii) ∧ D1 exclude dA = 2·dB —
  subsuming the is_frobenius_related gate on the class); the (2,2)
  kill via exact difference-multiset accounting (atoms →
  translate-rigidity → a D2 funnel; size-4 via a matching dichotomy
  whose exceptional torsion families die against D1/D2/counting/
  Ann — the pentagonal family by "no vanishing weight-3 sums of 5th
  roots of unity in char 2"). Two instance-independent fixed censuses
  (Z₅², Z₁₅²; embedding-complete by torsion factoring) carry the
  exceptional-family kills. Consequences: the 58-member corpus class
  + 111,840 battery members certified analytically; bb_72/bb_108/
  bb_90 subsumed; **Z₆×Z₁₄ [[168,12,6]] certified — first instance
  off the Z₃² odd part**; per-instance certificates are uniform
  O(|G|²) gate-checks (`a15_class_certify.py`). Write-up of record:
  `experiments/bb_lab/notes/A16_class_theorem_writeup.md`; track log
  `A5_goal2_log.md` Entries 8–13. Lives in `experiments/bb_lab/`
  (not `attempts/`).

- 2026-07-07 — bb-literal-lift-criterion (A11, Entry 3) — partial
  (criterion refuted weight-agnostic; line paused) —
  **The Entry-2b counterexample hunt found its target, and it
  VERIFIES: first observed dangerous-sector bind.** A weight-4×4 pair
  on Z₅×Z₅ ([[50,2,5]]), y-lift [[100,2,8]]: C-safe holds two-sidedly
  at enumeration grade (k, tight witness, safe minima 11 ≥ 10 both
  sides, (R)) yet d(cover) = 8 < 10 = 2d — the weight-8 X-logical
  pushes to a weight-6 nonzero stabilizer. "C-safe ⟹ doubling" is
  FALSE weight-agnostic; parity is the load-bearing hypothesis
  (d(base) = 5 and the safe minima are odd — impossible with |A|, |B|
  odd), the Entry-2b twice-refined residue is exactly the cell hit
  (D5 concentration violated), and A17's (M)-robustness conjecture
  (deficit-wall §9, corpus-class-scoped) becomes non-vacuous and
  provably scope-critical — not refuted: the odd-weight record stays
  2,058/2,058. [details](../experiments/bb_lab/notes/A11_literal_lift_criterion.md)

- 2026-07-06 — deficit-wall (A17-P3) — success (theorem + a correction) —
  **A14 §16's deficit-wall OQ answered: the wall *value* is a theorem,
  the *mechanism* is a pushforward, and the "stalls at exactly 2d − 2"
  premise is retracted as a measurement artifact.** Math
  (`notes/A17_deficit_wall.md`, machine-validated by
  `a17_deficit_wall_checks.py`): **(L0)** the safe sector is the
  transfer kernel — `im δ₂ = ker τ₁` (LES; span-verified on 9 covers
  incl. both bb_288 presentations and the Z₁₈×Z₃ re-decomposition), so
  `d_safe` = min weight of a base logical whose class *dies in the
  double cover*; **(L1, parity)** with |A|, |B| odd every base and
  cover 1-cycle has even weight (augmentation ring hom), so `d`, `d̃`,
  `d_safe` are all even and — since `d_safe ≥ 2d ⟺ SF` — **`2d − 2`
  is the unique maximal SF-failing value**: that is the whole
  "parity/duality mechanism" §16 asked for; **(L2/T1)** the collision
  sets `K_z = {g : (1+g)[z] safe} ⊇ Stab₀(z)` are subgroups with
  `[G : K_z] ≤ 2^{k/2}`, and where the containment is proper the
  difference classes give `d_safe ≤ 2d − 2·overlap` — fires on bb90-y
  (bound 10, tight at the freeze), **provably silent on bb108-y** (all
  54 min-weight logicals have `K_z = Stab₀`, exhausted by SAT — the
  hypothesized "2(d−1) base object" does not exist there); **(T2, the
  load-bearing mechanism)** under (R) `im p₁ = im δ₂` makes the
  pushforward of any surviving-class cover logical a safe base logical:
  `d_safe ≤ d̃_safe`, so a cover failing through its safe sector hands
  the safe floor its witness at no weight cost, and conversely SF
  forces the cover's whole safe sector to `≥ 2d` (the template
  re-derived; "SF-true ⟹ doubles", A11's 111/111, reduces to the new
  **(M)-robustness conjecture**: the dangerous sector never binds
  alone). Coupling observed tight everywhere: doublers at `2d = 2d`
  with overlap-free lifts; bb108-y at `14 = 14`. **The correction:**
  §15/§16's "orbit ceiling 18" and bb_288's "32–34" were *first-found
  SAT witness weights at the query bound, not minima* — exact
  descending ladders put stored bb108-y at **`d_safe = 14 = 2d − 6`
  exactly, certified both sides** (base UNSAT@12 on all orbit reps;
  cover `d̃_safe = 14` exactly, its UNSAT@12 ≈5 h of CaDiCaL at
  n = 216 — T2's coupling tight at 14 = 14), every ladder-sampled
  v1 finalist at `≤ 12` (first witnesses 16), while bb90-y's freeze value
  **= 10 = d exactly** (UNSAT@9, certified) — no measured instance
  attains the wall;
  correction blocks added to A14 §§15–16. Residue: the code invariant
  `maxSF ∈ {2d} ∪ {even ≤ 2d − 2}` (true value per code now measurable
  by ladders; A17-P1's corpus battery must report S4 weights as "≤"),
  the (M)-robustness conjecture, and the T1/T2-both-silent corner of
  the `≤ 2d` ceiling. **Lean layer LANDED (same session, axiom-clean,
  zero warnings): `Framework/Homological/BBDeficitWall.lean`** — L1
  parity (`sum_conv`, `cycle_support_even`, base+cover instantiations
  with descending hypotheses), L0 as the chain-level iff
  `pull1_mem_boundaries_iff_seamCoset` (sibling to
  `ker_pushH1_eq_range_pullH1`), T2 as
  `push1_mem_seamCoset_of_deckTrivial` +
  `not_seamCosetFloor_of_light_cover_cycle` (`d_safe ≤ d̃_safe`
  against the repo's own `SeamCosetFloor`/`DeckTrivialOnH1`,
  deliberately routing around A14.1(2)'s dimension count via
  deck-triviality), and the wall as the even-step upgrades
  `seamCosetFloor_of_even_of_pred` / `safeFloor_of_even_of_pred`.
  [theorem+battery](../experiments/bb_lab/notes/A17_deficit_wall.md)

- 2026-07-04 — safe-floor-screens (A14) — success —
  **A12's OQ4 answered in its own terms: the safe sector is canonical
  under (R), and a certified necessary-screen battery now decides
  condition-3 targets.** Math (Prop A14.1): under (R) — equivalently
  the Bezout membership `ε ∈ (A,B)` — `p₂ = 0`, the connecting map
  `Δ = δ₂` is **injective**, `im p_* = im Δ = Δ(ann_R(A,B))` of dim
  `k/2` (the extensibility doc's per-instance "half of k" observations
  are theorems), with closed-form **seam-carry representatives**
  (= `BBCover.seamC`, matched bit-for-bit against `SeamTables.lean`)
  and coset minima **constant on G-translation orbits** (gross: 63
  classes → 13 y-orbits = the MIm transport count → **5** full-G
  orbits); at `k̃ = k` the deck-Bockstein composite vanishes
  automatically (OQ2's remaining content lives off the doubling
  regime). Screens (necessity-by-construction — every rejection
  exhibits an explicit light coset element): S0 raw seams → S1/S1+
  descent → S2 CRT-block kills → S4 per-orbit-rep coset SAT. On the
  638-row T1 corpus with exact ground truth recomputed for every row
  (A9-profile cross-validation 0/152 mismatches): the cheap tiers
  reject **86%** of the 506 SF-failures at **zero false rejections**,
  and **every k-preserving short is SF-false** — on the direct-sweep
  frames the safe floor alone separates doubles from shorts (111/111).
  S4 with the 5-orbit transport: **hit3/4/6-y `SeamCosetFloor 12` all
  SAT-certified (~25 s each, floors exactly tight — all three engine
  targets viable, none overlap-rescued)**; gross's Lean-proven floor
  independently SAT-cross-checked (24 s); **bb_288 SF-refuted on both
  axes** (x: raw seam weight 24, turning the previously SAT-derived
  `d_safe ≤ 24` into a polynomial identity; y: witness weight 34,
  provably beyond the cheap tiers). Scripts
  `a14_{seam_formula_check,safe_floor_screens,phase2_screens,s4_ladder}.py`;
  columns wired into the A9 profiler (`a14_columns`). Residual
  (queued): the Phase-3 Lean package for A14.1(1)–(2), sharing the
  A13-L2b exactness chase. **Tower follow-up (§13):** every proven
  rung-1 double, re-doubled on the *same* axis, freezes at its rung-1
  distance — all five rung-2 safe floors refuted by S0 alone (raw seam
  = `d(rung-1)` exactly), SAT confirms `d_X ≤ d(rung-1)` (pair72-x full
  ladder `d_X = 8`; both `n = 288` towers SAT@12). This is the toric
  same-axis bottleneck, certified on the gross lineage; distance
  `> 12` must come from a larger-`d` base or a mixed (tour-de-gross)
  lift, not from towers. **d=10-base follow-up (§14):** all four
  bb_90/bb_108 literal-lift axes fail in three distinct modes —
  freeze-pattern light classes (bb90 both axes; bb90-x is the first
  S0-pass/S1+-reject), a first in-the-wild condition-2 death (bb108-x:
  `1+x⁹ ∉ (A,B)`), and bb108-y's deficit-2 near miss whose overlap
  rescue is refuted by an explicit weight-18 cover logical (3 s SAT).
  No `d = 20` doubles from stored corpus presentations; the hunt moves
  to presentation orbits (bb108-y first), mixed lifts, and wider
  `d ≥ 7` base enumeration.
  [plan+results](../experiments/bb_lab/notes/A14_safe_floor_criterion_plan.md)

- 2026-07-02 — bb-literal-lift-criterion (A11, Entry 1) — success —
  **A checkable doubling criterion emerges, and the A8 audit FLIPS the
  hit2/hit5 negatives.** Literal-lift doubling is presentation-sensitive
  within a (code, axis): the anchorable A8-presentations of ALL six
  engine-frame classes have d = 12 covers on BOTH axes (7 fresh SAT
  ladders, all 12), while their stored forms stay at 6/8 — A9's "hit2/
  hit5 do not double" was a presentation artifact. The discriminator is
  template condition 3's safe half: **doubling ⟺ safe-class coset minima
  ≥ 2d on every engine-frame cell tested** (base-side SAT probe, no
  cover SAT; 4/4 prospective predictions), and safe-floor ⟹ doubling
  with 0/465 violations on the full A9 hunt stream. Certificates
  (R0-sq…R2, linchpin) are universally satisfied — never discriminating
  (one-line mechanism: 1+δ ∈ (A,B) forces σ_* = id). A8's squaring
  identity alone is refuted as sufficient (62 small-frame shorts); its
  full package stands at 7/7 + gross + Z₆×Z₁₄, zero counterexamples.
  Dead end (first-class): the reachable-coset repair of the 41
  overlap-rescue rows fails 0/41 — the necessity gap is genuine slice
  mathematics. [details](../experiments/bb_lab/notes/A11_literal_lift_criterion.md)

- 2026-07-02 — descent-twist-screen (A10) — success (screens halted by design) —
  **The doubling-existence question ANSWERED: universal claim FALSE,
  marquee bases RESCUED.** Full descent-space (256-cover) twist screens
  over the anchorable Z₆×Z₆ frame: hit2 rescued by an x-class
  single-bit twist and hit5 by the mixed extension class at zero twist
  (both DRAT-certified d = 12 = 2d), so all five gross siblings carry
  exact [[144,12,12]] covers — while 13 small-frame bases
  (Z₃×Z₃/Z₃×Z₄/Z₃×Z₅) have their ENTIRE descent space fail (3328
  witness rows, numpy-re-verified, certificates committed — A14's
  must-catch corpus). Lemma L1: descent covers are
  presentation-invariant (screens are code-level exhaustive);
  constructive corollary — twist rescues ≡ presentation moves. R9
  keystone: 14101/14101 k-preserving fail witnesses break in the SAFE
  sector (mechanism later proven as A17-P3's
  transfer-kernel/pushforward theorems). Grids deliberately halted at
  the efficiency crossover (R11).
  [details](../experiments/bb_lab/notes/A10_descent_twist_screen.md)

- 2026-07-02 — deck-tower-descent (A13) — success —
  **Deck-trivial ⟺ k constant along `ℤ_{2^r}` doubling towers (A12 OQ1),
  answered YES.** For a free `ℤ_{2^r}` BB cover, `σ_* = id` on `H₁(top)`
  forces `k(top) = k(base)` (`r ≥ 2`; `r = 1` is A12). The hard direction
  is a completed elementary proof: A12 on the top `ℤ₂`-step gives the entry
  `ε^{N/2} ∈ (A,B)`, then a **descent** — apply deck-triviality to the
  canonical cycle `ε^{N-t}(f,g)`; the boundary coefficient satisfies
  `ε^t z = 0`, so ε-freeness divides it (`z = ε^{N-t}u`), yielding
  `ε ∈ (A,B) + ε^{N-t}S` — plus a ring-algebra tail-elimination. Simpler
  than the planned Bockstein-SS / obstruction-class route (none needed).
  **Lean payoff (public-side, axiom-clean):**
  `QEC/Stabilizer/Framework/Homological/BBDeckTower.lean` —
  `eps_mem_of_deckTrivial` (the ⟹), `descent`, `boost`/`iterate` over an
  abstract char-2 ring with the `EpsFree`/`DeckTrivial` predicates; pairs
  with the existing `BB.deckTrivial_of_bezout` (the ⟸) for the full ring
  iff. Builds 1.4 s; axioms = standard three, no `sorry`/`native_decide`.
  Screens (refutation-first, all clean):
  `a13_deck_tower_block_sweep.py` (endpoint + mechanism + intermediate
  identities, exhaustive to deck order 8) and `a13_gross_ladder.py` (gross
  x-tower `k≡12` + full deck-triviality to `[[576,12,·]]` from the
  level-free witness `(1+x²)B²=1+x⁶`; genuine `Z₁₂×Z₃` cover pairs).
  Residual (paper-level, plan item L1): the `H₁ ↔ DeckTrivial` /
  `𝔽₂[G]-free ↔ EpsFree` bridges. The family paper's k-row is now a
  theorem (T1–T3 + A13); growing distance still lives in the safe floor
  (condition 3), untouched here.
  [plan+resolution](../experiments/bb_lab/notes/A13_deck_tower_plan.md)

- 2026-07-03 — bockstein-equality (A13) — success (core) —
  **A12's OQ2 sharpest element-level form is now a machine-checked Lean
  theorem, and the full failure-danger zone is swept exhaustively clean.**
  Math: the transfer SES is the mod-`ε̂²` reduction of the **4-fold
  cover** — the analogue of the integral lift behind classical `β² = 0`
  — and freeness over `F₂[ℤ/4]` (`Ann(ε̂) = (ε̂³)`) kills the composite
  at the element level (`W = A·ε⁻¹(Bz) + B·ε⁻¹(Az) = 0` on the nose),
  for arbitrary order-2 decks incl. twisted. A toy 3-term free-D
  *self-dual* complex with `δ₁δ₂ ≠ 0` shows the originally scoped
  structural route (LES + Frobenius self-duality) is provably
  insufficient — liftability is the content. **Lean (W3, axiom-clean):**
  `Framework/Homological/BocksteinLift.lean` — `bockstein_element_form`
  (abstract capstone: element form from `char 2` + `Ann(ε)=(ε³)`) and
  `bockstein_element_form_deck` (unconditional on the ℤ/4 chain block);
  only `propext`/`Classical.choice`/`Quot.sound`. **Sweeps (W1,
  exhaustive):** every `(A,B)` pair over `F₂[Z₁₆]`, `F₂[Z₈×Z₂]`,
  `F₂[Z₄×Z₄]`, `F₄[Z₈]`, `F₄[Z₄×Z₂]`, `F₈[Z₂]`, `F₈[Z₄]`, `F₈[Z₂²]`
  (all decks; `≈` 2³² weighted pairs per |P|=16 block; hundreds of
  millions of live pairs) has `E = 2g`, `maxdef = 0` — closing OQ2's own
  "cheapest falsification path." W0 red-team agents were cut off by a
  session limit (Lean kernel now the referee). **L2 progress (commit
  `b7ee838`, `BBEpsFree.lean`, axiom-clean):** the ring hypothesis shared
  by OQ2 (`BocksteinLift`) and OQ1 (`BBDeckTower`'s `EpsFree`, on-branch
  after rebasing onto merged PR #54) has its reusable core proven —
  `epsFree_quotXpow` (chain ring `R[X]/(X^N)`) + `epsFree_of_free`
  (transfer across a free module) + `hann_of_epsFree` (bridge). General
  L2a now reduces to one wildcard: `Module.Free 𝔽₂[⟨σ⟩] 𝔽₂[G]` (coset
  basis, no mathlib support). **L2b core (commit `67b947e`,
  `BBBocksteinRank.lean`, axiom-clean):** the transfer-inequality heart —
  `finrank_ker_comp_le` + `finrank_sub_le_finrank_range_comp` (`ker p =
  range τ`, `ε = τ∘p` ⟹ `dim Hc − dim Hb ≤ dim (range ε)`), i.e. `E ≥
  k̃−k` once instantiated on homology. **Phase-1 instantiation landed
  (2026-07-04, axiom-clean): the inequality `E ≥ k̃ − k` is now a Lean
  theorem for every `XDoubleCoverData`** — `BBCover.lean` gained
  `push0_surjective` + `exists_pull_eq_add_boundary` (the chain-level
  diagram chase), and the new `BBTransferH1.lean` induces
  `pushH1`/`pullH1` on `H₁` via `Submodule.mapQ`, proves the exactness
  `ker p_* = range τ_*`, identifies `epsH1 = τ_*∘p_*` with `(1+σ)_*`
  pointwise, and concludes
  `finrank_H1_sub_le_finrank_range_epsH1 : dim H₁(cover) − dim H₁(base)
  ≤ dim (1+σ)H₁(cover)` — A12 part 2, previously paper-only, now
  kernel-checked. **The L2a wildcard is also CLOSED (2026-07-04,
  `BBEpsFreeGroupAlgebra.lean`, axiom-clean):** the group algebra
  `k[G]` is free directly over the chain ring `k[X]/(X^N)` via
  `X ↦ x^σ − 1` (coset-transversal basis: spanning by
  `x^g = (X+1)^j·C c • x^{t i}`, independence by `modByMonic`
  representatives + the invertible substitution `∘(X±1)` + orbit
  coefficient extraction), giving
  `epsFree_one_add_single_of_addOrderOf : EpsFree (1 + x^σ) (2^r)`
  for ANY abelian `G` (finite or not) and any char-2 base — the shared
  ring hypothesis of BOTH deck lines (OQ1 `eps_mem_of_deckTrivial`,
  OQ2 `bockstein_element_form` via `hann_of_epsFree`) is now
  unconditional for group algebras. **The L2 linear-algebra wiring is
  also COMPLETE (2026-07-04, axiom-clean):** `BBBocksteinRank` gained the
  exact defect identity `E + dim Hb + dim(range p ⊓ ker τ) = dim Hc +
  dim(ker τ)` and the tightness criterion `ker τ ≤ range p → E = dim Hc −
  dim Hb`; `BBTransferH1` instantiates them as `BocksteinVanishes D`
  (`ker τ_* ≤ range p_*` = `δ₁∘δ₂=0`), `finrank_range_epsH1_eq`
  (`E = k̃−k` under `BocksteinVanishes` — the headline `deck_finrank_eq`),
  `finrank_ker_epsH1_eq` (`dim ker ε_* = k`), and `epsH1_epsH1_apply`
  (`ε_*²=0`, unconditional). On the ring side, `BBEpsFreeGroupAlgebra` §7
  `bockstein_element_form_group_algebra` composes L2a into L1 to give the
  element form `δ₁δ₂=0` unconditionally in every order-4 deck group
  algebra `k[G]⧸(ε²)`. The conv↔group-algebra bridge is
  also landed (`BBConvRing.lean`, axiom-clean): `convEquiv` +
  `convEquiv_mul` (`conv` = the `𝔽₂[G]` product) + the deck-operator
  identifications, so L2a/element-form now speak about the repo's actual
  `conv`/deck action. The SOLE remaining gap is the homological transport
  identifying the element fact with `BocksteinVanishes` — the
  `seamC`↔connecting-map δ₂ step (`seamC_mem_cycles` is already δ₂ at
  chain level) reading `cycles/boundaries/H₁` as `convEquiv`-modules —
  the paper's main theorem, genuinely open (the toy self-dual free-`D`
  complex has `δ₁δ₂≠0`, so it is not automatic).
  Payoff once closed: `H₁(cover) ≅ D^{k̃−k} ⊕ F₂^{2k−k̃}` (rank data all
  in hand; needs the `𝔽₂[ε]/(ε²)`-module classification for the iso),
  with Theorem A12 as its `a = 0` slice.
  [result](../experiments/bb_lab/notes/A13_result.md) ·
  [plan](../experiments/bb_lab/notes/A13_bockstein_equality_plan.md) ·
  [L2 plan](../experiments/bb_lab/notes/A13_L2_formalization_plan.md)

- 2026-07-02 — bb-pair72-packaging (S3.9) — success —
  **`pair72StabilizerCodeWithDistance : StabilizerCodeWithDistance 72 4 8`**
  (`Codes/BivariateBicycle/Z3Z6/StabilizerCode.lean`): the second doubling
  instance packaged as a first-class code object, mirroring the gross
  Phase-5 packaging at pair72 scale (trimmed 68-generator list,
  decoder-certified independence, 4 logical qubits, distance transport).
  Axiom-clean (standard three + `native_decide` oracles, no `sorry`).
  Data generator with 15-check ALL-PASS gate:
  `experiments/bb_lab/scripts/gen_pair72_packaging_data.py`.
  [plan](../experiments/bb_lab/notes/S39_pair72_packaging_plan.md)

- 2026-07-02 — deck-homotopy-R-characterization (A12) — success —
  **The doubling template's condition 2 (homotopy R) is solved:
  (R) ⟺ `k(cover) = k(base)` ⟺ `1+x^ℓ ∈ (A,B)`** for every free ℤ₂ BB
  cover (transfer-LES inequality `dim (1+σ)H₁ ≥ k̃−k`, plus the
  constructive Koszul/Bezout converse). (R) is **not** automatic:
  explicit weight-3 counterexamples exist (dead-character blocks), the
  strict IBM monomial shape fails too, and among ~1.04M weight-3 cover
  pairs swept 11,307 violate (R) — the majority (9,612) via *subtle*
  non-dead-block mechanisms. Every historically checked cover (157/157:
  gross both directions, pair72, Z₆×Z₁₄ both directions, all 152 A9
  doubles) is k-preserving, where (R) is forced — the observed
  universality dissolved. Resolved in passing: the F₂-additive
  certificate form is complete (semantic (R) ⟺ certificate solvable),
  and the `im p_* ⊆ im Δ` linchpin is an *iff*. Lean payoff:
  `deckTrivial_of_bezout` in `BBDoubling.lean` (module-map homotopy from
  any Bezout witness; both instance identities are its `P = 0` case);
  pair72's (R) leg retrofitted to a kernel-`decide` 36-point identity.
  Open remainder: the quantitative `dim (1+σ)H₁ = k̃−k` (⟺ vanishing of
  the deck-Bockstein composite `δ₁∘δ₂`), exact on every instance and on
  ~10⁶ exhaustively swept local blocks.
  [details](../experiments/bb_lab/notes/A12_deck_homotopy_R.md)

- 2026-07-02 — bb-doubling-layer-second-instance — success —
  **The free-ℤ₂ doubling template is a parametric Lean layer, and the
  `[[36,4,4]] → [[72,4,8]]` pair is proven through it** (chain+Pauli
  `d = 8 = 2·d(base)`, gross axiom bar; packaging: see the S3.9 entry
  above).  The A9 target screen found 152 direct-sweep doubling pairs
  and corrected the Z₆×Z₆ census: gross has **five anchorable siblings,
  three with exact `[[144,12,12]]` y-covers** — in-frame
  engine-necessary follow-on targets.
  [details](../experiments/bb_lab/notes/A9_lean_target_screen.md)

- 2026-06-12 — gross-bb-analytic-bound — partial —
  **d(gross [[144,12,12]]) ≥ 6 fully analytic** (3× the published
  Lin–Pryadko floor of 2; goal 3 of the Phase-A program), via the
  small-cycle theorem (d_base ≥ 6 by hand) + the h=2 cover transfer with
  the dangerous-sector factor-2 lemma (M) proven unconditionally. The
  adversarial re-review passed (Entry 15: all links HOLD under an
  independent 49-check re-implementation + hand re-derivation of every
  prose argument) — the theorem is write-up grade. Goals 1 (d = 12) and 2
  (BB-class bound) remain open. Lives in `experiments/bb_lab/` (not
  `attempts/`): [handoff](../experiments/bb_lab/notes/A_HANDOFF.md),
  [A3 log entries 11–15](../experiments/bb_lab/notes/A3_track1p1_log.md).

- 2026-06-12 — gross-bb-analytic-bound (goal 1 closed) — success —
  **d(gross [[144,12,12]]) = 12**: the last statement (M-im)
  is proven by the confined-floor program (A3 Entries 22–26): hand
  engine lemmas (kill-multiset supports, T-classifiers from ψ₂² = ψ₃ψ₄
  and ψ₄ = ψ₁ψ₃, slope level-sets, the ρ²= 0 confinement with c₁ = c₂
  = 0 derived via column transforms) + finite residues
  (spine C-tables, 118 one-line ρ-link kills), double-cross-checked by
  the two independent machine closures. The adversarial skeptic pass
  over Entries 16–26 passed (Entry 27: all eight links HOLD under an
  independent 75-check re-implementation + hand re-derivation; two
  sharpenings found, off₀ = off₂ = 0 identically and a one-line c₂ = 0).
  Epistemic grade per the review: **verified-finite with a fully
  hand-proven analytic spine** — the Entry-24 C-table evaluations and
  the completeness of the Entry-25 achiever lists remain
  machine-certified; paying that debt is write-up organization
  (compressed-table walks), not new mathematics. Owed: the A4-style
  standalone write-up; goal 2 (BB-class bound) remains open. [A3 log
  entries 16–27](../experiments/bb_lab/notes/A3_track1p1_log.md).

- 2026-06-12 — gross-bb-analytic-bound (write-up debt paid) — success —
  **d(gross [[144,12,12]]) = 12, fully analytic** (A4 Part II, Theorem
  D): both Entry-27 residues discharged by hand. New structure that made
  the compression work: m′² = ω²m (only two slot labelings up to
  scale), the confined comps as full affine lines, the Γ₄ tie
  V₄L = ωV₄R + w₄, the pair-ratio lemma for fibre degeneration, and the
  hyperbolic-quadruple form of the slope lemma (no three points of
  uv = c ∪ {0} collinear). The ~6k-row wt-24 closure collapses to one
  standard form S(a,b) walked in 33 buckets (all ≥ 6); the achiever-list
  completeness follows from the achiever-structure lemma (parity-locked
  per-(V₀,γ) block minima ⟹ achievers = argmin products over sum-10
  loci) + rule-derived per-cell locus tables (118 achievers, each killed
  by a one-convolution ρ-link check). Certifier
  `a3_a4ext_recheck.py` all-PASS. Owed: the Part-II skeptic pass; goal 2
  remains open (the slot frame is instance-generic). [A3 log entry
  28](../experiments/bb_lab/notes/A3_track1p1_log.md).

- 2026-06-12 — gross-bb-analytic-bound (goal 1 update) — partial —
  **d(gross) = 12 now holds at the verified-finite level, doubly
  machine-verified** by two independent routes: the value-grammar
  completion sweep (Entry 20: CRT value dictionary + affine-graph
  completions, no coset element of weight ≤ 11 in any nonzero Smith
  class) and the light-cycle flux census (Entry 21: all 990 weight-8 and
  13248 weight-10 non-boundary cycles have nonzero seam flux). The last
  open statement (M-im) is reduced to three bounded hand obligations
  (Entry 22: the confined ρ-floor already closes two of the five orbits
  outright; the rest reduce to a weight-exactly-10 equality analysis).
  All other links — (M), (R) ker δ = im Δ via the B²-homotopy, the
  no-double-wrap flux characterization, the inversion duality — are
  fully analytic. Support-only COST floors (Entry 19) and route-B hand
  classification at weight 10 (368 orbits, Entry 21) are documented
  dead ends. [A3 log entries
  16–22](../experiments/bb_lab/notes/A3_track1p1_log.md).

- 2026-05-27 — bb_distance_conjecture_family_d_v3_h2_minwt_formula — partial —
  Pinned down the (4/9)|G| empirical pattern from session 1 as a rigorous
  structural identity for weight-3 BB codes: when there exist linearly-
  independent Z_3-homomorphisms φ_A, φ_B: G → Z_3 with each sending one
  polynomial's support to {0,1,2} and the other's to a constant, the
  element 1[φ_A ≠ 2 AND φ_B ≠ 2] is in H_2 with weight (4/9)·|G|. Verified
  437/437 corpus instances, 0 violations. Conjectured generalization
  ((w-1)/w)²·|G| for weight w (untested for w ≥ 4). Implemented as Tier-1
  feature `bb_lab.h2_minwt_formula` with 14 tests. Not a distance bound
  (per §6m); a positive structural identity. [details](attempts/bb_distance_conjecture_family_d_v3_h2_minwt_formula/result.md)
