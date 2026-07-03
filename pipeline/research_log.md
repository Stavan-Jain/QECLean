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
