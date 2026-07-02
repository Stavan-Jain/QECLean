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

- 2026-07-02 — bb-doubling-layer-second-instance — success —
  **The free-ℤ₂ doubling template is a parametric Lean layer, and the
  `[[36,4,4]] → [[72,4,8]]` pair is proven through it** (chain+Pauli
  `d = 8 = 2·d(base)`, gross axiom bar; packaging pending).  The A9
  target screen found 152 direct-sweep doubling pairs and corrected the
  Z₆×Z₆ census: gross has **five anchorable siblings, three with exact
  `[[144,12,12]]` y-covers** — in-frame engine-necessary follow-on
  targets.
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
