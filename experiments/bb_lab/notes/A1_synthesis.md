# A1 — Phase-1 synthesis: four-lane literature sweep, consolidated

Date: 2026-06-09 (lane verification passes ran through 2026-06-10).
Synthesis of lanes L1–L4 (`A1_literature_L{1,2,3,4}.md`), checked
against `A0_baseline.md` and HANDOFF.md §§6h–6k + "Reopened
directions". All verdicts below are the lanes' adversarially-verified
verdicts; nothing is upgraded here. Statuses: CONFIRMED /
CONFIRMED-WITH-CORRECTIONS (CWC) / UNVERIFIABLE (no verifier verdict —
researcher-grade only) / REFUTED.

**Headline.** Phase 1 found no kill for any Phase-2 track, one genuine
preemption (the odd-h cover transfer — published twice), a complete
verified toolkit for Tracks A and B, a published analytic anchor for
the bottom of gross's cover chain, and two internal errors in the
program's own documents (A0 observations 2-as-glossed and 3; two
phantom/apocryphal citations in HANDOFF).

**On the goal priorities (gross first).** The two highest-priority
goals are about gross specifically (1: d = 12; 3: any nontrivial
gross bound > the published LP floor of d ≥ 2). Phase 1 confirms the
*only* routes to those are the gross-directed Tier-1 leads (§3):
the h=2 Smith cover transfer (1.1, the goal-1 gate — and the crux is
now pinned to one new-math step, weight control through Δ = ∩ω on
gross's *realized* pr=0 branch) and the bivariate CMS / radical
attack on gross's own algebra (1.2, immune to the even-h wall). The
reachable-today results — a fully-analytic 2 ≤ d(bb_90) ≤ 10, and
d(bb_108) ≥ 4 from one structural d([[36,8,4]]) ≥ 4 — are goal-**2**
(non-gross) and, via the odd-h transfer, do **not** advance gross;
they are reachable precisely because they have the odd-h structure
gross lacks (the streetlight effect). They are banked as an
opportunistic Tier-2 side-deliverable (§3 lead 5), gross-relevant
only if 1.1 lands and propagates the base bound up gross's even-h
chain.

---

## 1. Claims table

Every load-bearing claim across the four lanes, with verification
status and one-line content. (Context-only findings the verifiers never
saw are listed at the end of each lane block as UNVERIFIABLE; they must
be re-verified before becoming load-bearing.)

### Lane L1 — repeated-root / non-semisimple abelian distance theory

| # | Finding | Status | Content |
|---|---|---|---|
| 1 | L1-cms-theorem1-exact-distance | CONFIRMED | CMS 1991 Thm 1: EXACT distance d = P_t̂·d(C̄_t̂) for repeated-root cyclic codes — the univariate non-semisimple prototype; blocker for gross is univariateness, not semisimplicity. |
| 2 | L1-cms-lemma1-Pt-multiplicity-weights | CONFIRMED | The P_t = ∏(t_i+1) weight ladder; for p = 2 the candidate multiplicative factors m(A) are powers of 2; d(C) ≤ P_t·d(C̄_t) for all t. |
| 3 | L1-vanlint-plotkin-2cover | CWC | Generalized van Lint (Chen–**Xie**–Ding arXiv:2402.02853 Thm 2.1): exact h=2 char-2 cover distance d = min{2d(C₁), d(C₂)} via Plotkin decomposition — no p∘τ transfer needed. |
| 4 | L1-ozadam-univariate-loewy-distance | CONFIRMED | Özadam–Özbudak Thm 3.6 (no odd-p restriction): complete distance ladder for all ⟨(x^n+γ)^i⟩ — exact per-axis weight atoms of F₂[Z₄] and F₂[Z₂]. |
| 5 | L1-monomial-like-product-distance | CONFIRMED | Monomial-like codes Thm 3.5: d(⟨(x−1)^a(y−1)^b⟩) = d_x(a)·d_y(b) in F₂[Z₄×Z₂]-type ambients — calibration target for any m(A). |
| 6 | L1-piga-definition-and-characterization | CWC | Fisher–Sehgal: F₂[A×B] is a PIGA iff the 2-Sylow B is cyclic; gross's F₂[Z₁₂×Z₆] is non-PIGA → JLLX line inapplicable. |
| 7 | L1-nonpiga-local-decomposition | CONFIRMED | Choosuwan: F₂[Z₁₂×Z₆] ≅ (F₂+uF₂)[Z₄] × ((F₄+uF₄)[Z₄])⁴ — canonical local coordinates (DFT step not weight-preserving). |
| 8 | L1-berman-charpin-radical-powers | CWC | Radical powers of elementary-abelian F_p[G] are RM codes (min weights classically known); the gap is exactly non-cyclic non-elementary 2-groups, i.e. Z₄×Z₂. |
| 9 | L1-pir-multivariate-characterization | CWC | Cazaran–Kelarev: gross's ambient F₂[x,y]/(x¹²−1, y⁶−1) is NOT a PIR (both axes repeated-root) — no generator-polynomial distance calculus exists for it. |
| 10 | L1-mmrua-repeatedroot-dcc2007 | CWC (abstract only; theorems unfetched) | MM-Rúa DCC 2007: distance computation for principally-generated multivariable chain-ring codes — the single must-fetch before any Track-A novelty claim. |
| 11 | L1-jitman-ling-2013-scope | CWC (abstract only) | JLLX 2013: PIGA-scoped semisimple-quotient UPPER bound + asymptotic badness; cannot block a lower bound on the non-PIGA gross ambient. |
| 12 | L1-coprime-bb-no-analytic-distance | CWC (**narrowed**) | Coprime BB: k analytic, d numeric in Wang–Mueller — but Wang–Pryadko 2022 (arXiv:2203.17216) gives weak analytic GB lower bounds covering coprime BB; novelty claims must read "no tight per-code analytic certification". |
| 13 | L1-drensky-lakatos-monomial-ideals | **REFUTED** | Quote was doctored (x^p inflated to x^{p^{s_i}}); D-L 1989 covers only elementary-abelian ambients — no shortcut to rad^t(F₂[Z₄×Z₂]) minimum weights. |
| 14 | L1-cms-asymptotic-badness | UNVERIFIABLE | CMS Thms 2–3: repeated-root cyclic codes asymptotically bad as δ→∞ (no force at gross's fixed δ). |
| 15 | L1-berman-codes-exact-distance | UNVERIFIABLE | Modern Berman-code revival has exact distances but no group-algebra ideal structure for even n. |
| 16 | L1-dinh-chainring-context | UNVERIFIABLE | Univariate chain-ring (F+uF) distance theory exists; checked instances assume p odd. |
| 17 | L1-roth-seroussi-1986 | UNVERIFIABLE | "Roth–Seroussi 1986" is the cyclic-MDS note, not a second source for the CMS reduction — attribute to CMS 1991 alone. |

### Lane L2 — Z₂-cover transfer, Smith theory, lifted/balanced products

| # | Finding | Status | Content |
|---|---|---|---|
| 18 | L2-srb-thm31-cover-conditions | CWC | SRB Thm 3.1 (sufficiency-only): formal BB h-cover class via voltage group Γ = Z_u×Z_t with FREE deck action; gross = 2-cover of [[72,12,6]]. |
| 19 | L2-srb-lemma44-even-h-collapse | CONFIRMED | p∘τ = h·I = 0 mod 2 for even h — the exact failure point; only injectivity/surjectivity arguments are lost (Remark 9). |
| 20 | L2-srb-odd-h-theorems | CWC | Thms 4.5–4.7 are odd-h; but the chain maps p_•, τ_• (Thms 4.1/4.3) carry NO parity hypothesis — reusable as-is at h=2. |
| 21 | L2-srb-thm48-weight-preserving-lift | CWC | Thm 4.8 (any h): a weight-preserving-lift chain map σ_•: base→cover (direction fixed by verifier) forces d_h ≤ d — parity-free non-saturation machinery. |
| 22 | L2-srb-s7-conjecture | CONFIRMED | SRB §7 conjecture: [[hn, k_h ≥ k, d ≤ d_h ≤ hd]] for ALL h. Track B is its h=2 case. |
| 23 | L2-guemard-zemor-prop35-transfer | CWC | GZ Prop 3.5 + Remark 3.6 (concurrent with SRB, not independent): odd-t transfer at full free-Γ-module chain-complex generality — includes BB covers. |
| 24 | L2-smith-sequence-machinery | CONFIRMED | Smith exact sequence for free involutions over F₂ (Degtyarev–Kharlamov A.1.1/A.1.5; Bredon Ch. 3); obstruction is Δ = ∩ω; zero QEC applications in the literature. |
| 25 | L2-kp2013-thm5-floor-bound | CWC | KP-2013 Thm 5: D ≥ ⌊d/c⌋ — the 2013 ancestor of the whole ⌈d/c⌉ family Track A must improve on. |
| 26 | L2-kp2013-thm8-9-even-c-over-F2 | CWC | KP-2013 Thms 8–9 (§IV.E): published F₂ EVEN-symmetry distance lower bounds via symmetric-part decomposition u^(1+x) + γᵀG_Z — best prior art for beating the 2-divisibility wall. |
| 27 | L2-wang-pryadko-statement3 | CONFIRMED | WLP arXiv:2305.06890 Statement 3: d_Z ≥ ⌈d₀/c⌉ for 2BGA, exact when N = {1}; gives 2 on gross. |
| 28 | L2-lin-pryadko-statement12-13 | CONFIRMED | LP Statements 12/13 verbatim with hypotheses; lower/upper bounds coincide when c = 1. |
| 29 | L2-srb-citing-papers-no-resolution | CWC | All **6** citing papers (count corrected; latest 2026-06-07) leave the even-h conjecture unresolved — novelty window open as of 2026-06-10. |
| 30 | L2-hsieh-legall-phantom-citation | CONFIRMED | "Hsieh–Le Gall 2020" does not exist (only joint paper: 2011 NP-hardness of decoding) — purge from HANDOFF.md:458, 632–633. |

### Lane L3 — publication frontier for gross d = 12

| # | Finding | Status | Content |
|---|---|---|---|
| 31 | L3-bravyi-mip-distance | CWC | Gross's d = 12 is ILP-computed (exact for 5 of 7 Table 3 codes, gross included); the source paper has no analytic distance proof or lower bound. |
| 32 | L3-bravyi-lemma1-dxdz | CONFIRMED | Lemma 1: n, k, d characterization + d_X = d_Z — any Phase-2 theorem need only bound d_Z. |
| 33 | L3-es-fundamental-exact-sequence | CONFIRMED | Eberhardt–Steffan Thm 2.3 fundamental exact sequence applies verbatim to gross — no semisimplicity hypothesis. |
| 34 | L3-es-gross-nonprincipal | CONFIRMED | ES Table 1 marks gross non-pure / non-principal / non-symmetric; principality guarantee needs ℓ, m odd — the explicit-basis shortcut is dead. |
| 35 | L3-lp-statement12 | CWC | LP Statement 12 is the identified (not provably "only") published applicable lower bound; "rank" = group order, c = \|N\| = 8 confirmed; gives d ≥ 2 on gross. |
| 36 | L3-srb-odd-h-theorem | CONFIRMED | SRB's rigorous parameter transfer is odd-h only (plus the any-h conditional upper bound Thm 4.8). |
| 37 | L3-srb-even-h-explicitly-open | CONFIRMED | The even-h case is an explicit SRB open question; authors say it "may require different tools"; no proving follow-up exists. |
| 38 | L3-otjens-citation-correction | CONFIRMED | "Otjens 2025" + the "no closed-form analytical formula" quote are apocryphal; the real source is Postema–Kokkelmans arXiv:2502.17052 ("exact tradeoff … remained unknown"). |
| 39–45 | L3 context findings (LP tables computational; PK Bravyi–Terhal bound vacuous at n=144; Arnault upper bound; Liang Gröbner analytic-for-k-only; QDistRnd randomized; Rabeti univariate upper-only; Wang–Mueller coprime k-only) | UNVERIFIABLE | Frontier context; re-verify before any becomes load-bearing. |

### Lane L4 — analytically-anchored base codes for the cover chains

| # | Finding | Status | Content |
|---|---|---|---|
| 46 | L4-18-8-2-is-HGP | CONFIRMED | The chain bottom [[18,8,2]] IS HGP(J₃,J₃) (verifier re-derived from scratch); its d = 2 is published-analytic. |
| 47 | L4-tz-hgp-distance-theorem | CONFIRMED | Tillich–Zémor Thm 15 (+ Lemmas 16/17): HGP distance ≥ min(d₁,d₂,d₁ᵀ,d₂ᵀ), with equality conditions — all hypotheses verified for [[18,8,2]]. |
| 48 | L4-kp-square-seed-family | CONFIRMED | KP arXiv:1202.0928 Eq. (12) square-circulant-seed HGP: simplest citable form of the anchor (and cleanest Lean target). |
| 49 | L4-lp-statement-8-hgp | CWC | LP Statement 8 + connectivity correction G_a·G_b = G: BB = HP exactly when supports separate (c = 1); holds for [[18,8,2]]. |
| 50 | L4-lp-statement-12-and-c1-equality | CWC | Equality is GUARANTEED only at c = 1 (one-directional, not "iff"); [[36,8,4]] (c = 2: bound 2 vs true 4) is the smallest concrete instance of the c > 1 gap. |
| 51 | L4-36-8-4-is-tiew-breuckmann-bp | CONFIRMED | [[36,8,4]] = Tiew–Breuckmann balanced-product q = 2 code; only a published UPPER bound (d ≤ 2q); table distances numerical. |
| 52 | L4-no-hgp-36-8-4 | CWC | Original Griesmer/TZ-Lemma-17 derivation (verifier re-checked): NO binary HGP code has parameters [[36,8,4]] — anchor cannot move up by HGP citation. |
| 53 | L4-tb-hgp-18q2-family | CWC | TB [[18q²,8,2q]]: the only weight-6 separated-support family with analytic exact distance at all sizes — the c = 1 control any c-aware bound must reproduce. |
| 54 | L4-srb-thm-4-6-4-7 | CONFIRMED | The only published rigorous cover transfer: odd h with k preserved (Thms 4.6 + 4.7). |
| 55 | L4-rigorous-odd-h-bases-exist | CWC | **A0 observation 3 is wrong**: bb_90 (3×3, h=5) and bb_108 (3×6, h=3) have rigorous odd-h bases with k′ = 8; SRB Thms 4.6+4.7 give fully-analytic 2 ≤ d(bb_90) ≤ 10 today (upper bound saturated). Sub-claim "gross is the only flagship lacking odd-h positive-k′ bases" REFUTED (bb_72 and bb_288 also lack them). |
| 56 | L4-liang-twisted-tori-correspondence | CONFIRMED | Liang et al. twisted-tori framework covers gross geometrically (Example 3 polynomials verified); zero analytic distance content. |
| 57 | L4-prior-art-clearance-2026 | CWC (`verified = false`; blanket sub-claims REFUTED) | Gross-specific clearance survives adversarial re-search; the blanket clause "nothing for non-separated weight-6 BB codes" is refuted by SRB's own odd-h theorem — all novelty claims must carve it out explicitly. |
| 58–60 | L4 context findings (SRB Examples 5–7 chain identifications; LP weight-4 toric classification; ECZoo distance statements — note ECZoo's HGP formula is stated UNconditionally, stronger than TZ proves) | UNVERIFIABLE | Verify before load-bearing use (esp. #58 before any Phase-2 text asserts the SRB cover identifications). |

**Refuted-claims summary (must never be propagated):** L1's
Drensky–Lakatos shortcut (#13); L4's blanket weight-6 clearance clause
and "gross uniquely lacks odd-h bases" (#55, #57); A0 observation 3
(internal, corrected by #55); the "Hsieh–Le Gall 2020" and "Otjens
2025" citations (#30, #38, phantoms in HANDOFF/program notes); A0's
"saturates d_cover = 2·d_base all the way down" gloss (false at the
[[72,12,6]] → [[36,8,4]] step: 6 ≠ 2·4 — L4 open question 3).

---

## 2. Per-track impact assessment

### Track A — radical-multiplicative Lin–Pryadko (d_A^⊥ ≥ m(A)·d̄ over the semisimple reduction, composed with LP Statement 12)

**Verdict: ENABLED.** No preemption, no kill; the lane delivered the
full toolkit and confirmed the target is genuinely open territory.

- **Tools now in hand (all verified):** the CMS 1991 Lemma-2 valuation
  mechanism as the exact proof template (project a codeword at its
  radical depth t; weight factorizes as ≥ P_t·d̄_t) — an EXACT theorem,
  not just a bound; the P_t powers-of-2 ladder for the candidate m(A)
  values; the per-axis weight atoms of F₂[Z₄] and F₂[Z₂]
  (Özadam–Özbudak, valid at p = 2); exact tensor-monomial distances
  d(⟨(x−1)^a(y−1)^b⟩) = d_x(a)·d_y(b) in F₂[Z₄×Z₂] as calibration
  targets; the Choosuwan decomposition F₂[Z₁₂×Z₆] ≅ (F₂+uF₂)[Z₄] ×
  ((F₄+uF₄)[Z₄])⁴ as canonical coordinates; the ES Thm 2.3 fundamental
  exact sequence (no semisimplicity hypothesis) for the logical-space
  anatomy; and the confirmed baseline c = \|N\| = 8 (Statement 12's
  "rank" = group order, verified from the paper's own usage).
- **Frontier pinned:** gross's ambient is verifiably non-PIGA
  (Fisher–Sehgal) and non-PIR (Cazaran–Kelarev) — every published
  generator-polynomial distance line stops structurally short of the
  two-repeated-axes case. L1 open question 3 (re-prove CMS's
  lower-bound half against the bivariate filtration with tensor
  weights as the P-ladder) has no literature obstacle and no precedent.
- **Novelty claim must be narrowed:** Wang–Pryadko 2022
  (arXiv:2203.17216) gives weak analytic GB lower bounds covering
  coprime BB — the defensible claim is "no tight per-code analytic
  certification, and nothing at all for the non-coprime /
  non-cyclic-Sylow regime". Must-fetch before publishing: MM-Rúa DCC
  2007 theorem statements; must-check at body level: Rowshan
  arXiv:2601.01137 (abstract over-claims relative to its theorems).
- **Cost increase:** the Drensky–Lakatos shortcut is REFUTED — Track A
  must derive the rad^t(F₂[Z₄×Z₂]) minimum weights itself (likely a
  visibility argument over sums of monomial-like ideals, calibrated
  against the confirmed tensor formula).
- Track A must also position itself explicitly against the 13-year-old
  ⌊d/c⌋ mechanism (KP-2013 Thm 5 → WLP St. 3 → LP St. 12): the bare
  mechanism is PREEMPTED; only the radical-multiplicative numerator
  improvement is new.

### Track B — h=2 cover transfer (d_cover ≥ d_base) + saturation criterion

**Verdict: ENABLED** (with the odd-h sub-case PREEMPTED — published
twice; per plan it converts to "verify + adapt", and nothing is lost
since the rigorous odd-h bound never reaches gross).

- **The target is confirmed open** as of 2026-06-10: SRB §7
  conjectured it, GZ proved only odd t (at free-Γ-module generality —
  any odd-h novelty claim is scooped on arrival), all 6 citing papers
  leave it unresolved, SRB is still v1. A Track-B proof would be the
  first proof of the h=2 case of a named open conjecture.
- **Failure point localized to one lemma:** SRB Lemma 4.4
  (p∘τ = h·I = 0 mod 2). The chain maps p_•, τ_• exist for ALL h and
  are reusable as-is; only the pr_*[L̃] = 0 branch needs new work
  (L2 open question 3 verified the other branch is already covered by
  the induced-map structure).
- **Two sourced replacement tools:** (1) the Smith exact sequence for
  free involutions over F₂ (Degtyarev–Kharlamov A.1.5 / Bredon Ch. 3)
  applies verbatim to gross's cover (free Z₂ action via GZ Lemma 3.8,
  F = ∅), with the residual obstruction identified exactly as
  Δ = ∩ω : H₂(base) → H₁(base), ω the explicit x-direction cut
  cocycle — never applied to QEC; (2) KP-2013 Thms 8–9 (§IV.E), a
  published rigorous F₂ EVEN-symmetry distance lower bound via
  symmetric-part decomposition with no transfer inversion. A third,
  classical precedent: the generalized van Lint theorem
  (Chen–Xie–Ding Thm 2.1) proves an exact h=2 char-2 cover distance by
  Plotkin decomposition — strong evidence the even-h obstruction is a
  proof-technique artifact, and the natural mechanism to lift along
  gross's free Z₂-translation.
- **Chain anchor upgraded:** [[18,8,2]] = HGP(J₃,J₃) with published
  analytic d = 2 via three hypothesis-verified routes (TZ Thm 15, KP
  Eq. (12), LP St. 8 + connectivity) — the chain bottoms out on a
  citation, not a weight-1 exhaustion. The anchor cannot move up by
  citation: [[36,8,4]] has only TB's upper bound and provably no HGP
  realization; [[72,12,6]] is in no known analytic family (the
  biggest remaining gap).
- **New milestones (available today):** A0 obs. 3 corrected — bb_90
  and bb_108 have rigorous odd-h bases with k′ = 8, so
  2 ≤ d(bb_90) ≤ 10 is fully analytic now, and an analytic
  d([[36,8,4]]) ≥ 4 yields a fully-analytic d(bb_108) ≥ 4 with no
  conjectural ingredient.
- **Saturation sub-goal REDIRECTED:** the chain-wide
  d_cover = 2·d_base law is empirically false at the
  [[72,12,6]] → [[36,8,4]] step (6 ≠ 8). The right target is
  d_cover ≥ d_base, with saturation treated per-step; SRB Thm 4.8's
  weight-preserving lifts are the parity-free vocabulary (existence ⟹
  d_h ≤ d certifies non-saturation; consistency check: no such lift
  can exist for the (gross, [[72,12,6]]) pair).

### Track C — single-prime-G_odd restriction of the R1+R4 radical-weight bound

**Verdict: UNCHANGED.** No lane addressed Track C directly (L1
explicitly: "Tracks C/D: no direct inputs beyond the novelty
framing"); no preemption, no kill, no new tool aimed at it.
Indirect effects: (a) Track C shares Track A's radical-weight
infrastructure, so the verified per-axis atoms, tensor-monomial
distances, and Choosuwan coordinates are usable, and the
Drensky–Lakatos refutation raises its cost the same way (rad^t
minimum weights must be derived in-house); (b) the novelty-framing
narrowing (Wang–Pryadko 2022, Rowshan body-check) applies to any
radical-weight write-up; (c) gross/[[72]]/[[288]] all have
G_odd = Z₃² (single prime), so the restriction's domain still
contains the engineering targets — nothing in Phase 1 changed that.

### Track D — multivariate HT/BCH under full-axis-support hypothesis

**Verdict: REDIRECTED.** No lane found a published multivariate
HT/BCH instrument for the non-semisimple bivariate case (L1's dead
end 1: the two-repeated-axes problem is untouched; the
character-theoretic family remains bounded by the semisimple quotient
per §6j), and nothing killed the direction. The literature suggests a
better formulation and imposes one mandatory check:

- **Better substrate:** the Liang et al. twisted-tori / anyon /
  Gröbner-basis framework (arXiv:2503.03827, PRX Quantum 2025) is the
  published geometric reframing of gross (Example 3 polynomials
  verified exact); its machinery is analytic for k but the d-slot is
  open — any HT/BCH-style full-axis-support argument should be stated
  there rather than against raw bivariate cyclic structure.
- **Mandatory pre-claim fetch:** Chen et al. arXiv:2503.04699
  (PRL 135, 076603 (2025)) reportedly derives BB distance scaling
  lower bounds O(L) via the Bernstein–Khovanskii–Kushnirenko theorem
  (unfetched in Phase 1). If per-family and analytic, it partially
  preempts family-level claims — Track D converts to "verify + adapt"
  against it. Also unfetched: Leverrier–Rozendaal–Zémor
  arXiv:2512.20532 (spot-check says odd-\|G\| only).
- Boundary fact to respect: Rowshan 2601.01137's BCH-like analytic
  bounds are for the SYNDROME distance only (per L1's body-level
  reading), and the coprime regime is already covered weakly by
  Wang–Pryadko 2022 — Track D's defensible novelty is the
  non-coprime, full-axis-support regime.

---

## 3. Phase-2 leads, ranked by directness toward the gross goals

**Re-ranking rationale (2026-06-10).** Goals in priority order are
(1) analytic proof gross d = 12, (2) analytic bound for a class of BB
codes, (3) any nontrivial analytic bound on gross. The first Phase-1
synthesis pass let "nearest-term publishable" float the bb_108/bb_90
results to the top — but those are goal-**2** (non-gross), and via the
*odd-h* SRB transfer they do **not** advance gross (gross's chain is
even-h at every level; different, unproven machinery). They are
reachable precisely because they have the odd-h structure gross
lacks — the streetlight effect. This section is re-ordered to lead
with the **gross-directed** tracks (goals 1 & 3) and to demote the
non-gross result to an opportunistic side-deliverable whose gross
relevance is *contingent on Track B*.

Note the floor: gross already has a published analytic d ≥ 2 (LP
Statement 12, c = 8 ⟹ ⌈12/8⌉ = 2). So "progress on gross" means
**beating 2**, and only the gross-directed tracks below can.

### Tier 1 — gross-directed (goals 1 & 3)

1. **Smith-sequence proof of the h=2 cover transfer (Track B core —
   the goal-1 gate).** This is the master key: a proven h=2 transfer
   `d_cover ≥ d_base` propagates *up* gross's even-h chain, so
   combined with any analytic base bound > 2 it lifts gross above the
   LP floor (e.g. transfer + [[36,8,4]] structural d ≥ 4 ⟹ d(gross)
   ≥ 4; deeper bases push higher; the conjectural ceiling is
   d(gross) ≥ 6 from [[72,12,6]]). Start from: Degtyarev–Kharlamov
   arXiv:math/0004134, Appendix A.1 (Thm A.1.1, A.1.2, Cor A.1.3,
   A.1.5; proofs in Bredon, *Compact Transformation Groups*, Ch. 3),
   plus SRB arXiv:2511.13560 Thms 4.1/4.3 (chain maps, valid at h=2)
   and GZ arXiv:2502.20297v2 Lemma 3.8 (free-Γ-module hypothesis).
   Two-branch skeleton set up in L2 (§ L2-smith-sequence-machinery,
   open questions 2–3); the only new mathematics is weight control on
   the pr_*[L̃] = 0 branch, obstruction identified exactly as
   Δ = ∩ω : H₂(base) → H₁(base) (ω = x-direction cut cocycle). Gap 5
   confirmed gross's pr=0 branch is *realized*, so this weight-control
   step is unavoidable and is genuinely new math (no bundle/product
   tool supplies it). State at free-Γ-module generality per GZ
   Remark 3.6.

2. **Bivariate CMS valuation theorem (Track A — the gross-native
   direct attack).** The one route that bypasses the even-h wall
   entirely: it works on gross's own group algebra F₂[Z₁₂×Z₆], no
   cover. This is the hedge if Track B's even-h transfer stays out of
   reach, and the only standalone path to a gross bound > 2. Start
   from: CMS 1991 (ETH Massey archive, BI433.pdf — only source for
   the exact statement), Lemma 1 / eqs. (7)–(13c) and the Lemma-2
   lower-bound mechanism (eqs. (20)/(21)/(25)/(27)); replace the
   (x−1)-adic valuation with the bivariate radical filtration of
   F₂[Z₄×Z₂] (nilpotency index 5), using the monomial-like tensor
   weights (arXiv:1003.3386 Thm 3.5) as the P-ladder and the
   Özadam–Özbudak atoms (arXiv:0906.4008 Thm 3.6) per axis. First
   sub-task: derive the rad^t(F₂[Z₄×Z₂]) minimum weights in-house
   (the D-L shortcut is refuted, Gap 1). Compose with LP Statement 12
   (arXiv:2306.16400) on the semisimple-reduction side. Gap 1
   confirmed the target is open across the entire MM-Rúa lineage.
   Pre-publication gates: fetch MM-Rúa DCC 2007
   (DOI 10.1007/s10623-007-9114-1); body-check Rowshan 2601.01137;
   cite and distinguish Wang–Pryadko arXiv:2203.17216.

3. **Translate KP-2013's repeated-codeword decomposition to the
   (gross, [[72,12,6]]) pair (Track B second route, gross-native).**
   A concrete, possibly more tractable alternative to the full Smith
   argument — it attacks the same even-h transfer but via an explicit
   F₂ even-symmetry decomposition rather than equivariant topology.
   Start from: Kovalev–Pryadko arXiv:1212.6703v2, §IV.E (Lemma 4,
   Thms 8–9, pp. 9–10) — the only published F₂ even-symmetry distance
   lower bound, proved by splitting any null vector as
   u^(1+x) + γᵀG_Z with no transfer inversion. Open work (L2 open
   question 1): does (gross, [[72,12,6]]) satisfy a BB analogue of
   k_i^(1+x) = k_i, and what does d = min(d₁,d₂,d̃₁,d̃₂) become in BB
   language? Classical h=2 mechanism to imitate: generalized van Lint
   theorem, Chen–Xie–Ding arXiv:2402.02853 Thm 2.1 (exact
   d = min{2d(C₁), d(C₂)} by Plotkin decomposition along a free
   Z₂-action).

4. **Compute the four terms of the ES fundamental exact sequence for
   gross (cheap groundwork — do this first; feeds Tiers 1.1–1.3).**
   Not itself a bound, but the cheapest gross-specific computation
   that produces structural understanding, and the natural input for
   any weight-aware argument on gross — it localizes where Track A's
   filtration and Track B's homology classes actually live in gross's
   12-dimensional logical space. Start from:
   Eberhardt–Steffan arXiv:2407.03973 (IEEE TIT 2025), Theorem 2.3,
   with R = F₂[Z₁₂×Z₆], c = x³+y+y², d = y³+x+x²: compute
   dim ann(c)/ann(c)(d), dim ann(d)/(c)ann(d), dim ((c)∩(d))/(cd),
   dim ann(cd)/M (L3 open question 2). The literature marks gross
   non-pure but never quantifies the pure/obstruction split of its
   12-dimensional logical space; this is unpublished, cheap
   (computational), and is the natural input for any weight-aware
   minimum-weight argument on gross — including where Track A's
   filtration and Track B's homology classes actually live.

### Tier 2 — opportunistic (goal 2; gross-relevant only via Tier 1.1)

5. **Structural d ≥ 4 for [[36,8,4]] from scratch.** *Demoted from
   the first pass's #2.* Standalone this is a goal-2 result: composed
   with the *odd-h* SRB Thm 4.7 it gives the program's first
   fully-analytic bound on a Bravyi instance, d(bb_108) ≥ 4 (and the
   free rider 2 ≤ d(bb_90) ≤ 10 from SRB Thms 4.6+4.7 over the h=5
   cover of [[18,8,2]], upper bound saturated) — but **bb_108 and
   bb_90 are not gross**, and the odd-h route does not reach it. Its
   one path to gross is via Tier 1.1: *if* the even-h transfer is
   proven, this same base bound propagates up gross's even-h chain to
   d(gross) ≥ 4. So pursue it **only** (a) as a cheap goal-2 banking
   move once Tier 1 is underway, or (b) if its proof *technique* — a
   structural "no weight-≤3 logical" argument on the balanced-product
   logical space — looks like it scales conceptually to gross's
   144-qubit space (where enumeration is hopeless). Test that
   scalability explicitly before investing; if it's [[36,8,4]]-specific
   combinatorics, it stays a consolation prize. *Redirected by Gap 3:*
   no published analytic route exists (BE 2012.09271 wrong shape +
   vacuous expansion; LP tops out at 2); the obligation is
   structural, *not* a `decide`/ILP enumeration (which fails the
   analytic bar by the same logic that excluded SAT — trust base ≠
   analytic). Inputs: Tiew–Breuckmann arXiv:2411.03302 §VI.B
   (balanced-product realization, q=2 identity verified); the
   L4-no-hgp-36-8-4 impossibility closes the HGP shortcut; the TB
   Gurobi check (github.com/h1010134/balanced-product-cyclic-codes)
   validates the target number, not the proof.

---

## 4. Honest gaps — what Phase 1 could not determine

**Unfetched / paywalled sources (each gates a specific claim):**

- MM-Rúa DCC 2007 theorem statements (Springer paywall) — Track A's
  must-fetch before any novelty claim; expected PIR-confined but
  unverified at source.
- JLLX 2013 exact theorem text (IEEE paywall, no arXiv) — abstract
  level only; needed only for scholarly completeness.
- Rowshan arXiv:2601.01137 at body level — its abstract claims more
  about coprime-BB distance than its theorems appear to deliver;
  must be settled before Track A/D novelty wording.
- Chen et al. arXiv:2503.04699 (BKK scaling bounds) and
  Leverrier–Rozendaal–Zémor arXiv:2512.20532 — both unfetched; both
  gate family-level analytic-lower-bound novelty claims (Tracks A/D).
- Dinh IEEE TIT 55(4) 2009 (chain-ring constacyclic distance
  formulas for the (F+uF)[Z₄]-type local components) — unread; would
  feed Track A's decomposed coordinates.

**Open mathematical questions Phase 1 surfaced but could not answer:**

- Minimum weights of rad^t(F₂[Z₄×Z₂]) (and of F₂[G₂] for general
  non-cyclic, non-elementary-abelian 2-groups): not published
  anywhere in closed form; the D-L hope is refuted. Must be derived.
- Any weight-distortion bound relating Hamming weight in F₂[A×G₂]
  coordinates to the Choosuwan DFT components R_i[G₂]: nothing found
  — the missing transfer step for chain-ring-based Track A routes.
- When is Δ = ∩ω : H₂(base) → H₁(base) zero or controllable for BB
  chain complexes? (On [[72,12,6]] the relevant H₂/syzygy space is
  12-dimensional.) Nobody has attempted this; it is exactly Track B's
  new mathematics.
- Does the (gross, [[72,12,6]]) pair satisfy a BB analogue of
  KP-2013's repeated-codeword hypothesis k^(1+x) = k? Unchecked.
- [[72,12,6]]'s analytic status: in no known analytic family (not
  HGP — c = 4; not in the TB families — k = 12). The single biggest
  gap between the [[18,8,2]]/[[36,8,4]] anchors and gross.
- Whether SRB's Remark-8 rank/nullity + mapping-cone sketch yields a
  checkable sufficient condition for k_h ≥ k at h = 2 on the gross
  chain.
- bb_288's d_A^⊥ (kernel dim 24 exceeds the brute-force cap) — the
  d = d_A^⊥ pattern (A0 obs. 1) is untested there; needs
  Brouwer–Zimmermann or SAT.
- Whether the ECZoo's UNconditional HGP distance formula is proven
  anywhere (candidate: Zeng–Pryadko) — until then cite TZ Thm 15's
  conditional version only.

**Verification residue (claims standing on one pass only):**

- Four L1 findings, seven L3 context findings, and three L4 context
  findings never received a verifier verdict (marked UNVERIFIABLE in
  §1) — including the SRB Examples 5–7 chain identifications (#58),
  which Phase-2 text must not assert without verification.
- The KP-2013 Thm 5 proof was not re-read to close the last residue
  of the "rank = \|N\|" reading (the paper's terminology settles it;
  the proof-level check is cheap insurance before Track A invests).
- Scoop risk is live: SRB is v1 with 6 citing papers and counting;
  re-run the even-h preemption search immediately before any Track-B
  publication (L3 open question 6).

**Policy question left open:** whether a transcribed ILP
dual/optimality certificate for d = 12 would count as "analytic"
(L3 open question 3) — currently excluded by the no-IP rule; needs an
explicit program decision, not literature.

---

## 5. Corrections to program documents (consolidated action items)

1. **`A0_baseline.md` observation 3** is wrong by its own tables:
   replace with "only bb_90 (3×3, h=5) and bb_108 (3×6, h=3) have
   rigorous odd-h bases with k′ > 0; bb_72, gross, and bb_288 lack
   them." Do NOT write "gross is the only instance lacking them."
2. **`A0_baseline.md` observation 2's** "saturates d_cover = 2·d_base
   all the way down" is false at [[72,12,6]] → [[36,8,4]] (6 ≠ 2·4);
   only gross→72 and 36→18 saturate. Track B's target inequality is
   d_cover ≥ d_base.
3. **HANDOFF.md:458, 632–633**: purge "Hsieh–Le Gall 2020" (phantom;
   the only joint paper is the 2011 NP-hardness-of-decoding result).
4. **HANDOFF §6j closing line + `notes/T2.3_literature_survey.md`
   Conjectures item 1**: replace "Otjens 2025" and its apocryphal
   quote with Postema–Kokkelmans arXiv:2502.17052 and the verbatim
   "exact tradeoff … remained unknown" sentence.
5. **`notes/T2R4.0_literature.md` §3e**: attribute the repeated-root
   reduction theorem to CMS 1991 alone (Berman 1967 as precursor);
   "Roth–Seroussi 1986" is the unrelated cyclic-MDS note.
6. **Novelty-claim phrasing rules** for all Phase-2 write-ups: carve
   out SRB Thm 4.7 (odd-h covers) from any "no analytic lower bound
   for non-separated weight-6 BB codes" statement; narrow "no
   analytic BB lower bound anywhere" to "no tight per-code analytic
   certification" citing Wang–Pryadko arXiv:2203.17216; audit
   arXiv:2510.05211 (self-dual weight-6 → color codes) before final
   prior-art wording; cite the full four-author JLLX list and the
   three-author Chen–Xie–Ding list.

---

## 6. Supplementary round (critic gaps 1–5, resolved 2026-06-10)

The Phase-1 completeness critic flagged five decision-blocking gaps;
each was closed by a dedicated research agent with primary-source
fetches and verbatim quotes. Verdicts below; full reports preserved
in the session transcripts, key quotes inline.

### Gap 1 — MM-Rúa 2007 does NOT preempt Track A (and only weakly enables it)

Full text of Martínez-Moro–Rúa, DCC 45:219–227 (2007) obtained
(Springer PDF, public). Their Theorem 2 (the distance result) applies
to arbitrary ideals — including two-repeated-axes ideals — but its
entire content is a chain-ring → residue-field reduction:
`d(K) = d(⟨χ̄ₓ⟩)` over `F_q`. For gross's ambient the coefficient
ring is already `F₂` (nilpotency index t = 1), so **Theorem 2
collapses to the tautology d(K) = d(K)**. Their Theorem 1
independently re-certifies gross's ambient as non-principal (both
`x¹²−1 = (x³−1)⁴` and `y⁶−1 = (y³−1)²` fail square-freeness).
Across all 21 citing papers, the only field-level repeated-root
multivariable distance computations are for **single-monomial ideals**
`⟨(x₁−1)^{i₁}···(xₙ−1)^{iₙ}⟩` in full p-power-length ambients
(Martínez-Moro–Özadam–Özbudak–Szabo, J. Algebra Comb. Discrete
Struct. Appl. 2(2):75–95 (2015): product formula Cor 3.5, and the
multivariable weight-retaining Theorem 5.4 — the closest extant
relative of Track A's m(A) mechanism). BB's 2-generated mixed-length
ideals are untouched: **Track A's bivariate target is open in this
entire lineage.** Bibliographic note: the supposed companion "On the
structure of multivariable codes over finite chain rings" does not
exist — the real companion is the SIAM JDM 20(4):947–959 (2006)
serial-codes paper (arXiv math/0505491). Treat the other title as a
phantom citation.

### Gap 2 — Chen et al. BKK paper does NOT preempt Track D; LRZ has no even-degree content

arXiv:2503.04699 = PRL 135, 076603 (2025) is real and is about BB
codes, but BKK/mixed-volume machinery is used to compute the
**topological index Q (anyon count / k)** — "we relate the
topological index Q to the mixed volume of Newton polytopes" — and
the paper contains **no distance bound of any kind** (sole distance
sentence: exactness "guarantees … the code distance is macroscopic",
citing prior refs). The critic-feared "BKK → O(L) distance" claim was
a misreport; an AI-generated gloss on EmergentMind asserting a
Newton-polytope distance result is hallucinated — do not cite it.
Leverrier–Rozendaal–Zémor arXiv:2512.20532 (23 Dec 2025) exists, id
correct: no even-degree lift distance theorem; only the trivial
sandwich bound, which they call "too loose to be very useful"; their
Theorem 1 (degree-2) is dimension-only. **Tracks B and D both remain
unpreempted.**

### Gap 3 — No published route to d([[36,8,4]]) ≥ 4: prove it from scratch

Settles the L2/L4 contradiction: **the skeptical assessment was
right.** Breuckmann–Eberhardt arXiv:2012.09271's only distance
theorems (Thm 21/22, Cor 23, imported from Panteleev–Kalachev)
require Tanner-code × cycle-graph shape plus (α,β)-expansion — wrong
shape for a balanced product of two weight-3 cyclic codes, and
expansion is vacuous at n = 36 (decisive internal evidence: BE could
not analytically bound their own 1014-qubit example and used Monte
Carlo). Tiew–Breuckmann arXiv:2411.03302 defines the family —
[[36,8,4]] **verified** (not just "probably") as the q = 2 member of
[[18q,8,≤2q]] up to monomial/automorphism equivalence and X↔Z swap —
but their only analytic statement is the UPPER bound d ≤ 2q; the
published d = 4 is an exact **Gurobi ILP certificate** (parity checks
at github.com/h1010134/balanced-product-cyclic-codes — useful ground
truth for validating any formalization). Lin–Pryadko Statement 12
applies cleanly (c = |N| = 2, d⊥_A = d⊥_B = 4) and gives d_Z ≥ 2;
it structurally cannot reach 4. The SRB composition keystone is
verified verbatim (Thm 4.7: "suppose h is odd and kh = k. Then
d ≤ dh ≤ hd"), so an analytic d([[36,8,4]]) ≥ 4 composes to a
fully-analytic d(bb_108) ≥ 4.

**The proof obligation must be structural, not a `decide`.** The base
result is "no nontrivial logical of weight ≤ 3 on 36 qubits." It is
tempting to discharge this with the repo's Lean anti-witness/`decide`
pattern — but a raw `decide` over the weight-≤3 ball is **not
analytic**, and is excluded by the same program decision that
excluded SAT. Rationale (this corrects an earlier framing of this
note that treated it as an open Phase-2 question):

- "Analytic vs computational" and "trust base" are orthogonal axes.
  SAT+DRAT, a Lean kernel `decide`, and a human referee differ only
  in *trust base*. The program's "fully analytic" constraint is about
  the *other* axis — a structural, generalizing argument vs
  exhaustive case enumeration. Swapping SAT → kernel changes the
  trust base and leaves the result just as computational (a `decide`
  is in fact *dumber* than SAT — no clause learning, only kernel
  reduction). The four-color theorem is the standard illustration:
  kernel-checkable in principle, still the canonical example of a
  proof that certifies without explaining.
- The "fully analytic only — no SAT load-bearing" decision was taken
  precisely to forbid a finite computation carrying the weight of the
  result. A `decide` base case is that same forbidden hybrid
  ("analytic transfer theorem + computed base distance") with a
  different checker. It also defeats goals 1–2: enumerating
  [[36,8,4]] tells you nothing about gross (infeasible to enumerate)
  or the family.
- Where the line genuinely sits: a finite check is *not* automatically
  non-analytic — the disqualifier is *brute* enumeration. An analytic
  reduction (e.g. an automorphism/symmetry argument on the
  logical-operator space) that collapses the problem to a *handful* of
  human-surveyable cases, with the kernel discharging only that
  residue, *is* analytic (the small toric/surface-code distance proofs
  in this repo are roughly this shape). What fails the bar is `decide`
  over the whole weight-≤3 ball with no structural reduction in front
  of it.

So Track B's nearest-term deliverable is a *structural reason* no
weight-≤3 logical of [[36,8,4]] exists — a combinatorial/algebraic
argument about its logical space — not an enumeration. The TB ILP
check (and a `decide`) remain valid as ground-truth validation that
the analytic argument targets the right number; they cannot *be* the
argument.

### Gap 4 — Gross's 2-cover chain verified as SRB-class; every step is even-h; [[72,12,6]] has no analytic family

Computational verification (scripts now at
`scripts/a1_srb_cover_chain_check.py`, `scripts/a1_es_purity_check.py`):
all three steps gross→[[72,12,6]]→[[36,8,4]]→[[18,8,2]] satisfy SRB
Theorem 3.1's mod-(ℓ′,m′) monomial congruence conditions with no F₂
cancellation, each with h = 2. **Premise correction propagated**: the
lower-bound direction is Theorem 4.7 (h odd AND k_h = k), not 4.6
(upper bound, h odd only). The k-drop step is 72→36 (12 → 8); k is
preserved at gross→72 and 36→18 — all moot for SRB's theorems since
h-evenness kills them at every step: **the whole chain sits in SRB's
conjectural regime**, exactly Track B's target. SRB themselves print
gross→72 as Example 5 and the 36↔18 steps as Examples 6–7 (mirrored
orientation); §6 prose covers 72→36/18; footnote 3 credits a
V. Guemard QIP-2025 talk for the gross-double-cover observation.
[[72,12,6]]: **no analytic-family identification with provable
distance exists.** Computed not-ES-pure (dim(H_h+H_v) = 8 < k = 12 ⇒
not principal; ES Table 1 has no row for it); it is the (r,b)=(1,0)
member of Yoder et al. "Tour de gross" arXiv:2506.03094's closed-form
family with **conjectured** d = 6(2r+b−1); GB reduction blocked
(gcd(6,6) ≠ 1); Tiew–Breuckmann's family covers the chain's k = 8
members only. Its d = 6 remains numerical (Bravyi et al.).

### Gap 5 — Fiber-bundle/twisted-product literature: no weight-control transfer, no preemption; gross sits in the hard regime

HHO arXiv:2009.03921's distance machinery is engineered to make the
dangerous branch (pr_*[L̃] = 0) **empty by hypothesis**: Lemma 2.5(iii)
(fiber connectivity) forces Π_* iso on H₁ — and a free Z₂ cover's
fiber S⁰ is disconnected, failing (iii) in exactly the way that
creates the branch. Both HHO weight engines die at fiber size 2
(F₀-sum weight = m_F → 2|x|, i.e. SRB's τ; string-sliding needs fiber
1-cells, which don't exist). Panteleev–Kalachev arXiv:2111.03654
never bound d(lift) via d(base) at all (expansion of the total
object; their Lemma 4 degrades expansion by |G|); Hastings weight
reduction has no cone/extension distance lemma; Freedman–Hastings
goes code→manifold. **No preemption of h=2 transfer** — and one hard
negative calibration: per SRB's Example-8 discussion, gross has
X-logicals that project to zero, so the dangerous branch is
**realized on the flagship instance** and genuine weight control
through the Smith connecting map Δ = ∩ω is unavoidable. Keyword
sweeps re-confirm zero QEC applications of Smith theory to date.

### Net effect on the ranked leads (§3 — re-ranked 2026-06-10)

*(Lead numbers below refer to the re-ranked §3: Tier 1 = gross-directed
1.1 Smith h=2 transfer, 1.2 Track A CMS, 1.3 KP-2013 even-symmetry,
1.4 ES substrate; Tier 2 = opportunistic 5. [[36,8,4]]→bb_108.)*

- **1.1 (Smith h=2 transfer, the goal-1 gate)** stands at #1, with the
  crux now exact: weight control on the realized pr=0 branch of gross's
  own cover. Genuinely new mathematics; no tool in the bundle/product
  literature supplies it (Gap 5).
- **1.2 (bivariate CMS / Track A)** promoted to the #2 gross-native
  attack (immune to the even-h wall, the hedge if 1.1 stalls);
  confirmed open across the entire MM-Rúa lineage (Gap 1); new assets:
  monomial-like product formula + multivariable weight-retaining
  theorem (MOOS 2015).
- **5. ([[36,8,4]] → bb_108)** DEMOTED to opportunistic goal-2: no
  published analytic route (Gap 3), prove d ≥ 4 structurally (not
  `decide`/ILP — fails the analytic bar by the same logic that
  excluded SAT). It is **not gross**; its only path to gross is
  *through* 1.1 (even-h transfer propagating the base bound up). SRB
  Thm 4.7 + k₃ = k = 8 composition to bb_108 verified.
- **Track D** confirmed unpreempted (BKK misreport resolved, Gap 2).
- The fully-analytic floor *on gross* is d ≥ 2 (LP Statement 12,
  published). Beating it requires either 1.1 + an analytic base bound
  (e.g. + lead 5's d([[36,8,4]]) ≥ 4 ⟹ d(gross) ≥ 4), or 1.2 directly.
  The chain's deepest published analytic anchor is [[18,8,2]] d = 2
  (HGP); [[72,12,6]] has no analytic handle (Gap 4; Yoder family
  distance conjectured only).
