# A15 — base-floor generalization: mathematical landscape + plan (v2)

> **Execution log: `A5_goal2_log.md` Entries 8–11** (2026-07-06/07).
> **T1 IS CLOSED (modulo three bounded polish items)**: the class
> small-cycle theorem v1 is assembled (Entry 11.4) — D1 ∧ D2 ∧ (iii) ∧
> no-period ∧ Ann ≠ 0 ∧ floor-bearing frame ⟹ no cycle of weight ≤ 5,
> d ≥ 6, covers inherit. Proof pieces: field-generic engine (E8.1b,
> §1.3 CONFIRMED), difference-multiset (v)-kill (E9: Lemma A/Thm D;
> E10: Thm G + Lemmas E/F/H + family collapse), Frobenius-square (iv)-
> kill (E11: Lemma I/Thm J/Lemma K — `is_frobenius_related` subsumed
> by (iii) on class members). Battery: 111,840 members / 8 frames / 0
> violations. Certifier: `a15_class_certify.py` (T1.2) — every
> obligation uniform, no per-member censuses; **Z₆×Z₁₄ [[168,12,6]]
> CERTIFIED = 4th analytic instance, 1st off-Z₃² odd part (T3a.3
> subsumed)**. Residue: polish items P1–P3 (→ A16 consolidation),
> then T2 (Lean layer), T4 (w = 5), T3c (Z₄ pilot).
>
> **Status: v2, 2026-07-06; T1 closed-mod-polish 2026-07-07** — deep-dive
> revision of the same-day v1. Successor to the goal-2 track (A4 §7, `A5_goal2_log.md`
> Entries 1–7) and the base-floor half of
> `docs/gross-distance-extensibility.md` §6. New in v2: the structural-algebra
> anatomy (§1), the full landscape map including the Cv/T2/T3 falsification
> arcs and the published repeated-root toolbox (§3), a field-genericity
> derivation that re-scopes the odd-part track (§1.3, to-verify), the
> |G| ≥ 2w(w−1)+1 frame constraint for higher w (§6.T4), and a re-scoped,
> cheaper Z₄-frame track grounded in published atoms (§6.T3c).
>
> **Charter.** The d(gross)=12 proof consumes d(base)=6 (A4 Theorem A),
> whose engine is the CRT decomposition F₂[Z₆²] ≅ F₂[Z₂²] × F₄[Z₂²]⁴ plus
> difference-set combinatorics. That argument is already partially
> generalized (§2). This note plans the next push, optimizing ONE target:
> **maximize the number of BB codes for which a version of the argument
> certifies a distance** (floor, and where possible the exact value), at the
> analytic grade (A_HANDOFF §1) and — wherever cheap — the Lean grade.

---

## 1. Anatomy of the argument (the structural-algebra view)

### 1.1 The objects

For G abelian, R = F₂[G], the BB complex is the **Koszul complex** of the
pair (A,B): ∂₂z = (Bz, Az), ∂₁(u_L,u_R) = Au_L + Bu_R; d_Z = min weight
over nontrivial H₁ classes; k > 0 ⟺ (A,B) is not a regular sequence. R is
a **symmetric (Frobenius) algebra**, so annihilator duality is exact:
dim Ann(x) = |G| − dim xR, Ann(Ann(I)) = I. The X-side is the Z-side
conjugated by the inversion duality (A4 Lemma 2.1, generic BB).

### 1.2 CRT into local components; the three layers of Theorem A

CRT over the odd part: R ≅ ∏_j K_j[G₂], K_j = F_{2^{r_j}} (one factor per
Frobenius orbit of odd characters), G₂ = the 2-Sylow of G. Each factor is a
**local** Frobenius algebra (max ideal = augmentation ideal of the G₂-part;
semisimple ⟺ G₂ = 1); Â_j is a unit iff ε_{G₂}(Â_j) ≠ 0. Theorem A is
three interacting layers:

1. **Parity (PAR):** |A|, |B| odd ⟹ augmentation kills mixed-parity
   splits. Also equivalent to "Â₀, B̂₀ are units", which is what forces
   per-layer even weight in the one-sided floor. Everything downstream of
   PAR silently assumes odd weight.
2. **One-sided floor** (μ(Ann A), μ(Ann B) ≥ 2w): per-component support
   constraints (zero at unit components, inside the self-annihilating
   ideal (D̂_j) at radical components) + a weight-vs-Fourier-support
   dictionary on the odd part (d₃/d_H) + the layer-parity doubling. The
   d_H rows are classical-style **abelian-code minimum-weight lemmas**.
3. **Two-sided grid** (no light (u_L,u_R) cycle): difference-set
   combinatorics (D1 Sidon, D2 disjoint) + **quotient-hom projections**
   π_x, π_y (the ring homs R → F₂[Z_ℓ], F₂[Z_m]) + per-instance
   census/translate comparisons. Frame-agnostic; polynomial-sensitive.

The gross d=12 machinery ABOVE the floor (A4 §§8–14: Smith cosets, slot
frame, S(a,b) walk, locus rules R1–R5, 118 ρ-link kills) is a fourth layer
that consumes the F₄ geometry much more deeply (AG(2,F₄) collinearity,
hyperbolic quadruples, T-classifiers from ψ₂²=ψ₃ψ₄) — it is
**instance-generic in shape, per-instance in discharge**, and out of scope
for the class program except through the doubling layer (§6.T6).

### 1.3 What is field-generic vs. F₄-locked (new, TO VERIFY before use)

Re-deriving the engine over an arbitrary component field K (U = 1+s_x,
V = 1+s_y in K[Z₂²]):

- Every element of the augmentation ideal (U,V) squares to zero (char 2,
  U² = V² = 0) — square-zero radicals are automatic on **elementary**
  2-parts over ANY K. (Dies at Z₄: (1+s)² = 1+s² ≠ 0.)
- For D = aU + bV + cUV with (a,b) ≠ 0: the ideal (D) = span_K{D, UV} and
  Ann(D) = (D) (Frobenius dimension count) — **field-generic**.
- αD + βUV has coefficient vector (α(a+b)+β, αa+β, αb+β, β) over
  (1, s_x, s_y, s_xs_y); it has ≥ 3 nonzero coordinates for every
  (α,β) ≠ 0 **iff {0, a, b, a+b} are pairwise distinct ⟺ a ≠ 0, b ≠ 0,
  a ≠ b** — a per-instance checkable condition on the radical components,
  with no reference to |Kˣ| = 3.

**Consequence (if it survives verification):** the Z₂²-frame one-sided
floor "≥ 3 layers × even ⟹ μ ≥ 6" runs verbatim on Z₂²-frames with ANY
odd part — including heterogeneous F₈/F₆₄ components (Z₆×Z₁₄'s Z₃×Z₇). The
A5 checker's `engine_radical` predicate (currently narrated as "Z₂² only:
one zero + three pairwise-distinct nonzero values") is exactly the
distinctness condition and should be re-scoped as field-generic. What is
genuinely **F₄-locked**: everything that pins VALUES rather than supports —
co-point rigidity "up to scalar" (3 distinct nonzero values exhaust F₄ˣ),
the C-ratio consistency system, direction forcing, the D-pair/Prop-10
classification, and all of Part II. So: **floors port; classifications
don't** (without new work). First task of §6.T3a is to verify this
derivation (machine-sweep F₈/F₆₄ components, then a hand proof).

### 1.4 The frame-indexed engine family (what A5 already established)

| 2-part | engine | one-sided floor | instance proven |
|---|---|---|---|
| Z₂×Z₂ | co-point support dichotomy | "≥3 layers × even" ⟹ ≥ 6 | bb_72 (A4) |
| Z₂ | Ann(A) = (1+s)⊗I(W_A) | 2·d_H(W) | bb_108 (A5 E2, μ=12) |
| 1 (semisimple) | Ann(A) = I(V_A) exactly | d_H(V) | bb_90 (A5 E4, μ=10) |
| Z₄ or deeper | **none** (radical depth ≥ 4) | — | open |

Plus the **pullback dictionary**: radical/vanishing characters of order 3
factor through Z₃², so gross's d₃ dictionary transfers with a κ-fold
multiplier (bb_108: 6 = 2·3·d₃((3,F)); bb_90: 10 = 5·d₃((3,F))); the shared
object across the three instances is the orbit set {ψ₁,ψ₃,ψ₄}/{ψ₂,ψ₃,ψ₄},
NOT one floor formula (E7 correction). Theorem-B transfer is free: every
free-Z₂ cover of a floor-c instance inherits d ≥ c.

---

## 2. The generalization achieved so far (the determination)

1. **Three fully-analytic instance theorems**: d ≥ 6 for bb_72 (A4),
   bb_108 (A5 E2), bb_90 (A5 E4) — 3-for-3 across frame shapes, each
   radiating d ≥ 6 to its free-Z₂ covers.
2. **The class conjecture (C-iv′)/(C-v′)**: weight-3 (Z_ℓ×Z_m, A, B) with
   (a) floor-bearing frame (2-part ∈ {1, Z₂, Z₂²}, Ann ≠ 0, μ(Ann) ≥ 6),
   (b) D1 ∧ D2, (iii) mirrored coordinate projections ⟹ d ≥ 6.
   58/58 corpus members pass the full grid; (a)+(b) alone is REFUTED
   (Z₃×Z₅ d=4 family); the ONE open uniform step is the
   **multiplicity-profile residue lemma** (E6.4), whose first ingredient is
   the corrected even-period weight lemma (E7.3: |a·(1+y^δ)| ≤ 2 ⟺ 3-AP
   with difference δ OR (2δ ≡ 0 ∧ supp ⊇ a δ-orbit pair)). Current honest
   form: "(a)+(b)+(iii) ⟹ d ≥ 6 with a 2-step surveyable residue per
   member".
3. **Two-sided distillation + obstruction theory** (extensibility §6):
   D1 ∧ D2 ∧ D3; the char-2 Frobenius square A = B² is a genuine
   frame-independent obstruction that no clean predicate set robustly
   excludes (Z₈²/Z₁₃²/Z₁₅² spread-B squares pass D1∧D2∧D3); the stable gate
   is the explicit `is_frobenius_related` exclusion; sufficiency of
   D1∧D2∧D3∧¬Frob is open; floor = 2w exactly on 900+ spike-spread codes.
4. **Boundaries found with certificates**: no engine for Z₄+ 2-parts;
   class level stops at d ≥ 6 (= 2w); F_q value-rigidity fails off Z₃²
   (for the classification layers); literal-lift doubling of corpus codes
   to d > 12 closed negative (A14 §§13–16, deficit wall at 2d−2) — which
   makes base-floor generalization **the only open route to certified
   d > 12**.

---

## 3. The landscape map

### 3.1 Published lower-bound machinery and its walls

- **The ⌈d/c⌉ family** — KP-2013 Thm 5 → WLP Stmt 3 → LP Stmt 12
  (d ≥ ⌈min(d_A^⊥,d_B^⊥)/c⌉): sound, and **arithmetically capped** —
  c = 8 on gross ⟹ ≤ 2 forever (A2's verified wall). Nothing routed
  through a degeneracy divisor can certify the class values. LP remains
  the correct *baseline* to cite and beat.
- **HT/Roos/Camion apparent-distance/BBCS multivariate BCH**: evaluated in
  T2R3 — **trivial (= 1) on all five Bravyi codes**; these see only the
  semisimple quotient and BB's vanishing sets are BCH-hostile. Shelved for
  code-level bounds. (Scoped exception: such machinery may still prove
  individual **d_H dictionary rows** on small odd groups — a per-lemma
  tool, not a code-level bound; treat as optional.)
- **ES pure/non-pure split** (Eberhardt–Steffan Thm 2.3): the non-pure
  half of H₁ is invisible to ALL single-block arguments — the structural
  reason the one-sided half alone never determines d (extensibility §6:
  two-sided logical lighter ~47% of the time). Any class theorem MUST
  carry a two-sided half; there is no single-block shortcut.
- **Cover-transfer lane**: SRB (arXiv:2511.13560) Thms 4.6/4.7 = published
  odd-h transfer (h odd ∧ k_h = k ⟹ d ≤ d_h ≤ hd); GZ Prop 3.5 same at
  free-Γ-module generality; **even-h is SRB's open §7 conjecture and the
  repo's Theorems B–D are its first (saturating) h=2 instances**. Useful
  free rider: bb_90/bb_108 have odd-h bases, so weak analytic floors
  compose today (d(bb_108) ≥ 4 would follow from an analytic
  d([[36,8,4]]) ≥ 4) — our direct grid (≥ 6) already beats that route.
- **HGP/Tillich–Zémor**: BB = HGP exactly at c = 1 (separated supports);
  TZ Thm 15 then gives exact distance machinery. All class members of
  interest have c > 1 — the anchor [[18,8,2]] is the only chain member on
  a citation.
- **k-only machinery** (BKK mixed volumes arXiv:2503.04699; Liang
  twisted-tori/Gröbner; Postema–Kokkelmans existence): no distance
  content (verified Gap 2 — the "BKK ⟹ O(L) distance" gloss circulating
  on aggregator sites is hallucinated); useful only as fast k-gates in
  enumeration hunts.

### 3.2 The repeated-root / chain-ring toolbox (the Z₄ assets)

For 2-parts beyond elementary — components become chain-ring group
algebras K[Z₄], K[Z₄×Z₂] (gross ambient: Choosuwan
F₂[Z₁₂×Z₆] ≅ (F₂+uF₂)[Z₄] × ((F₄+uF₄)[Z₄])⁴) — the literature supplies
exact atoms the engine never needed on elementary frames:

- **CMS 1991 Thm 1**: exact d = P_t̂·d(C̄_t̂) for repeated-root cyclic
  codes — the univariate valuation prototype (blocker: univariateness).
- **Özadam–Özbudak Thm 3.6**: complete min-weight ladders for
  ⟨(x−1)^i⟩ ⊂ F₂[Z_{2^s}] — the per-axis atoms of F₂[Z₄], F₂[Z₂].
- **Monomial-like codes + MOOS 2015**: exact
  d(⟨(x−1)^a(y−1)^b⟩) = d_x(a)·d_y(b) in F₂[Z₄×Z₂]-type ambients, plus the
  multivariable weight-retaining theorem (5.4) — "the closest extant
  relative of the m(A) mechanism" (A1 Gap 1).
- **Berman/Charpin**: radical powers of F₂[Z₂ᵏ] are Reed–Muller codes with
  known minimum weights — underwrites elementary frames at any k (only
  reachable bivariately as Z₂², but relevant for multivariate/tricycle
  extensions).
- **Named open gaps** (A1 §4, still open): minimum weights of
  rad^t(F₂[Z₄×Z₂]) for general (non-monomial-like) ideals; any
  weight-distortion bound between Hamming weight and the chain-ring DFT
  coordinates. These two lemmas are exactly what a Z₄-frame ENGINE needs.

### 3.3 The internal falsification arcs (negative space — binding)

The Cv/T2/T3 program (pre-A3) tried to shortcut the whole problem with
closed-form invariant bounds. Every attempt except one narrow conditional
survivor is **unsound** (bound > true d), not merely loose:

- **Cv2** (d ≥ ⌈min_O min(w₁(A,O), w₁(B,O))/c⌉, w₁ = per-orbit radical-
  aware annihilator min weight): falsified on 85% of the corpus AND on
  bb_108 (bound 12 > d 10). All five alternative formulations falsified.
- **Cv3** (Cv2 gated to loosely-elementary G_odd ∧ c ≥ 3): survives its
  74-row domain, then falsified-as-stated out of domain (78 weight-4
  violations on Z₆×Z₆; a Z₁₂×Z₁₂ overshoot 18 > 12).
- **Cv4/R1+R4** (joint-vanishing-orbit restriction): falsified
  (Z₃×Z₁₅, bound 4 > d 2); the restriction's premise (min-weight kernel
  elements live on jointly-vanishing orbits) is simply false.
- **Feature screens** (T2): min(d_A^⊥, d_B^⊥) dominates tightness
  prediction (93.9% Gini); dimension-type invariants are invalid RHS;
  w_μ(A,O) survives as a *definition* (a genuine weight invariant), not
  as a bound ingredient.

**The lesson encoded in this arc**: divisor-style closed-form bounds with
radical-aware numerators are the WRONG SHAPE for BB distance — what
survived instead is the small-cycle case grid over actual cycles (Theorem
A) + cover transfer (Theorems B–D). The class program should generalize
the grid, not resurrect invariant formulas. Any new "invariant ⟹ floor"
proposal must first clear the Cv graveyard (§4).

### 3.4 The analytic bar (program doctrine, A1 Gap 3)

"Analytic" ≠ "kernel-checked": a bare `decide`/SAT over a weight ball is
certification, not explanation, and is excluded from grade-A claims by the
same rule that excluded SAT. The line: **structural reduction first, with
a small hand-surveyable residue** (censuses of 1–3 classes: fine; a raw
|G|³ table: not). This is why T1's certifier must emit projection-reduced
tables, and why the Lean layer (T2) is explicitly two-grade.

### 3.5 Freshness (post-A1-sweep items; A1's sweep is 2026-06-09)

- **arXiv:2605.14173, "Univariate Bicycle Quantum LDPC Codes: Explicit
  Logical Structure and Distance Bounds"** (May 2026) — post-dates the
  sweep; univariate/GB regime with BCH-type distance bounds via associated
  cyclic codes. MUST-FETCH: check against the semisimple-frame column
  (bb_90-style, where Ann = I(V) is exactly a classical abelian code) and
  against coprime-BB novelty wording.
- **Coprime BB codes** now journal-published (Quantum, 2026-02-23) — the
  known Wang–Mueller line (k analytic, d numeric); positioning unchanged.
- Standing rule: re-run the SRB-citing preemption search + a fresh BB-
  distance search immediately before any write-up (6+ citing papers as of
  June; the even-h window was still open then).

---

## 4. Falsified-claims ledger (do not re-propose)

1. (C-iv)/(C-v) from (a)+(b) without (iii) — FALSE (Z₃×Z₅ d=4 family).
2. D1∧D2 ⟹ two-sided floor ≥ 2w — FALSE (Frobenius square; wt-4 logical
   in [[98,12,4]] on Z₇²).
3. "D3 excludes Frobenius" — FALSE off small moduli (Z₈²/Z₁₃²/Z₁₅²).
4. Uniform 3-AP weight lemma — FALSE on even-period axes (needs the
   2δ ≡ 0 orbit-pair branch).
5. "Square-zero radical dies beyond 2-part Z₂" — wrong; correct constraint
   is elementary-abelian 2-part (and Z₃²-exactness only for the
   value-rigidity layers, per §1.3).
6. Distance towers by iterated doubling — falsified both styles (A8/A14).
7. **Cv2/Cv3/Cv4-style divisor bounds** (radical-aware numerator / c) —
   unsound (§3.3); do not re-derive variants without clearing the recorded
   counterexamples (bb_108; weight-4 Z₆²; Z₁₂×Z₁₂; Z₃×Z₁₅).
8. HT/Roos/apparent-distance as code-level BB bounds — trivial on the
   family (§3.1).
9. Phantom/apocryphal citations to purge on sight: "Hsieh–Le Gall 2020",
   "Otjens 2025" (real source: Postema–Kokkelmans 2502.17052), the
   Drensky–Lakatos rad^t shortcut (doctored quote), the EmergentMind
   "BKK distance" gloss.

---

## 5. Goal and metric

Breadth ledger (distinct codes at each certification grade):

| grade | meaning | today |
|---|---|---|
| **A** (analytic) | structural proof, surveyable residues (A_HANDOFF §1) | 3 (bb_72, bb_108, bb_90) + 55 conditional |
| **L** (Lean) | kernel/native artifact in-repo | 2 base floors (bb_72, pair72-base); 2 doubled codes (gross 12, pair72 8) |
| **S** (solver) | SAT/DRAT certificate | hundreds |

Targets: grade A = the whole (a)+(b)+(iii) class (58 known + future
members mechanically); grade L ≈ grade A via a generator; ≥ 1 member off
the Z₃²-odd-part family; ≥ 1 member at w = 5 (the d > 12 lane); each with
its free-Z₂ covers inheriting the floor.

---

## 6. The tracks (revised)

### T1 — Close the w=3 class theorem (unchanged goal, sharpened attack)

The one open uniform step is the **multiplicity-profile residue lemma**.
Deep-dive reframing: after the two mirrored quotient-hom projections
(§1.2 layer 3) narrow a (2,2)/(1,3) candidate to the 3-AP branch, the kill
compares coordinate-multiplicity profiles of A·{0,δ_L} against
B-translates — a statement about **fibre multiplicities of a Sidon-set
translate along the two quotients**, i.e. a two-projection uncertainty
lemma, with the corrected even-period weight lemma (E7.3) as ingredient 1.

1. Falsify-first on fresh mirror frames (Z₉×Z₃, Z₂₁×Z₃, Z₁₅×Z₅ mirrors,
   plus even-period y-axes where the E7.3 second branch is live), then
   attempt the presentation-free lemma. Time-box: 2 sessions.
2. Fallback (fully acceptable, per §3.4): the **recipe-certifier**
   (`a5_recipe_certify.py`, extending `a5_instance_hypotheses.py` +
   `twosided_recipe_status.py`) emitting per-member ordered obligations
   with surveyable projection-reduced tables inline — converting all 55
   conditional members to grade A at ~zero marginal cost.
3. Scope the 19 non-mirror Z₆×Z₆ members explicitly (their d ≥ 6 is true
   for reasons outside this mechanism — E3.5): one session to identify the
   second mechanism or record them out-of-scope.

Deliverable: theorem or certifier + A5 Entry 8; extensibility §6 upgraded.

### T2 — Parametric Lean base-floor layer (breadth multiplier; two-grade)

Mirror `BBCover.lean`'s bundle pattern: `BBSmallCycleData` over
(ℓ, m, A, B) with decidable obligations — parity facts, D1/D2 (≤|G|²
decides), frame tag, annihilator basis + μ ≥ 6 via the `kerBasis_spans`
2^dim-combo pattern, census kills — and a generic
`chain_distance_ge_6_of_data`, composing with the existing Theorem-B/
BBDoubling layer. Budget rules from Tier-3 findings: kernel decide ≤ ~512
lookups; the raw (v)-table (~4.7M on Z₆²) is native_decide-only
(engineering grade), swapped for the T1 lemma at analytic grade — design
the bundle so both discharge routes fit one field. Generator
`gen_base_floor_lean.py` (never transcribe); pilots bb_108/bb_90, then the
24 d=6 members with weight-6 annihilator witnesses (`A·z* = 0` one-
convolution decides) for `IsLeast` packaging. Effort 1–2 weeks; no
research risk.

### T3a — Field-generic engine + heterogeneous odd parts (pilot Z₆×Z₁₄)

1. **Verify §1.3** (the distinctness-condition derivation): machine-sweep
   radical components over F₈/F₆₄ (Z₆×Z₁₄'s components), then the short
   hand proof. If confirmed, re-scope the checker's `engine_radical` and
   the A5 §3.2 table: hypothesis (a) covers Z₂²-frames with ANY odd part.
2. **d_H dictionary rows for Z₃×Z₇** (and Z₂₁ pullbacks) as hand-provable
   lemmas (A3 Entry-10 style; classical abelian-code projection arguments
   optional per §3.1). Heterogeneous floors (μ_A = 12, μ_B = 6 there) are
   fine — the grid consumes the min.
3. Run the Theorem-A‴ grid on Z₆×Z₁₄ [[168,12,6]] — the one genuinely-new
   corpus base, in-frame (2-part Z₂²), covers already SAT-known to double
   to [[336,12,12]] both axes. Success = first analytic member off the Z₃²
   odd-part family + a concrete new engine-target lineage.

### T3c — Z₄-bearing frames: the chain-ring engine (upgraded from moonshot)

Re-scoped around §3.2's published atoms — cheaper than v1 assumed, and
with the Cv graveyard as guardrails (the target is a small-cycle GRID with
a chain-ring one-sided engine, NOT a closed-form divisor bound):

1. **Pilot on small corpus frames with 2-part Z₄** (Z₃×Z₄, Z₄×Z₆ rows
   have exact d in the corpus): compute one-sided floors from
   Özadam–Özbudak atoms + parity per component (Ann of a chain-ring
   element c·(x−1)^e·unit is ⟨(x−1)^{4−e}⟩-shaped; min weights known);
   validate against SAT; find where the naive per-component floor is
   loose (the Cv3 Z₁₂×Z₁₂ overshoot says value-linkage across components
   matters — exactly the ρ-link phenomenon).
2. Derive the two missing lemmas in-house (both named-open in A1 §4):
   rad^t(F₂[Z₄×Z₂]) minimum weights for the ideals that actually occur
   (calibrate against the MOOS monomial-like formula), and the
   weight-vs-chain-ring-coordinate distortion bound.
3. Escalate to one full instance theorem on the best-behaved Z₄-frame
   corpus code; only then assess bb_288's base (Z₁₂×Z₁₂ ≅ Z₄²×Z₃²) and
   the direct gross-as-base grid (A4 §7 flagged the depth-4 blow-up).
   Payoff: the tour-de-gross ∀r column (d = 6(2r+b−1)) runs entirely
   through Z₄+ frames — this is the strategic lane, now with a graded
   on-ramp. Time-box the pilot: 2 sessions to a floors-vs-SAT table.

### T4 — Raise w (the deficit-wall bypass; strategic breadth)

A14 closed literal-lift d > 12 from the w=3 corpus; the class argument
certifies 2w, and **w is the free parameter**. New structural constraint
from the dive: D1∧D2 forces |dA| + |dB| = 2·2·C(w,2) ≤ |G| − 1, i.e.
**|G| ≥ 2w(w−1) + 1** — w = 4 needs |G| ≥ 25, w = 5 needs |G| ≥ 41
(n = 2|G| ≥ 82). So w = 5 class codes are necessarily mid-size; that is
where certified-d=10 bases (→ certified-d=20 doubles) would live.

1. **w = 5 first, w = 4 deprioritized**: even w kills PAR (ε(A) = 0 makes
   Â₀ radical — the parity spine AND the unit-component step both change
   qualitatively; separate study, likely weaker floors — consistent with
   the T3-A weight-4 d=4 cluster).
2. Sweep-before-proving: extend the twosided sweeps to w = 5 on
   |G| ≥ 41 floor-bearing frames; enumerate the obstruction family
   explicitly (A = B², B⁴, shared factors) at w = 5; measure whether
   floor = 10 holds on D1∧D2∧(iii)∧¬Frob members. Exact-SAT + k > 0 gate
   every structural hit (cover-cascade lesson).
3. Fresh enumeration with a14 columns (the queued A14 residue) doubles as
   the w = 5 member hunt: target d = 10 bases whose covers pass the
   safe-floor screens.
4. Write the w-generic census schema ((1,t) ⟹ t ≥ w under D1∧D2 is
   already parametric; the triangle census becomes a weight-w polygon
   census), instantiate at w = 5 on the best candidate.

### T5 — Past 2w per instance (depth pilot: bb_108 → 8 → 10)

One-sided splits are dead to k ≤ 11 (μ = 12/10); missing are the even-
weight two-sided splits at weights 6 and 8 — seven splits at weight 6,
nine at weight 8 (odd totals die by PAR). Each dies by the same three
mechanisms; censuses grow. Pilot bb_108 to d ≥ 8, stop at the first split
whose census exceeds ~10 classes and record the wall. If tractable,
promote "grid depth" as an optional certifier parameter (certifying exact
d for the d ∈ {8,10} class members). The published odd-h route (SRB 4.7)
caps at ≥ 4 here — our grid already beats it; no shortcut exists (§3.3).

### T6 — Routing into the doubling layer (standing)

Every new base floor feeds: Theorem-B transfer (free); the A14 screen
battery + A11 C-safe criterion (which covers double); BBCover/BBDoubling
for the ×2 Lean assembly — whose per-code cost is the engine
re-instantiation (Prop-10 + MIm analogues). hit3-y stays the queued pilot
for "second engine instantiation on the same frame"; T3a's Z₆×Z₁₄ is the
pilot for "off-frame". Both after T1/T2 (depth-per-code, not breadth).

---

## 7. Prioritization

| rank | track | breadth payoff | effort | risk |
|---|---|---|---|---|
| 1 | T1 residue lemma / certifier | +55 codes grade A, mechanical forever | days–2 wks | low (certifier fallback) |
| 2 | T2 Lean layer + generator | grade L ≈ grade A | 1–2 wks | ~zero |
| 3 | T4.2 w=5 sweep (cheap gate) | opens the d>12 lane | days | low |
| 4 | T3a field-generic + Z₆×Z₁₄ | first off-Z₃² member; widens (a) | 1–2 wks | medium |
| 5 | T3c Z₄ pilot (floors-vs-SAT) | on-ramp to ∀r family | 2 sessions | medium |
| 6 | T5 bb_108 depth | exactness for d=10 members | 1–2 wks | census blow-up |

Sequencing: T1 and T2.1 start in parallel (bundle design doesn't wait on
the residue lemma). T4.2's sweep result decides whether slot 3 continues
into full T4 or defers to T3a. T3c's pilot is deliberately cheap — its
result (how loose the atom-based floors are) is itself the go/no-go for
the ∀r lane. First execution session: T1.1's counterexample hunt + the
§1.3 verification sweep (both cheap, both falsify-first).

---

## 8. Standing discipline (inherited, binding)

- **A_HANDOFF §1** + §3.4 doctrine: machine checks are confirmation;
  grade-A = structural reduction + surveyable residue; label every number.
- **Falsify before proving**; enumerate obstructions explicitly
  (`is_frobenius_related` mandatory); clear the §4 ledger before proposing
  any invariant-shaped bound.
- **Presentation pinning**: (iii)/coordinate-disjointness are not
  Aut-invariant; orbit-sweep before declaring a code out.
- **k > 0 + exact SAT validation** of every structural hit.
- **Re-derive agent claims** (E7 lesson; both directions).
- **Lean budgets**: kernel decide ≤ ~512 lookups; tuple-quantified
  native_decide validated to ~3.7·10⁵; generate data modules, never
  transcribe.
- **Claim discipline**: contribution axes are mechanism / integration /
  generality; never "first verified value"; carve out SRB odd-h and
  Wang–Pryadko in novelty wording; purge §4.9 phantoms; fetch
  arXiv:2605.14173 and re-run preemption before any write-up.
