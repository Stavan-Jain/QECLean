# A2 — Phase-2 scouting synthesis (gross-directed track ranking)

Date: 2026-06-10. Consumes the substrate agent's structural report and
the three track scouts (1.1 Smith h=2 cover transfer; 1.2 bivariate
CMS/radical + LP; 1.3 KP-2013 even-symmetry decomposition), against
`A1_synthesis.md` §3 and `A0_baseline.md`. All scout optimism is
discounted per the program's hard lessons (a bound held on 400+ codes
then died on one hostile example; citation drift). Ranking is by
*expected progress toward the gross goals per unit effort*, not
prestige.

Goal priority (fixed): (1) analytic d(gross)=12; (2) analytic bound for
a class of BB codes; (3) ANY nontrivial analytic bound on gross beyond
the published LP floor d ≥ 2. A beats-the-floor gross bound (goal 3)
outranks a class result (goal 2).

Independent re-verification done for this note (arithmetic + lab probes,
all discovery-only): LP wall `ceil(12/8)=2`; Smith projection split
rank 6 / kernel 6 with all weight-12 minima in the kernel
(`scratch/a1_smith_projection_probe.py`); safe-branch tightness — an
explicit weight-6 cover X-logical projecting to a nontrivial weight-6
base class (`scratch/a1_smith_safe6_check.py`); ES purity
`dim(H_h+H_v)=6` on gross (`scripts/a1_es_purity_check.py`). These pin
the *shape* of the obstruction; they are NOT load-bearing toward any
bound (same exclusion as SAT).

---

## 1. Gross structural picture (condensed from substrate)

Gross's 12-dim logical space H = ker H_X / im H_Z^T splits, via the
Eberhardt–Steffan Theorem 2.3 fundamental exact sequence, into:

- a **6-dim PURE part** (= im β = H_h + H_v): logicals representable on
  a single circulant block (supported in ker M_A or ker M_B). The naive
  pure-generator count T1+T2 = 12 over-counts; α injects a 6-dim
  ann(cd)/M of horizontal/vertical *relations*, so the honest pure
  dimension is **6, not 12** (β-image = 6 = independently-computed
  dim(H_h+H_v), re-confirmed here).
- a **6-dim NON-PURE part** (= coker β = ((c)∩(d))/(cd), term T3):
  logicals that require *both* blocks simultaneously — invisible to any
  single-block / pure weight argument.

The four ES terms are all equal: (T1,T2,T3,T4) = (6,6,6,6). T1=T2 is
forced by gross's x↔y automorphism; the full 6,6,6,6 regularity is a
**single-instance observation** and is exactly the trap shape the
program has died on before — do NOT conjecture "all four ES terms
equal" or "= k/2" without corpus + adversarial testing.

Algebra side: R = F₂[Z₁₂×Z₆] is non-semisimple (|G|=72=2³·3²;
2-Sylow Z₄×Z₂ non-cyclic ⇒ neither PIGA nor PIR). Loewy length 5,
layer dims [8,7,5,3,1]; 5 Frobenius orbits on Ĝ_odd (sizes 1,2,2,2,2),
3 vanishing of depth 2 for each of A,B. Weight-aware radical-filtration
witnesses on vanishing orbits sit at w_μ ≥ 36 — far above d=12 — so
single-block witnesses are heavy; any radical bound must combine across
orbits.

Two consequences that drive the ranking:

- **The pure/non-pure split is a hard ceiling on single-block
  arguments.** A single-block-dominance argument (Track A's hope,
  motivated by d_A^⊥=d_B^⊥=12=d) can at most control the 6-dim pure
  half; the other 6 dims are non-pure and need a genuinely two-block
  (homological) treatment. "All logicals are single-block" is dead on
  gross — confirmed quantitatively, not just by ES Table 1's X-mark.
- **The non-pure 6-dim sector is the same object across Tracks 1.1 and
  1.3.** It is (claimed) the Smith dangerous branch ker(pr_*) = im(tr_*)
  AND the KP anti-symmetric sector coker(tr_*) = im(Δ=∩ω). Verified on
  gross only and by each scout's own probe — see §2 caveat. If true,
  1.1 and 1.3 attack one obstruction.

Floor to beat: gross has published analytic d ≥ 2 (LP Statement 12,
c=8, ceil(12/8)=2). "Progress on gross" = beating 2.

---

## 2. Per-track crux table

| track | objective | crux | quick-probe outcome | tractability | value-if-solved (beats d≥2 on gross?) |
|---|---|---|---|---|---|
| **1.1 Smith h=2 cover transfer** | prove `d_cover ≥ d_base` (and ideally the factor-2 `≥ 2·d_base`) for the free-Z₂ 2-cover, propagate up gross's even-h chain | weight LOWER bound on representatives of the **6-dim dangerous sector** ker(pr_*)=im(tr_*) through the Smith connecting map Δ=∩ω — genuinely new math, zero QEC precedent | rank(pr_*)=6, kernel 6; ALL weight-12 minima sit in the dangerous sector; safe branch provably TIGHT at d_base=6 (explicit wt-6 cover logical → nontrivial wt-6 base class). Chain maps p, τ, p∘τ=0 are structural facts that transfer. | needs-genuinely-new-math; months; high risk. Two ingredients (p,τ chain maps; Smith exactness) are assembly. The crux is the whole ballgame. | **literal transfer**: d(gross) ≥ 2 (no gain) / ≥ 4 (if structural d([[36,8,4]])≥4) / ≥ 6 (needs analytic [[72,12,6]], which doesn't exist). **YES beats floor via the ≥4 route.** Factor-2 dangerous-sector gain ⇒ d(gross) ≥ 12 = goal 1. |
| **1.2 bivariate CMS/radical + LP** | `d_A^⊥ ≥ m(A)·d̄_A^⊥` on gross's own algebra, then compose with LP Statement 12 | **ARITHMETIC WALL**: LP numerator is d_A^⊥; true value 12; ceil(12/8)=2; need numerator > 16 to reach 3; a lower bound cannot exceed the true 12. c=8 is untouched by the radical mechanism. | LP wall re-confirmed (ceil(12/8)=2). m(A) is NOT a clean Loewy scalar — d_A^⊥/d̄ scatters {1,2,3,4,6} on gross's own group, hits 1. Salvage: `d_A^⊥ = min_O d_O^⊥` held 0 violations / 1330 hostile trials (but coarse projection, classic trap shape). | stated objective **mostly-infeasible** (hard arithmetic cap, not a difficulty estimate). Salvage (classical `d_A^⊥=12` re-derivation) weeks–months. | **NO** — capped at exactly 2 on gross. Salvage is goal-2 classical structure only. A gross bound >2 needs a non-LP per-orbit→quantum argument that bleeds into Track B's homological territory (not standalone). |
| **1.3 KP-2013 even-symmetry** | translate `u = (1+σ)w + γᵀG_Z` decomposition to (gross,[[72,12,6]]) as a second F₂ route to the same `d_cover ≥ d_base` | weight control of the **anti-symmetric (non-pure) sector**: 6 classes σ fixes only at homology level, (1+σ)r ∈ rowspan H_Z, no σ-fixed chain rep. KP Thm 8 gets exactness only BECAUSE its hypothesis k^(1+x)=k kills this sector — and gross violates it by a 6-dim gap. | σ verified free involution + code automorphism. Symmetric decomposition captures exactly 6/12 classes (= ES-pure); σ-fixed wt-12 reps restrict to nontrivial base wt-6 logicals (doubling). Anti sector nonempty at EVERY chain step (72→36: 11/12 anti). | needs-genuinely-new-math; NOT easier than 1.1. Symmetric half is 1–2 weeks of assembly but discharges the 6 dims that were never the obstruction. Anti half = the identical Δ=∩ω wall as 1.1. | symmetric-half "wt ≥ 12" is **vacuous for distance** (d = min over all 12 logicals; anti 6 uncontrolled) ⇒ **NO on its own beyond d≥2**. Full technique = same value as 1.1. Realizable in isolation: a clean lemma controlling the pure sector. |

**Caveat on the shared-sector identity.** All three scouts assert the
6-dim non-pure / dangerous / anti-symmetric sectors *coincide* on gross.
The substrate's ES split (6+6) and the Smith rank-6/kernel-6 split are
independently re-verified here. The three-way *identity* (Smith
ker(pr_*) = KP anti = ES non-pure) is verified on **gross only** and by
each scout's own (now-removed) script; an attempted independent
reconstruction of the KP σ-decomposition rank gap here did not cleanly
reproduce the "6" (a quotient-convention mismatch in the ad-hoc rebuild,
not a refutation). Treat the identity as plausible-but-single-instance.
Its main *ranking consequence is conservative*: it makes 1.3 look like a
reformulation of 1.1's crux rather than an independent route, which is
the cautious read anyway.

---

## 3. Ranking of gross-directed tracks (expected progress per unit effort)

**Rank 1 — Track 1.1 (Smith h=2 cover transfer).** The only track that
(a) touches gross's quantum distance directly and (b) has a path to
*both* goal 3 (beat the floor) and goal 1 (=12). Its crux is **sharply
localized**: a single weight-lower-bound lemma on a concretely
identified 6-dim sector, through a concretely named map Δ=∩ω. The
program's own preference rule ("prefer tracks whose crux is sharply
localized over 'needs new math, unclear where'") points squarely here.
The two-branch skeleton is de-risked: chain maps p, τ and p∘τ=0 are
structural facts (re-verified), and the safe branch is *provably*
exhausted at d_base — so there is no hidden easy win being overlooked
and no ambiguity about where the work is.

**Rank 2 — Track 1.3 (KP even-symmetry).** Demoted to a *reformulation
of 1.1*, not an independent track. Its probe is honest and decisive
*against itself*: the symmetric half it can prove is vacuous for code
distance, and the anti half is bit-for-bit 1.1's Δ=∩ω wall. Its genuine
value is as an alternative F₂-linear-algebra *vocabulary* for the same
crux — worth keeping in 1.1's toolbox (the KP γᵀG_Z degeneracy
accounting may make the dangerous-sector bound easier to manipulate),
but not worth a parallel serial push. Running it in parallel with 1.1
risks duplicated effort on one obstruction.

**Rank 3 — Track 1.2 (CMS/radical + LP).** Lowest expected progress on
the *gross* goals despite being the most "gross-native." Its stated
objective is dead by a verified arithmetic wall, not a difficulty
estimate: ceil(12/8)=2 regardless of any achievable numerator. Its only
surviving deliverable (`d_A^⊥ = min_O d_O^⊥`, re-deriving the classical
12 analytically) is a goal-2 classical-coding result that *still yields
only 2 on gross via LP*. The substrate independently kills the broader
hope: even a perfect single-block argument controls only the 6-dim pure
half, and the pure witnesses are heavy (w_μ ≥ 36). A gross bound > 2
from this machinery requires a non-LP per-orbit→quantum argument that
merges into Track B anyway. Keep 1.2 alive ONLY as a parked goal-2
banking move with a low time budget, not as a gross-beating route.

**Co-leading?** No. 1.1 is a clear single leader. 1.3 is its
reformulation (tiebreak moot — fold it in). 1.2 is third on gross
despite first on "directness of contact with gross's algebra," because
directness is worthless behind an arithmetic cap.

---

## 4. Recommendation: first serial deep-push

**Push Track 1.1 (Smith h=2 cover transfer) first, serially.** Reasons:
it is the *only* track with a route to goal 1 and a credible route to
goal 3; its crux is a *single, sharply localized* lemma (not "new math,
unclear where"); the surrounding skeleton is de-risked (chain maps and
the safe-branch ceiling are settled); and 1.3's honest self-assessment
shows it collapses into 1.1's crux, so 1.1 is where the obstruction
actually lives. 1.2 is behind an arithmetic wall and cannot, as scoped,
move gross past 2.

**First work-block (serial spine):**
1. Make Δ=∩ω explicit on the [[72,12,6]] base chain complex: ω the
   x-direction cut 1-cocycle; compute Δ: H₂(base)→H₁(base) (H₂/syzygy
   space ~12-dim) and identify im(Δ)=ker(tr_*) concretely.
2. For a base cycle c with [c]∈im(Δ), the cover class tr_*[c] has rep
   τ(c) of weight 2|c|; the target lemma is **fibre-disjointness**: the
   free Z₂ action makes the two fibre sheets weight-disjoint up to the
   cut, so |τ(c)+∂s| ≥ 2·minwt[c] for any cover stabilizer ∂s. Formalize
   this as the new structural lemma — it is the factor-2 gain.
3. Borrow KP's γᵀG_Z degeneracy accounting (Track 1.3 vocabulary) and
   the generalized van Lint / Plotkin h=2 mechanism (Chen–Xie–Ding
   Thm 2.1) as candidate structural templates for the fibre-disjointness
   argument — these are the closest analytic precedents for an exact
   char-2 cover-distance split.

**Written kill criterion (parks 1.1, triggers fallback):** After making
Δ=∩ω explicit, if NO structural mechanism can be exhibited forcing
dangerous-sector reps to weight ≥ 2·d_base — concretely, if cover
stabilizers can be shown to *mix the two fibre sheets* so that
fibre-disjointness provably fails — then the Smith argument yields only
the safe-branch `d_cover ≥ d_base`, which the probe shows is tight at 6.
That leaves d(gross) ≥ 6 *contingent on an analytic d([[72,12,6]]) that
does not exist*, and realistically only ≥ 4 (via a structural
d([[36,8,4]])≥4) or ≥ 2 (current floor). A second, earlier kill: if
making Δ explicit reveals it is analytically unwieldy on the BB chain
complex (finite-dimensional but no human-surveyable structure), park
before sinking months into computation.

**Fallback order after a 1.1 kill:**
1. **Tier-2 goal-2 banking — structural d([[36,8,4]]) ≥ 4.** Cheapest
   floor-relevant deliverable. If 1.1's *literal* transfer survives
   (safe branch ≥ d_base) even when the factor-2 lemma dies, this base
   bound composes UP gross's even-h chain to d(gross) ≥ 4 — beating the
   floor (goal 3). It is also a standalone goal-2 result via the odd-h
   SRB transfer to bb_108. MUST be structural ("no weight-≤3 logical on
   the balanced-product logical space"), NOT a `decide`/ILP enumeration
   (fails the analytic bar by the same logic as SAT). Test scalability
   to gross's 144-qubit space before investing.
2. **Track 1.2 salvage (`d_A^⊥ = min_O d_O^⊥`).** Bank the classical
   analytic re-derivation of d_A^⊥=12 as a goal-2 result. Does NOT beat
   the gross floor; pursue only as low-cost consolation.
3. **Accept the negative result** if all structural routes to the
   dangerous sector are exhausted: the program's honest deliverable
   becomes "the analytic obstruction to gross d>2 is precisely the
   weight-control of the 6-dim Smith/ES non-pure sector through Δ=∩ω,
   for which no QEC machinery exists" — itself a first-class output in
   this program's tradition.

---

## 5. Division of labor during the serial push

**Serial proving spine (one focused agent, no parallelism on the
crux):**
- Make Δ=∩ω explicit on [[72,12,6]].
- Prove (or refute) the fibre-disjointness lemma `|τ(c)+∂s| ≥ 2·minwt[c]`
  on the dangerous sector — this is the single load-bearing step and
  must not be split.
- State everything at free-Γ-module generality (GZ Remark 3.6) so a
  success generalizes to the even-h BB cover class (goal 2 spillover).

**ultracode falsification sweeps / skeptic panels (parallel, never on
the spine):**
- **Sector-identity falsification.** The "Smith dangerous = KP anti =
  ES non-pure" three-way identity is verified on gross only. Sweep the
  corpus and adversarial instances for a code where these three 6-dim
  sectors do NOT coincide. A counterexample would not kill 1.1 on gross
  but would forbid stating the lemma at family generality — catch it
  before the write-up does.
- **ES-regularity trap.** Test whether (T1,T2,T3,T4)=(6,6,6,6) and the
  "pure = k/2" split are gross-specific coincidences (forced by x↔y
  symmetry + k=12) or hold across the corpus. The program's 400+-code
  death makes this mandatory before any term-equality is leaned on.
- **Fibre-disjointness skeptic panel.** As soon as the spine drafts the
  fibre-disjointness lemma, run an adversarial panel hunting a cover
  stabilizer that mixes the two fibre sheets and drops a dangerous rep
  below 2·d_base — this is exactly the kill criterion, and finding it
  computationally (even though computation is not load-bearing) saves
  months of doomed proving.
- **Scoop / preemption watch.** SRB is v1 with ≥6 citing papers; re-run
  the even-h-transfer preemption search before any write-up (the crux is
  a named open conjecture; someone else could land it).
- **Convention/orientation audit.** Pin logZ = ker H_X / im H_Z^T and
  which boundary "cycle" refers to (τ-lifts are H_X-cycles) before any
  lemma is formalized — a careless X/Z swap produces a vacuously
  true/false statement. The quotient-convention mismatch in this note's
  own ad-hoc KP rebuild (§2 caveat) is a live example of how easily this
  slips.

All ultracode computation is discovery/validation only and can never be
load-bearing in the final proof, exactly as the SAT distances and ES
term counts are not.
