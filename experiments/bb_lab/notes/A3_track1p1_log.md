# A3 — Track 1.1 deep-push running log (Smith h=2 cover transfer)

Serial proving log for the gross-directed Track 1.1, per `A2_scouting.md` §4.
Moonshot conventions: failures and dead-ends are first-class; every computed
number is discovery/validation only and can NEVER be load-bearing in a final
analytic proof (same exclusion as SAT). Newest entry at the bottom.

Goal: an analytic lower bound on d(gross) beyond the published floor d ≥ 2.
The target theorem is the h=2 free-Z₂ cover transfer, whose useful form on gross
is the **factor-2** statement d_cover ≥ 2·d_base on the dangerous sector.

---

## Entry 0 (2026-06-10) — framework + key reduction; one scout bug caught

### Setup (conventions pinned)

Base B = [[72,12,6]], G_b = Z₆×Z₆, A=x³+y+y², B=y³+x+x²; cover = gross,
G_c = Z₁₂×Z₆, same polynomials. The cover is the **x-direction double cover**
(ℓ: 6→12, m: 6 fixed); deck group Γ = ⟨σ⟩ ≅ Z₂, where σ is the shift x ↦ x+6
on Z₁₂. F₂[G_c] is a free rank-2 F₂[G_b]-module; every base cell has exactly
two lifts (x and x+6), so a cover chain is a pair of "sheets" v = (v₀, v₁) of
base chains, with σ(v₀,v₁) = (v₁,v₀).

Three maps (chain level, C₁):
- projection **p**(v₀,v₁) = v₀+v₁ (sum the sheets);
- lift/transfer **τ**(u) = (u,u) (copy to both sheets), |τ(u)| = 2|u|;
- p∘τ = 1+σ ↦ 2 = **0** over F₂ (SRB Lemma 4.4) — the obstruction that kills
  the naive transfer.

On homology, pr_* : H₁(cover) → H₁(base) and tr_* : H₁(base) → H₁(cover).
Smith exactness for the free involution gives the connecting map
Δ = ∩ω : H₂(base) → H₁(base) (ω = the x-direction cut 1-cocycle) with
**im(tr_*) = ker(pr_*)** and **ker(tr_*) = im(Δ)**.

### Trustworthy structural facts (`scripts/a3_dangerous_structure.py`)

Derived from F₂ linear algebra + the established d_gross = 12 certificate only
— NOT from any hand-rolled CNF:

- **F1.** pr_* : F₂¹² → F₂¹² has **rank 6, kernel 6**. The 6-dim ker(pr_*) is
  the "dangerous sector."
- **F2.** Each of the 6 dangerous logical reps projects to the **zero chain**
  p(v)=0 (not merely a trivial class). Since p sums the two sheets, p(v)=0 ⟺
  v₀=v₁ ⟺ v = τ(u) for the common sheet u.
- **F3.** That u is a **nontrivial base logical** (u ∈ ker H_X^base,
  u ∉ rowspan H_Z^base) of weight exactly **6 = d_base**; so the dangerous rep
  has weight 2|u| = **12 = 2·d_base**.
- **F4.** Dangerous-sector minimum weight = **12**, by trusted reasoning: the
  reps achieve 12, and nothing is below d_gross = 12. (No SAT needed.)
- **F5.** Safe-sector minimum weight ≥ 12, forced by d_gross = 12.

### The decisive structural finding

**The entire distance of gross lives in the dangerous sector.**
- *Safe sector* (pr_* ≠ 0): the projection p gives the bound |v| ≥ |p(v)| ≥
  d_base = 6 *for free, analytically* (p never increases weight; p(v) is a
  nontrivial base logical). So the published Smith "safe branch" already
  proves d ≥ 6 here — but that's all it gives, and the truth is ≥ 12 anyway.
- *Dangerous sector* (pr_* = 0): p(v) = 0, so the safe branch gives
  |v| ≥ |p(v)| = 0 — **nothing**. Yet this is exactly where the minimum-weight
  (weight-12) logicals live (F2–F4).

So the gap between "analytically free" (6 on safe, **0** on dangerous) and the
truth (12, 12) is worst — total — on the dangerous sector. **Proving any gross
bound > the d ≥ 6 safe-branch floor reduces entirely to lower-bounding the
weight of the dangerous sector**, and the natural target is the factor-2 value
2·d_base = 12 it actually attains.

### Bug caught (skeptic discipline)

The scout script `scripts/a1_smith_sector_sat.py` reports **safe-sector min = 6**.
That is **impossible**: d_gross = 12 (SAT+DRAT certificate in `certificates/`),
so no logical of weight < 12 exists in either sector. It is an encoding error
in the hand-rolled CNF (the "nontrivial ∧ safe" constraint admits something it
shouldn't). Flagged, not relied upon; all structural facts above were
re-derived without it. Lesson logged: treat every scout CNF's sector numbers as
suspect until cross-checked against d=12 + linear algebra.

### The lemma to prove (precise), and the attack

**Fibre-disjointness lemma.** Let u be a nontrivial base logical
([u] ∉ im Δ) and let t be any cover Z-stabilizer (t ∈ rowspan H_Z^cover). Then

    |τ(u) + t| ≥ 2·d_base.

In sheet coordinates t = (t₀,t₁), this is

    |u + t₀| + |u + t₁| ≥ 2·d_base.                          (★)

Cover stabilizers obey the cut-coupling: writing the base Z-boundary map as
∂* = ∂*_nc + ∂*_c (non-seam-crossing + seam-crossing parts), a cover stabilizer
from cover 2-chain w=(w₀,w₁) is
    t₀ = ∂*_nc w₀ + ∂*_c w₁,   t₁ = ∂*_c w₀ + ∂*_nc w₁.
Hence t₀ + t₁ = ∂*_base(w₀+w₁) is a **base Z-boundary**, so u+t₀ and u+t₁ lie in
the **same base Z-logical coset** as each other, and (since u is a logical and
t₀+t₁ is a stabilizer) that coset is u's nontrivial class.

**Plotkin/van Lint strategy (the intended proof of ★).** If u+t₀ and u+t₁ were
each guaranteed to be a *nontrivial base logical*, each would have weight
≥ d_base and (★) would follow immediately (2·d_base). The whole difficulty is
that the cut-coupling lets t₀ (individually) fail to be a base X-cycle, so
u+t₀ need not be a base logical on its own — the seam can "leak" weight between
sheets. Controlling that leakage is precisely the content of Δ = ∩ω: the
seam-crossing parts ∂*_c are the cap-product-with-ω terms. The classical char-2
precedent for exactly this split is the generalized van Lint / Chen–Xie–Ding
Thm 2.1 Plotkin decomposition along a free Z₂-action (A1 lane L2), and KP-2013
§IV.E's u = (1+σ)w + γᵀG_Z accounting is the algebraic bookkeeping for the
seam terms.

### Status

- Framework + reduction: **done and computationally grounded** (F1–F5).
- Fibre-disjointness lemma (★): **stated precisely, not yet attempted.** This is
  the single load-bearing step (Task #5) and the next session's work.

### Next concrete sub-steps

1. Make ∂*_nc / ∂*_c (equivalently ω and Δ) **explicit** on the base BB complex:
   identify which monomials of A, B cross the x-seam (exponent wrap mod 6 ≠ the
   lifted exponent), and write Δ: H₂(base)→H₁(base) as a matrix; confirm
   im(Δ) is the 6-dim ker(tr_*) (cross-check against F1's rank count).
2. Attempt (★) via the sheet/Plotkin split; the crux is bounding the weight lost
   to seam leakage when u+t₀ is not individually a base cycle.
3. Before trusting any drafted argument: ultracode skeptic sweep hunting a cover
   stabilizer t that mixes sheets to drop |τ(u)+t| below 12 (the kill criterion).

---

## Entry 1 (2026-06-10) — §1 complete (Δ explicit); §2 reduced; a promising-but-unverified simplification

### §1 done: the sheet/cut framework and Δ are explicit and verified

- **Sheet/cut structure of the cover boundary, verified exactly**
  (`scripts/a3_cut_decomposition.py`). Permuting the lab-built cover H_X and H_Z
  into (sheet, base) order gives precisely the block form
  `[[d_nc, d_c],[d_c, d_nc]]` for *both* boundaries, with d_nc + d_c = the base
  boundary and d_c the x-seam-crossing part (36 nonzero entries, supported on the
  x-monomials x³ of A and x, x² of B — exactly as predicted). This confirms
  τ(u)=(u,u) and p(v)=v₀+v₁ form a short exact sequence of complexes
  `0 → C_base →τ C_cover →p C_base → 0` (both are chain maps; p∘τ = 1+σ = 0).
- **Δ = ∩ω has the closed form `Δ[z] = [∂₂c · z]`** (seam part of the base
  boundary ∂₂ applied to the base 2-cycle z), derived by the snake lemma
  (lift z↦(z,0); ∂₂cover(z,0) = τ(∂₂c z) since ∂₂base z = 0). Verified
  (`scripts/a3_delta_explicit.py`): dim H₂(base) = 6, and **im(Δ) = ker(tr_*)**
  as subspaces of H₁(base), both 6-dim — Smith exactness confirmed end to end.

### §2 reduction: both sheets share a base syndrome

For a cover X-cycle v=(v₀,v₁), the cycle condition ∂₁cover v = 0 in sheet
coordinates is d_nc v₀ + d_c v₁ = 0 and d_c v₀ + d_nc v₁ = 0. Adding the base
syndromes: **∂₁base v₀ = ∂₁base v₁ = d_c·p(v) =: s** (both sheets carry the
*same* base X-syndrome, equal to the seam part applied to the sheet-sum). The
factor-2 lemma |v₀|+|v₁| ≥ 2·d_base then splits:

- **s = 0 (easy):** v₀, v₁ are base cycles with [v₀] = [v₁] (they differ by
  p(v), a base stabilizer). If that common class is nontrivial, each has weight
  ≥ d_base, so |v| ≥ 2·d_base. ✓ The 6 dangerous *reps* are exactly this case
  (they are τ(u), p(v)=0 ⇒ s=0, [u] nontrivial).
  *(Open subcase: [v₀]=0 — both sheets base stabilizers; must check such v is a
  cover stabilizer, i.e. trivial, hence excluded.)*
- **s ≠ 0 (hard):** v₀, v₁ are NOT base cycles — the seam leaks weight between
  sheets. The crude syndrome-weight bound is insufficient; this is the genuine
  open crux (the "new math" the scouting flagged), where Δ=∩ω enters.

### Promising-but-UNVERIFIED simplification (trap-shaped — do not lean on)

`scripts/a3_syndrome_split_probe.py` finds: the hard case is non-vacuous
(36/72 stabilizer generators produce s≠0), **but in 40k random samples every
s≠0 dangerous member has weight ≥ 16, while the weight-12 minima are all s=0.**
If this held rigorously it would be a major de-risking: the factor-2 bound on
the *minimum* would follow from the easy s=0 case alone, and the hard seam-
leakage case would only ever produce off-minimum (heavier) logicals.

**This is random sampling, and "held on N samples then died on a hostile
example" is exactly how this program's prior conjectures failed.** It is logged
as a lead, NOT a result. The map v ↦ s(v) = d_c·p(v) is *linear* on the
dangerous logical space, so {s=0} is a subspace and the s≠0 members are its
nonzero cosets — which makes the question "is every s≠0 coset's min weight
> 12?" a well-posed (if hard) coset-min-weight problem, not just a sampling
hope.

### Status

- §1 (Δ explicit + framework): **complete, verified** (3 scripts).
- §2 (factor-2 lemma): reduced to the syndrome split; easy case done modulo one
  subcase; **hard case (s≠0) open**; a sampling lead suggests the hard case may
  be off-minimum but this is unverified.

### Next concrete sub-step (highest value)

Rigorously decide the s≠0 lead: build a **trustworthy** constrained min-weight
check (carefully encoded, cross-checked against d=12 — NOT the buggy scout CNF)
for "minimum weight of a dangerous logical with s ≠ 0." If provably > 12, pivot
the proof to the easy case + an "s≠0 ⇒ off-minimum" lemma. If a weight-12 s≠0
member exists, the hard seam-leakage case is unavoidable and the months estimate
stands. Then (either way) close the s=0 [v₀]=0 subcase.

---

## Entry 2 (2026-06-10) — the lemma's three cases, rigorously located (validated SAT)

Built `scripts/a3_s_nonzero_sat.py` and `scripts/a3_s0_subcase.py` — constrained
min-weight SATs whose encodings **pass a sanity ladder** (they reproduce
d_cover = 12: nontrivial-logical min is UNSAT at w≤11, SAT at w=12). This is the
validation the scout's `a1_smith_sector_sat.py` lacked (its "safe min = 6" is the
encoding bug). Encoding: cycle H_X v=0; dangerous (P^T g_i)·v=0 ∀ base logX g_i
[⟺ [p(v)]=0]; nontrivial OR_a(L_a·v=1) over cover logX; s constraints as
equalities (s=0) or an OR-of-parities (s≠0); [v₀]=0 via (Π₀^T g_i)·v=0.

**The factor-2 lemma decomposes into three cases, and only one binds the
minimum:**

| case | meaning | min weight (validated SAT) | analytic status |
|---|---|---|---|
| **s=0, [c]≠0** | both sheets are nontrivial base logicals | **12 = 2·d_base** (achieved) | **clean: |v₀|,|v₁| ≥ d_base ⇒ |v| ≥ 2·d_base** |
| s=0, [c]=0 | both sheets base-trivial | ≥ 15 (UNSAT ≤14) | off-minimum; analytic ≥12 still owed |
| s≠0 | seam leakage | 14 (UNSAT ≤13) | off-minimum; analytic ≥12 still owed |

So the minimum-weight (12) dangerous logicals are **exactly** the clean
s=0,[c]≠0 ones, and that case has a one-line analytic proof. The sampling lead
from Entry 1 is now confirmed with a trustworthy encoding (the true s≠0 min is
14, not the sampled 16).

**What this does and does NOT establish.** It does NOT prove the lemma — the SAT
results are discovery/confidence (same exclusion as the d=12 certificate), and
the two off-minimum cases still owe an *analytic* ≥ 2·d_base (we now know both
are true with margin: ≥14 and ≥15). What it DOES is crystallize the proof
strategy and de-risk it substantially:
- the factor-2 *value* is correct and is attained precisely where the clean
  argument applies;
- the obstruction (seam leakage, s≠0) and the degenerate subcase ([c]=0) are
  provably **off the minimum**, so a complete analytic proof needs only crude
  (≥12, not tight ≥14/≥15) bounds there, which should be far easier than a tight
  seam analysis.

**Reframing of the crux (possible major simplification — to test next).** The
σ-involution makes the cover code a candidate for the *classical* van Lint /
Chen–Xie–Ding Plotkin double-cover distance theorem (A1 lane L2,
arXiv:2402.02853 Thm 2.1: d = min{2·d(C₁), d(C₂)} along a free Z₂-action). If
that theorem (or KP-2013 Thms 8–9) applies to the BB cover, the dangerous-sector
bound 2·d_base is a KNOWN result, not new math — which would contradict the
"months" estimate in the good direction. The catch the scouts flagged: the
clean theorem's hypothesis (KP's k^(1+x)=k) FAILS on gross, and the failure is
exactly the s≠0 seam leakage. The computational finding "s≠0 ⇒ off-minimum"
suggests the *conclusion* survives the hypothesis failure — i.e. the remaining
analytic work is precisely bridging that gap (the conclusion holds, the standard
proof doesn't). This is the sharpest statement of the crux so far.

### Status

- §1: complete, verified.
- §2: lemma TRUE (validated SAT, all 3 cases ≥12, minimum at the clean case);
  clean case proven analytically; **two off-minimum cases owe an analytic ≥12.**
  Crux reframed as "extend the classical Plotkin double-cover bound past the
  hypothesis (k^(1+x)=k) that gross violates."

### Next

1. Read Chen–Xie–Ding arXiv:2402.02853 Thm 2.1 and KP-2013 Thms 8–9 hypotheses
   in full; pin exactly which hypothesis gross violates and whether the
   conclusion's proof can be salvaged on the off-minimum cases (crude ≥12).
2. Attempt the analytic ≥12 for s≠0 and for s=0/[c]=0 (crude bounds suffice).
3. Skeptic sweep before trusting any drafted bridge argument.

---

## Entry 3 (2026-06-10) — Plotkin reformulation; the precise analytic obstruction for s≠0

### Plotkin coordinates make the clean case a one-liner and expose the gap

Reparametrize a dangerous cover X-cycle by (a, b) := (v₀, p(v)=v₀+v₁), so
v = (a, a+b) and |v| = |a| + |a+b| — literally the classical Plotkin/[u|u+v]
shape. The cycle condition becomes the single relation **∂₁a = d_c·b** (= s),
and dangerous ⟺ b = p(v) is a base stabilizer ([b]=0). Then:

- **b = 0 (s=0):** a is a base cycle, v = τ(a); nontrivial ⟹ [a] ≠ 0 ⟹
  |v| = 2|a| ≥ 2·d_base. The clean case, now a one-liner in these coordinates.
- **b ≠ 0 (s≠0):** ∂₁a = d_c·b ≠ 0, so **a is not a base cycle.** This is the
  exact point where the classical Plotkin theorem (d = min{2·d(C₁), d(C₂)})
  fails to apply: that theorem needs the first component `a` to range over a
  *code with its own minimum distance*; here `a` ranges over an **affine
  syndrome class** {a : ∂₁a = d_c b}, which contains arbitrarily light vectors.
  (This is the concrete form of the "k^(1+x)=k" hypothesis that KP-2013 Thm 8
  needs and gross violates.)

### The precise obstruction (why crude bounds miss)

Correct each sheet by a min-weight syndrome representative e (∂₁e = s): then
a+e and (a+b)+e are base cycles, giving
    |v| = |a| + |a+b| ≥ (|a+e|−|e|) + (|a+b+e|−|e|) ≥ 2·d_base − 2|e|
when both corrected cycles are nontrivial base logicals. This **loses 2|e|**,
so it only yields 2·d_base when s=0. The validated SAT says the truth on this
sector is ≥ 14 > 12, so the real bound has slack the syndrome-correction throws
away: the seam structure must force a and a+b into *heavy* classes (not merely
nontrivial), which this argument does not capture. Closing it is the genuine
new-math step — consistent with the scouting "months" estimate, now pinned to a
one-line gap.

### Honest status of the analytic bound (no overclaim)

What is **analytically proven** today (given d_base = 6 as the transfer input):
- safe sector: |v| ≥ |p(v)| ≥ d_base = 6 (the published projection branch);
- dangerous sector, clean case (s=0, [c]≠0): |v| ≥ 2·d_base = 12.

What is **NOT yet analytically proven**: the two off-minimum dangerous cases
(s≠0 → truth ≥14; s=0,[c]=0 → truth ≥15). Until those have analytic ≥-bounds,
**there is no complete analytic lower bound on d(gross) beyond the known
Lin–Pryadko floor d ≥ 2** — a dangerous logical could, as far as *proven* math
goes, hide light in the unanalyzed cases (computation says it does not). So:
real structural progress and a fully de-risked target, but the headline bound
is not yet improved. State it this way to anyone reading.

### Two honest forks for the next session

- **Fork A (full factor-2, goal 1 route):** close the s≠0 and [c]=0 cases with a
  seam-aware weight argument (the heavy-class forcing). Genuinely new; high
  payoff (d_gross = 12 if the base case d_base=6 is itself made analytic).
- **Fork B (modest but complete, goal 3 route):** look for an analytic
  dangerous-sector ≥ 6 (not 12) that covers ALL cases — if even a weak uniform
  dangerous-sector bound exists, combined with the safe ≥6 it gives a complete
  analytic d_gross ≥ 6, beating the floor. This may be far easier than the
  factor-2 and directly serves goal 3; worth scoping before grinding Fork A.

### Citation flag

A1 lane L2 cited "Chen–Xie–Ding arXiv:2402.02853 Thm 2.1" for the Plotkin
double-cover distance. The arXiv abstract (fetched) describes a repeated-root
*cyclic codes* construction and does not surface that theorem; Thm 2.1 is likely
a restated classical (van Lint/Castagnoli) lemma, but the exact statement was
not re-confirmed here. Re-verify before any write-up leans on it. The analytic
conclusion above (classical Plotkin needs `a` code-constrained; gross's `a` is
only syndrome-constrained) does not depend on the citation.

---

## Entry 4 (2026-06-10) — Fork B is analytically vacuous (it degrades to the floor); Fork A is necessary

Tested Fork B (a uniform dangerous-sector bound via the elementary projection
inequality). Found a clean rigorous bound — then found it cannot beat the floor
fully-analytically. Recorded because the *reason* is the sharpest justification
yet for why the factor-2 (Fork A) is the only viable analytic route.

### The elementary projection bound (rigorous, but bounded by d_base)

For ANY nontrivial cover logical v=(v₀,v₁): **|v| ≥ |p(v)|** (triangle
inequality; p sums the sheets and is a projection chain map — verified). Casing
on p(v):
- p(v)=0: v = τ(v₀), [v₀]≠0, so |v| = 2|v₀| ≥ 2·d_base;
- p(v)≠0, [p(v)]≠0 (safe): |v| ≥ |p(v)| ≥ d_base;
- p(v)≠0, [p(v)]=0 (dangerous, b≠0): p(v) is a nonzero base Z-stabilizer, so
  |v| ≥ |p(v)| ≥ μ_Z := min nonzero base-stabilizer weight.

Hence **d_cover ≥ min(d_base, μ_Z)**. Computed (`scripts/a3_forkB_projection_bound.py`,
SAT with sanity checks): for the base [[72,12,6]], μ_Z = μ_X = **6**, so the
bound reads d_gross ≥ min(6, 6) = **6** — *if* d_base = 6 and μ_Z = 6 are taken
as given.

### Why it is analytically vacuous (the fatal catch)

`min(d_base, μ_Z) ≤ d_base`: the bound is **monotonically non-increasing under
the cover chain — it can never grow.** To make d_base = d([[72,12,6]]) analytic,
recurse the same bound: d₇₂ ≥ min(d₃₆, μ₃₆) ≤ d₃₆ = 4 < 6. Continuing,
d₃₆ ≥ min(d₁₈, μ₁₈) ≤ d₁₈ = 2. The chain bottoms at the one analytic anchor
(Phase 1: [[18,8,2]] = HGP(J₃,J₃), analytic d=2), so **fully-analytically this
bound gives only d_gross ≥ 2 — exactly the published LP floor, no improvement.**
It yields ≥ 6 *only* as a hybrid that imports SAT's d₇₂ = 6, which the program's
"fully analytic" constraint forbids (same exclusion as SAT).

### The payoff: Fork A is necessary, and we know precisely why

The elementary bound caps at d_base because the only sectors it controls give
≥ d_base (safe) or ≥ μ_Z (dangerous, b≠0). **The single growth mechanism in the
whole picture is the symmetric case p(v)=0, which gives 2·d_base** — and that is
exactly the factor-2 (Fork A) lemma. So:
- Fork B (uniform projection bound): rigorous but ≤ d_base ⇒ degrades to 2
  fully-analytically. **Dead for goals 1 and 3.**
- Fork A (factor-2 on the symmetric/dangerous sector): the *only* route that
  grows the bound past the base, and the only path to beating the floor
  analytically — for d_gross ≥ 4 (with a structural d([[36,8,4]])≥4 base via the
  even-h chain) up to d_gross = 12 (full factor-2 + analytic base).

This converts the earlier "two forks" into one: **Fork A is mandatory.** The
crux remains the s≠0 seam-leakage analytic bound (Entry 3), now known to be not
just the hard part but the *essential* part — no elementary projection shortcut
exists.

### Status (Track 1.1, end of session)

- §1 complete and verified (framework, Δ explicit).
- §2 factor-2 lemma: TRUE (validated SAT, all cases ≥12, minimum at the clean
  symmetric case which is proven analytically); the two off-minimum cases (s≠0,
  [c]=0) owe an analytic ≥ 2·d_base; that seam-aware weight argument is the
  genuine open new-math step, and Entry 4 shows it is unavoidable.
- No fully-analytic improvement on the d ≥ 2 floor yet; the path to one is
  Fork A specifically.
