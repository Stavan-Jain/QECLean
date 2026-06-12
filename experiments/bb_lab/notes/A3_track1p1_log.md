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

---

## Entry 5 (2026-06-12) — the m(b) collapse: the case trichotomy was a coordinate artifact

The s=0 / s≠0 / [c]=0 case split of Entries 1–3 is not intrinsic. There is a
single exact identity that organizes the whole dangerous sector, indexed by
the projected stabilizer b = p(v), and it converts the factor-2 lemma into a
one-parameter family of statements about the **base code alone**. Every claim
below is script-verified (`a3_mb_foundations.py`, all checks PASS), and the
derivation is short enough to verify by hand.

### The derivation

**Cuts.** For each cut position j ∈ Z₆ (fundamental domain {j,…,j+5} in x),
split the base boundaries along the seam: ∂₁ = d1nc_j + d1c_j (= H_X) and
∂₂ = d2nc_j + d2c_j (= H_Zᵀ). For *every* j the cover boundaries take the
block form [[nc_j, c_j],[c_j, nc_j]] (V1), the chain identities
d1nc·d2nc + d1c·d2c = 0 = d1nc·d2c + d1c·d2nc hold (V2), and the snake map
Δ_j[ζ] = [d2c_j ζ] on H₂ = ker ∂₂ (dim 6, V3) satisfies
**im Δ_j = ker tr_\*** (V5) — so im Δ is cut-independent, Smith exactness
holds per cut.

**Parametrization.** Dangerous cycles = τ(Z₁) + im ∂₂^cov, as an exact
equality of subspaces (dim 72, V6); v = τ(u) + ∂₂^cov w is a nontrivial
logical iff [u] ∉ im Δ (V8).

**Sheet formula.** Fix v = τ(u) + ∂₂^cov w. Let z := p(w) and
b := p(v) = ∂₂ z ∈ Stab_Z(base) — both cut-free. In cut-j sheet coordinates
w = (w₀, w₁):

    v₀ = u + d2c_j z + ∂₂ w₀ ,      v₁ = v₀ + b .          (V7)

(One line: ∂₂^cov w has sheets (d2nc_j w₀ + d2c_j w₁, d2c_j w₀ + d2nc_j w₁)
= (∂₂ w₀ + d2c_j z, ∂₂ w₁ + d2c_j z).)

**Boolean identity.** For any x, b over F₂: |x| + |x+b| = |b| + 2·|x off supp b|.
So pointwise, for every cut j simultaneously,

    |v| = |b| + 2·|v₀(j) restricted off supp(b)| .

**Slice minimum.** Fix b and minimize over the slice
{v nontrivial dangerous : p(v) = b}. As (u, ζ ∈ ker ∂₂, w₀) range, the sheet
v₀(j) ranges exactly over d2c_j z_b + {u' ∈ Z₁ : [u'] ∉ im Δ} (z_b a fixed
∂₂-preimage of b; ζ shifts [u'] by Δ_j[ζ] ∈ im Δ, which preserves
"∉ im Δ"; ∂₂w₀ absorbs Stab). Hence for every j

    min{|v| : v nontriv. dangerous, p(v) = b} = |b| + 2·m_j(b),
    m_j(b) := min{ |(d2c_j z_b + u') off supp b| : u' ∈ Z₁, [u'] ∉ im Δ } .

The left side does not mention j, so **m_j(b) =: m(b) is cut-independent**;
and it is G-translation-invariant (the slice for T·b is the T_cover-image of
the slice for b). The factor-2 lemma is exactly

    **(M)   |b| + 2·m(b) ≥ 12 = 2·d_base   for every b ∈ Stab_Z(base).**

Immediate rungs:
- **b = 0**: v₁ = v₀, so v = τ(v₀) with [v₀] = [u'] ∉ im Δ nonzero ⟹
  |v| = 2|v₀| ≥ 2·d_base ✓. (The old clean case, now with the Δ-twist
  subsumed — no [c]-side condition needed.)
- **|b| ≥ 12**: trivial ✓.
- **0 < |b| ≤ 11**: the entire open content. A question about the base
  [[72,12,6]] code and its seam split only — the cover has left the stage.

### Discovery scan (`a3_mb_scan.py`; numbers are validation only, as always)

- **Light stabilizers**: the b with 0 < |b| ≤ 11 are *exactly* 36 single
  hexagons (|b| = 6, b = ∂₂δ_g) and 216 overlapping pairs (|b| = 10,
  b = ∂₂(δ_g + δ_{g+δ}), δ in an explicit 12-element difference set D).
  Nothing else — no weight-8, no k ≥ 3 face-supports.
- **m-values**: m(0) = 6 ✓ (= d_base); m(single hexagon) = 4 (all 36, one
  orbit); m(pair) = 3 at worst. So the slice minima are 12 (b = 0),
  14 (singles), 16 (pairs): **(M) holds on every light slice, with margin 2,
  and the global dangerous minimum 12 is carried exactly by b = 0.**
- **Cut-independence and translation-invariance of m**: verified on samples
  (m_j identical for j = 0..5; translated b gives equal m).
- **Witness decode**: the Entry-2 s≠0 weight-14 minimizer has b = a single
  hexagon, |v₀ off b| = 4 = m(b), i.e. 14 = 6 + 2·4 exactly; its seam-syndrome
  flags across the six cuts are s_j = [1,1,1,0,0,0] — *the same v is "s≠0" for
  three cuts and "s=0" for the other three.* The trichotomy was an artifact of
  fixing j = 0.
- **Sharpening**: the [c]=0 sub-case is UNSAT at weight ≤ 15 (Entry 2 had only
  established ≥ 15): its true minimum is ≥ 16.

### Dead reductions (first-class; do not retry)

1. **Single-sheet decoupling is FALSE.** The natural relaxation
   |v| ≥ 2·dist(u + d2c z, Stab) (drop the shared-β coupling between the two
   sheets) cannot prove (M): there exist weight-6 *cover stabilizers* whose
   sheets occupy exactly the same affine data (u' + d2c z_b with u' in a
   non-im Δ class can lie inside Stab + C_Σ). Concretely, for any class
   [u] ∈ φ(D)\imΔ realized by a [c]=0 configuration u + d2c z₀ ∈ Stab, the
   perturbation z = z₀ + (single face with flux) makes dist(u + d2c z, Stab)
   ≤ 3 while the true slice values stay ≥ 14. Any valid proof must use the
   same-β coupling — which is exactly what the off-supp(b) puncture in m(b)
   encodes. This kills the "seam-aware weight argument bounding |a| below"
   as literally proposed in A_HANDOFF §4; the viable version is the punctured
   form m(b).
2. **Multi-cut leverage is VACUOUS for minima.** Since the slice minimum
   equals |b| + 2·m_j(b) for every j, all six cuts see the same value; for a
   *fixed* v, |v₀(j) off supp b| = (|v| − |b|)/2 for all j. The six cut
   decompositions are an invariance, not six independent inequalities. (They
   remain useful for *choosing* a convenient cut in proofs, e.g. one with
   d2c_j z_b ⊆ supp b.)
3. **The s/[c] trichotomy** is the cut-0 shadow of the b-grading: s_j = d1c_j b
   varies with j at fixed v (witness above). Statements should be made about
   b-slices, not s-cases.

### Status

- The factor-2 lemma is now **equivalent** (by a verified, hand-checkable
  reduction) to (M): |b| + 2 m(b) ≥ 12 for all base stabilizers b, with
  b = 0 and |b| ≥ 12 proven, and the light range 0 < |b| ≤ 11 open.
- Computationally the light range holds with margin (slices ≥ 14): the open
  analytic content is the classification of light stabilizers + lower bounds
  on m for the two families. → Entry 6.

---

## Entry 6 (2026-06-12) — the analytic ladder for (M): k ≤ 7 closed, rungs verified, tail = k ≥ 8

Entry 5 reduced the factor-2 lemma to (M): |b| + 2 m(b) ≥ 12 over base
stabilizers, open only for 0 < |b| ≤ 11. This entry builds the analytic
ladder for that range. Structural data in `a3_mb_structure.py` (T1–T6),
end-to-end SAT crosschecks in `a3_mb_crosscheck.py` (C1–C2).

Notation: hexagon h(g) := supp ∂₂δ_g (one face's stabilizer, |h(g)| = 6);
for z ∈ C₂ let k(z) = |supp z| (face count) and k_min(b) = min over the
ker ∂₂-coset of preimages (ker ∂₂ has dim 6, min weight 16 — T5).

### Ladder step 1 — light-stabilizer classification (b with |b| ≤ 11)

**(L-A) Two hexagons overlap in ≤ 1 qubit — PROVEN.** The overlap of h(g)
and h(g+δ) is the autocorrelation count |A ∩ Aδ| + |B ∩ Bδ|. The difference
sets are (computed symbolically and machine-confirmed, T1):
    dA = {(0,±1), (3,±1), (3,±2)},   dB = swap(dA) = {(±1,0), (±1,3), (±2,3)},
each with 6 *distinct* elements, and disjoint **in both coordinates**:
x(dA) ⊆ {0,3}, x(dB) ⊆ {1,2,4,5}; y(dA) ⊆ {1,2,4,5}, y(dB) ⊆ {0,3}.
Hence ov(δ) ≤ 1 for every δ ≠ 0, with ov = 1 exactly on D := dA ∪ dB
(|D| = 12). Consequences: k = 1 gives |b| = 6 (the 36 hexagons); k = 2 gives
|b| = 12 − 2·ov ∈ {10, 12}, i.e. the 216 D-pairs at weight 10 and nothing
else below 12.

**(L-B) k ∈ [3,7] ⟹ |b| ≥ 12 — PROVEN (modulo one finite check at k = 7).**
Counting lemma: for any z with k faces, every qubit q covered cov_q times
contributes parity(cov_q) = cov_q − 2⌊cov_q/2⌋ to |b|, and
Σ_q ⌊cov_q/2⌋ ≤ Σ_q C(cov_q, 2) = Σ_{face pairs} ov(pair) = e(S), the number
of D-pairs among the k faces (using ov ≤ 1). So
    **|b| ≥ 6k − 2·e(S)**, valid for every preimage z.
Now bound e(S) in the Cayley graph Cay(Z₆², D):

*K₄-freeness of Cay(Z₆², D) — full hand proof.*
(i) *Triangles are monochromatic.* If a ∈ dA and b ∈ dB then
y(b−a) ∈ {0,3} − {1,2,4,5} ⊆ {1,2,4,5}, so b−a ∉ dB; and
x(b−a) ∈ {1,2,4,5} − {0,3} ⊆ {1,2,4,5}, so b−a ∉ dA. Hence no triangle mixes
dA- and dB-edges.
(ii) A K₄'s four triangles pairwise share edges, so all 6 edges have one
color; by the swap symmetry assume all in dA. The dA-graph lives on
Z₂ × Z₆ (x ∈ {0,3} ≅ Z₂), generators {(0,±1), (1,±1), (1,±2)}.
(iii) Three same-ε points (ε = Z₂-coordinate) would need pairwise y-diffs
in {±1}: impossible for 3 distinct points (two ±1-steps from any point
differ by 2). This kills ε-splits 4+0 and 3+1 of a K₄.
(iv) Split 2+2: WLOG p = (0,0), q = (0,1), r = (1,t), s = (1,t+1). The four
cross differences force {t−1, t, t+1} ⊆ {1,2,4,5} = Z₆ \ {0,3} — but every
3 consecutive residues mod 6 contain 0 or 3 (they are antipodal). ∎
Turán then gives e(S) ≤ ex(k, K₄) = e(T(k,3)), so
    k=3: |b| ≥ 18−6 = 12;  k=4: 24−10 = 14;  k=5: 30−16 = 14;  k=6: 36−24 = 12.
*k = 7:* ex(7, K₄) = 16 with the **unique** extremal graph T(7,3) = K(3,2,2)
⊇ K(2,2,2). Every edge of an octahedron K(2,2,2) lies in a triangle and its
triangles are edge-connected, so an octahedron is monochromatic and would
live in the dA-graph; Cay(Z₆², D) contains **zero** octahedra (T6, exhaustive;
hand case-analysis in Z₂×Z₆ owed — the only nontrivial ε-split is 3+3).
Hence e(S) ≤ 15 at k = 7 and |b| ≥ 42 − 30 = 12. ∎

**(L-C) k_min ≥ 8 — OPEN (the tail).** Statement to prove: every
b ∈ Stab_Z(base) whose minimal face support is ≥ 8 has |b| ≥ 12. True with
margin computationally (the SAT enumeration found NO |b| ≤ 11 beyond k ≤ 2).
Pure counting cannot close this: for large k, 6k − 2e(S) goes vacuous
(e(S) ~ k²/6 in a 12-regular graph). Partial analytic result (x-collapse):
summing the x-columns, |b| ≥ |z̄| + |(1+y+y²)z̄| where z̄ = z mod (1+x) ∈
F₂[y]/(y⁶+1) — kills configurations with z̄ outside the annihilator pattern
but bottoms out at z̄ ∈ (1+y)(1+y³)F₂[y] (where (1+y+y²)z̄ = 0). The right
tool is the repeated-root filtration along BOTH primes of x⁶+1 =
((1+x)(1+x²+x⁴))·… = ((1+x)(1+x+x²))² — i.e. exactly the van Lint /
generalized-van-Lint machinery from lane L1 (now verbatim-verified, see
citation note below). This is the single remaining unbounded-structure claim.

### Ladder step 2 — the m-rungs for the two light families

For a single face, the seam part of one column is a sub-vector of that
column: supp(d2c_j δ_g) ⊆ h(g) (the c/nc split is an entrywise split of ∂₂).
So m(hexagon) = min{|u' off h(g)| : u' ∈ Z₁, [u'] ∉ imΔ}, shift-free; and for
a D-pair, supp(d2c_j z_b) ⊆ h(g) ∪ h(g′) = supp(b) ∪ {q*} (q* the overlap
qubit), so m(pair) ≥ min{|u' off (h(g) ∪ h(g′))|}.

**(L-D6) m(hexagon) ≥ 3 ⟸ every 1-cycle supported in h(g) ∪ {q₁,q₂} lies in
{0, ∂₂δ_g}.** Verified exhaustively: rank H_X|h = 5 (cycle space inside a
hexagon is exactly {0, b}), and over all 2145 choices of 2 extra qubits the
cycle space never grows (T3) — not even by imΔ-class cycles. Hand-proof
shape (owed): any two distinct qubits share ≤ 1 X-check — PROVEN: the
cross-correlation A·B̄ has 9 distinct terms and the autocorrelations are
multiplicity-free (T6) — so a 1-or-2-qubit tail outside the hexagon cannot
match the hexagon's check-space except in the finitely many adjacent
positions, which are then excluded one by one (translation-reduces to ONE
hexagon).

**(L-D10) m(D-pair) ≥ 2 ⟸ no non-imΔ 1-cycle supported in
(h(g) ∪ h(g′)) ∪ {1 qubit}.** Verified exhaustively over all 12 pair types ×
all extra qubits: zero such cycles (T3); the cycle space of the bare 11-qubit
union is exactly span{∂₂δ_g, ∂₂δ_{g′}} (rank 9, all 12 types). For the
12-target only m ≥ 1 is needed, i.e. only the bare-union fact (12
translation-reduced rank checks — surveyable); m ≥ 2 gives the observed
slice value 14.

Assembly check: 6 + 2·3 = 12 ✓ and 10 + 2·1 = 12 ✓ (with the verified
margins: 6+2·4 = 14, 10+2·3 = 16). Note (H0) d_base ≥ 6 enters ONLY at the
b = 0 rung; the b ≠ 0 slices need no distance input at all.

### End-to-end crosschecks (`a3_mb_crosscheck.py`)

- **C1**: direct cover SAT: dangerous ∧ nontrivial ∧ p(v) ≠ 0 is UNSAT at
  w ≤ 13 and SAT at 14 — exactly the assembled prediction (worst slice =
  hexagon: 6 + 2·4). The m(b) ladder accounts for the entire dangerous
  sector; the global minimum 12 sits at b = 0 alone.
- **C2**: the imΔ-distance of the base code (min weight of a cycle in a
  NONZERO imΔ class) is **12** = 2·d_base — the Smith-killed classes are
  exactly twice as heavy as d_base; no weight-6 logical is imΔ (T4: all 84
  weight-6 logicals are non-imΔ, max hexagon overlap 2, never spanning
  fewer than 2 x-columns).

### The conditional theorem (current best form)

**Theorem (dangerous-sector factor-2; conditional).** Assume
  (H0) d_Z(base) ≥ 6   [transfer input, used only at b = 0];
  (T-tail) every base Z-stabilizer with minimal face support ≥ 8 has
           weight ≥ 12   [OPEN — Entry-6 L-C];
  (T-oct) Cay(Z₆², D) is octahedron-free   [verified; finite hand check owed];
  (T-rungs) the hexagon+2 and pair-union+1 local cycle facts
           [verified exhaustively; local hand proofs owed].
Then every nontrivial dangerous gross logical has weight ≥ 12 = 2·d_base.
All other ingredients (the m(b) reduction; ov ≤ 1; K₄-freeness; k ∈ [3,7];
the counting lemma) are PROVEN above.

### Status and the honest scoreboard

- No analytic improvement on d ≥ 2 is claimed yet (unchanged); but the
  "months"-grade obstruction of Entries 3–4 (the s≠0 seam-leakage case) has
  been **dissolved into the m(b) ladder**, of which every rung except the
  k ≥ 8 tail is either fully proven or a verified finite local fact with a
  clear hand-proof route. The tail is a *classical* statement about one
  abelian 2-block group code — squarely in the repeated-root lane the
  program already surveyed — and is true with margin.
- Citation flags from A_HANDOFF §6: both DISCHARGED by source verification
  (2026-06-12). Chen–Xie–Ding arXiv:2402.02853 Thm 2.1 is verbatim the
  "generalized van Lint theorem", attributed to Chen–Ding 2023 [5] ← van
  Lint 1991; its Plotkin hypothesis (first component ranges over a code
  C₁ ⊇ C₂) is exactly what the gross cover violates, as Entry 3 said.
  Postema–Kokkelmans arXiv:2502.17052 (authors/title/quote) confirmed; the
  Otjens-2025 misattributions in T2.3_literature_survey.md relabeled to
  "PK Thm 2.18 (from Arnault et al. 2026)".

### Next steps (ranked)

1. **The k ≥ 8 tail (L-C)** via the repeated-root/(1+x,1+y)-adic filtration
   of F₂[Z₆×Z₆] (two squared primes per direction). This is now THE open
   problem of Track 1.1.
2. Hand-organize the owed finite checks: octahedron-freeness in Z₂×Z₆ (3+3
   split only), and the two rung locality proofs (shared-check ≤ 1 is
   already proven; the residue is a one-hexagon neighborhood analysis).
3. Then assemble the full conditional factor-2 write-up and revisit the
   recursion bookkeeping (what (M) at every level + an analytic anchor
   actually yields for goals 2/3 — note Entry 4's caution that the safe
   sector caps the full-code bound at d_base).

---

## Entry 7 (2026-06-12) — (T-oct) proven by hand; CRT component frame for the tail (groundwork)

Two increments past Entry 6: the octahedron-freeness input to the k = 7 rung
is now a full hand proof (no finite sweep left in the k ≤ 7 classification),
and the algebraic frame for the k ≥ 8 tail is set up and validated.

### Octahedron-freeness of Cay(Z₆², D) — hand proof (closes T-oct)

*Step 1 (color reduction).* In K(2,2,2) every edge lies in a triangle, and
the edges at a common vertex are linked through triangles (for edges (a,p),
(a,q) with p,q in the same part, route via a third-part vertex c: triangles
a-p-c and a-q-c share the edge (a,c)); since every triangle of Cay(Z₆², D)
is monochromatic (Entry 6, step (i)), all 12 edges of an embedded octahedron
carry one color. By the swap symmetry take dA: the octahedron embeds in
Cay(Z₂×Z₆, D'), D' = {(0,±1), (1,±1), (1,±2)} (first coordinate ε ∈ Z₂ is
the x-degree /3, second is y ∈ Z₆).

*Step 2 (accounting).* K(2,2,2) has 6 vertices, 12 edges, and 3 non-edges
forming a perfect matching. Within an ε-class, an edge needs y-difference
±1 (an induced subgraph of the 6-cycle C₆); across classes, an edge needs
y-difference ∈ {±1, ±2}, i.e. ∉ {0, 3}. m distinct vertices of one ε-class
induce ≤ max(m−1, …) C₆-edges: ≤ 2 for m = 3, ≤ 3 for m = 4, ≤ 4 for m = 5,
≤ 6 for m = 6.

*Step 3 (kill every ε-split a + (6−a)).*
- a ∈ {0,1}: the big class has C(6−a,2) ≥ 10 internal pairs but at most
  (induced edges) + (3 non-edges) ≤ 6 + 3 = 9 < 10 of them are realizable. ✗
- a = 2: internal edges ≤ 1 + 3 = 4, so cross edges ≥ 12 − 4 = 8 = all cross
  pairs; hence all 3 non-edges are internal and the 4-class induces exactly
  3 C₆-edges — forcing 4 consecutive y-values {y, y+1, y+2, y+3} whose three
  non-adjacent pairs (y,y+2), (y+1,y+3), (y,y+3) would all be non-edges; they
  are not pairwise disjoint, contradicting the perfect matching. ✗
- a = 3: internal edges ≤ 2 + 2, so ≥ 8 of the 9 cross pairs are edges, i.e.
  at most one cross pair has y-difference ∈ {0,3} ⟺ equal residues mod 3.
  With residue multisets (n₁,n₂,n₃), (n'₁,n'₂,n'₃) (each n ≤ 2 since a mod-3
  class of Z₆ has 2 elements), conflicts = Σ n_c n'_c ≤ 1 forces, up to
  relabeling, (2,1,0) against (0,1,2). The (2,·)-class has y-values
  {α, α+3, β}: the pair (α, α+3) has difference 3 — a non-edge; of (α,β) and
  (α+3,β), the differences differ by 3 so at most one is ±1 (an edge), and
  whichever of them is not an edge is a non-edge sharing a vertex with
  (α, α+3) or with the other — contradicting disjointness of the matching. ✗
No split survives; Cay(Z₂×Z₆, D') and hence Cay(Z₆², D) is octahedron-free. ∎

Consequence: with Entry 6's Turán-uniqueness step, **the light-stabilizer
classification is now fully proven for every face-support k ≤ 7** — no finite
sweep remains anywhere in the k ≤ 7 range. The conditional theorem's (T-oct)
hypothesis is discharged; the remaining gaps are (T-tail) and the two rung
locality write-ups.

### CRT component frame for the k ≥ 8 tail (set up, validated — not yet a proof)

G = Z₆² ≅ Z₂² × Z₃² via x = s_x·t_x (s_x = x³, t_x = x⁴), same in y. Then
R = F₂[G] ≅ Π_{j=0..4} R_j with R_j = F_j[Z₂²], F₀ = F₂ at the 3-part
character (ξ,η) = (1,1), and F₁..₄ = F₄ at the Frobenius orbits of
(ξ,η) = (ψ(t_x), ψ(t_y)) ∈ {(1,ω), (ω,1), (ω,ω), (ω,ω²)}. Writing u = 1+s_x,
v = 1+s_y (u² = v² = 0; R_j is local with radical (u,v)):

    Â_j = (1+η+η²) + u + ηv ,    B̂_j = (1+ξ+ξ²) + v + ξu ,

so Â_j is a unit iff η = 1 and otherwise the pure radical element u + ηv
(resp. B̂_j unit iff ξ = 1, else v + ξu). Hand computation of
Ann(Â) ∩ Ann(B̂) per component gives kernel components
(0, 0, 0, F₄·uv, span_F₄{ωu+v, uv}) — F₂-dims (0,0,0,2,4) — **verified
numerically** via idempotent projectors (probe in session transcript; sum of
the five idempotents = I, ranks 4/8/8/8/8, kernel projections 0/0/0/2/4,
total 6 ✓ matching the known dim ker ∂₂ = 6).

Structural reading: components (1,1), (1,ω), (ω,1) are *rigid* — at least one
of Â, B̂ is a unit there, so ẑ_j ≠ 0 is directly visible in b̂_j; the two
*doubly-radical* components (ω,ω), (ω,ω²) host the entire kernel and all the
"invisible" directions. The Entry-6 x/y-collapse partial bounds are the
(ξ=1)- and (η=1)-shadows of this decomposition.

Attack plan (next session): per-s-layer weight dictionary over the t-grid
Z₃² — a nonzero layer whose 3-part Fourier support is {trivial} has t-support
9; one F₄-orbit: 6; trivial + one orbit: 3 (coset of a Z₃ line); two generic
orbits: ≤ 4 (witness (1+t_x)(1+t_y)); the ≥-side of this dictionary is the
to-verify half. Combine with the rigidity pattern: a light b pins the
component support of ẑ on the rigid components, leaving freedom only in the
doubly-radical pair, where multiplication by u+ηv, v+ξu has a 2-step
filtration — the repeated-root layer analysis lives entirely in two F₄[Z₂²]
local rings. Goal shape: |b| ≤ 10 forces ẑ rigid-component-supported like a
monomial or D-pair, and the doubly-radical freedom is exactly mod-kernel.

### Status

- k ≤ 7 classification: fully PROVEN (Entries 6 + 7).
- Remaining for the conditional factor-2 theorem: (T-tail) k ≥ 8, and the
  two rung locality hand write-ups (hexagon+2, pair-union+1).
- The component frame is validated and ready as the tail's working language.

---

## Entry 8 (2026-06-12) — tail attack I: the layer dictionary, and "light ⟹ all five components alive"

First working session on (T-tail) in the Entry-7 CRT frame
(`a3_mb_tail_dictionary.py`). The frame is now fully instrumented and it
produced its first global structural result on light stabilizers.

### The instrument (all machine-verified)

- **Layer dictionary d₃.** For f ∈ F₂[Z₃²] nonzero with Fourier support
  inside a set W of character orbits (|orbits| = 5: trivial + four), the
  minimum weight d₃(W) depends only on (n, ε) = (#nontrivial orbits in W,
  trivial ∈ W) — the GL₂(Z₃)-symmetry permuting the four directions — with
  table (n,ε): (0,1)→9, (1,0)→6, (1,1)→3, (2,0)→4, (2,1)→3, (3,·)→2,
  (4,0)→2, (4,1)→1. Verified by brute force over all 512 functions.
- **Component transforms.** Â_j, B̂_j derived *empirically* as partial
  Fourier transforms of the lab ∂₂δ₀ columns (guaranteeing the
  multiplicativity ĥat(Az)_j = Â_j·ẑ_j by translation-equivariance — a
  first hand-coded version had the orientation backwards and was caught by
  exactly this check). Structure as predicted by Entry 7: comp 0 both
  units; comp 1 A-radical/B-unit; comp 2 mirror; comps 3,4 both radical;
  kernel dims (0,0,0,2,4).
- **Support grammar.** Per component the realizable pairs
  (supp Â_jẑ_j, supp B̂_jẑ_j) over all ẑ_j: radical sides take only
  co-point (3) or full (4) supports; comp 4 is rigid (B̂₄ = ω·Â₄ forces
  equal supports, only 6 pairs); pair-set sizes (16, 53, 53, 20, 6).
- **The bound.** |b| ≥ COST(pattern(z)) := Σ_s d₃(W_s^A) + Σ_s d₃(W_s^B)
  over the four s-layers. Validity verified on 200 random z; **tight on
  both exceptional families**: hexagon = 6, D-pair = 10 (and the per-layer
  accounting matches the hand computation: hexagon = three δ-point layers
  per block; dA-pair = (1,1,2 | 1,1,2,2)).

### New result: the component-support lemma (verified finite minimization)

Minimizing COST over the full grammar (mixed-radix DP over per-layer alive
counts, exhaustive):

- global minimum = **6**, achieved only by the 4 hexagon-type patterns
  (S₀ = a co-point, all four nontrivial components full on those 3 layers);
- forcing ANY single component dead (j = 0: S₀ = ∅; j ∈ {1,2,3,4}: the
  joint-annihilator grade) gives minimum **12**.

**Lemma (component support).** Every b ∈ Stab_Z(base) with |b| ≤ 11 has all
five CRT components visibly alive: for every j, (Â_jẑ_j, B̂_jẑ_j) ≠ (0,0).
Status: exhaustive verified computation over a verified relaxation; the
counting is structured enough (support sizes × the d₃ table) that a hand
proof looks like a tractable LP-style argument — owed, not claimed.

### The sub-12 landscape (the equality-analysis target list)

All-components-alive patterns with COST ≤ 11, by cost:
6: 4 (exactly the hexagon patterns) · 7: 24 · 8: 85 · 9: 136 · 10: 456 ·
11: 904. Structure: every pattern of cost ≤ 9 is a "3-layer near-hexagon"
(three alive layers per block, counts mostly 4, S₀ inside the alive
layers); the 2-layer-S₀ families appear at cost 10 — and the actual D-pair
pattern (S₀ on 2 layers, computed signature SA = (1010,1110,1010,1110,1110),
SB = (1010,1111,1111,1011,1110)) sits there, again tight.

### What this does and does not give

- It does NOT yet prove (T-tail): COST is a lower bound, so sub-12-cost
  patterns are *candidates* that an actual light b must realize — the tail
  now reduces to: **(i)** hand-organize the two finite minimizations
  (component-support lemma; the ≥ 12 floor outside the explicit sub-12
  list), and **(ii)** an equality analysis showing each sub-12 pattern
  class is realized at weight ≤ 11 only by hexagons and D-pairs (mod
  kernel). The forcing tools for (ii): a weight-1 layer with full support
  is a δ-point; co-point ideal elements have 2-parameter coefficient
  rigidity across their 3 layers; comp-4 support equality; S₀ shared
  between blocks.
- The pattern list is finite, explicit, and small at the cheap end — the
  near-hexagon (≤ 9) band looks provably hexagon-only by δ-point forcing;
  the 10–11 band is where D-pairs live and needs the genuine case analysis.

### Next

1. Equality analysis for the ≤ 9 band (δ-point forcing ⟹ z ≡ monomial mod
   kernel candidates), then the 10–11 band (D-pair forcing).
2. Hand-organize the two finite minimizations (the component-support lemma
   first — it is the cleanest standalone statement).
3. Keep the rung locality write-ups (Entry 6) on the queue; unchanged.

---

## Entry 9 (2026-06-12) — tail attack II: profile completeness closes (T-tail) at the verified-finite level

The equality analysis planned in Entry 8 turned out to admit a much cleaner
organization than the 705-pattern list — and it finishes the job
(`a3_mb_tail_profiles.py`). The light-stabilizer classification, hence the
whole (M)-ladder, is now closed with no unbounded-structure gap, by a route
independent of the Entry-6/7 k ≤ 7 combinatorics.

### Profile completeness (three lemmas)

Write b = (Bz, Az) in s-layers over Z₂² (each layer a function on Z₃²,
weights w_s^B, w_s^A ∈ [0,9], |b| = Σ both blocks).

- **(i) Parity (hand-proven).** The two blocks have identical layer
  parities: the layer-parity vector of a block is its component-0
  transform, and A, B have the *same multiset of s-parts* {1, s_x, s_y}
  (A: x³ ↦ s_x, y ↦ s_y, y² ↦ 1; B: y³ ↦ s_y, x ↦ s_x, x² ↦ 1), so
  Â₀ = B̂₀ = [1] + [s_x] + [s_y] and both blocks see the same w₀ = Â₀ẑ₀.
- **(ii) Floor (machine ingredient).** Each block is supported on ≥ 3
  layers: component 4 is alive for |b| ≤ 11 (Entry-8 component-support
  lemma) and its radical ideal admits only co-point (3) or full (4)
  supports (hand-proven ideal structure).
- **(iii) Evenness (hand-proven).** |Az| ≡ |Bz| ≡ |z| (mod 2), so |b| is
  even; |b| ≤ 11 means |b| ≤ 10, and Σ of one block ≤ 10 − 3 = 7.

Under (i)–(iii), the layer-weight pair (w^A, w^B) of any b with |b| ≤ 10
ranges over an explicitly enumerable set: 252 placements in **28 profile
families** (e.g. {1,1,1}+{1,1,1} at |b| = 6; {2,1,1}+{2,2,1,1} at 10).

### Exhaustive family checks (syndrome hash-join)

For each family, enumerate ALL layer contents (subsets of the 9-cell Z₃²
grid of the prescribed sizes, both blocks) and keep exactly the pairs that
form a genuine stabilizer — membership tested exactly via the 42-bit
syndrome key K = ker(∂₂ᵀ): b ∈ colspan ∂₂ ⟺ K_B·b_B = K_A·b_A, a hash-join
of the two sides. Results over all 28 families:

    {1,1,1}+{1,1,1}            →  exactly the 36 hexagons
    {2,1,1}+{2,2,1,1} (+mirror) →  exactly the 216 D-pairs (108 + 108)
    all 25 other families       →  EMPTY

Cross-checks: every |b| = 8 family is empty (matches SAT: no weight-8
stabilizers); the D-pairs land exactly in the (4,6)/(6,4) block splits
predicted by the T1 overlap analysis; total counts 36/216 match the
Entry-5 enumeration.

**Theorem-grade statement (verified-finite).** Every b ∈ Stab_Z(base) with
0 < |b| ≤ 11 is a single hexagon or a D-pair. Ingredients: lemmas (i),(iii)
hand-proven; lemma (ii) = comp-4-aliveness (verified finite minimization,
Entry 8); the 28-family exhaustive content check. This supersedes the
k-graded route: the k ≥ 8 tail no longer exists as a separate problem.
(The Entry-6/7 hand proofs remain the fully-analytic cover of the k ≤ 7
range and an independent confirmation.)

### Status of the (M)-ladder = the dangerous-sector factor-2 lemma

| rung | status |
|---|---|
| b = 0 (m(0) ≥ 6) | PROVEN given d_base ≥ 6 |
| \|b\| ≥ 12 | PROVEN (trivial) |
| classification 0 < \|b\| ≤ 11 | k ≤ 7 fully hand-proven (E6–7); ALL \|b\| ≤ 10 closed verified-finite (E9) |
| m(hexagon) ≥ 3 | verified exhaustive (E6); hand route sketched |
| m(D-pair) ≥ 1 | verified (12 rank checks, E6); hand route sketched |

**Every step of the factor-2 lemma is now either hand-proven or a verified
finite check with a bounded hand-proof route. No unbounded-structure gap
remains.** Per the program's analytic bar (§1 of A_HANDOFF): the finite
checks are NOT yet human-surveyable residues, so this does NOT yet claim an
analytic proof — what remains is hand-organization, now a bounded list:
  (a) comp-4-aliveness for light b (the one machine ingredient of (ii));
  (b) rigidity arguments replacing the 28-family enumeration — the
      δ-point/ψ-evaluation rigidity (a weight-1 layer is a δ-point whose
      component values are the point's character evaluations; co-point
      ideals are 1-parameter, fixing cross-layer evaluation ratios, hence
      pairwise point differences) kills whole bands at once: the 8
      A={1,1,1} families reduce to one lemma, etc.;
  (c) the two m-rung locality proofs (unchanged from E6).

### Next

1. Hand-organize (a)–(c). Suggested order: (b)'s δ-point rigidity lemma
   first (it carries the most families), then (a) via the cost-table LP,
   then (c).
2. Then assemble the full conditional factor-2 write-up (theorem +
   dependency tree), and revisit the recursion bookkeeping for goals 2/3.

---

## Entry 10 (2026-06-12) — hand-organization I: engine, floor, one-block, R1; six-shape architecture

First block of the hand-proof program replacing Entry 9's machine checks
(`a3_mb_rigidity.py` for the verifications G1–G4). Outcome: the load-bearing
chain for profile completeness is now FULLY hand-proven (the Entry-8
component-support DP is no longer needed anywhere), the analysis collapses
to SIX shape lemmas via a pivot-on-the-lighter-block architecture, and two
of the six (plus the shared engine and endgame) are proven by hand below.

### Dictionary lemma (hand proof, completing Entry 8's d₃ table)

For nonzero f ∈ F₂[Z₃²]: |f| mod 2 = f̂(trivial); weight-1 elements are
δ-points (full Fourier support); weight-2 elements are pairs δ_t + δ_t′
with support exactly the three nontrivial orbits not orthogonal to t − t′;
the three nonzero elements of a single-orbit ideal are the tr∘χ indicators,
weight 6; lines (cosets of order-3 subgroups) have weight 3 and support
{trivial, orthogonal orbit}; crossing-line pairs have weight 4 and support
two nontrivial orbits. These plus parity give every entry of the d₃ table:
(0,T)=9, (1,F)=6, (1,T)=3, (2,F)=4, (2,T)=3, (3,·)=2, (4,F)=2, (4,T)=1.

### Engine lemma (G1; hand proof)

Let D be any of the six radical multipliers Â₁, Â₃, Â₄, B̂₂, B̂₃, B̂₄. Its
value vector has three nonzero values, pairwise distinct, plus one zero —
so {values of αD} = all of F₄ for α ≠ 0. The ideal (D) = {αD + β·1⃗}
(1⃗ = uv = the constant vector), and:
- α = 0: the nonzero constant vectors — support FULL;
- α ≠ 0: β = αD[s₄] for exactly one layer s₄ — support exactly the
  CO-POINT Z₂² \ {s₄}, value vector α(D + D[s₄]1⃗): one F₄-line per s₄.
Hence: a full-support ideal element is CONSTANT; a co-point element has
fixed value ratios. Two corollaries used everywhere: (a) any nonzero
V_j^X (j radical on side X) has ≥ 3 nonzero layers; (b) on a block whose
nonzero layers are δ-points, V_j^X[s] = ψ_j(t_s), so constancy or ratio
rigidity translate into character equations on the cells t_s, and ψ₃, ψ₄
(or any two of the three radical characters) separate Z₃².

### One-block lemma (G2; hand proof)

If z′ ∈ Ann(A) \ ker ∂₂ then |Bz′| ≥ 12 (mirror: Ann(B), |Az′| ≥ 12).
Proof: ẑ′₀ = ẑ′₂ = 0 (units), ẑ′_j ∈ Ann(Â_j) = (Â_j) for j ∈ {1,3,4}
(the ideal is its own annihilator: D² = 0, D·1⃗ = 0, dimension count).
Then V′^B₄ = ωÂ₄ẑ′₄ = 0; V′^B₃ = B̂₃ẑ′₃ ∈ F₄·1⃗ (B̂₃Â₃ is a nonzero socle
multiple since the generators are non-proportional); V′^B₁ = B̂₁ẑ′₁ ∈ (Â₁).
So Bz′ has component support ⊆ {1, 3} with d₃({1}) = d₃({3}) = 6,
d₃({1,3}) = 4. If component 1 is alive its support has ≥ 3 layers, each of
cost ≥ 4: |Bz′| ≥ 12; if only component 3, all four layers cost 6 each:
≥ 24; if neither, Bz′ = 0 and z′ ∈ ker. ∎  (Exact minimum: 16, G2.)

### Floor lemma (hand proof — replaces the component-support dependency)

If b ≠ 0, |b| ≤ 10, then BOTH blocks have ≥ 3 nonzero layers. Suppose the
A-block has ≤ 2. Then every A-radical V_j^A has support ≤ 2, hence = 0
(engine (a)), so ẑ_{1,3,4} ∈ Ann(Â_j), giving V^B₄ = 0, V^B₃ ∈ F₄·1⃗,
V^B₁ ∈ (Â₁); also S₀ ⊆ (A-layers), so |S₀| ≤ 2.
- A-block = 0: w₀ = 0 and ẑ₂ = 0 (unit), so the B-side has components
  ⊆ {1,3}: the one-block lemma gives |b| = |Bz| ≥ 12. ✗
- A-block ≠ 0: its layers have W ⊆ {0,2}, cost ≥ 3 each, so |Az| ≥ 3. On
  the B-side: if component 3 is alive, V^B₃ is a nonzero constant, so ALL
  FOUR B-layers are nonzero at cost ≥ 2: |Bz| ≥ 8 and |b| ≥ 11 ⟹ 12 by
  evenness. If component 3 is dead and component 1 alive: ≥ 3 layers with
  W ⊆ {0,1,2}, at most two carrying the trivial flag: |Bz| ≥ 3+3+4 = 10,
  |b| ≥ 13. If 1 dead, 2 alive: ≥ 3 layers, W ⊆ {0,2}: ≥ 3+3+6 = 12. If
  1, 2, 3 all dead: B-block ⊆ component 0 on ≤ 2 layers: either Bz = 0
  (then z ∈ Ann(B) \ ker and the mirror one-block lemma gives
  |Az| ≥ 12 ✗) or |Bz| ≥ 9, |b| ≥ 12. ∎
**Profile completeness (parity + floor + evenness) is now fully
hand-proven.** The Entry-8 component-support lemma is demoted to a
corollary/confirmation; nothing load-bearing rests on the DP anymore.

### The six-shape architecture (pivot on the lighter block)

For |b| ≤ 10 both blocks have ≥ 3 nonzero layers, so the lighter block has
weight 3, 4 or 5; by the x↔y swap symmetry (A(x,y) = B(y,x)) take it to be
the A-block. Its layer profile is one of SIX shapes:
  weight 3: (1,1,1);  weight 4: (1,1,1,1), (2,1,1);
  weight 5: (2,1,1,1), (2,2,1), (3,1,1).
Each shape needs one lemma of the form "the f ∈ im(A·) of this shape are
exactly […], and their completions b = (B(z₀+z′), f) at |b| ≤ 10 are
exactly […]" — with the uniform ENDGAME: once f = A·g for an explicit
light generator g (monomial or pair), z − g ∈ Ann(A) and
|B(z − g)| ≤ |Bz| + |Bg| ≤ 7 + 4 < 12, so the one-block lemma forces
z ≡ g mod ker. Master data (G4, per translation class of im(A·)):

  shape    | im(A·) classes | min |f|+μ_B | light completions
  (1,1,1)  | 1  (= A·monomial)        | 6  | hexagons only
  (1,1,1,1)| 1  (the δ-column)        | 16 | none
  (2,1,1)  | 3  (= A·(dA-pairs))      | 10 | the dA D-pairs
  (2,1,1,1)| 1                        | 14 | none
  (2,2,1)  | 3                        | 14 | none
  (3,1,1)  | NONE in im(A·)           | —  | none
  [(2,2,1,1), weight 6, arises only as the HEAVIER block: 12 classes, of
   which exactly the 3 dB-pair classes complete to 10 — handled by the
   mirror of (2,1,1) on the B-side, never as a pivot shape.]

### R1 (shape (1,1,1)) — hand proof

Let the A-block be three δ-point layers (Az)_{s_i} = δ_{t_i}, fourth layer
zero. Every V_j^A is supported in {s₁,s₂,s₃} with V_j^A[s_i] = ψ_j(t_i) ≠ 0,
so for the A-radical j ∈ {1,3,4} the engine forces V_j^A = α_j C_j(s₄): the
ratios give ψ_j(t_i − t_k) = C_j(s₄)[s_i]/C_j(s₄)[s_k], explicit constants.
ψ₃, ψ₄ separate Z₃², so all pairwise differences t_i − t_k are determined
(and the comp-1 equations are a consistency condition); translating in s
(WLOG s₄ = [s_xs_y], where C_j = Â_j) and solving the two-character linear
system shows the unique solution is the difference pattern of A·δ_g — i.e.
f is a hexagon A-block. G3 confirms: the (1,1,1)-shaped elements of im(A·)
are EXACTLY the 36 A·δ_g. Endgame: z − δ_g ∈ Ann(A) and
|B(z − δ_g)| ≤ 7 + 3 < 12 ⟹ z ≡ δ_g mod ker: **b is a hexagon.** ∎
This kills all thirteen families with a {1,1,1} block.

### R-(1,1,1,1) — hand kill

A-block = four δ-point layers ⟹ all V_j^A (j ∈ {1,3,4}) are full-support
ideal elements ⟹ CONSTANT vectors (engine) ⟹ ψ_j(t_s − t_{s′}) = 1 for
all layers; ψ₃, ψ₄ separate ⟹ all t_s equal = t*: f is the δ-column
Σ_s δ_{(s,t*)} (the unique im(A·) class, G4). Its parities force S₀ = all
four layers, so the B-block is all-odd with |Bz| ≤ 6: profile (1,1,1,1) or
(3,1,1,1). For (1,1,1,1): the mirror argument makes the B-block a δ-column
at some t₀, so V₂^B, V₃^B, V₄^B are constants AND V₁^A = ψ₁(t*)·1⃗ ≠ 0;
but then ẑ₁ would satisfy both Â₁ẑ₁ = (nonzero const)·1⃗ and
B̂₁ẑ₁ = εẑ₁ = (const)·1⃗, forcing ẑ₁ ∈ F₄·1⃗ and hence Â₁ẑ₁ = 0 —
contradiction. For (3,1,1,1): the B-radical constants force the three
δ-layers of B at a common cell t₀ and the weight-3 layer P to satisfy
Σ_{t∈P} ψ_j(t) = ψ_j(t₀) for j ∈ {2,3,4}; then Q := P △ {t₀} is a nonzero
even set with Fourier support ⊆ {orbit 1}, |Q| ≤ 4 < 6 = d₃({1}) —
contradiction (dictionary). ∎  Kills the (1,1,1,1) families.

### Status & remaining obligations

Hand-proven as of this entry: dictionary, engine, one-block, floor
(⟹ profile completeness fully analytic), R1, R-(1,1,1,1).
Remaining shape lemmas (statements fixed, tools assigned, all
machine-confirmed via G4):
1. **R-(2,1,1)** (the D-pair lemma): 2-point-layer direction forcing —
   the layer's cell difference must avoid the three radical-character
   kernels (else an A-radical support drops to 2), leaving only the
   t_y-direction; then ratio rigidity as in R1 pins f to A·(dA-pair); the
   endgame closes at |b| = 10. Also its mirror covering the (2,2,1,1)
   heavier-block classes.
2. **R-(2,1,1,1)**: hybrid of R-(1,1,1,1) (three constants) + one 2-point
   layer; expect the same Q-style dictionary kill (G4: single class,
   μ-heavy).
3. **R-(2,2,1)**: one δ-layer + two 2-point layers; direction forcing on
   both pairs + ratio consistency (G4: 3 classes, all μ ≥ 14: kill).
4. **R-(3,1,1)**: show im(A·) has NO such element: the weight-3 layer is a
   line or a non-collinear triple; in either case some A-radical
   component vanishes on that layer (line: the orthogonal orbit among
   {1,3,4}; triple: the killed orbit), dropping its support to ≤ 2 while
   the δ-layers keep it nonzero — engine contradiction. (To write out:
   the only subtlety is triples whose dead orbit is the A-unit comp 2.)
Plus the two m-rung locality proofs (unchanged), and then the assembled
write-up. The G4 table is the complete specification of what each lemma
must produce.

## Entry 11 (2026-06-12) — hand-organization II: the D-pair lemma R-(2,1,1), via a sharpened one-block lemma

Second block of the hand-proof program (`a3_shape_lemmas.py`, checks V1–V5,
all PASS). Outcome: **R-(2,1,1) is fully hand-proven** — the (2,1,1)-shaped
elements of im(A·) are exactly the 108 A-blocks of dA-pairs, and their only
light completions are the dA D-pairs at |b| = 10. The endgame needed the
one-block floor raised from 12 to ≥ 14; the same case analysis gives the
exact 16. Three of the six shapes are now closed (R1, R-(1,1,1,1), R-(2,1,1)).

### C-table normalization (V1) — used by every remaining shape lemma

For an A-radical component j ∈ {1,3,4} write η_j := ψ_j((0,1)) (so η₁ = η₃ = ω,
η₄ = ω²; η³ = 1 and η² = 1 + η). The value vector of Â_j over the layers
(1, s_x, s_y, s_xs_y) is (1+η_j, 1, η_j, 0), so the rigid co-point vector
vanishing at s₄ = [1] is

    C_j([1]) = Â_j + Â_j[1]·1⃗ = (0, η_j, 1, η_j²),

and in general C_j(s₄)[s] = η_j^{e(s₄,s)} on the co-point, with exponents
e(s₄,s) ∈ {0,1,2} **independent of j** (translate the s₄ = [1] table). Two
consequences used throughout: (i) all C-ratios are powers of η_j with a
j-independent exponent, so a system "ψ_j(τ) = C-ratio_j for j ∈ {1,3,4}" is
automatically consistent and pins τ to a multiple of (0,1) (ψ₃, ψ₄ separate);
(ii) any cross-layer ratio equation reduces to η-power bookkeeping.

### Direction forcing (V2)

Let f ∈ im(A·) have a zero layer s₄ and a weight-2 layer s_P = {p, p+δ}, with
some δ-point layer elsewhere. Each radical V_j = f̂_j is a nonzero ideal
element vanishing at s₄, hence co-point-supported (engine) — so V_j[s_P] =
ψ_j(p)(1 + ψ_j(δ)) ≠ 0, i.e. δ ∉ ker ψ_j, **for all three j ∈ {1,3,4}**. The
kernels are the directions span(1,0), span(1,2), span(1,1); avoiding all three
leaves δ ∈ {(0,1), (0,2)}: **every weight-2 layer of a co-point shape runs in
the t_y direction**. (Mirror, B-side: radical j ∈ {2,3,4}, kernels span(0,1),
span(1,2), span(1,1); pairs run in t_x. Verified for the realized shapes.)

### R-(2,1,1): classification (V3)

Shape: pair layer s_P, two δ-point layers, zero layer s₄; translate s₄ = [1].
With δ = (0,1) (the (0,2) case is the same 2-set rebased) and e := (0,1):
1 + ψ_j(δ) = 1 + η_j = η_j², so the pair layer reads ψ_j(p)·η_j² and the
rigidity V_j = α_j C_j([1]) gives, per choice of s_P:

- **s_P = s_y**: V_j[s_x]/V_j[s_y] = η_j/1 forces ψ_j(a−p)·η_j⁻² = η_j,
  i.e. ψ_j(a−p) = η_j³ = 1 ⟹ a = p; V_j[s_xs_y]/V_j[s_x] = η_j ⟹ c = a + e.
  Pattern `(s_x: a) (s_y: {a, a+e}) (s_xs_y: a+e)`.
- **s_P = s_x**: ψ_j(p−b) = η_j² ⟹ p = b + 2e, then c = b + 2e = p. Pattern
  `(s_x: {p, p+e}) (s_y: p+e) (s_xs_y: p)`.
- **s_P = s_xs_y**: ψ_j(p−b) = 1 ⟹ p = b, a = b + e. Pattern
  `(s_x: b+e) (s_y: b) (s_xs_y: {b, b+e})`.

Every equation is of the uniform form ψ_j(τ) = η_j^k, so the j = 1 line is
automatically consistent (C-table consequence (i)) and no arrangement dies —
in each, the solution is unique up to the base cell (9 t-translates). All
three patterns sit inside a **single t_y-fibre** {t, t+e, t+2e}. Conversely
each pattern is realized: A(δ_g + δ_{gd}) for d = y, x³y², x³y respectively
(direct expansion; e.g. A(δ₀+δ_y) = x³ + y + y³ + x³y is the s_P = s_y
pattern). Verified (V3): the (2,1,1) elements of im(A·), the 36·3 pattern
translates, and the 108 dA-pair A-blocks are **the same set**. Moreover
dA ∩ dB = ∅, so every dA-pair has block weights (|A·p|, |B·p|) = (4, 6).

### Sharpened one-block lemma: |Bz′| ≥ 16 on Ann(A) \ ker (V4)

Entry 10's one-block lemma gave ≥ 12; the D-pair endgame needs > 12, and the
same component analysis yields 16 with one more split. For z′ ∈ Ann(A) \ ker:
V₀ = V₂ = V₄ = 0, V₃ ∈ F₄·1⃗ (socle), V₁ ∈ (Â₁) with support ∅/co-point/full
(engine). Cases (layer costs from the d₃ table; W_s ⊆ {1,3} throughout since
the parity component is dead):
- **V₃ ≠ 0** (a nonzero constant): all four layers have orbit 3 alive.
  V₁ full: four layers of W = {1,3}, cost ≥ 4 each: **≥ 16**.
  V₁ co-point: three layers at 4 plus one at d₃({3}) = 6: ≥ 18.
  V₁ = 0: four layers at 6: ≥ 24.
- **V₃ = 0**: Bz′ ≠ 0 forces V₁ ≠ 0; its ≥ 3 alive layers have W = {1},
  d₃({1}) = 6 each: ≥ 18 (co-point) or ≥ 24 (full).
Minimum over all cases: **16**, attained (V4: per-case minima 16/18/24/18/24
match the case bounds exactly; exhaustive min = 16 = G2). Mirror statement
for Ann(B) \ ker by the x↔y swap. ∎

### Endgame: the light completions of a dA-pair are exactly the D-pairs (V5)

Let f = A·p be one of the 108 classified blocks (p = δ_g + δ_{gd}, d ∈ dA) and
z = p + z′ any completion (z′ ∈ Ann(A)) with |b| = |Bz| + 4 ≤ 10. Then
|Bz′| ≤ |Bz| + |Bp| ≤ 6 + 6 = 12 < 16, so z′ ∈ ker by the sharpened one-block
lemma: z ≡ p mod ker, b is **the** D-pair of p, and |b| = 6 + 4 = 10 exactly.
(V5: per class, the completions with |Bz| ≤ 6 are exactly the 64 kernel
translates, all with Bz = Bp; the non-kernel minimum is 12 — which is why the
12-floor of Entry 10 was not enough and 14 was the real threshold.)

**R-(2,1,1) is closed.** Consequences of the pivot architecture: a light b
whose lighter block has weight 4 is either killed (shape (1,1,1,1), Entry 10)
or is a dA-pair (this entry); the x↔y swap covers lighter-B-blocks, i.e. the
dB-pairs — this is the promised "mirror of (2,1,1)" that handles the twelve
(2,2,1,1) heavier-block classes without ever pivoting on a weight-6 shape.

### Status

Hand-proven so far: dictionary, engine, one-block (now ≥ 16), floor, R1,
R-(1,1,1,1), **R-(2,1,1) + endgame**. Remaining: the three weight-5 kills
R-(2,1,1,1), R-(2,2,1), R-(3,1,1) (next entry), then the two m-rung locality
proofs, then the assembled write-up.

## Entry 12 (2026-06-12) — hand-organization III: the weight-5 kills; light-b classification fully hand-proven

Final block of the shape-lemma program (`a3_shape_lemmas.py`, checks V6–V8,
all PASS — same script as Entry 11). Outcome: **R-(3,1,1), R-(2,1,1,1) and
R-(2,2,1) are killed by hand**, so all six pivot shapes are closed and the
light-stabilizer classification — every b ∈ Stab_Z(base) with 0 < |b| ≤ 11
is one of the 36 hexagons or 216 D-pairs — is **fully hand-proven**, with no
machine ingredient left anywhere in the chain.

### The comp-1 transfer operator (the new shared tool, V7)

B̂₁ = 1 + u + v is a self-inverse unit, so on component 1 the two blocks are
locked together: V₁ᴬ = T·V₁ᴮ with **T := Â₁·B̂₁⁻¹ = Â₁(1+u+v)**. Direct
expansion gives T = u + ωv + (1+ω)uv, whose value vector is exactly
C₁([1]) = (0, ω, 1, ω²) — and T·1⃗ = 0 (it lies in the radical ideal). Two
consequences: T kills constant vectors, and T·δ_σ is the co-point vector
vanishing at layer σ. So whenever the B-side pins V₁ᴮ to a constant-plus-spike
shape, the A-side value V₁ᴬ is forced to a co-point with a *prescribed* zero —
one comparison with the A-side classification then kills the configuration.

### R-(3,1,1): im(A·) has no such element (V6)

Layers: weight-3 layer P at s_T, two δ-point layers, zero layer s₄. Each
radical V_j (j ∈ {1,3,4}) is co-point (nonzero at the δ-layers, zero at s₄),
so V_j[s_T] ≠ 0 is forced for all three.

- **P a line** {p, p+g, p+2g}: V_j[s_T] = ψ_j(p)(1 + ψ_j(g) + ψ_j(2g)) = 0
  unless the orbit j is orthogonal to g. Only one orbit class is, so at least
  two of {1,3,4} die at s_T. ✗
- **P a triangle** {p, p+g, p+h} (g, h independent): with
  κ_j := 1 + ψ_j(g) + ψ_j(h), κ_j = 0 ⟺ {ψ_j(g), ψ_j(h)} = {ω, ω²}
  ⟺ (j·g, j·h) ∈ {(1,2), (2,1)}; since j ↦ (j·g, j·h) is a bijection from
  functionals to Z₃², **exactly one orbit class is dead**, and it can be any
  of the four. Dead ∈ {1,3,4}: support kill as above. ✗
- **Dead = comp 2** (the A-unit — the subtle family): all radical supports
  survive, so the kill must come from rigidity. The ratio system
  ψ_j(p − t₁)·κ_j = C-ratio_j (j ∈ {1,3,4}) is solvable only if the values
  respect the character relation ψ₄ = ψ₁·ψ₃; the C-ratios do respect it
  (Cr₄ = Cr₁·Cr₃, by the j-independent exponents and η₁η₃ = η₄), so
  solvability forces **κ₄ = κ₁·κ₃**. This is base-point-invariant (rebasing
  scales both sides by ψ₄), and the 6-case enumeration of dead-2 triangles
  (gₓ = 1, hₓ = 2, the six non-collinear (g_y, h_y)) shows it **never
  holds** (V6 table). ✗

So im(A·) has no (3,1,1) element; by the x↔y swap neither does im(B·) — the
fact the other two kills lean on. (V6 cross-check: direct enumeration finds
0 and 0.)

### R-(2,1,1,1): classification, then the kill (V7)

*Classification.* All four layers alive, so radical supports are co-point or
full; the three δ-layers keep every V_j nonzero on ≥ 3 layers. The pair
difference δ lies in at most one radical kernel:

- δ in **no** radical kernel (t_y direction): all three V_j full ⟹ constant
  (engine) ⟹ the three δ-cells coincide at t*, and the pair-layer equation
  ψ_j(p)·η_j² = ψ_j(t*) gives ψ_j(p − t*) = η_j for all j ⟹ p = t* + (0,1).
  Pattern: **δ-cells t* on three layers, pair {t*+e, t*+2e} on the fourth** —
  again a single t_y-fibre; one translation class, 36 elements (V7: equals
  the enumerated set).
- δ in **exactly one** radical kernel j₀: the other two V_j are full ⟹
  constant ⟹ the three δ-cells coincide; but then V_{j₀} takes the *same*
  value on the three δ-layers, while a co-point vector takes three *pairwise
  distinct* values there (C-table). ✗

*Kill.* A completion with |b| ≤ 10 has |Bz| = 5 (lighter-block pivot) and
shares layer parities: S₀ = the three δ-layers. A weight-5 block with ≥ 3
alive layers and exactly three odd ones is (3,1,1) (zero layer at s_P) or
(2,1,1,1) (pair at s_P):

- B-block (3,1,1): impossible — no (3,1,1) element of im(B·) (above).
- B-block (2,1,1,1): the mirror classification pins it to δ-cells t₀ on the
  three S₀-layers and a t_x pair {t₀+eₓ, t₀+2eₓ} at s_P. Then ψ₁ kills the
  t_x pair (ψ₁(eₓ) = 1), so V₁ᴮ = ψ₁(t₀)·(1⃗ + δ_{s_P}), and the transfer
  gives V₁ᴬ = ψ₁(t₀)·T·(1⃗ + δ_{s_P}) = ψ₁(t₀)·shift_{s_P}(T): a co-point
  vector **vanishing at s_P**. But the A-side classification makes V₁ᴬ the
  nonzero *constant* ψ₁(t*)·1⃗ — full support. ✗

(V7: the completion minimum is |Bz| = 9, i.e. |f| + μ_B = 14 — the kill with
a 4-unit margin.)

### R-(2,2,1): classification, then the kill (V8)

*Classification.* Zero layer s₄ ⟹ co-point rigidity; direction forcing
(Entry 11) puts **both** pairs in the t_y direction (each pair layer is in
every radical co-point support). Writing the δ-layer cell as t, the same
η-power bookkeeping as in Entry 11 forces each pair layer to {t, t + k·e}
where η^k = C(s_δ)/C(s_pair) — concretely, the three nonzero layers carry
{t}, {t, t+e}, {t, t+2e} in an order determined by the arrangement. Three
translation classes (relative position s_δ − s₄), 108 elements, all inside
a single t_y-fibre (V8: equals the enumerated set; fibre check passes).

*Kill.* A completion with |b| ≤ 10 has |Bz| = 5 with exactly **one** odd
layer, at s_δ (parity matching: S₀ = {s_δ}). The only weight-5 layer profile
with one odd part and ≥ 3 alive layers is {1, 2, 2} — so the B-block is
(2,2,1) with its δ-layer at s_δ, and the mirror classification puts its two
pairs in the t_x direction. ψ₁ kills both t_x pairs, so V₁ᴮ = ψ₁(t′)·δ_{s_δ}
and the transfer gives V₁ᴬ = ψ₁(t′)·shift_{s_δ}(T): a co-point vector
vanishing at **s_δ**. But the A-side rigidity makes V₁ᴬ = α₁·C₁(s₄), which
vanishes at **s₄** and is nonzero at s_δ (it equals ψ₁(t_δ) there). ✗

(V8: completion minimum |Bz| = 9 for every class — again margin 4.)

### Milestone: the classification rung is fully analytic

Assembling the pivot architecture (all pieces now hand-proven): for
b ∈ Stab_Z(base) with 0 < |b| ≤ 11, evenness gives |b| ≤ 10; parity + floor
give both blocks ≥ 3 alive layers, so the lighter block (WLOG the A-block,
by the x↔y swap) has weight 3, 4 or 5 and shape among the six;

- (1,1,1) ⟹ b is a hexagon (R1 + endgame, |b| = 6);
- (2,1,1) ⟹ b is a dA D-pair (Entry 11, |b| = 10); the swap covers dB;
- (1,1,1,1), (2,1,1,1), (2,2,1), (3,1,1) ⟹ no light b at all.

**Theorem (light-stabilizer classification, hand-proven).** Every nonzero
b ∈ Stab_Z(base) with |b| ≤ 11 is one of the 36 hexagons (|b| = 6) or the
216 D-pairs (|b| = 10). In particular the minimum nonzero stabilizer weight
is 6, and there are no stabilizers of weight 8.

The Entry-8 component-support DP and the Entry-9 28-family hash-join are now
*entirely* demoted to numerical confirmations. Dependency chain of the
theorem: dictionary + engine + one-block(16) + floor + parity + evenness
(Entries 8–11) + the six shape lemmas (R1, R-(1,1,1,1): Entry 10; R-(2,1,1) +
endgame: Entry 11; the three weight-5 kills: this entry). Everything sits on
explicit F₄[Z₂²] computations a referee can check line by line.

### Status

Remaining for the conditional factor-2 theorem (M): the two m-rung locality
proofs — m(hexagon) ≥ 3 (no non-imΔ cycle in hexagon+2 qubits) and
m(D-pair) ≥ 1 (cycle space of the 11-qubit pair union) — then the assembled
write-up with the full dependency tree, and the recursion bookkeeping
(Entry 4's caution) for what the factor-2 statement yields downstream.

## Entry 13 (2026-06-12) — the small-cycle theorem: m-rungs closed AND (H0) discharged

Working the two owed m-rung locality proofs forced a stronger statement, and
the stronger statement is *better*: it has a clean hand proof, it closes both
rungs in two lines each, and it **proves (H0) — the d_base ≥ 6 transfer
input — outright**, removing the last hypothesis of the conditional theorem.
All intermediates machine-verified in `a3_small_cycles.py` (W1–W9, all PASS).

### Theorem (no small cycles)

**Every nonzero 1-cycle u = (u_L, u_R) ∈ ker H_X of the base [[72,12,6]]
code has |u| ≥ 6. The same holds for ker H_Z.** (W6: exhaustive hash-join
over all weight splits a + b ≤ 5 finds zero solutions on both sides;
W7 census: exactly 120 weight-6 cycles = 36 hexagons + 84 logicals,
matching T4.)

*Proof.* A cycle satisfies A·u_L = B·u_R =: σ over F₂[Z₆²]. Split by
(|u_L|, |u_R|), using |A·f| ≡ |f| and |B·f| ≡ |f| (mod 2) (odd generator
weights), which forces |u_L| ≡ |u_R| (mod 2) and kills the splits
(1,2), (2,1), (2,3), (3,2), (1,4), (4,1).

- **(k,0) and (0,k), k ≤ 5** — u_L ∈ Ann(A) (resp. u_R ∈ Ann(B)) nonzero.
  Engine: the unit components force ẑ₀ = ẑ₂ = 0, the radical components lie
  in the self-annihilating ideals (Ann(Â_j) = (Â_j)), so a nonzero element
  has ≥ 3 alive layers (co-point-or-full) and all layers even (ẑ₀ = 0):
  weight ≥ 6, and even. (W1: exact minima 6, all weights even — kills
  (5,0)/(0,5) by parity too.)
- **(1,1)** — A·g = B·r forces the two translate 3-sets to coincide, hence
  their difference sets: dA = dB. But dA ∩ dB = ∅. ✗ (W3.)
- **(1,3) and (3,1)** — |B·z| = 3 for a 3-set z requires (inclusion–
  exclusion with ov ≤ 1) all three pairs of columns to overlap with **no**
  common triple cell: z is a dB-triangle with distinct overlap cells.
  dB-triangles form one translation+reflection class (W4): the chirality
  rep {0, (1,0), (2,3)} has a common triple cell, |B·z| = 7 ✗; the other,
  {0, (1,0), (5,3)}, gives B·z = a translate of y³(1 + x² + x⁴) — three
  cells with the **same y-coordinate**. But A·g has y-coordinates
  g_y + {0,1,2}, pairwise **distinct**. ✗ Mirror for dA-triangles
  (constant-x image vs. the three distinct x-coordinates of B·r). ✗
- **(2,2)** — write π_x, π_y for the coordinate projections (ring
  homomorphisms onto F₂[Z₆]): π_y(A) = 1+y+y², π_y(B) = y³, π_x(A) = x³,
  π_x(B) = 1+x+x². Two sub-cases by |σ|:
  - **|σ| = 4** (both pairs overlapping): ℓ-diff ∈ dA, r-diff ∈ dB.
    Matching |π_y(σ)| forces the ℓ-pair's y-gap to be 1 (the (3,±2) diffs
    give weight 4 vs. ≤ 2) and the r-pair's y-gap to be 3. If
    ℓ-diff = (0,±1): π_x(u_L) = 0, so (1+x+x²)·π_x(u_R) = 0 with
    |π_x(u_R)| ≤ 2 < 4 = min wt Ann(1+x+x²) (W5) ⟹ r_x-gap 0 ⟹
    r-diff = (0,3) ∉ dB. ✗ If ℓ-diff = ±(3,1): matching |π_x| forces
    r-diff = ±(1,3); then up to translation σ = A(1+x³y), whose
    x-coordinate multiplicity multiset is {3,1}, while B(1+xy³) has
    {2,1,1} — translation-invariant mismatch. ✗ (W5.)
  - **|σ| = 6** (both pairs disjoint): ℓ-diff ∉ dA, r-diff ∉ dB. If the
    ℓ-pair has y-gap 0: π_y(u_R) = 0 forces r_y-gap 0, and matching
    |π_x| = 2 forces r_x-gap ±1, i.e. r-diff = (±1,0) ∈ dB. ✗ If y-gap
    ±1: ℓ-diff = (e,±1) with e ∈ {1,2,4,5}; π_y forces r-diff = (f,3)
    with f ∈ {0,3}; then |π_x(σ)| = 2 from the left but 0 (f = 0) or 6
    (f = 3) from the right. ✗ y-gaps ±2, 3 die on |π_y| alone (4 or 6
    vs. ≤ 2). ✗

All splits dead; weight-5 splits die by parity and Ann-evenness. The ker H_Z
side follows by the inversion duality below (and was checked directly, W6). ∎

### Corollary 1: (H0) is a theorem — d(base [[72,12,6]]) ≥ 6, analytically

A nontrivial Z-logical is in particular a nonzero 1-cycle: d_Z(base) ≥ 6.
**The transfer input (H0) is no longer a hypothesis.** (Sharpness: the
classification says weight-6 stabilizers are exactly hexagons, so *any*
weight-6 non-hexagon cycle is a nontrivial logical; the census finds 84 —
exhibiting one explicitly makes d_Z(base) = 6 a hand fact too.)

### Corollary 2: the m-rungs (the last two owed local facts)

- **m(hexagon) ≥ 3.** Let b = ∂₂δ_g, supp b = h(g). Since
  supp(d2c_j δ_g) ⊆ h(g) (the seam split is entrywise, W8), m(b) =
  min |u′ off h(g)| over cycles u′ with [u′] ∉ imΔ. If |u′ off h| ≤ 2:
  replace u′ by u′ + b if needed so that |u′ ∩ h| ≤ 3; the new rep has
  weight ≤ 3 + 2 = 5 < 6, hence is 0 — but then [u′] = 0 ∈ imΔ. ✗
- **m(D-pair) ≥ 1.** b = ∂₂(δ_g + δ_{g′}), supp(d2c_j z_b) ⊆ h ∪ h′ =
  supp b ∪ {q*} (q* the unique overlap qubit, W8). If m(b) = 0, some
  cycle u′ with [u′] ∉ imΔ is supported in the 11-qubit union. Write
  u′ = (P, P′, ε) over the regions (h\h′, h′\h, {q*}) and average over the
  coset {u′, u′+b₁, u′+b₂, u′+b₁+b₂} (b_i the two hexagons): the four
  weights sum to 5+5+5+5+2 = 22 < 4·6, so some rep has weight ≤ 5, hence
  = 0 — but then u′ ∈ span{b₁, b₂} and [u′] = 0. ✗

With Entry 12's classification this **completes every rung of (M)**:
m(0) ≥ 6 (Corollary 1 — a non-imΔ class is nonzero); hexagons 6 + 2·3 ≥ 12;
D-pairs 10 + 2·1 ≥ 12; |b| ≥ 12 trivial; no other light b exists.
**(M) is proven: |b| + 2m(b) ≥ 12 for every base Z-stabilizer b — with no
hypothesis left.**

### Corollary 3: the inversion duality d_X = d_Z (any BB code)

Inversion ι(g) = g⁻¹ is an algebra automorphism for ANY abelian group —
including the cover group Z₁₂×Z₆. The map Φ(w_L, w_R) := (ι(w_R), ι(w_L))
sends ker H_Z bijectively to ker H_X (apply ι to B̄w_L + Āw_R = 0) and the
X-stabilizer row space onto the Z-stabilizer column space
(Φ(row g of H_X) = ∂₂δ_{g⁻¹}), preserving weight. Hence **d_X = d_Z for the
base and for gross** (W9: verified for both). The separate ker H_Z
small-cycle check (W6) independently confirms the base case.

### Status

The factor-2 ladder (M) is fully proven, unconditionally. Next entry
assembles the consequence — the first fully-analytic distance bound on
gross beating the published floor — with its complete dependency tree.

## Entry 14 (2026-06-12) — assembly: d(gross) ≥ 6, fully analytic — the floor is beaten

Putting Entries 5–13 together yields the program's first headline result.

### Theorem (analytic gross bound)

**d(gross [[144,12,12]]) ≥ 6, by a fully analytic proof** — no SAT, no
`decide`, no enumeration anywhere in the load-bearing chain; every finite
case split in the proofs is human-surveyable (≤ a dozen lines each).

*Proof.* d = min(d_X, d_Z) = d_Z by the inversion duality (Entry 13,
Cor. 3). Let v be a nontrivial Z-logical of the cover.

- **Safe sector** (pr_*[v] ≠ 0): p is a weight-non-increasing chain map, so
  |v| ≥ |p(v)|, and p(v) is a *nonzero* base 1-cycle, so the small-cycle
  theorem (Entry 13) gives |v| ≥ 6.
- **Dangerous sector** (pr_*[v] = 0): b := p(v) ∈ Stab_Z(base), and the
  Entry-5 sheet identity gives |v| = |b| + 2·|v₀ off supp b| with
  v₀ = d2c_j z_b + u′, [u′] ∉ imΔ — so |v| ≥ |b| + 2·m(b) ≥ 12 by **(M)**,
  now fully proven (Entries 6–13).

min(6, 12) = 6. ∎

This **triples the published analytic floor** (Lin–Pryadko ⌈12/8⌉ = 2) and
achieves **goal 3** of the program. It also proves d(base [[72,12,6]]) ≥ 6
(Entry 13, Cor. 1) — to our knowledge the first analytic distance bound
matching the true distance for a Bravyi-family BB code (A1-L3 found no
analytic distance proofs in the literature for any of these).

### Complete dependency tree (every leaf hand-proven; scripts are confirmation only)

```
d(gross) ≥ 6
├── d_X = d_Z: inversion duality Φ                      [E13 Cor.3; W9]
├── SAFE ≥ 6: p weight-non-increasing (SRB safe branch) [E0/E5]
│   └── small-cycle theorem (min nonzero cycle ≥ 6)     [E13; W1–W7]
└── DANGEROUS ≥ 12:
    ├── sheet identity |v| = |b| + 2|v₀ off b|          [E5; a3_mb_foundations V1–V8]
    │   └── cover block form + SES + Smith Δ            [E0/E5; a3_cut_decomposition,
    │                                                    a3_delta_explicit]
    └── (M): |b| + 2m(b) ≥ 12 for all b ∈ Stab_Z:
        ├── b = 0: m(0) ≥ 6 ← small-cycle theorem       [E13]
        ├── 0 < |b| ≤ 11 ⟹ hexagon or D-pair:
        │   ├── parity + floor + evenness               [E9/E10]
        │   ├── dictionary + engine + one-block(16)     [E10/E11]
        │   └── six shape lemmas                        [E10 (R1, R-(1,1,1,1)),
        │                                                E11 (R-(2,1,1) + endgame),
        │                                                E12 (weight-5 kills)]
        ├── m(hexagon) ≥ 3, m(D-pair) ≥ 1               [E13 Cor.2]
        └── |b| ≥ 12: trivial
```

Machine confirmations: `a3_mb_foundations.py`, `a3_mb_rigidity.py` (G1–G4),
`a3_shape_lemmas.py` (V1–V8), `a3_small_cycles.py` (W1–W9), plus the
end-to-end SAT crosschecks `a3_mb_crosscheck.py` (C1: dangerous b≠0 min 14;
C2: imΔ-distance 12) — all consistent with the bound (true d = 12 ≥ 6; the
dangerous bound 12 is *tight*, attained by the τ(u) reps).

### Honest scoreboard and the next frontier

- **Goal 3 (beat the floor): ACHIEVED** — pending one round of adversarial
  re-review next session (the discipline: a fresh skeptic pass over the two
  newest links, the Entry-5 reduction and the Entry-13 case analysis,
  before any external write-up).
- **Goal 1 (d = 12): the dangerous side is DONE and tight.** The safe
  sector now caps the bound: |v| ≥ |p(v)| alone cannot beat 6 because
  weight-6 base logicals exist. But pointwise
  |v| = |p(v)| + 2|v₀ ∧ v₁| — the slack is the sheet overlap, and SAT says
  the true safe minimum is ≥ 12. So the precise remaining problem for
  goal 1 is a **safe-sector analogue of (M)**: for w a nontrivial base
  logical cycle, every cover cycle v with p(v) = w has
  |w| + 2|v₀ ∧ v₁| ≥ 12. The same slice machinery applies (v₀ ranges over
  a syndrome-shifted coset); this is where the old "s ≠ 0" structure
  returns, now in its correct home.
- **Goal 2 (a class of BB codes): the machinery is a template.** The
  small-cycle engine analysis used only: the CRT component structure of
  F₂[Z₆²], multiplicity-free difference sets with dA ∩ dB = ∅, and the
  x/y projections. Each ingredient is checkable per BB instance; running
  the template on the other Bravyi bases (and odd-h SRB covers, e.g.
  bb_90/bb_108 with k′ = 8) is now mechanical exploration.

### Next steps (ranked)

1. Adversarial re-review of the full chain (fresh session, skeptic mode).
2. Standalone write-up note (theorem + dependency tree + the surveyable
   case tables) — the deliverable form of the result.
3. Safe-sector (M)-analogue for goal 1 (d = 12).
4. Template run on other BB bases for goal 2.
