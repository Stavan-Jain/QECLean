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
