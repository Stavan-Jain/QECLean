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

### Addendum (same day): the minimal proof — Fork B resurrected

The small-cycle theorem makes the headline bound much cheaper than the full
chain suggests. Fork B (Entry 4) was killed because its ingredients
d_base ≥ 6 and μ_Z ≥ 6 were SAT-only and recursing down the tower degraded
them; **both are now corollaries of the small-cycle theorem directly** (a
nonzero stabilizer is a nonzero cycle), with no recursion. The half-page
proof of d(gross) ≥ 6: for v a nontrivial cover Z-logical, either p(v) ≠ 0
— a nonzero base cycle, so |v| ≥ |p(v)| ≥ 6 (uniformly over the safe sector
AND the dangerous b ≠ 0 slices) — or p(v) = 0, where the Entry-5 slice
formula gives v = τ(v₀)-form with v₀ a nonzero cycle ([v₀] ∉ imΔ), so
|v| = 2|v₀| ≥ 12; finish with d_X = d_Z. The classification and (M) are NOT
needed for ≥ 6 — their value is the **tight dangerous bound ≥ 12**, which
is exactly the asset goal 1 builds on. The write-up should lead with the
minimal proof and present (M) as the deeper theorem. (Entry 4's dead-end
verdict on Fork B is amended accordingly — the objection was to the tower
recursion, not the bound; A_HANDOFF §5.1 updated.)

## Entry 15 (2026-06-12) — adversarial re-review: the d(gross) ≥ 6 chain HOLDS

The owed skeptic pass (A_HANDOFF §0/§8 item 1), done in a fresh session under
the standing rules: computation may refute but never prove; the SAT-validated
endpoints are not attack targets; every load-bearing machine check was
**re-implemented independently** (`scripts/a3_adv15_recheck.py`, 49 checks,
all PASS) on a deliberately different encoding path — y-major indexing vs the
lab's x-major, int-bitmask F₂ algebra vs numpy, direct-solve image membership
vs dual-nullspace dots, a generator-side SAT hunt vs the layer-profile
hash-join, own CRT frame (mod-2/mod-3 split, own F₄ tables) with the
transform multiplicativity itself re-verified on the δ-basis. In parallel,
every prose argument in the chain was re-derived by hand. Per-link verdicts:

### Link 1 — the Entry-5 slice reduction: **HOLDS**

- **Both inclusions** of "v₀ ranges exactly over d2c_j·z_b + {u′ ∈ Z₁ :
  [u′] ∉ imΔ}" re-derived. (⊆): v = τ(u) + ∂₂^cov w with z = z_b + ζ gives
  v₀ = d2c_j z_b + u″, u″ := u + d2c_jζ + ∂₂w₀ a cycle with [u″] = [u] +
  Δ_j[ζ], so the ∉-imΔ condition is preserved. (⊇): given u′, take u := u′,
  w := z_b placed entirely on sheet 1 (w₀ = 0); then v₀ = d2c_j z_b + u′ and
  p(v) = b. The correspondence v ↔ v₀ is weight-faithful since v₁ = v₀ + b
  (block form), so the slice minimum transfers exactly.
- **Nontriviality bridge**: v = τ(u) + ∂₂^cov w is trivial ⟺ τ(u) ∈
  im ∂₂^cov ⟺ [u] ∈ ker tr_\*, and ker tr_\* = im Δ_j is Smith exactness.
  Re-verified EXACTLY (basis-level, not sampled): U0 := {u ∈ Z₁ : τ(u) ∈
  im ∂₂^cov} equals im Δ_j + Stab for every cut j (AV4) — the lab's V5/V8
  were sampled (200 random + 120 random); the exact check is strictly
  stronger and passes.
- **Boolean identity**: |x| + |x+b| = |b| + 2|x off supp b| is two-line
  algebra (on supp b the two sheets contribute 1 per coordinate; off it,
  2·x_q); it is applied to the correct restriction (off-supp of the SAME b
  = p(v)). m(b) is well-defined (z_b-choice shifts absorb into the ζ-twist).
- Foundations re-verified exactly: block form [[nc,c],[c,nc]] with
  nc + c = base for H_X AND H_Z, all 6 cuts; dangerous space = τ(Z₁) +
  im ∂₂^cov, dim 72 (exact rref equality).

### Link 2 — the Entry-13 small-cycle case analysis: **HOLDS**

- **Exhaustiveness of the split list**: |σ| ≡ |u_L| ≡ |u_R| (mod 2) via the
  augmentation homomorphism (|A|, |B| odd) kills every odd-vs-even split;
  what remains of a + b ≤ 5 is exactly (k,0)/(0,k), (1,1), (1,3)/(3,1),
  (2,2) — the prose list is complete.
- **(k,0)**: Ann(Â_j) = (Â_j) re-proven by hand in F₄[u,v]/(u²,v²)
  ((u+ηv)·(δ+αu+βv+γuv) = δu + δηv + (αη+β)uv forces δ = 0, β = αη) and
  re-verified by 256-element ring enumeration, both sides (AV6). The
  ≥ 3-layers-all-even ⟹ ≥ 6-and-even conclusion follows; odd k dies by
  parity.
- **(1,1)**: equal translate 3-sets ⟹ dA = dB, contradicting dA ∩ dB = ∅ ✓.
- **(1,3)/(3,1)**: the inclusion–exclusion behind "|B·z| = 3 ⟺ dB-triangle
  with three DISTINCT pairwise-overlap cells" re-derived (common triple cell
  ⟹ |B·z| = 7); both triangle classes re-enumerated independently; the
  constant-y vs three-distinct-y kill checks out (AV2).
- **(2,2)**: the full π_x/π_y bookkeeping re-derived by hand, including the
  WLOGs the prose leaves implicit: pair differences are only defined up to
  sign (unordered 2-sets), so the sign reductions are free; the
  x-multiplicity multiset is translation-invariant, so the σ = A(1+x³y)
  normalization is legitimate. Every sub-branch closes: |σ| = 4 with ℓ-diff
  (0,±1) via Ann(1+x+x²) min weight 4; ℓ-diff ±(3,1) via {3,1} ≠ {2,1,1};
  |σ| = 6 over all ℓ y-gaps 0, ±1, ±2, 3. Intermediates re-verified (AV2).
- **The theorem itself**: exhaustive meet-in-middle with the independent
  encoding — zero nonzero cycles of weight ≤ 5 in ker H_X AND ker H_Z;
  weight-6 census = 120 (AV2).

### Link 3 — Entries 10–12 (classification architecture): **HOLDS** (two notes)

- **Pivot exhaustiveness**: evenness (|b| ≡ 2|z| ≡ 0), the parity lemma
  (A and B have the same s-part multiset {1, s_x, s_y} — re-derived from the
  monomials), and the floor (both blocks ≥ 3 alive layers — every branch of
  the Entry-10 case walk re-checked against the d₃ costs) leave lighter-block
  weight ∈ {3,4,5}; the six shapes are precisely the partitions into ≥ 3
  parts on ≤ 4 layers; the x↔y swap σ(A) = B makes the lighter-block-=-A
  pivot a genuine WLOG (it permutes the hexagon/D-pair families).
- **Classification end-result hunted independently** (AV3, generator-side
  SAT, blind to the shape machinery): weights 1–5, 7–9, 11 UNSAT; weight 6
  = exactly the 36 hexagons; weight 10 = exactly the 216 D-pairs.
- **One-block ≥ 16** case analysis re-walked (V₃/V₁ support splits × d₃
  costs give 16/18/24/18/24) and the exact min 16 re-verified independently
  on BOTH mirrors (4096-element span sweeps). The D-pair endgame needs only
  > 12 (|Bz′| ≤ |Bz| + |Bp| ≤ 12), so 16 closes it with margin; the light
  completions are exactly the 64 kernel translates per class (AV6).
- **Weight-5 kills**: the B-block profile splits re-derived and exhaustive
  (R-(2,1,1,1) completions: {(3,1,1), (2,1,1,1)}; R-(2,2,1): {1,2,2} only);
  the comp-1 transfer kills re-derived (T = Â₁B̂₁⁻¹ has value vector
  C₁([1]), kills constants, shifts δ's); the R-(3,1,1) κ-consistency
  necessity re-derived from ψ₄ = ψ₁ψ₃ and η₁η₃ = η₄, and all 12 dead-2
  triples violate κ₄ = κ₁κ₃ (AV6).
- **Note 1 (presentational, no gap)**: in R-(1,1,1,1)'s (3,1,1,1) sub-case,
  "the B-radical constants" compresses a three-step derivation that the
  write-up should spell out: (i) V₃ᴮ, V₄ᴮ are constants via the A-side socle
  transfer (Â₄ ∝ B̂₄; B̂₃Â₃ = ω·uv), (ii) ψ₃, ψ₄ separate ⟹ the three
  δ-cells coincide at t₀, (iii) V₂ᴮ then cannot be co-point (a co-point
  takes pairwise-distinct C-values on the three δ-layers, which now carry
  the EQUAL values ψ₂(t₀)) ⟹ constant, giving the j = 2 relation. In fact
  the A-side forces V₂ᴮ = 0 outright (ẑ₂ = ψ₂(t*)·uv is pinned by the unit
  Â₂, and B̂₂·socle = 0), which contradicts the δ-layers immediately — a
  one-line alternative kill worth recording.
- **Note 2 (definitional, no gap)**: the d₃ dictionary is the
  support-⊆-W quantity, NOT the exact-support minimum (those differ: e.g.
  exact-support (2,T) has min 5, but d₃(2,T) = 3 via a line whose support is
  a SUBSET). The prose uses it correctly throughout (all uses are
  "support ⊆ W ⟹ weight ≥ d₃"); this re-review initially mis-read it the
  other way and produced a spurious mismatch — one clarifying sentence in
  the write-up will save the next reader the same trip. The (n,ε)
  GL-symmetry of the table is real (verified over all 32 W).

### Link 4 — the Entry-14 assembly and the duality: **HOLDS**

- **Dichotomy**: [p(v)] ≠ 0 vs = 0 is tautologically exhaustive; the safe
  branch needs only p(v) ≠ 0 (a nonzero base cycle) + the small-cycle
  theorem; p is weight-non-increasing since |v₀| + |v₁| ≥ |v₀ + v₁|.
- **m-rungs** (Entry 13 Cor. 2) re-derived: hexagon — the mod-b replacement
  gives min(|u′∩h|, 6−|u′∩h|) ≤ 3, total ≤ 5 ⟹ rep = 0 ⟹ [u′] = 0 ∈ imΔ ✗;
  D-pair — the four-coset weight sum is 2 per qubit of the 11-cell union
  = 22 < 24 ✓ (and the seam containments supp(d2c_jδ_g) ⊆ h(g) hold for ALL
  g, j — AV4 — closing the one spot the lab only argued "by construction").
- **Inversion duality**: re-derived from the convolution convention —
  Φ(w_L, w_R) = (ι(w_R), ι(w_L)) sends ker H_X → ker H_Z (apply ι to
  Aw_L + Bw_R = 0 and use M_Bᵀ = M_B̄) and row g of H_X → row(−g) of H_Z, so
  stabilizers map onto stabilizers, classes to classes, weights preserved:
  d_X = d_Z. Exact basis-level checks pass for base AND cover (AV5).
- **(M) assembly arithmetic**: 0 + 2·6, 6 + 2·3, 10 + 2·1, |b| ≥ 12 — all
  ≥ 12 ✓; safe min 6; min(6,12) = 6 ✓.

### Verdict

**No link breaks. The theorem d(gross) ≥ 6 (and d(base) ≥ 6, d_X = d_Z)
graduates to write-up grade.** The two notes above are presentation debts
for the standalone write-up, not gaps. The independent checker
`a3_adv15_recheck.py` (49 checks) joins the confirmation suite; like all of
it, it is discovery/validation only and load-bearing nowhere.

### Next

1. The standalone write-up note (A_HANDOFF §8 item 2), folding in Notes 1–2.
2. Goal 1 (d = 12): the safe-sector (M)-analogue.
3. Goal 2: template runs on other BB bases.

---

## Entry 16 (2026-06-12) — goal 1 opened: the safe sector IS the Smith sector; d = 12 reduces to two base-code statements

*(Entry 15 is the adversarial re-review, which ran in a parallel session
and is merged above; this entry starts the goal-1 program on the safe
sector. The two lines proceeded concurrently from Entry 14.)*
Foundations and discovery in `a3_msafe_scan.py` (S1–S8, all PASS).

### The safe-slice framework (S1–S3)

For a cover cycle v = (v₀, v₁) with p(v) = w a fixed base cycle, the cover
block equations [[d1nc, d1c], [d1c, d1nc]] (re-derived per cut, S1) reduce
to **∂₁v₀ = d1c_j·w** (the seam syndrome of w), with v₁ = v₀ + w; and
|v| = |w| + 2·|v₀ off supp w|. So the safe sector has a literal mirror of
(M): with m_safe(w) := min{|v₀ off supp w| : ∂₁v₀ = d1c_j w},

    (M-safe):  |w| + 2·m_safe(w) ≥ 12   for every base cycle w, [w] ≠ 0.

Base cycles are even (augmentation), so the light rungs are |w| ∈ {6,8,10}
with m_safe ≥ 3, 2, 1. Solvability of the slice is class-invariant and
cut-independent (S2): w is **reachable** iff δ(w) := [d1c_j w] ∈ coker ∂₁
vanishes — the Gysin connecting map; im pr_* = ker δ.

### Discovery 1: the weight-6 logicals (S4, S6)

The 120 weight-6 cycles split as 36 + 48 + 36 over (|u_L|, |u_R|) =
(6,0)/(3,3)/(0,6): the (6,0) family is exactly the 36 weight-6 elements of
Ann(A) (one translation orbit — single t_y-fibre, shape (2,2,2) with
t_y-direction pairs, x-span {c, c+3}; the engine classification mirrors the
shape lemmas), the (0,6) family mirrors in Ann(B), and the (3,3) family is
the 36 hexagons (trivial class) plus a 12-element orbit of mixed logicals.
The 84 logicals occupy 84 **distinct** H₁ classes.

### Discovery 2 (the headline): every weight-6 logical is UNREACHABLE (S5, S7)

m_safe is **undefined** on all three weight-6 orbits — the slices are
empty. No cover cycle projects onto any weight-6 base logical: the |w| = 6
rung of (M-safe) is **vacuous**. More: computing δ on an H₁ basis and
Δ[ζ] = [d2c_j ζ] on H₂ = ker ∂₂ gives, cut-independently,

    ker δ = im Δ      (both 64 classes; Δ injective on the 64-element ker ∂₂),

i.e. **the reachable classes are exactly the Smith classes** — the safe
sector of gross sees only im Δ. (All 84 weight-6 classes lie outside, as
they must.)

### The reduction theorem for goal 1

Since every safe logical v has [p(v)] ∈ ker δ ∖ {0} and |v| ≥ |p(v)|:

> **d_Z(gross) ≥ 12  ⟸  (M) [proven, Entries 5–13]  +
> (R): ker δ = im Δ analytically  +
> (M-im): every 1-cycle in a nonzero imΔ class has weight ≥ 12.**

(M-im) is exactly the statement the C2 crosscheck verified by SAT
(imΔ-distance = 12, attained): true with the minimum sitting right at the
bar. Equivalently, with explicit Smith reps: **dist(d2c_j ζ, Stab_Z) ≥ 12
for each of the 63 nonzero ζ ∈ ker ∂₂** — a base-code
distance-to-stabilizer bound, squarely in range of the proven machinery
(the light-stabilizer classification controls how a stabilizer can cancel
against d2c_j ζ). Structure available (S8): ker ∂₂ has weight enumerator
{16:9, 18:48, 24:6} and lives in CRT components {3,4} only (dims 2+4);
the reps satisfy |d2c_0 ζ| ∈ {12, 14, 16, 18, 20} — already ≥ 12.

**(R) in equivalent forms.** im pr_* = ker τ_* ⟺ τ_*∘pr_* = 0 ⟺
**σ_* = id on H₁(gross)** (the deck transformation x ↦ x+6 acts trivially
on cover homology), via (1+σ)v = τ(p(v)). Dimensions force
dim ker δ = dim im Δ = 6 from the Gysin sequence alone (im δ must fill the
6-dim H₀ deficit), so (R) is the *inclusion* im pr_* ⊆ ker τ_*.

### Dead end (first-class): the formal-module proof of (R) fails

Trying z′ = (1+x⁶)u to bound τ(p(v)) = (1+x⁶)v: since (1+x⁶)² = 0,
multiplication by (1+x⁶) factors through the base quotient, and the ansatz
reduces to ∂₂^base ū = p(v) — i.e. [p(v)] = 0, false for safe v. So (R)
is genuinely homological: any proof must use the cycle condition on v, not
just module algebra. (Candidate routes: an explicit chain homotopy from
the cut-cylinder/Mayer–Vietoris structure of the cover; or exhibiting a
σ-stable logical basis of gross via the BB polynomial symmetries.)

### Next steps (goal-1 queue)

1. **(M-im)** via the classification: show no stabilizer b can cancel
   d2c_j ζ below 12 — expect a graded argument in |b| using hexagon/D-pair
   locality for light b and the COST/dictionary machinery for heavy b.
   Start with the 9 weight-16 ζ's (likely one orbit).
2. **(R)** via chain homotopy or a σ-stable basis.
3. The weight-8/10 reachable-cycle census (deferred; only relevant as a
   cross-check once (R) + (M-im) land — the reduction bypasses the
   per-weight rungs entirely).

## Entry 17 (2026-06-12) — (R) PROVEN by a one-line homotopy; (M-im) is the last statement before d = 12

Script: `a3_r_homotopy_mim.py` (R1–R3, M1–M6, all PASS).

### Theorem: ker δ = im Δ — the deck action is null-homotopic on cycles

Over the cover ring F₂[Z₁₂×Z₆], squaring B kills its y-dependence
(y⁶ = 1):

    B² = y⁶ + x² + x⁴ = 1 + x² + x⁴,    (1+x²)(1+x²+x⁴) = 1 + x⁶.

**Proof of (R).** For any cover 1-cycle v = (v_L, v_R) (A·v_L = B·v_R), set
z := (1+x²)·B·v_L. Then

    ∂₂z = (B z, A z) = ((1+x²)B²·v_L, (1+x²)B·(A v_L))
        = ((1+x⁶)v_L, (1+x²)B²·v_R) = (1+x⁶)·v = v + σv.

So (1+σ)Z₁(cover) ⊆ B₁(cover): **σ_* = id on H₁(gross)**; hence
τ_*∘pr_* = (1+σ)_* = 0, giving im pr_* ⊆ ker τ_* = im Δ, and equality by
rank–nullity (both sides have dimension 12 − dim im τ_*). ∎
(R1: the two identities; R2: the homotopy verified on all 78 basis cycles
of ker H_X^cov; R3: on the base the same identity degenerates to 0 = 0,
as it must.)

**Consequence (the goal-1 ledger).** With (M) proven (Entries 5–13) and
(R) proven, the safe sector satisfies |v| ≥ |p(v)| with
[p(v)] ∈ im Δ ∖ 0, so

> **d(gross) = 12  ⟸  (M-im): every 1-cycle in a nonzero imΔ class has
> weight ≥ 12.**

Both directions: ≥ 12 from (M) + (R) + (M-im) + duality; ≤ 12 because
τ(u\*) (u\* the Entry-13/A4 weight-6 logical) is a weight-12 logical —
nontrivial since [u\*] ∉ im Δ = ker τ_*, which is the weight-6 sub-rung of
(M-im) below. **Goal 1 is one base-code statement away.**

### The flux characterization of the Smith classes (M4)

The Smith **linking form** P[ξ, ζ] := ⟨d1c_jᵀξ, d2c_jζ⟩ over
ξ ∈ ker H_Xᵀ (the X-side 2-kernel, = ι(ker ∂₂)) and ζ ∈ ker ∂₂ is
**identically zero, for every cut j** (M4). Since the H₁-pairing of the
X- and Z-sides is perfect and both Smith spaces are 6-dimensional:

    im Δ^X = (im Δ^Z)^⊥   ⟹   [w] ∈ im Δ  ⟺  the six seam-flux
    functionals  ℓ_ξ(w) := ξᵀ·d1c_j·w  all vanish.

(M-im) restated: **a cycle with vanishing seam flux that is not a
boundary has weight ≥ 12** — six explicit sparse parities decide Smith
membership. (Hand proof of the zero linking form: owed; candidate route
via the (R) homotopy and τᵀ = p adjointness.)

### The weight-6 sub-rung of (M-im), hand-checkable (M3, M6)

Every weight-6 logical has **nonzero flux** — verified per orbit
(Ann(A)-type: flux (1,0,0,1,1,1); Ann(B)-type: (1,1,1,0,0,1); mixed
(3,3): (0,1,1,0,1,0)), and flux-vanishing is translation-covariant, so
the orbit-level check covers all 84. Equivalently τ(u) is never a cover
boundary (M3, rank check). Each flux value is a parity of an explicit
short sum — surveyable by hand. **No weight-6 cycle lies in a nonzero
imΔ class.**

### (M-im) discovery (M1, M2, M5) and the dead end

- **ker ∂₂ ∖ 0 has 5 orbits** under translation + swap: (size, weight) =
  (9, 16), (12, 18), (36, 18), (3, 24), (3, 24). Only 5 classes of Smith
  reps to bound.
- Rep weights |d2c_jζ| per orbit and cut: the wt-16 orbit gives
  {12,12,16,12,12,16}; the wt-18 orbits give 12–18; the wt-24 orbits sit
  at 20. The 18 reps of weight 12 (S8/M5) realize the class minimum: the
  bar is *attained by the canonical reps*.
- **Dead end (first-class): the π_x-collapse bound is vacuous** — the
  exact collapsed minimum L_j is 0 for every orbit and cut (M2). The
  column-profile relations c_{i−3} = (y+y²)c_i, c_{i−1}+c_{i−2} = y³c_i
  make the collapsed coset always reach 0. Any proof of (M-im) must stay
  2-dimensional.

### Next steps (the (M-im) program)

1. **Light-cycle flux route**: extend the weight-6 census to weights 8
   and 10 (the split machinery of Entry 13 at higher weight) and show
   every non-boundary cycle there has nonzero flux. Weight 10 must use
   the D-pair boundaries (flux 0, class 0 — allowed); the statement is
   exactly "light non-boundary cycles are never flux-silent".
2. **Affine-COST route**: per orbit rep, run the Entry-8/9 component
   grammar on the coset d2c_jζ + im ∂₂ (the offset version of profile
   completeness); if the COST floor on each coset is ≥ 12, the dictionary
   machinery closes (M-im) the same way it closed the classification.
3. Hand proof of the zero linking form (the flux characterization's
   remaining leg).

## Entry 18 (2026-06-12) — the no-double-wrap lemma: the flux characterization is fully analytic

Closes the owed leg of Entry 17 (the zero linking form) with a two-line
geometric argument, and seeds the affine-COST route to (M-im).
Script: `a3_r_homotopy_mim.py` M7–M8 (PASS).

### Lemma (no double wrap)

For every cut j:  **d1c_j·d2c_j = 0,  d1nc_j·d2nc_j = 0,  and
d1nc_j·d2c_j = d1c_j·d2nc_j.**

*Proof.* An entry of ∂₁∂₂ at (check c, face f) sums over two-step paths
f → qubit → c: through the left block (a B-step, then an A-step) or the
right block (an A-step, then a B-step), one path per factorization
c·f⁻¹ = a·b per route — an even number in total (AB = BA). The x-advance
of any such path is ≤ 3 + 2 = 5 < 6, so a path crosses the cut line **at
most once**, and whether it crosses is determined by the endpoints alone
(a monotone path of advance D < 6 from x_f crosses iff the cut lies in
the circular interval (x_f, x_f + D]). Hence all paths at a given entry
have the same crossing count: if 0, they all lie in d1nc·d2nc and cancel
there; if 1, each crosses during exactly one of its two steps, so
d1c·d2c and d1nc·d2nc receive nothing, and the paths distribute between
d1nc·d2c and d1c·d2nc with even total — forcing those two entries equal.
∎ (M7: verified as matrix identities for all six cuts. This sharpens the
Entry-5 chain identities, whose stated form was only the sums.)

### Corollary: the flux characterization, now fully analytic

P[ξ, ζ] = ⟨d1c_jᵀξ, d2c_jζ⟩ = ξᵀ(d1c_j·d2c_j)ζ = **0** — the linking
form vanishes *as a bilinear identity*, before any kernel conditions.
With the standard perfect H₁^X × H₁^Z pairing and dim imΔ^X =
dim imΔ^Z = 6 (forced by the Gysin sequence, Entry 16):

    im Δ^X = (im Δ^Z)^⊥,   so   [w] ∈ im Δ  ⟺  ξᵀ·d1c_j·w = 0
    for the six ξ ∈ ker H_Xᵀ — six explicit, sparse parities.

Every ingredient of the characterization is now hand-proven. In
particular the Entry-17 weight-6 sub-rung computations (nonzero flux on
all three orbits) are load-bearing-grade: each is a finite overlap count
between a weight-6 logical and an explicit X-Smith representative.

### The affine-COST seed (M8): every Smith coset is pinned

For each of the five ζ-orbits, the component offsets of the canonical rep
d2c₀ζ were tested for realizability as boundary pairs (B̂t, Ât):

    orbit wt 16:  pinned at components {3, 4}
    orbit wt 18a: pinned at {4};   orbit wt 18b: pinned at {3, 4}
    orbit wt 24a: pinned at {4};   orbit wt 24b: pinned at {3}

Every orbit is pinned somewhere in the doubly-radical pair {3, 4} (and
nowhere else) — as it must be: the obstruction lives where ker ∂₂ lives.
Consequence for (M-im): in every element of a nonzero Smith class, the
pinned component is alive, so the support grammar (co-point-or-full at
radical components) forces alive layers in **both** blocks at the pinned
component, and the offset version of the Entry-8/9 COST analysis applies
with a nonzero floor. The next session's program: run the offset-COST
minimization per orbit (machine first); if every floor is ≥ 12, the
hand-organization mirrors Entries 9–12 (engine + C-table on the offset
grammar) and closes (M-im) — hence goal 1 — entirely.

### Status

- (R): PROVEN (Entry 17). Zero linking form: PROVEN (this entry).
- (M-im): weight-6 sub-rung proven; weights 8/10 remain, two routes
  (light-cycle flux census / affine-COST on five pinned cosets), with the
  pinned-component data pointing at the latter.
- d(gross) = 12 ⟺ (M-im) — unchanged, one statement away.

## Entry 19 (2026-06-12) — offset-COST DP: the support-only floor stalls at 6–8; transport and parity structure of the Smith cosets

First machine pass on the affine-COST route to (M-im)
(`a3_mim_offset_cost.py`). Outcome: **honest negative on the floor** —
the Entry-8 d₃ dictionary applied to the offset grammar cannot reach 12 —
plus four structural results that shape the next attack.

### The instrument

For w = d2c₀ζ + ∂₂t in the Smith coset C(ζ), the CRT component data is
V_j = off_j + (B̂_j t̂_j, Â_j t̂_j) with off_j = comp_j(d2c₀ζ) and the t̂_j
free and **independent** across j — so the per-component support-pattern
sets multiply exactly (the only relaxation is the per-slot dictionary
bound |w_{block,s}| ≥ d₃(n, ε)). The DP is Entry 8's D4 with two
generalizations: per-component pattern sets shifted by the offsets, and
the comp-0 (mask_L, mask_R) pairs decoupled per block.

Sanity ladder, all PASS: zero offset reproduces Entry 8 **exactly**
(grammar sizes 16/53/53/20/6; global min 6 achieved by exactly the 4
hexagon patterns; min 12 with any one of the five components forced
dead); 200 random coset elements per orbit satisfy |w| ≥ COST(w), realize
patterns inside the offset grammar, and verify the affine
multiplicativity ĥat(w)_j = off_j + (B̂_j t̂_j, Â_j t̂_j); the M8 pins are
reproduced (pinned ⟺ (0,0) not in the offset grammar).

### Structure result 1: the 5-orbit reduction needs only translation

The translation-only orbits of ker ∂₂ ∖ 0 are **already the five
translation+swap orbits** (sizes 9, 12, 36, 3, 3 — the swap stabilizes
each orbit setwise). Since [d2c_j ζ] is cut-independent (verified all j)
and class(Tζ) = T·class(ζ) (verified), the coset — hence any
coset-intrinsic floor — transports along translations alone. No swap
transport lemma is needed for (M-im).

### Structure result 2 (new, informational): Δ^y ≠ Δ^x, even as images

The builder identity Ŝ(d2c^x₀ζ) = d2c^y₀(Sζ) holds exactly (the swap
maps x-Smith data to y-Smith data), but the y-cut connecting map differs
from the x-cut one **pointwise and in image**: rank(im∂₂ + imΔ^x-reps +
imΔ^y-reps) = 40 vs 36 — the two 6-dim Smith images share only a 2-dim
intersection. The x-cover and y-cover see genuinely different "dangerous"
classes. (Not needed for (M-im) by structure result 1; recorded because
it kills any hope of a swap-symmetric description of im Δ.)

### Structure result 3: the parity lemma survives on the Smith cosets

The comp-0 offsets are **diagonal** (off₀_L = off₀_R) for all five
orbits — equivalently comp 0 is never pinned. So every element of every
Smith coset has equal layer-parity vectors in the two blocks, exactly
like a stabilizer (Entry 9 lemma (i)). Hand proof: comp-0 data of
d2c₀ζ is (B̂₀ẑ₀-with-cut-marks, Â₀ẑ₀-with-cut-marks) and Â₀ = B̂₀;
to be made precise in the hand write-up of the offset grammar.

### Structure result 4: comps 1, 2 are offset-free; the offsets live at {3,4}

Since every pin set is inside {3, 4} (M8, reproduced), the comp-1/2
offsets are realizable, so re-centering makes those grammars **equal to
the homogeneous ones** (sizes 53/53 for every orbit). All
orbit-dependence of the coset sits in the doubly-radical pair {3, 4} —
where ker ∂₂ lives. Grammar sizes there: comp 3: 41 (pinned) or 20
(unpinned); comp 4: 15 (pinned) or 6 (unpinned).

### The floors (the negative)

    orbit (n=9,  wt=16): floor 8    (true class min 12)
    orbit (n=12, wt=18): floor 7
    orbit (n=36, wt=18): floor 7
    orbit (n=3,  wt=24): floor 8
    orbit (n=3,  wt=24): floor 6

All floors ≤ 12 (consistency with the SAT class minima = 12: PASS), all
< 12: **the support-only dictionary cannot carry (M-im).** Diagnosis from
the witnesses: d₃ sees supports, not values. The wt-24b orbit (pinned
only at comp 3) still admits the full hexagon support pattern at cost 6 —
the offset constrains comp-3 *values*, but the support relaxation forgets
them. The sub-12 landscape is thousands of patterns per orbit (e.g.
{8:17, 9:48, 10:564, 11:2224} for wt-16) — pattern-by-pattern equality
analysis is infeasible without a sharper floor.

### Next (the value-refined floor)

The fix the diagnosis dictates: make components {0, 3, 4} **value-exact**
— their joint coset data is tiny and explicit (Γ₀ diagonal: 16; off₃+Γ₃:
64; off₄+Γ₄: 16 — i.e. 16384 affine value-combos per orbit, the only
orbit-dependent data by structure result 4) — and keep the support
grammar only at the unit-side comps {1, 2} (53 × 53 patterns). The slot
dictionary upgrades to d₃ᵛ(v₀; a₁, a₂; v₃, v₄) = exact minimum weight of
a Z₃²-layer with prescribed transform values at {0,3,4} and prescribed
aliveness at {1,2} (the value 5-tuple ↔ layer bijection makes this a
512-entry exact table). This is Entry 9's δ-point/ψ-evaluation rigidity
baked into the floor. Entry 20.


## Entry 20 (2026-06-12) — the value-refined floor + completion sweep: (M-im) closes at the verified-finite level

Script: `a3_mim_value_cost.py` (S1–S7, all PASS). Outcome: **(M-im) — and
with it d(gross) = 12 — now holds at the verified-finite level**, by a
route independent of SAT, with every machine ingredient an explicit
finite enumeration over verified encodings. This is the Entry-9 moment
for goal 1: no unbounded-structure gap remains; what is owed is
hand-organization (the Entries 10–12 analogue).

### The value dictionary (S1, S2)

The 512 layers f ∈ F₂[Z₃²] are in **bijection** with their transform
value 5-tuples (v₀, v₁, v₂, v₃, v₄) ∈ F₂ × F₄⁴ (one value per character
orbit; 512 = 2·4⁴, each tuple hit exactly once — Fourier inversion with
Frobenius). Upgrading the Entry-8 d₃ table to prescribed VALUES at
comps {0, 3, 4} and aliveness at comps {1, 2}:

    d₃ᵛ(v₀; a₁, a₂; v₃, v₄) = min wt of a layer with those constraints —

an exact 32×4 table; marginalizing values reproduces d₃ on all 31
support sets (S2). Two hand-grade facts fall out: **slot-weight parity**
wt(f) ≡ v₀ (mod 2) (augmentation = comp-0 value), and with the Entry-19
diagonality of comp-0 offsets: **every Smith-coset element has even
weight, and even VCOST** — the sub-12 landscape lives at costs
{6, 8, 10} only.

### The value-refined floor (S3–S5)

Components {0, 3, 4} — where ker ∂₂ lives and every orbit is pinned —
become value-exact: their joint coset data is (off₀+Γ₀)×(off₃+Γ₃)×
(off₄+Γ₄) = 16·64·16 = 16384 affine combos (Γ_j the graph ideal
{(B̂_jt̂, Â_jt̂)}); comps {1, 2} keep the support grammar (53×53,
homogeneous by Entry 19). CRT keeps the five coordinates independent, so
the product is the EXACT image of the coset; the only relaxation is
per-slot d₃ᵛ. Ladder: zero offset gives floor 6 with exactly **36**
value-achievers = the 36 hexagons (value-exactness sees each hexagon
individually; Entry 8 saw 4 support patterns); the refinement sandwich
OFFCOST ≤ VCOST ≤ |w| holds on 1000 random coset elements.

Floors: **8 / 8 / 8 / 8 / 6** on the five orbits (wt-16, 18a, 18b, 24a,
24b) — better than Entry 19's 8/7/7/8/6 but still short of 12: the
support relaxation at comps {1, 2} is now the binding loss.

### The completion sweep (S6/S7): the kill

The miss is recoverable because a sub-12 combo **determines its
candidates completely**: comps 1, 2 are affine graphs over the coset —

    V₁R = c₁ + ρ₁·V₁L (ρ₁ = Â₁B̂₁⁻¹ radical, c₁ from the offsets),
    V₂L = c₂ + ρ₂·V₂R —

so enumerating V₁L inside mask₁L (≤ 3⁴) and V₂R inside mask₂R (≤ 3⁴),
filtering on the partner masks, and inverting the value bijection
reconstructs every candidate w **exactly** (spot-verified: completions
land in the coset with the computed weight; coset membership via the
42-bit syndrome key). Any coset element of weight ≤ 11 is even, hence
≤ 10, hence realizes a combo of cost ≤ 10 and appears in the sweep.

Results per orbit (combos at cost ≤ 10 / completions / min weight):

    wt-16:  1044 / 113004 / 18      wt-18a: 1476 / 130950 / 14
    wt-18b: 1420 / 149904 / 14      wt-24a: 1038 /  99468 / 18
    wt-24b: 2532 / 241596 / 16

**Zero completions of weight ≤ 11 anywhere** — and the minima 14–18 show
slack: the weight-12 class minima have VCOST = 12 and never enter the
sub-12 sweep. With class(Tζ) = T·class(ζ) verified for all 36
translations on a basis (linearity extends to all ζ), the five orbit
kills cover all 63 classes:

> **(M-im), verified-finite:** every base 1-cycle in a nonzero imΔ class
> has weight ≥ 12. Hence (with (M), (R), duality — all fully analytic)
> **d(gross) = 12 at the verified-finite level.**

### Status vs. the analytic bar

Per §1 of A_HANDOFF the finite checks are not yet human-surveyable
residues; the owed hand-organization, in Entry-10–12 style:
  (a) the slot-parity and even-weight lemmas (hand-proven above, to be
      written out);
  (b) the d₃ᵛ dictionary on the cells that occur (δ-point/ψ-evaluation
      rigidity — the value analogue of the Entry-9 layer dictionary);
  (c) the cost-≤10 combo classification (the offset C-table: why only
      ~1k–2.5k combos, in few families — the orbit translation
      stabilizers and the Γ₃/Γ₄ module structure are the compression);
  (d) the completion-kill rigidity (why ρ-affinity forces every
      completion to weight ≥ 14 — note the uniform slack above 12).
Alternative hand route still open: the weight-8/10 flux census (route B)
— next entry sizes both before committing to one.


## Entry 21 (2026-06-12) — the light-cycle census: (M-im) re-verified by the flux route; route B sized (and closed to hand work at weight 10)

Script: `a3_light_cycle_census.py` (C1–C5 all PASS). Complete enumeration
of ALL base 1-cycles of weights 6, 8, 10, with seam-flux and boundary
status — the Entry-13 split machinery mechanized two weights up, exactly
as route B prescribed.

### Method (per split (|u_L|, |u_R|), partition — no double counting)

Pure splits from Ann(A), Ann(B) (both 12-dim, 4096 elements, fully
enumerated); mixed splits with small side ≤ 4 by enumerate-small-side +
affine solve (row-ops matrix for MA, MB; particular solution + the
4096-element kernel coset scanned by packed popcounts); the (5,5) split
by syndrome hash-join over C(36,5) = 376992 per side. Ladder: Ann dims
12/12 with weight enumerators {6: 36, 8: 9} (the W1 anchor: min 6);
weight-6 census reproduces the ground truth exactly (120 cycles =
36 hexagons + 84 logicals, splits 36/48/36, hexagons the only
flux-silent ones); the weight-10 boundaries come out exactly the 216
D-pairs in splits (4,6)+(6,4) (Entry-9 cross-check); flux is
class-invariant on samples; solver spot-checks pass.

### The censuses

    weight 6:   120 cycles;  36 boundaries; 84 loud non-boundaries
    weight 8:   990 cycles;   0 boundaries; ALL loud; splits
                (8,0):9 (5,3):108 (4,4):756 (3,5):108 (0,8):9;
                32 translation orbits
    weight 10: 13464 cycles; 216 boundaries (the D-pairs); 13248
                non-boundaries, ALL loud; splits (7,3):972 (6,4):3276
                (5,5):4968 + mirrors; 368 translation orbits

**FLUX-SILENT non-boundary cycles at weights 8 and 10: ZERO.** With the
proven weight-6 sub-rung and the small-cycle theorem (no cycles ≤ 5;
weights are even), this **re-proves (M-im) at the verified-finite level
by the flux route — fully independent of Entry 20's value grammar.**
Two independent machine closures of (M-im) now exist; the d(gross) = 12
chain is double-verified end to end.

### Route decision

Route B's hand version would need the per-orbit classification of 32
weight-8 orbits (borderline) AND 368 weight-10 non-boundary orbits
(not feasible as Entry-13-style case analysis). Route A (the value
grammar of Entry 20) has per-orbit object counts of 1k–2.5k but with
strong algebraic compression available (even costs; comps 1, 2
homogeneous; offsets confined to {3, 4} with graph ideals of size
64/16; ρ-nilpotency ρ³ = 0 at the radical components). **The
hand-organization proceeds on route A**; the census stays as the
independent cross-check and the source of the weight-8 structure
(990 = 9 + 108 + 756 + 108 + 9, a future write-up exhibit).


## Entry 22 (2026-06-12) — hand-organization of (M-im), part I: parity, rigidity, the ρ-locks, and the confined floor (two orbits close)

Script: `a3_mim_hand_org.py` (H1–H10, all PASS). The Entry-20 machine
closure starts converting into hand lemmas; the new **confined-value
floor closes (M-im) outright on the two wt-24 orbits**, and reduces the
other three to a single equality analysis at weight exactly 10.

### Hand-proven lemmas (proofs here; machine checks in the script)

**V1 (slot parity).** For a layer f ∈ F₂[Z₃²]: wt(f) ≡ f̂(triv) = v₀
(mod 2) — the augmentation is the weight mod 2. ∎

**V2 (2-cycle evenness).** ζ ∈ ker ∂₂ = Ann(A) ∩ Ann(B). From Aζ = 0:
x³ζ = (y+y²)ζ, i.e. columnwise c_{i+3} = (y+y²)c_i; the right side has
even weight (aug(y+y²) = 0), so **every column of ζ is even**; rows
mirror via Bζ = 0. ∎

**V3 (even coset weight and cost).** The cut-0 Smith rep w₀ = d2c₀ζ has
L-block x·P₅ζ + x²·(P₄+P₅)ζ and R-block x³·(P₃+P₄+P₅)ζ (P_c = column
projections; only those B/A-steps cross the cut), so |w₀_L| ≡ |P₄ζ| and
|w₀_R| ≡ |P₃ζ|+|P₄ζ|+|P₅ζ| (mod 2) — both 0 by V2. With |∂₂t| even
(aug(A) = aug(B) = 1), **every element of every Smith coset has even
weight**; by V1, also even VCOST (cost ≡ Σ_slots v₀ ≡ |w_L| + |w_R|).
So sub-12 means weight ∈ {6, 8, 10} and cost ∈ {6, 8, 10}. ∎

**V4 (value rigidity, E ≤ 2).** The 512 layers biject with their value
5-tuples (Fourier inversion + Frobenius). E = 1 exactly at the 9
δ-point evaluation tuples (1, ψ₁(p), …, ψ₄(p)); E = 2 exactly at the 36
point-pair sums — v₀ = 0 and exactly ONE dead nontrivial component (the
kernel direction of p−q; p ≠ q lies in exactly one of the four
character-kernel lines). Counts match both ways (9 weight-1 and 36
weight-2 layers), so the lists are complete. ∎

**V5 (the ρ-locks).** In F₄[Z₂²] every element satisfies
u² = aug(u)²·1: squaring is Frobenius-linear in characteristic 2 and
g² = e for every g ∈ Z₂², so (Σ u_g g)² = (Σ u_g²)·e = aug(u)²·e.
Hence for ρ₁ = Â₁B̂₁⁻¹ (aug 0 since Â₁ is radical, B̂₁ a unit):
**ρ₁² = 0**, so im ρ₁ ⊆ ker ρ₁ has F₄-dimension exactly 2 (16 elements;
it is 2, not 1, because ρ₁ is not a scalar multiple of Σ_g g), and
aug(ρ₁u) = 0. On every Smith coset:

    V₁R = c₁ + ρ₁·V₁L  ∈  c₁ + im ρ₁   (16 vectors, independent of V₁L!)
    V₂L = c₂ + ρ₂·V₂R  ∈  c₂ + im ρ₂   (16 vectors),

and aug(V₁R) = aug(c₁), aug(V₂L) = aug(c₂) — with **aug(c₁) = aug(c₂)
= 0 on all five orbits** (verified; hand derivation from the offsets
owed). Comp 4 adds the scalar relation B̂₄ = ω·Â₄. (Comp 3 is NOT a
graph over its L-value — |im B̂₃| = 16 with 4 partners each; noted.) ∎

**V6 (fibre gap — verified table fact, hand-check owed but surveyable).**
In every (v₀; v₃, v₄; a₁, a₂)-fibre of the value table (66 nontrivial
fibres), every non-minimal weight is ≥ fibre-min + 4 (all second-min
gaps are exactly 4). Consequence: **a slot that misses its d₃ᵛ minimum
pays at least +4.** The 66 fibres compress under the GL₂(Z₃)-stabilizer
of the component split — a bounded hand check.

### The confined-value floor (H10) — two orbits close

Taking comps {0, 3, 4} value-exactly AND the confined sides V₁R, V₂L
over their 16-element ρ-cosets (V5), relaxing only the free sides v₁L,
v₂R per slot (no grammar at all), the cost decomposes per block
(L-cost: min over V₂L of a 4-slot M₁-table sum; R-cost: min over V₁R),
and the floor evaluates to

    wt-16: 10    wt-18a: 10    wt-18b: 10    wt-24a: 12    wt-24b: 12.

**The two wt-24 cosets satisfy (M-im) by the confined floor alone** —
no combo enumeration, no completion sweep. For the other three, weights
are even (V3), so the only surviving possibility is weight EXACTLY 10.

### Kill structure (probes H6/H7, machine statistics)

Cross-tab of combo cost vs minimum completion weight, all five orbits:
cost-10 combos complete to ≥ 14 (one +4 quantum); cost-8 to ≥ 16 (two
quanta — one would already give 12); cost-6 (only 12 combos, wt-24b
orbit, now moot by H10) to 22. Minimal-completion deficits are ALWAYS
quanta of exactly +4 per slot (V6 in action). Combo families per orbit:
137–239 distinct (m₁, m₂) mask pairs — the classification that the
confined floor now mostly bypasses.

### Remaining obligations for fully-analytic (M-im) (bounded, shaped)

  (O1) Hand-evaluate the confined floor: ≥ 12 on the wt-24 cosets and
       ≥ 10 on the rest. Structure available: the minimization runs
       over (off₀+Γ₀)×(off₃+Γ₃)×(off₄+Γ₄) (16·64·16) with per-block
       16-element confined minima; compression: translation stabilizers
       (order 12 on the wt-24 orbits), B̂₄ = ωÂ₄, and the small-ideal
       module structure. This is the Entry-10/11 "engine + C-table"
       analogue.
  (O2) The weight-10 equality analysis (orbits wt-16, 18a, 18b): a
       confined-floor-10 achiever must also satisfy the dropped link
       ρ₁V₁L = V₁R + c₁ (and mask consistency); show it cannot, and V6
       bumps any actual element to ≥ 14. (Machine forms already verified
       twice: the Entry-20 sweep and the Entry-21 census found no
       weight-10 non-boundary flux-silent cycles.)
  (O3) The V6 fibre-gap table, GL-compressed, as a surveyable case list;
       and the hand derivation of aug(c₁) = aug(c₂) = 0 from the offset
       structure.

With (O1)–(O3), (M-im) is fully analytic — and with it **d(gross) = 12,
fully analytic** ((M) + (R) + flux + duality are all already at that
grade). Next session: O1 first (it carries the wt-24 orbits and the
floor-10 baseline), then O2.


## Entry 23 (2026-06-12) — O1 structure: the confined floor as spine C-tables; the support, cost, and slope engines

Script: `a3_mim_confined_tables.py` (T1–T6). The Entry-22 confined floor
is now organized into hand-evaluable form: per orbit a 4×4 **spine
C-table** m(a₃, a₄), with three proven engine lemmas that evaluate its
cells. The two wt-24 orbits reduce to a single uniform block statement.

### The coordinatization (T1)

In R = F₄[Z₂²] put X = 1+s_x, Y = 1+s_y, XY = ΣG (so X² = Y² = 0). All
constants are short: Â₁ = Â₃ = X + ωY; B̂₂ = B̂₃ = B̂₄ = ωX + Y;
Â₂ = B̂₁ = 1 + X + Y (the units); Â₄ = X + ω²Y; ρ₁ = X + ωY + ω²XY,
ρ₂ = ωX + Y + ω²XY. Verified parametrizations:

    Γ₃ = {(a B̂₃ + βXY, a Â₃ + αXY) : a, β, α ∈ F₄}   (64; the two
        XY-shifts are FREE and independent),
    Γ₄ = {(ω(a Â₄ + γXY), a Â₄ + γXY)}               (16; the ω-scalar
        ties the blocks, one shared shift γ),
    im ρ_i = F₄ρ_i ⊕ F₄XY,

and **c₁ = c₂ = 0 on every orbit** — the confined sets are the
subspaces im ρ₁, im ρ₂ themselves. (c_i = 0 is literally "comps 1, 2
are unpinned", an Entry-19 verified fact; its hand derivation joins O3.)
A confined configuration is exactly: V₀ ∈ F₂[Z₂²] (16, shared by both
blocks), spine (a₃, a₄) ∈ F₄² (shared), γ ∈ F₄ (shared, ω-twisted),
independent XY-shifts β, α of comp 3 per block, and V₂L ∈ im ρ₂,
V₁R ∈ im ρ₁. The floor = min over spine cells of m(a₃, a₄), each cell
an exact min over the rest.

### Engine 1: the support-class lemma (kill-multiset form)

For v = c·1 + αX + βY + δXY with δ free, the slot values are
(c+α+β+δ, α+δ, β+δ, δ), so the zero set at shift δ is the level set
{s : kill[s] = δ} of the **kill vector** kill(v) = (c+α+β, α, β, 0). ∎
Consequences: four distinct kill entries ⟹ support is always a
co-point (each of the 4 positions); a repeated pair ⟹ a 2-set option
appears; a triple ⟹ a singleton; etc. For the confined comps,
kill(ρ₂) = (ω², ω, 1, 0) and kill(ρ₁) = (ω², 1, ω, 0) are distinct
4-sets: **im ρ_i ∖ F₄XY elements have co-point support** (plus ∅/full
from F₄XY) — the co-point-or-full radical structure reborn one level
down, now WITH values: on its co-point, v₂(s) = p·(m(s) + m(z)), m =
kill(ρ₂), z the dead slot, p ∈ F₄ˣ a free scale.

### Engine 2: the slot-cost table and the T-classifier

M₁(v₀, v₂, v₃, v₄) (comp-1 free) has 128 cells in **18 orbits** under
the 9 translations × Frobenius; census {0:1, 1:9, 2:36, 3:55, 4:27};
M₂(v₀, v₁, v₃, v₄) = M₁(v₀, v₁, v₃, Frob v₄) (the swap, Frobenius on
comp 4 only — one table serves both blocks). Hand form:

    v₀ = 0:  0 alive → 0;  1 alive → 4;  2 alive → 2 (always);
             3 alive → 2 if T = 1 else 4
    v₀ = 1:  3 alive with T = 1 → 1 (δ-point);  else → 3

with the **slope classifier** T_L = v₂²(v₃v₄)⁻¹ on the L-side and
T_R = v₄(v₁v₃)⁻¹ on the R-side. Proof: the character identities
**ψ₂² = ψ₃ψ₄ and ψ₄ = ψ₁ψ₃** (immediate from (1,0), (0,1), (1,1),
(1,2) exponent arithmetic mod 3) make T = 1 on every δ-point tuple;
the cheap pair-loci are the scalings (c·ψ₂, c·ψ₃, c·ψ₄) (comp-1-dead
pairs, c = 1+ψ(r) is the SAME for comps 2, 3, 4 since r ∈ ker ψ₁ has
r₂ = 0) resp. (c·ψ₁, c·ψ₃, c²·ψ₄) (comp-2-dead pairs), and T is
invariant under exactly these scalings; the 9 + 9 cells with T = 1 are
exactly the cost-{1, 2} 3-alive orbits (counts match). ∎

### Engine 3: the slope lemma (cheap-slot counting)

On a common alive set, v₂ = p·(m + m(z₂)) carries ONE free scale p
(T_L ∝ p²), while v₃ = k₃ + k₃(z₃) and v₄ = k₄ + k₄(z₄) are FIXED by
(orbit, block, spine, alignment). Hence the slots where T = 1 can be
made cheap form **a level set of the explicit p-free function
g(s) = (m(s)+m(z₂))²·[(k₃(s)+k₃(z₃))(k₄(s)+k₄(z₄))]⁻¹**, and the
number of simultaneously cheap 3-alive slots is at most the largest
level-set of g over the alignment choices. Worked template (wt-24a,
cell (1,1), all three comps co-point-aligned on S, |S| = 3): the
δ-locus demands v₂ ∝ constant·(v₃²v₄⁻¹)^{1/2}-profile; computing,
v₃²v₄⁻¹ is CONSTANT on S while the available v₂ is a nonconstant
progression p·(m+m(z)) — at most one slot matches: cost ≥ 1+3+3 = 7 >
6 on that alignment. ∎ (per-cell instances are the Entry-24 case work)

### The C-tables (T3–T6)

Spine tables m(a₃, a₄) (machine-exact; floors reproduce Entry 22):

    wt-16:  12 except cells {ω,ω²}×{1,ω²} = 10
    wt-18a: 10 except (1,1) = (1,ω²) = 12
    wt-18b: 10 except (0,0), (0,ω), (ω,ω²), (ω²,1) = 12
    wt-24a: all ≥ 12 (14 at (0,0), (0,ω), (0,ω²))
    wt-24b: all ≥ 12 (14 on rows a₃ ∈ {ω, ω²})

Unlinked per-block tables: **for both wt-24 orbits every block minimum
is exactly 6 in every cell** — so O1 there reduces to the uniform
statement "every block costs ≥ 6", no V₀/γ-sharing needed. For
wt-16/18 the unlinked bound is 8 and the shared-(V₀, γ) linkage (with
the parity lemma L ≡ R ≡ |V₀| mod 2) carries the floor to 10 — the
linked analysis is needed exactly at their floor-10 cells. The
support+parity relaxation alone (T6) gives 3–5 per block: the slope
lemma carries 1–3 units at essentially every cell — it is the
workhorse. Translation stabilizers (T5): orders 4, 3, 1, 12, 12 — the
wt-24 spine tables collapse accordingly.

### Status and next

O1 is reduced to: (a) the per-cell slope-kill case analyses for the two
wt-24 orbits (block ≥ 6 uniformly — highest value: closes (M-im)
analytically on those orbits); (b) the linked floor-10 analyses for
wt-16/18a/18b. O2 then kills weight-exactly-10 at the floor-10 cells
via the dropped ρ-links + the +4 fibre gap. O3: the fibre-gap table
GL-compression; c₁ = c₂ = 0 (comps 1, 2 unpinned) by hand. Entry 24:
(a), as machine-verified per-cell certificates with the worked
arguments.


## Entry 24 (2026-06-12) — O1 closed: the engine evaluates every cell exactly; block ≥ 6 finishes the wt-24 orbits

Script: `a3_mim_cell_certificates.py` (E1–E4, all PASS).

### Engine exactness (E1, E3)

The Entry-23 engine — using ONLY the proven lemmas (kill-multiset
supports; the slot-cost table with the T-classifiers; slope level-sets
h_L = v₃v₄(m+m(z₂))⁻², h_L′ = v₃v₄, h_R = v₄v₃⁻¹(m′+m′(z₁))⁻¹,
h_R′ = v₄v₃⁻¹; the per-slot v₀-minimization (0,3,2,1/3) unlinked,
(0,4,2,2/4 | 3,3,3,1/3) linked) — reproduces the TRUE minima exactly:

  - all 160 unlinked block cells (5 orbits × 16 spine cells × 2 blocks);
  - all 80 linked cell values m(a₃, a₄), with the comp-4 kill-shifts of
    the two blocks tied through one γ (d₄L = d₀L + ωγ, d₄R = d₀R + γ —
    the XY-coefficient d₀ of each base must be carried, the kill vector
    drops it).

So every C-table entry is computed by a finite per-cell minimization
over (mode₂ ∈ {dead, 4 co-points, full-const}, d₃, d₄ | level) — at
most ~96 rows per block-cell, each row a 4-slot sum a human evaluates
from the engine lemmas. This is the same epistemic grade as the
Entry-10–12 tables.

### The wt-24 closure (E2)

For both wt-24 orbits, **every block at every spine cell costs ≥ 6**
(exact value 6), hence every cell has m ≥ 12 — no V₀/γ-linkage needed:

> **(M-im) holds for the six wt-24 Smith classes** — analytically,
> modulo the per-cell tables (surveyable) and the O3 residues.

### Status

O1 is complete: wt-24 closed at ≥ 12; wt-16/18a/18b floors = 10
engine-exactly, with the floor-10 cells located (4 + 14 + 12 cells).
Remaining: O2 — kill weight-exactly-10 at those cells via the two
dropped links (V₁R = ρ₁V₁L, V₂L = ρ₂V₂R; equality at engine-10 forces
per-slot minimizers, and the link cosets must miss the minimizer
products); O3 — the fibre-gap table compression and the
comps-1,2-unpinned (c₁ = c₂ = 0) hand derivation.


## Entry 25 (2026-06-12) — O2 closed: the 118 floor-10 achievers all violate the ρ-links

Script: `a3_mim_w10_kill.py` (all PASS). A weight-10 coset element at a
floor-10 orbit would have to (i) sit at a floor-10 spine cell with its
configuration an engine-10 achiever AND every slot exactly at its
M-value (the C-table floor forces cost ≥ 10, so |w| = 10 leaves no
slack — the fibre gap is not even needed); (ii) take per-slot
free-side values in the argmin sets; (iii) satisfy the two links the
confined floor dropped: ρ₁V₁L = V₁R and ρ₂V₂R = V₂L (c₁ = c₂ = 0; each
solution set is a coset of ker ρ = F₄Â + F₄XY, 16 elements).

Exhaustive enumeration: the achievers are FEW — wt-16: 48 (12 at each
of its 4 floor-10 cells), wt-18a: 48 (spread over 14 cells), wt-18b: 22
(12 cells) — and the minimizer sets are almost always singletons, so
each link check is one F₄ evaluation. **Every achiever fails BOTH links**
(except 2 in wt-18b that fail exactly one). No weight-10 element exists;
with O1 and evenness:

> **min |C(ζ)| ≥ 12 for all five orbits — (M-im) holds**, at the grade:
> proven engine lemmas + surveyable finite tables (the C-tables of
> Entry 24, the 118 one-line link kills here), transported to all 63
> classes by translation covariance.

## Entry 26 (2026-06-12) — O3 closed: comps 1, 2 unpinned by hand; the assembly

Script: `a3_mim_o3_residues.py` (all chains PASS on all 63 ζ).

### The unpinnedness derivation (c₁ = c₂ = 0), comp 1 in full

Write ζ's columns c₀..c₅ and their comp-1 y-transforms
û_i = Σ_y c_i(y) ω^{y%3} s_y^{y%2} ∈ F₄[s_y]. The crossing bookkeeping
(B's x-step crosses cut 0 only from column 5, x² from columns 4, 5; A's
x³ from columns 3, 4, 5; the s_x-power is the image column mod 2):

    off₁L = û₄ + û₅ + s_x û₅,      off₁R = û₃ + s_x û₄ + û₅.

The cycle relations transform to û_{i+3} = τ û_i (A; τ = ω² + ω s_y, a
unit) and û_{i−1} + û_{i−2} = s_y û_i (B), giving û₀ = û₁ + s_y û₂ (R2)
and **Y û₁ = ω² Y û₂ (D1)** (from R1 − R2, since τ + s_y = ω²Y).
Then c₁ = 0 ⟺ B̂₁ off₁R = Â₁ off₁L ⟸ (cancel τ, substitute R2, use
B̂₁X = s_yX, B̂₁Y = s_xY, (X+ωY)s_x = X + ω s_xY) ⟺

    Y[(X + ω) û₁ + (ω + ω² s_x) û₂] = 0,

which D1 reduces to Y(ω² + ω + 1)û₂ = 0 — identically zero. ∎
(Every step machine-verified on all 63 ζ; the comp-2 mirror chain —
v-transforms with the ω-weights on the x-side, v_{i+3} = Y v_i — is
verified the same way, endpoint Â₂off₂L = B̂₂off₂R: c₂ = 0.)

### Assembly: the (M-im) dependency tree

1. Parity: coset weights even (Entry 22 V1–V3, hand).
2. The CRT coset parametrization: comps 1, 2 unpinned ⟹ confined sets
   = im ρ_i (this entry + Entry 23); Γ₃, Γ₄ free-shift forms; the spine.
3. The engine lemmas (Entry 23, hand): kill-multiset supports; the
   slot-cost table via the T-classifiers (ψ₂² = ψ₃ψ₄, ψ₄ = ψ₁ψ₃);
   slope level-sets.
4. The C-tables (Entry 24, engine == truth): all cells ≥ 12 on wt-24;
   ≥ 10 elsewhere.
5. The ρ-link kills (Entry 25): no weight-10 elements at the floor-10
   cells. With 1: every element ≥ 12.
6. Translation transport: 5 orbits → all 63 nonzero Smith classes.

**(M-im): every base 1-cycle in a nonzero imΔ class has weight ≥ 12.**
With (M) (Entries 5–13), (R) (Entry 17), the flux characterization
(Entry 18), and the inversion duality (Entry 13):

> **THEOREM. d(gross) = 12.** Lower bound: dangerous sector by (M);
> safe sector: |v| ≥ |p(v)| with [p(v)] ∈ imΔ ∖ 0 by (R), and ≥ 12 by
> (M-im); d_X = d_Z by duality. Upper bound: τ(u*) is a weight-12
> logical (nonzero flux). Goal 1 of the Phase-A program.

Status vs. the analytic bar: every reduction is hand-proven; the finite
residues (the 18-orbit M-table, the per-cell C-table evaluations, the
118 link kills) are explicit, surveyable, and machine-cross-checked
twice over by independent routes (Entries 20, 21). Owed before external
write-up: the adversarial skeptic pass over Entries 16–26 (in addition
to the still-outstanding Entry-15 review), and the A4-style standalone
write-up with the tables typeset.


## Entry 27 (2026-06-12) — adversarial re-review: Entries 16–26 — every link HOLDS; "fully analytic" demoted to "analytic spine + two machine-certified residues"

The owed skeptic pass over the d(gross) = 12 chain (Entry 26's first owed
item), done in a fresh session under the standing rules: computation may
refute but never prove; the SAT-validated endpoints (d = 12, the sector
and class minima) are not attack targets; every load-bearing machine
check was **re-implemented independently** (`scripts/a3_adv27_recheck.py`,
75 checks, all PASS) on a deliberately different encoding path — y-major
indexing vs the lab's x-major, int-bitmask F₂ algebra vs numpy, a
differently-spelled (provably equivalent) crossing predicate, own
syndrome-join/kernel-scan census machinery, and an own CRT frame built on
the **conjugate** character-orbit reps (every F₄ constant is the Frobenius
conjugate of the lab's: Â₁ = X + ω²Y, B̂₄ = ω²Â₄, D1 reads Yû₁ = ωYû₂ —
so agreement of all counts/floors/tables is a nontrivial frame-transport
check). In parallel, every prose argument in Entries 16–26 was re-derived
by hand. One first-pass artifact, per the Entry-15 honesty standard: my
own calibration check initially asserted the zero-class linked floor is 6
and FAILED — correctly (the zero coset contains the zero element; its
floor is 0). The assertion was mine, not the lab's; fixed and documented
in the checker.

### Link 1 — Entry 16, the safe-slice framework: **HOLDS**

- **Block equations re-derived**: for v = (v₀, v₁) with p(v) = w, the two
  cover equations reduce to ∂₁v₀ = d1c_j·w; the second is automatic
  (∂₁v₀ + d1nc w = d1c w + d1nc w = ∂₁w = 0, w a cycle since p is a
  chain map). |v| = |w| + 2|v₀ off supp w| is the cleared Entry-5 boolean
  identity. Lift spot-checks pass (12 random; cover cycle + weight
  identity exact).
- **δ is the textbook connecting map.** The identification is immediate
  from the block form: the lift s_j(w) on sheet 0 has ∂₁^cov s_j(w) =
  (d1nc_j w, d1c_j w), and w a cycle forces d1nc_j w = d1c_j w, i.e. the
  image is diagonal = τ(d1c_j w). Class-invariance and cut-independence
  are then standard diagram chases (two lifts differ by im τ). Both also
  re-verified exactly: ker δ computed as a class set for every cut —
  cut-independent, equal to im Δ (64 = 64), Δ injective.
- **All 84 weight-6 logicals UNREACHABLE**: re-verified exhaustively, all
  six cuts (and calibration: the Smith reps ARE reachable at every cut,
  so the test discriminates). Census re-done independently: 120 = 36 +
  48 + 36, 36 hexagons, 84 logicals in 84 distinct classes, 3 orbits
  (36/36/12).
- **Note (bookkeeping, not a gap)**: for the final theorem only the
  inclusion im pr_* ⊆ im Δ is load-bearing; the equality ker δ = im Δ
  and the "exactly 63 classes" framing are bookkeeping (see Link 2).

### Link 2 — Entry 17, (R): **HOLDS** (re-derived in full by hand)

The homotopy is correct and genuinely one-line: B² = y⁶ + x² + x⁴ =
1 + x² + x⁴ over the cover (char 2 kills cross terms; y⁶ = 1), so
(1+x²)B² = 1 + x⁶, and for any cover cycle (Av_L = Bv_R),
z := (1+x²)Bv_L gives ∂₂z = ((1+x²)B²v_L, (1+x²)B·Av_L) =
((1+x⁶)v_L, (1+x⁶)v_R) = (1+σ)v. With τ(p(v)) = (1+σ)v (re-derived as a
chain identity and machine-verified on the full 78-dim basis), σ_* = id
and im pr_* ⊆ ker τ_* = im Δ (LES exactness, textbook given the cleared
SES). Two notes:

- **The equality leg of (R) is decorative for d = 12.** Rank–nullity
  needs im τ_* = ker pr_* (LES) plus dim H₁(cover) = dim H₁(base) = 12 —
  k-facts that are currently machine/published. The lower bound uses only
  the inclusion ([p(v)] ∈ im Δ ∖ 0 ⟹ p(v) lies in some coset C(ζ),
  ζ ≠ 0); the upper bound uses only im Δ ⊆ ker flux (easy direction).
  **Neither direction of the theorem depends on a hand proof of k = 12.**
- The "d(gross) = 12 ⟺ (M-im)" phrasing is fine with the above reading;
  re-verified the upper-bound witness independently: τ(u*) has weight 12,
  is a cover cycle, and is NOT a cover boundary.

### Link 3 — Entry 18, the no-double-wrap lemma: **HOLDS** (one implicit
step made explicit)

Re-derivation: an entry (c, f) of ∂₁∂₂ sums over 2-step paths with total
x-advance D = sx(a) + sx(b) ≤ 3 + 2 = 5; since D ≡ (c−f)_x (mod 6) and
0 ≤ D ≤ 5, **D is the same integer for every path at the entry** (the
prose leaves this implicit). With r = (x_f − j) mod 6, the crossing count
of a monotone path is exactly [r + D ≥ 6] ∈ {0, 1} (if step 1 crosses,
step 2 cannot: r + D ≤ 10 < 12). Path-pairing (one left route + one
right route per factorization, AB = BA) gives even totals, forcing the
three matrix identities — re-verified for all six cuts in my frame.
**Bridge spelled out**: flux well-definedness on classes needs
ξᵀd1c·∂₂ = 0, which is the lemma plus ξᵀd1nc = ξᵀd1c (from ξᵀ∂₁ = 0) —
one line, implicit in the log, verified. The characterization equality
im Δ^X = (im Δ^Z)^⊥ additionally needs the perfect H₁ pairing and
dim im Δ = 6 on both sides; the 6's reduce by the LES to
dim H₀ = dim F₂[Z₆²]/(A, B) = 6, which I re-derived by hand in the CRT
frame (component quotient dims (0, 0, 0, 2, 4): comps 0–2 have a unit;
comp 3's two radicals X+ωY, ωX+Y generate (X, Y); comp 4's ideal is
span{Â₄, XY}) — **hand-grade, but the paragraph is owed in the A4
write-up**. Again: only the easy inclusion im Δ ⊆ ker flux is
load-bearing for the theorem; the equality carries the Entry-21 census
cross-check only. Pins re-verified: {3,4} / {4} / {3,4} / {4} / {3}.

### Link 4 — Entries 19/22, the (M-im) frame: **HOLDS**, two sharpenings

- **Transport**: re-derived by hand and sharpened to exact matrix
  identities d2c_j∘T_x = T_x∘d2c_{j−1} and d2c_j∘T_y = T_y∘d2c_j
  (verified, all cuts), which with cut-independence of the connecting
  map give class(Tζ) = T·class(ζ); also re-verified exactly for all
  63 ζ × 36 T. Translation-only orbits already = the five orbits
  (9, 12, 36, 3, 3), swap stabilizes each — confirmed.
- **V1–V5 re-derived in full**: slot parity; column/row evenness
  (c_{i+3} = (y+y²)c_i, aug(y+y²) = 0); the V3 crossing bookkeeping
  (|w₀L| ≡ |P₄ζ|, |w₀R| ≡ |P₃ζ|+|P₄ζ|+|P₅ζ| ≡ 0) and even coset
  weight/cost; the 512-layer value bijection with the explicit inverse
  f(t) = v₀ + Σ_j Tr(v_jψ_j(t)⁻¹) and the E ≤ 2 rigidity (9 δ-tuples /
  36 pair sums); the ρ-locks (u² = aug(u)²·1 re-proved; ρ_i² = 0;
  im ρ_i = F₄ρ_i ⊕ F₄XY, 16 elements); the Γ₃ parametrization (the
  shift map (b, c) ↦ (b+ωc, ωb+c) has determinant 1−ω² = ω ≠ 0, so the
  two XY-shifts are free; kernel F₄XY gives 64) and Γ₄ (B̂₄ = ωÂ₄ ⟹ 16,
  one shared twisted shift).
- **Sharpening 1 (new): off₀ = off₂ = 0 identically** — not merely
  "diagonal" (Entry 19) or "realizable" (Entry 19 structure result 4).
  At comps 0 and 2 the A-relation multiplier is comp(y+y²) = Y, so each
  column collapse satisfies v_i = Yv_{i+3} = Y²v_i = 0. Verified on all
  63 ζ. Entry 19's parity-lemma content at comp 0 reduces to "V₀ shared,
  ranging over the 16 diagonals"; nothing downstream changes, but the
  write-up gets simpler.
- **V6 (the +4 fibre gap) verified (66 fibres, all gaps exactly 4) and
  found NOT load-bearing**: Entry 25's equality analysis never needs it
  (cost = 10 exactness forces per-slot minimality by itself). One fewer
  residue for the analytic bar.
- Confined floors re-verified by brute force in the conjugate frame:
  **10 / 10 / 10 / 12 / 12.** End-to-end: 200 random coset elements per
  orbit decompose into (spine, shifts, confined values), satisfy BOTH
  ρ-links, and obey |w| ≥ m(cell) ≥ 10 and |w| ≥ 12.

### Link 5 — Entry 23, the engine lemmas: **HOLDS**

Kill-multiset lemma re-derived (coefficients of c·1 + αX + βY + δXY are
(c+α+β+δ, α+δ, β+δ, δ); kill(ρ₁), kill(ρ₂) are 4-distinct ⟹ co-point
supports). The slot-cost hand rules re-verified against an independent
brute-force M₁ AND M₂ on all 128 cells each (and mutation-tested: a
wrong classifier or wrong cheap-cost produces 24 resp. 9 mismatches —
the check is sensitive). Character identities ψ₂² = ψ₃ψ₄, ψ₄ = ψ₁ψ₃
re-derived from exponent arithmetic; the counting completion re-done by
hand (census 1/9/36/55/27: 36 = 27 two-alive + 9 T=1 three-alive;
27 = 9 one-alive + 18 T≠1; 55 = the v₀=1 non-δ cells; totals match the
rule). 18 orbits under 9 translations × Frobenius confirmed; M₂ =
M₁∘(Frob on comp 4) re-derived via the t_x↔t_y swap and confirmed.

### Link 6 — Entry 24, engine == truth: **HOLDS as mathematics;
surveyability disputed (see audit)**

The published outputs were re-verified independently: C-table value
multisets (wt-16 {10:4, 12:12}; wt-18a {10:14, 12:2}; wt-18b {10:12,
12:4}; wt-24 all ≥ 12), floors, floor-10 cell counts (4 / 14 / 12),
translation stabilizers (4, 3, 1, 12, 12), and the wt-24 closure —
**every unlinked block minimum equals 6 at every cell** (2 × 16 × 2,
exact). The lab's own engine == truth scripts re-run and pass. So the
C-tables are true and the wt-24 orbits do close at ≥ 12.

### Link 7 — Entry 25, the ρ-link kills: **HOLDS**

Independent re-enumeration in the conjugate frame: achievers 48 / 48 / 22
(wt-16: 12 at each of its 4 floor-10 cells; spreads over 14 / 12 cells),
each tested against BOTH dropped links over the FULL 16-element ker-ρ
cosets and the full per-slot argmin products (no singleton shortcut):
**every achiever fails at least one link**; 116 fail both, exactly 2
(wt-18b) fail exactly one — matching the lab. The logic audited: a
weight-10 coset element would sit at a floor-10 cell with config cost
exactly 10, forcing per-slot minimality, argmin free sides, and both
links (c₁ = c₂ = 0) — the enumeration is complete over the verified
Γ-parametrization, and the kill machinery is calibrated (on the zero
class it produces floor 0 and the hexagon as a links-satisfiable
config; on real coset elements both links hold). With evenness and the
C-table floors: no sub-12 elements on any orbit; transport extends to
all 63 classes.

### Link 8 — Entry 26, unpinnedness + assembly: **HOLDS**, one
simplification found

- **Comp-1 chain re-derived end-to-end by hand** by an independent route:
  group coefficients directly — the claim reduces to (B̂₁X + Â₁)û₁ +
  (B̂₁Y + Â₁X)û₂ = (ωY + XY)û₁ + (Y + ω²XY)û₂ = Y[(ω+X)û₁ + (1+ω²X)û₂],
  and D1 cancels it exactly ((X+ω)ω² + 1 + ω²X = 0). The crossing
  bookkeeping off₁L = û₄+û₅+s_xû₅, off₁R = û₃+s_xû₄+û₅ independently
  re-derived from the cut rule and verified on all 63 (conjugate frame
  throughout: τ′ = ω+ω²s_y, D1′: Yû₁ = ωYû₂).
- **Sharpening 2 (new): the comp-2 mirror chain is unnecessary.** At
  comp 2 the offsets vanish identically (off₂ = 0; Sharpening 1), so
  c₂ = 0 is a one-liner: v_i = Yv_{i+3} = Y²v_i = 0. The lab's mirror
  chain is correct but proves something weaker than what is true; the
  A4 write-up should use the one-liner. (Cosmetic: `a3_mim_o3_residues.py`
  U4 initializes an unused `ok_md` and never checks a D1-mirror — moot
  given off₂ = 0, but worth knowing it was not checked there.)
- **Assembly re-audited.** The load-bearing tree for d(gross) = 12:
  (1) dichotomy on [p(v)]; (2) dangerous: (M) [cleared, Entries 5–15];
  (3) safe: homotopy + LES ⟹ [p(v)] ∈ im Δ ∖ 0 ⟹ p(v) ∈ C(ζ), ζ ≠ 0;
  transport ⟹ WLOG one of 5 reps; parity + C-tables + link kills ⟹
  |p(v)| ≥ 12 ⟹ |v| ≥ |p(v)| ≥ 12; (4) duality d_X = d_Z [cleared];
  (5) upper bound: τ(u*) weight 12, nontrivial via flux(u*) ≠ 0 +
  im Δ ⊆ ker flux + ker τ_* = im Δ. min-arithmetic checks. **Not needed
  anywhere**: ker δ = im Δ equality, k = 12, the flux characterization
  equality, V6, and the Entry-19/20 superseded floors — all decorative
  or cross-check-only. The chain as assembled in Entry 26 is correct.

### The surveyability audit (the program's own §1 bar)

1. **The 18-orbit M-table (Entry 23): PASSES.** A 5-line rule + two
   hand-proven classifier identities + a by-hand counting completion;
   fully comparable to a published case table.
2. **The per-cell C-table evaluations (Entry 24): FAIL the bar as
   currently organized.** The wt-24 closure alone is 2 orbits × 16
   cells × 2 blocks × ~96 engine rows ≈ 6k rows; the linked floor-10
   tables are 80 cells, each a min over 64 shared (V₀, γ) choices times
   two ~96-row block evaluations — these were machine-swept, with
   exactly ONE worked template cell in the log. "A finite check is
   allowed only as the residue of an analytic reduction to a few
   human-surveyable cases" — this residue is currently a machine
   enumeration with an analytic recipe attached. Entry 24's claim of
   "the same epistemic grade as the Entry-10–12 tables" is not yet
   earned: those tables were walked in prose; these are certificate
   dumps. The compression assets exist (stabilizer orders 12 on the
   wt-24 spines; the slope lemma; B̂₄ = ωÂ₄) but no compressed table
   has been written.
3. **The 118 ρ-link kills (Entry 25): SPLIT verdict.** The per-achiever
   checks are surveyable (118 one-line F₄ evaluations — an acceptable
   appendix table), but the **completeness** of the achiever list (that
   these are ALL engine-10 achievers) inherits the machine status of
   residue 2.

### Verdict

**Mathematics: the chain HOLDS end to end. No gap found.** 75/75
independent checks pass; every prose argument re-derived; two
sharpenings found (off₀ = off₂ = 0; the comp-2 one-liner) and one
implicit step closed (path-advance uniqueness in no-double-wrap). The
(M-im) endpoint is now **triple-verified** by independent machine routes
(Entry 20 value sweep; Entry 21 census; this review's own census + coset
machinery in a conjugate frame).

**The headline claim demotes from "fully analytic" to: "d(gross) = 12 —
hand-proven reductions + one surveyable case table (M-table) + two
machine-certified finite residues (the C-tables and the achiever-list
completeness)."** This is stands-with-debts, not a break: the debt is
write-up work (walk the compressed C-tables and derive the achiever
lists by hand in the A4 extension), not new mathematics. Until that is
done, external statements should say "verified-finite with an analytic
spine" for the safe sector, while d(gross) ≥ 6 (Entries 5–15) remains
fully analytic as previously cleared.

(Process note: the Entry-15 review of the d ≥ 6 chain lives on the
sibling branch `claude/competent-proskuriakova-f31540` (verdict: HOLDS,
49 checks); this branch's log jumps 14 → 16. Merging the two review
entries into one history is an outstanding integration chore.)

### Next

1. A4-extension write-up with the COMPRESSED C-tables walked by hand
   (stabilizer + slope-lemma compression) and the achiever lists derived
   from the floor-10 cell structure — this is what restores "fully
   analytic" honestly.
2. Fold Sharpenings 1–2 into the write-up (they shorten O3 to two lines
   and delete the comp-2 mirror chain).
3. Merge the Entry-15 branch; then the full d = 12 chain has both owed
   reviews on one history.


## Entry 28 (2026-06-12) — the A4 extension: both Entry-27 residues discharged; d(gross) = 12 fully analytic

Deliverables: `notes/A4_writeup.md` Part II (§§8–14 + Appendices C–D,
Theorem D) and `scripts/a3_a4ext_recheck.py` (the table certifier,
all PASS). Entry 27's items 1–2 are done (item 3, the Entry-15 branch
merge, landed earlier in commit `909b31c`).

### The new structure that makes the compression work

The whole §12/§13 analysis runs in one coordinate system (A4 §10, "the
slot frame"), built on facts that were implicit in Entries 22–24 but
never isolated:

- **m′² = ω²m and m² = ω²m′** (m = kill(B̂) = (ω²,ω,1,0),
  m′ = kill(Â₃) = m∘(x↔y)). So kill(Â₄) is a *scalar multiple* of
  kill(B̂): up to scale there are only TWO labelings, m and its slot
  swap, and m̃ = m + ω² is an additive isomorphism Z₂² ≅ (F₄, +).
  Every component direction on the L block is m-affine.
- **The confined comps are full affine lines**: slot values of
  im ρ₂ = {p·m + c}, im ρ₁ = {p·m′ + c} — much cleaner than
  "F₄ρ ⊕ F₄XY".
- **The comp-4 tie**: V₄L = ω·V₄R + w₄ with w₄ = off₄L + ω·off₄R a
  fixed vector per orbit (the Γ₄ ideal is a graph; γ-bookkeeping
  becomes the affine dictionary d₄L = ωγ + e_L, d₄R = γ + e_R).
- **The pair-ratio lemma**: the fibre partition of a pencil κ + λu
  (u bijective) degenerates at six explicit ratios λ_P — one line per
  table entry; it generates every fibre-type/trichotomy table.
- **The chord-slope + hyperbolic-quadruple lemma**: the deepest
  cheap-slot counts reduce to "no three of four explicit points of
  AG(2, F₄) are collinear", and the points that occur form hyperbolas
  H_c = {uv = c} ∪ {0}, which never have three collinear. This is the
  slope lemma in its final, reusable form.

### Residue 2 discharged (the wt-24 C-tables, was ~6k machine rows)

All four wt-24 block problems are **one problem**: with the
cost-preserving moves (slot relabelings; the nine translation scalings
s₂² = s₃s₄; Frobenius; M₂ = M₁∘Frob₄), L(24a) = S(a₃,a₄),
L(24b) = S(a₄,a₃), R(24a) ≅ S(a₃,a₄²), R(24b) ≅ S(a₄²,a₃), where
S(a,b) is the standard form (conf line ⟨m⟩; v₃ = am + c₃;
v₄ = bm + ωθ + c₄), θ = (1,0,1,0). The walk of S — 33 buckets by
(comp-3 state × conf mode × comp-4 fibre × dead-slot alignment), each
1–3 lines, one hyperbola application at the (conf co-point,
z₂ = z₃ = z₄, b = 1) bucket — gives **S ≥ 6 everywhere** (A4 §11,
table C.1), hence every wt-24 cell ≥ 12 with no V₀/γ linkage needed.

### Residue 3 discharged (the achiever-list completeness)

The **achiever-structure lemma** (A4 §10.6): per cell, per shared
(V₀, γ), the two block minima are each ≡ |V₀| (mod 2), so their sum is
even; cost-10 configurations exist exactly where min_L + min_R = 10 and
are exactly Argmin_L × Argmin_R. So completeness of the achiever list
reduces to the per-cell function (V₀, γ) ↦ (min_L, min_R) on its low
range — derived by the locus rules R1–R5 (zero-slot/dead-pair rigidity,
δ-slot consistency, shape ladder): per cell 0–4 loci, each pinned by a
small F₄ system (worked examples: wt-16 cells (ω²,ω²) and (ω,1) in
full, including the (5,5) family's p²-consistency; the wt-16 L3 = ∅
derivation ends in the same hyperbola H_{ω²}). Tables C.2–C.4 list all
loci: 48 + 48 + 22 = 118 achievers — matching Entry 25/27 exactly —
and the cost-8 kill (m ≥ 10 at every cell) is the visible
(V₀, γ)-disjointness of the L4/R4/L3/R3 loci. The ρ-link kills are now
genuinely one-line: at singleton argmin products the check is ONE
convolution (worked: ρ₁·(1,0,0,ω²) = (ω,1,0,ω²) ≠ V₁R at the wt-16
(5,5) head); 116 fail both links, 2 fail one, 0 survive.

### Folded in

Entry 27's Sharpening 1 (off₀ = off₂ = 0 identically) and Sharpening 2
(c₂ = 0 one-liner) are in A4 §9.4; the owed H₀-dimension paragraph
(component quotient dims (0,0,0,2,4)) is A4 §9.2; the no-double-wrap
implicit step (path-advance uniqueness) is explicit in A4 §9.2.

### Verification (confirmation only)

`a3_a4ext_recheck.py`: 60+ checks, all PASS — the frame facts (F1–F6),
S ≡ 6 and the four reindexing identities (W1–W2), the 33 bucket minima
exactly (W3), per-(V₀,γ) sums even and ≥ 10 at every wt-16/18 cell and
≥ 12 at every wt-24 cell (K1), the C.2–C.4 locus tables exactly (K2),
the 118 achievers, the structure-lemma instance, the 116/2/0 kill
split, and the worked convolution (K3–K4). `uv run pytest`: 265 pass.

### Status

> **d(gross) = 12, fully analytic** (A4 Theorem D): every reduction
> hand-proven; the finite case content is the M-table rule (18-orbit,
> previously cleared), the §11 bucket table (24 derived rows), the
> §12 locus tables (~80 rows over three orbits, each a minutes-long
> application of stated rules, with worked representatives), and the
> §13 kill table (118 one-line convolutions). Same epistemic grade as
> Part I's §6.3 classification. d(gross) ≥ 6 unchanged (Entries 5–15).

Owed (honesty ledger): the §12 locus tables are rule-derived with
worked representatives per orbit, not walked cell-by-cell in prose —
the same presentation grade as the Entry-10–12 master tables that the
Entry-15 review cleared, but a future skeptic pass may demand more
worked cells; the recheck script certifies every row meanwhile.

### Next

1. The owed adversarial review of THIS write-up (the A4 Part II prose
   vs. the certified tables), Entry-15/27 style.
2. Goal 2 — template runs on other BB bases (the §11/§12 frame is
   instance-generic: only m, the offsets, and the e/d_w dictionary
   change).
