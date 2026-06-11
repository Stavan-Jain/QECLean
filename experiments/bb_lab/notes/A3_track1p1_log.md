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
