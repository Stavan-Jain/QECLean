# A1 — L2 literature: Z₂-cover transfer, Smith theory, lifted/balanced-product distance

Date: 2026-06-09 (research pass) / 2026-06-10 (adversarial verification pass).
Lane L2 of Phase 1 of the analytic-bound program. All quotes below are the
**verifier's** re-fetched verbatim text, with the verifier's corrections
applied to the claims.

**Lane verdict.** The Track-B target — an h=2 (even) cover-transfer distance
theorem over F₂ — is **genuinely open as of June 2026** and the literature
hands us both the exact failure point and two viable replacement tools. The
odd-h theorem is published twice (SRB Thm 4.7, arXiv:2511.13560; Guémard–Zémor
Prop 3.5, arXiv:2502.20297v2, at the full generality of free-Γ-module chain
complexes), so Track B must not claim odd-h novelty; the even-h case is
conjectured by SRB (§7) and unresolved by all 6 citing papers (count corrected
from 5 by the verifier — a 6th appeared 2026-06-07 and also does not resolve
it). The proof dies at exactly one lemma (SRB Lemma 4.4: p∘τ = h·I = 0 mod 2
for even h) while the chain maps p_•, τ_• themselves exist for **all** h, so
Track B needs only a new injectivity/surjectivity argument, not new maps. The
two surviving tools: Kovalev–Pryadko 2013 Thms 8–9 — a published, rigorous,
F₂, **even**-symmetry distance lower bound whose symmetric-part decomposition
sidesteps the transfer collapse — and classical Smith theory for free
involutions (Bredon via Degtyarev–Kharlamov), which no one has ever applied to
QEC covers. All 13 findings verified: 6 CONFIRMED, 7
CONFIRMED-WITH-CORRECTIONS, 0 refuted. One phantom citation
("Hsieh–Le Gall 2020") confirmed dead and must be purged from HANDOFF.md.

## Scoreboard

| id | verdict | feeds |
|---|---|---|
| L2-srb-thm31-cover-conditions | CONFIRMED-WITH-CORRECTIONS | B |
| L2-srb-lemma44-even-h-collapse | CONFIRMED | B |
| L2-srb-odd-h-theorems | CONFIRMED-WITH-CORRECTIONS | B |
| L2-srb-thm48-weight-preserving-lift | CONFIRMED-WITH-CORRECTIONS | B (stretch) |
| L2-srb-s7-conjecture | CONFIRMED | B |
| L2-guemard-zemor-prop35-transfer | CONFIRMED-WITH-CORRECTIONS | B |
| L2-smith-sequence-machinery | CONFIRMED | B (core tool) |
| L2-kp2013-thm5-floor-bound | CONFIRMED-WITH-CORRECTIONS | A, B |
| L2-kp2013-thm8-9-even-c-over-F2 | CONFIRMED-WITH-CORRECTIONS | B (best prior art) |
| L2-wang-pryadko-statement3 | CONFIRMED | A, B |
| L2-lin-pryadko-statement12-13 | CONFIRMED | A, B |
| L2-srb-citing-papers-no-resolution | CONFIRMED-WITH-CORRECTIONS | B (novelty window) |
| L2-hsieh-legall-phantom-citation | CONFIRMED | all (citation hygiene) |

## Verified findings

### L2-srb-thm31-cover-conditions — the formal cover class (CONFIRMED-WITH-CORRECTIONS)

**Claim (corrected).** SRB's main theorem (Thm 3.1) gives **sufficient**
conditions — *not* a biconditional characterization, per the verifier; the
formal statement is one-directional and the "must satisfy" reading exists only
in the paper's informal prose — for one BB code's Tanner graph to be an h-fold
cover of another's: with Q(A,B,l,m) and Q̃(Ã,B̃,l̃,m̃), if (1) l̃ = ul,
(2) m̃ = tm, (3) the monomial exponents of Ã reduce mod (l,m) to those of A,
(4) same for B̃ vs B, then T̃ is graph-isomorphic to the derived graph D(T,Γ)
with voltage group Γ = (Z_u × Z_t, +). Thm 3.3 makes
π((ã,b̃)) = (Mod(ã,l), Mod(b̃,m)) a |Γ|-covering; Thm 3.4 gives an infinite
sequence of h-cover codes with h := ut. The voltage-group form (deck
transformations ≅ Γ) makes the cover a **free** Γ-action — the hypothesis a
Smith-theory argument needs.

**Source.** Symons–Rajput–Browne, *Sequences of Bivariate Bicycle Codes from
Covering Graphs*, arXiv:2511.13560v1 — Thm 3.1 (p.15), Thm 3.3 (p.17),
Thm 3.4 + Example 5 (p.18).

**Verified quote.**

> Suppose the following conditions are met: 1. l̃ = ul 2. m̃ = tm
> 3. Mod(α̃_i1, l) = α_i1 and Mod(α̃_i2, m) = α_i2, where α̃_i = (α̃_i1, α̃_i2)
> are the powers of x and y in the monomials Ã_i = x^a y^b in
> Ã = Ã_1 + Ã_2 + Ã_3, and similarly for α_i = (α_i1, α_i2) and the monomials
> A_i in A. 4. Mod(β̃_i1, l) = β_i1 and Mod(β̃_i2, m) = β_i2 […] Then the
> Tanner graph T̃ is graph isomorphic to the derived graph G = D(T, Γ).
>
> [Thm 3.3] Under the conditions in Theorem 3.1, the Tanner graph T̃ equipped
> with the natural projection map π : Z_l̃ × Z_m̃ → Z_l × Z_m defined as
> π((ã, b̃)) = (Mod(ã, l), Mod(b̃, m)) is a |Γ|−covering of the Tanner graph T.
>
> [Example 5] The gross code [[144, 12, 12]] with (Ã = x³ + y + y², B̃ = y³ +
> x + x², l̃ = 12, m̃ = 6) is a double cover of the [[72, 12, 6]] code with
> (A = x³ + y + y², B = y³ + x + x², l = 6, m = 6). The polynomials defining
> the two codes are the same, so the fact that the gross code is a double
> cover simply follows from the fact that l̃/l = 2.

**Applicability to gross.** Direct: gross = 2-cover (u=2, t=1, Γ=Z₂) of
[[72,12,6]] over G' = Z₆ × Z₆ with identical polynomials; the verifier
re-derived conditions 3–4 independently (all exponents < l = m = 6, so they
hold trivially). No semisimplicity/Sylow hypotheses to drop.

**Feeds.** Track B — this is the formal definition of the cover class the h=2
transfer theorem must be stated over.

### L2-srb-lemma44-even-h-collapse — the exact failure point (CONFIRMED)

**Claim.** SRB Lemma 4.4 is the exact point where the even-h proof breaks:
the projection map p (eq. (21): p(x^ã y^b̃) = x^Mod(ã,l) y^Mod(b̃,m)) composed
with the lifting map τ (eq. (32): τ(x^a y^b) = Σ_{j<u} Σ_{k<t} x^{a+lj}
y^{b+mk}) satisfies p∘τ = h·I (proof's intermediate step), which over F₂ is
the identity for h odd and the **zero map** for h even. (Verifier note: p and
τ are the underlying linear maps on monomial spaces; the chain maps p_•, τ_•
are built degree-wise from them in Thms 4.1/4.3.) This confirms the program's
belief (HANDOFF 6k) about where the proof fails — and SRB's Remark 9 says
explicitly that only injectivity/surjectivity arguments are lost, leaving
other routes open.

**Source.** SRB arXiv:2511.13560v1 — Lemma 4.4 + proof (pp.24–25), Remark 8
(pp.25–26), Remark 9 (p.27), eqs. (21)/(32) at Remarks 6/7.

**Verified quote.**

> Lemma 4.4. […] When h is odd, p ∘ τ = I. When h is even, p ∘ τ = 0.
> [Proof:] (p∘τ)(x^a y^b) = … = ut x^a y^b = h x^a y^b. Since we are working
> over F_2, (p ∘ τ)(x^a y^b) = x^a y^b when h is odd and (p ∘ τ)(x^a y^b) = 0
> when h is even.
>
> [Remark 8] When h is even, we have p_• ∘ τ_• = 0 and therefore
> H_1(p_•) ∘ H_1(τ_•) = 0. […] We empirically observe k_h ≥ k for h even in
> all cases tested (see Section 6) and conjecture this to be the case
> theoretically. We leave the proof of this or the construction of a
> counter-example for future research.
>
> [Remark 9] When attempting to generalize these arguments to situations
> where h is even or k ≠ k_h, we arrive at points in the proof where the
> injectivity or surjectivity of p_i or τ_i respectively or their
> corresponding induced maps in homology are needed. These are clearly not
> guaranteed in general.

**Applicability to gross.** Gross's cover is h=2 (even), so SRB's rigorous
bounds give nothing for it; the collapse p∘τ = 2·I = 0 mod 2 is precisely
realized on gross.

**Feeds.** Track B — pinpoints the gap; any Track-B proof must avoid every
step requiring p∘τ invertible.

### L2-srb-odd-h-theorems — what survives for all h vs odd h only (CONFIRMED-WITH-CORRECTIONS)

**Claim (corrected).** SRB's rigorous parameter bounds are odd-h: Thm 4.5
(h odd ⟹ k_h ≥ k), Thm 4.6 (h odd ⟹ d_h ≤ hd), Thm 4.7 (h odd and k_h = k ⟹
d ≤ d_h ≤ hd). **Correction (verifier):** the headline "all rigorous results
are odd-h" overlooked Thm 4.8 — a rigorous **any-h** conditional bound
d_h ≤ d (see next finding) — and Thms 4.1/4.3/Lemma 4.4 are themselves
rigorous any-h results. The load-bearing structural fact stands: the chain
maps exist for ALL h — Thm 4.1 (projection p_• is a chain map Q̃_• → Q_•
inducing p̂_1 on H₁) and Thm 4.3 (lifting τ_• = (p^•)ᵀ is a chain map
Q_• → Q̃_• inducing τ̂_1) carry no parity hypothesis; only the homological
injectivity/surjectivity arguments need h odd. So Track B can reuse p_• and
τ_• as-is and needs only a new argument that τ̂_1 is injective (or p̂_1
surjective) for h=2.

**Source.** SRB arXiv:2511.13560v1 — Thm 4.1 (pp.19–20), Thm 4.3 (p.23),
Thm 4.5 (p.25), Thm 4.6 (p.26), Thm 4.7 (p.27).

**Verified quote.**

> Theorem 4.5. With the same conditions as in the preceding lemma, if h is
> odd then k_h ≥ k. […] Theorem 4.6. Let Q(A,B,l,m) and Q̃(Ã,B̃,l̃,m̃) be two
> BB codes with parameters [[n,k,d]] and [[n_h = hn, k_h, d_h]] respectively
> that satisfy the conditions of Theorem 3.1 so that Q̃ is an h-cover code of
> Q. If h is odd, d_h ≤ hd. […] Theorem 4.7. With the same conditions as in
> the preceding theorem, suppose h is odd and k_h = k. Then d ≤ d_h ≤ hd.
>
> [Thm 4.1(a), no parity hypothesis] Then p_• is a chain map and induces a
> map p̂_1 := H_1(p_•): H_1(Q̃_•) → H_1(Q_•).
>
> [Thm 4.3(a), no parity hypothesis] Then τ_• = (p^•)^T and is a chain map.
> τ_• induces a map τ̂_1 := H_1(τ_•): H_1(Q_•) → H_1(Q̃_•) such that
> τ̂_1 = (p̂^1)^T.

**Applicability to gross.** Thm 4.7 as stated does not apply to gross (h=2
even). The chain maps of Thms 4.1/4.3 DO apply to gross's cover pair
(gross, [[72,12,6]]).

**Feeds.** Track B — these are the statements whose even-h analogues are the
target, and the reusable infrastructure.

### L2-srb-thm48-weight-preserving-lift — parity-free saturation tool (CONFIRMED-WITH-CORRECTIONS)

**Claim (corrected).** SRB Thm 4.8 gives a parity-free distance **upper**
bound mechanism: if a "weight-preserving lift" σ_• (built from a section s of
the graph cover, σ(x^a y^b) = x^{a+lγ_a} y^{b+mδ_b}, Defs 18/19, Remark 10)
forms a chain map σ_• : Q_• → Q̃_• (base → cover — **verifier correction**:
the paper's inline theorem text has a typo writing Q̃_• → Q_•, but its own
diagram (41), proof, and Remark 10's p∘σ = I all force base → cover, which is
what the researcher quoted), then d_h ≤ d, for ANY h. Failure to find such a
chain map does NOT imply d_h > d — SRB frame it as a numerical screening
tool, not a saturation certificate.

**Source.** SRB arXiv:2511.13560v1 — Defs 18/19 + Remark 10 (p.27), Thm 4.8 +
discussion (p.28).

**Verified quote.**

> Theorem 4.8. Let Q̃• and Q• be the chain complexes as in Remark 3 […] with
> the same properties as in the statement of Theorem 3.1. Suppose there is a
> chain map σ• [diagram (41), vertical arrows σ2, σ1, σ0 pointing from
> Q2, Q1, Q0 up to Q̃2, Q̃1, Q̃0] where σ1 := σ′ ⊕ σ′ and σ1, σ′, σ0 need not
> be the same maps. Then dh ≤ d. […] Failure to find a weight-preserving lift
> does not in general rule out that dh ≤ d however. The checking of
> weight-preserving lifts should be treated as a numerical tool for
> efficiently ruling out low distance codes as opposed to a method for
> guaranteeing that distance has increased relative to the base code.

**Applicability to gross.** Applies to gross's h=2 cover with no parity
hypothesis. Since d_gross = 12 > 6 = d_base, no weight-preserving-lift chain
map can exist for the (gross, [[72,12,6]]) pair — a checkable consistency
fact.

**Feeds.** Track B stretch goal (saturation criterion d_cover = 2·d_base): an
analytic NON-existence proof of weight-preserving lifts is necessary-side
machinery; conversely existence proofs certify non-saturation. Works for
even h.

### L2-srb-s7-conjecture — the conjecture Track B is the h=2 case of (CONFIRMED)

**Claim.** The SRB conjecture (abstract, Introduction, and §7 Conclusion):
every h-cover BB code of a base [[n,k,d]] BB code has parameters
[[n_h = hn, k_h ≥ k, d ≤ d_h ≤ hd]] for ALL h (including even). Evidence:
Table 1 (k_h ≥ k for all unique covers, h = 2..5, over bases [[18,8,2]],
[[72,12,6]], [[14,6,2]]); Tables 2–5 (weight-6 cover sequences, distances
exact via MIP up to d = 14, BP-OSD upper bounds beyond); Tables 6–10
(weight-8 sequences). The authors attribute the proof breakdown explicitly to
char(F₂) | h. The proven/conjectured split is clean: proofs odd-h only (and
d ≤ d_h additionally requires k_h = k); conjecture unconditional in h.

**Source.** SRB arXiv:2511.13560v1 — Abstract; §7 Conclusion (p.39); §6
Tables 1–10 (pp.33–38).

**Verified quote.**

> We have empirically observed the same behaviour for codes with even h and
> conjecture that the parameters of a h-cover code satisfy [[n_h = hn,
> k_h ≥ k, d ≤ d_h ≤ hd]] for any h. All the numerical evidence we have
> gathered to date supports this conjecture. […] This work raises several
> outstanding open questions. Our proof techniques for establishing bounds on
> k and d break down when h is even as then the characteristic of F_2 divides
> h (see for example Lemma 4.4). While we have numerical evidence that all
> h-cover BB codes obey the conjectured bounds k_h ≥ k and d ≤ d_h ≤ hd
> regardless of h, establishing this rigorously may require different tools
> from those employed here.

**Applicability to gross.** If the d ≤ d_h direction is proven for h=2, the
chain gross → [[72,12,6]] → [[36,8,4]] → [[18,8,2]] gives an analytic floor
d_gross ≥ 2 (weight-1 exhaustion at the base), and d_gross ≥ 6 if applied
only at the top step with d_base = 6 taken as input.

**Feeds.** Track B IS this conjecture's h=2 case. As of June 2026 it is open
(see L2-srb-citing-papers-no-resolution). The authors' own "different tools"
remark is consistent with the program's Smith-theory plan.

### L2-guemard-zemor-prop35-transfer — concurrent odd-t result at free-Γ-module generality (CONFIRMED-WITH-CORRECTIONS)

**Claim (corrected).** Guémard–Zémor proved the same odd-degree result via
the cellular-homology transfer homomorphism — **concurrently, not
"independently"** (verifier correction: SRB's acknowledgments thank Guémard
for discussions and comments on an early draft, and SRB footnote 2
anticipates GZ v2; the two posted 38 minutes apart on 2025-11-17, neither
citing the other's result as a source, but not in mutual isolation) — and
explicitly generalized it beyond quantum Tanner codes to ANY lifted code that
is a chain complex of free Γ-modules (Remark 3.6), which **includes BB
h-covers** (researcher's inference, verifier-checked as sound: GZ never
mention BB codes, but Remark 3.6's sole hypothesis is satisfied by Galois
h-covers of BB codes). Prop 3.5: Galois t-lift with t odd gives ñ = tn,
k̃ ≥ k, d̃ ≤ td, and if k̃ = k then d̃ ≥ d. Same even-t obstruction:
π#∘τ# = t·I = 0 over F₂ for even t (this sentence follows the proposition
statement in the paper, not precedes it — verifier correction of the quote
label). GZ v1 (2025-02-27) has no transfer section; v2 (2025-11-17) still
handles only odd t.

**Source.** Guémard–Zémor, *Moderate-length lifted quantum Tanner codes*,
arXiv:2502.20297v2 — Prop 3.5, Remark 3.6, Lemma 3.8 (§3.3). SRB footnote 2
+ ref [45] cross-checked.

**Verified quote.**

> Proposition 3.5. Let C̃ be a quantum Tanner code obtained by a Galois
> t-lift, with t odd, of a quantum Tanner code C with parameters [[n, k, d]].
> Then, the parameters [[ñ, k̃, d̃]] of C̃ satisfy ñ = tn, k̃ ≥ k, and
> d̃ ≤ td. Moreover, if k̃ = k, then d̃ ≥ d.
>
> Remark 3.6. The validity of Proposition 3.5 extends to the code lifting
> method of [Gue25], as made clear from the technics, which does not depend
> on the structural specificities of quantum Tanner codes. In particular, the
> result just relies on the lifted quantum code C̃ to be a chain complex of
> free modules over a group Γ of order t.
>
> The composition π# ◦ τ# is multiplication by t, and since we consider F2-
> vector spaces, this map is the zero map when t is even.
>
> Lemma 3.8. Let C be a quantum (Tanner) code and C̃ a connected Galois lift
> of C with group of deck transformations Γ. Then, C̃ is a chain complex of
> free Γ-modules.

**Applicability to gross.** Gross's t=2 cover is a Galois 2-lift (deck group
Z₂ acts freely), so gross's cover complex IS a chain complex of free
F₂[Z₂]-modules — Prop 3.5's framework applies but its t-odd hypothesis fails.

**Feeds.** Track B: (a) preempts any "novel" odd-h theorem — both papers
already cover it, GZ at full free-Γ-module generality; (b) confirms the
even-t case was open as of Nov 2025 in BOTH research lines; (c) Lemma 3.8's
"chain complex of free Γ-modules" is exactly the free-action hypothesis a
Smith-sequence argument needs — Track B should state its theorem at this
generality.

### L2-smith-sequence-machinery — the Smith exact sequence, citable form (CONFIRMED)

**Claim.** The precise Smith-theory algebra for Track B, with citable source:
for a space (here: chain complex) X with involution c, fixed set F, quotient
X′ = X/c, over F₂ (the survey's global Z₂-coefficient convention) one defines
Sm_*(X) = Ker[(1+c_*) : S_*(X) → S_*(X)]; there are canonical identifications
Sm_*(X,F) = Im(1+c_*), Sm_*(X) = S_*(F) ⊕ Im(1+c_*), and the chain-level
transfer tr_* : S_*(X′,F) → Sm_*(X,F) is an **isomorphism**; the Smith long
exact sequences arise from 0 → Sm_*(X) → S_*(X) —(1+c_*)→ Sm_*(X,F) → 0.
For a FREE involution (F = ∅, the BB 2-cover case) this specializes — the
specialization is the researcher's own derivation, verifier-checked as a
faithful, hypothesis-preserving consequence — to
0 → C_*(base) —tr→ C_*(cover) —(1+σ)→ C_*(base) → 0, with long exact sequence
… → H_p(X′) —tr→ H_p(X) —pr→ H_p(X′) —Δ→ H_{p−1}(X′) → …, where
Δ(x) = x ∩ ω, ω ∈ H¹ the characteristic class of the double cover. Proofs:
Bredon, *Introduction to Compact Transformation Groups*, Chapter 3 (the
survey's hedge: "Most results cited in this section are due to P. A. Smith;
proofs can be found, e.g., in [Br, Chapter 3]").

**Source.** Degtyarev–Kharlamov, *Topological properties of real algebraic
varieties: du côté de chez Rokhlin*, arXiv:math/0004134 — Appendix A.1:
Thm A.1.1, item A.1.2 (transfer; an unnamed numbered paragraph, not formally
labeled "Theorem" — verifier note), Cor A.1.3, A.1.5; [Br] = Bredon 1972.

**Verified quote.**

> A.1.5. Geometrical construction of the Smith sequences. Introduce the Smith
> chain complexes Sm∗(X) = Ker[(1 + c∗) : S∗(X) → S∗(X)], Sm∗(X, F) =
> Ker[(1 + c∗) : S∗(X, F) → S∗(X, F)]. […] There is a canonical isomorphism
> Sm∗(X, F) = Im[(1 + c∗) : S∗(X) → S∗(X)] and a canonical splitting
> Sm∗(X) = S∗(F) ⊕ Im(1 + c∗). Furthermore, tr∗ : S∗(X′, F) → Sm∗(X, F) is an
> isomorphism, and in view of the above identifications the Smith sequences
> are the long homology and cohomology exact sequences associated with the
> short exact sequence of complexes 0 → Sm∗(X) —inclusion→ S∗(X) —(1+c∗)→
> Sm∗(X, F) → 0.
>
> [A.1.1] The homology and cohomology connecting homomorphisms ∆ are given by
> x ↦ x ∩ ω ⊕ ∂x and x ⊕ f ↦ x ∪ ω + δf, respectively, where ω ∈ H¹(X′ ∖ F)
> is the characteristic class of the double covering X ∖ F → X′ ∖ F.

**Applicability to gross.** Applies as stated: gross's deck Z₂-action on the
3-term BB chain complex is free (Galois cover, GZ Lemma 3.8), F = ∅,
coefficients F₂. No hypothesis blocks it. What Smith theory does NOT
immediately give: weight control of homology representatives — that is the
new mathematics Track B must add; the sequence only controls classes.

**Feeds.** Track B core tool. Skeleton: for a cover logical L̃ with class
[L̃] ∈ H₁(cover), either pr_*[L̃] ≠ 0 in H₁(base) (then |L̃| ≥ |p(L̃)| ≥
d_base, since p never increases weight — requires pr_*[L̃] nontrivial), or
pr_*[L̃] = 0 and by exactness [L̃] ∈ Im(tr_*), i.e. L̃ = τ(c) + boundary with
τ weight-doubling. The failure mode is exactly Ker(tr_*) = Im(Δ = ∩ω :
H₂(X′) → H₁(X′)) — the "corrected obstruction map" is the cap product with
the cover's characteristic class ω, which for BB 2-covers is explicit (the
x-direction cut cocycle).

### L2-kp2013-thm5-floor-bound — ancestor of the ⌈d/c⌉ family (CONFIRMED-WITH-CORRECTIONS)

**Claim (corrected).** The ancestor of the whole d/c bound family is
Kovalev–Pryadko 2013, Theorem 5, for hyperbicycle codes (CSS codes from sums
of Kronecker products with an internal cyclic symmetry of order c):
D ≥ ⌊d/c⌋ with d = min(d₁, d₂, d̃₁, d̃₂) over the constituent classical codes
and their transposes (descendants strengthen floor to ceiling).
**Corrections (verifier):** the arXiv title of 1212.6703 is "Quantum
'hyperbicycle' low-density parity check codes with finite rate" (the
Kronecker-sum-product title is the published PRA 88, 012311 (2013) title of
the same paper); Lin–Pryadko Statement 12 cites it as "Ref. 14" (not [16]) in
arXiv v1; and the second descendant is **Wang–Lin–Pryadko** arXiv:2305.06890
Statement 3 (not the Wang–Pryadko GB-distance-bounds paper arXiv:2203.17216,
whose Statement 3 is unrelated).

**Source.** Kovalev–Pryadko, arXiv:1212.6703v2 / PRA 88, 012311 (2013) —
Thm 5 and Thm 6, §III.C "CSS hyperbicycle codes: general distance bounds"
(p.8).

**Verified quote.**

> Theorem 5. The minimum distance of the code with generators (19) satisfies
> the lower bound D ≥ ⌊d/c⌋, d ≡ min(d1, d2, d̃1, d̃2).
>
> Theorem 6. For every p(x), a binary factor of x^c − 1 such that k1^(p) > 0
> and k̃2^(p) > 0, the minimum distance D of the code with generators (19)
> satisfies D ≤ min(d1^(p), d̃2^(p)). Similarly, when k2^(p) > 0 and
> k̃1^(p) > 0, we have D ≤ min(d2^(p), d̃1^(p)).

**Applicability to gross.** Hyperbicycle form requires an explicit order-c
cyclic block symmetry; for gross the relevant quasi-cyclic symmetry order is
large (c = 8 in the LP-St-12 incarnation), so ⌊d/c⌋ is hopelessly loose
(12/8 → 1).

**Feeds.** Tracks A and B baseline. The ⌊d/c⌋ mechanism is the same
"divide by the symmetry order" loss that makes LP Statement 12 give only 2 on
gross. Any Track-A improvement must explain what it does differently from
this 2013 argument.

### L2-kp2013-thm8-9-even-c-over-F2 — prior art beating the 2-divisibility wall (CONFIRMED-WITH-CORRECTIONS)

**Claim (corrected).** PRIOR ART FOR BEATING THE 2-DIVISIBILITY WALL:
Kovalev–Pryadko 2013 Theorems 8 and 9 prove distance lower bounds over F₂
for codes with an EVEN-order (including order-2) internal cyclic symmetry —
exactly the regime where the SRB/GZ transfer dies. Under "repeated codewords"
hypotheses (k_i^(1+x) = k_i, i.e. all constituent classical codewords fully
symmetric under the block shift; r_i = n_i; the four component
generator-matrix codes having distance ≥ 2): for c = 2,
D = min(d₁,d₂,d̃₁,d̃₂) EXACTLY (Thm 8); for general even c, (2/c)d ≤ D ≤ d
(Thm 9). The technique decomposes any null vector as "actual solution plus
degeneracy", u^(1+x) + γᵀG_Z. **Corrections (verifier):** the section is
**IV.E**, not III.E, in arXiv v2 (page numbers p.9–10 correct); and Lemma 4
forces the symmetric part's sublattice weights to be 0 or **≥ d** (the
"0 or ≥ 2" dichotomy applies to the degeneracy-correction terms
wgt(γ′_s + γ″_s) ≥ 2, eq. (39), from the distance-≥-2 hypothesis). Also a
caveat on "transfer-free": the Thm 9 proof does use a sum-over-all-c-shifts
averaging step, but purely over F₂ with no division by c, so the intended
sense (no invertibility of the symmetry order needed) is accurate.

**Source.** Kovalev–Pryadko, arXiv:1212.6703v2 / PRA 88, 012311 (2013) —
§IV.E "Codes with repeated codewords": Lemma 4 + Thm 8 (p.9), Thm 9 (p.10).

**Verified quote.**

> Lemma 4. A symmetric vector u = (w1, w2), wi = Σ_s β_s^i ⊗ g ⊗ α_s^i with
> g = (1, . . . , 1), i = 1, 2, that satisfies GX u = 0 and is linearly
> independent from the rows of GZ, has sublattice weights wgt(wi) either zero
> or ≥ d. […] Theorem 8. Suppose c = 2, ai and bi in Eq. (21) are such that
> ki^(1+x) = ki > 0, ri = ni and binary codes with generator matrices Σai,
> Σai^T, Σbi and Σbi^T have distances at least 2. Then the CSS quantum code
> with generators Eq. (19) has parameters [[4n1n2, 2k1k2, d]], where
> d = min(d1, d2, d̃1, d̃2). […] Theorem 9. Suppose c is even […] Then the
> quantum code in Eq. (19) has parameters [[2n1n2c, 2k1k2, D]], where
> (2/c)d ≤ D ≤ d and d ≡ min(d1, d2, d̃1, d̃2).
>
> [Proof of Thm 8:] any vector u such that GX u = 0 can be decomposed as the
> sum of an "actual" solution plus degeneracy, u^(1+x) + γ^T GZ […]

**Applicability to gross.** Not directly: gross-as-2-cover is not literally
in hyperbicycle Eq. (19) form with the repeated-codeword hypotheses, and
whether the (gross, [[72,12,6]]) pair satisfies a translated analogue of
k^(1+x) = k is unchecked (open question). The value is the proof TECHNIQUE,
not the statement.

**Feeds.** Track B — the single most actionable prior art found. A Track-B
proof of d_cover ≥ d_base for BB 2-covers should attempt the same
decomposition: any cover codeword splits as (1+σ)-symmetric part plus
stabilizer; symmetric vectors are τ-lifts (weight 2× base weight); the
remaining case is handled by projecting. Translating the restrictive
k_i^(1+x) = k_i hypotheses to the BB-cover setting is the open work.

### L2-wang-pryadko-statement3 — 2BGA ⌈d₀/c⌉ bound (CONFIRMED)

**Claim.** Wang–**Lin**–Pryadko's distance lower bound for 2BGA codes
(note the verified authorship — three authors; cf. the misattribution
correction under L2-kp2013-thm5-floor-bound): Statement 3 (Version of
Theorem 5 from KP-2013): for a, b ∈ F[G] with intersection subgroup
N = G_a ∩ G_b of size c = |N| CENTRAL in G, with d₀ = min(d(C_A^⊥),
d(C_B^⊥)) over the classical codes with parity checks A = L(a), B = R(b):
d_Z ≥ ⌈d₀/c⌉. The bound becomes EXACT when N = {1}, in which case each
double-coset subcode is a hypergraph-product code of classical group codes.
No even/odd or semisimplicity hypothesis appears (verifier confirmed:
semisimplicity/Maschke appears solely in the dimension-parity context, never
as a hypothesis of this bound) — the loss is purely the 1/c factor.

**Source.** Wang–Lin–Pryadko, *Abelian and non-abelian quantum two-block
codes*, arXiv:2305.06890v2 — Statement 3 + following paragraph, §III run-in
heading "Lower distance bounds for 2BGA codes" (p.4).

**Verified quote.**

> Statement 3 (Version of Theorem 5 from Ref. [16]). Given any two group
> algebra elements a, b ∈ F[G] such that the intersection subgroup
> N ≡ Ga ∩ Gb of size c ≡ |N| is central in G, consider classical codes with
> parity check matrices A = L(a) and B = R(b). Let d0 = min{d(C⊥_A), d(C⊥_B)}
> be the minimum of their distances. Then, the distance dZ of the 2BGA code
> LP[a, b] satisfies the inequality dZ ≥ ⌈d0/c⌉.
>
> In fact, this lower bound becomes exact when the intersection subgroup is
> trivial, N = {1}. In this case each double-coset subcode of the 2BGA code
> LP[a, b] is equivalent to a hypergraph-product code constructed from
> classical codes with parity-check matrices LGa(a) and RGb(b) over the
> corresponding subgroups, the individual blocks of L(a) and R(b).

**Applicability to gross.** Applies as stated (G abelian, so N central
automatically): d₀ = 12, c = 8, bound = ⌈12/8⌉ = 2. Loose by 10.
Hypothesis-wise nothing blocks it; it is just weak.

**Feeds.** Tracks A and B baseline: published state of the art for
per-instance analytic BB lower bounds. Track A's job is precisely to shrink
the effective denominator c. The "exact when N = {1}" clause formalizes why
the engineering target (degenerate, c > 1) is the hard regime — matches
HANDOFF 6i.

### L2-lin-pryadko-statement12-13 — the program's named baseline, verbatim (CONFIRMED)

**Claim.** Lin–Pryadko's Statement 12 (the program's named baseline)
verbatim, plus its matching upper bound Statement 13 and the surrounding
tightness facts: d_Z ≥ d₀ = ⌈min(d_A^⊥, d_B^⊥)/c⌉ where c is the rank of
N = G_a ∩ G_b (abelian and normal in both support groups); the upper bounds
guarantee d_Z ≤ c·min(ℓ_a, ℓ_b) (ℓ_a = [G_a : N], ℓ_b = [G_b : N]); upper and
lower bounds coincide when c = 1. Also Statement 5: d ≥ d_S = d(A, Bᵀ) when
both rank defects vanish. (Verifier: every hypothesis and conditional
reproduced without drift; PRA 109, 022407 (2024) publication confirmed via
APS/ADS.)

**Source.** Lin–Pryadko, *Quantum two-block group algebra codes*,
arXiv:2306.16400 / PRA 109, 022407 (2024) — Statement 12, Statement 13,
§IV.F "The case of quasi-abelian lifted-product codes" (p.8); Statement 5
(p.5).

**Verified quote.**

> Statement 12 (Version of Theorem 5 from Ref. 14). Given elements
> a, b ∈ F[G] such that the intersection subgroup N ≡ G_a ∩ G_b of rank c is
> abelian and normal in both support groups, let d_A^⊥ and d_B^⊥ be the
> distances of classical F-linear group algebra codes with parity check
> matrices A = L(a) and B = R(b). Then the distance d_Z of the code LP[a, b]
> satisfies d_Z ≥ d_0 ≡ ⌈min(d_A^⊥, d_B^⊥)/c⌉. […]
>
> Statement 13 (Version of Theorem 6 from Ref. 14). Let J be a maximal ideal
> in F[N], C_J the two-sided coset code generated by J, and Ĉ_J ≡ P C_J its
> image under the linear map (5). Denote d′ the distance of the subcode
> C_A^⊥ ∩ C_J. Then, if C_{B^T}^⊥ ∩ Ĉ_J ≠ {0}, the distance of the 2BGA code
> LP[a, b] satisfies the upper bound, d_Z ≤ d′. […]
>
> Then, for a non-trivial 2BGA code, the parameter d_0 in Statement 12
> satisfies d_0 ≤ min(ℓ_a, ℓ_b), while the upper bounds guarantee
> d_Z ≤ c min(ℓ_a, ℓ_b) […] The upper and the lower bounds on d_Z coincide
> when c = 1.

**Applicability to gross.** Applies as stated: on gross d_A^⊥ = d_B^⊥ = 12,
c = 8, bound = 2. The A0 scoreboard's numbers are confirmed against the
actual printed statement.

**Feeds.** Track A directly (denominator-shrinking target); Track B
indirectly (composition target: cover-transfer theorem + Statement 12 on a
deeper base). Statement 13's maximal-ideal upper-bound machinery is the right
vocabulary for the saturation criterion.

### L2-srb-citing-papers-no-resolution — the novelty window is open (CONFIRMED-WITH-CORRECTIONS)

**Claim (corrected).** As of the verifier's re-check (2026-06-10), Semantic
Scholar lists **6** papers citing SRB arXiv:2511.13560 — the researcher's
"5 as of 2026-06-09" snapshot is stale (plausible given indexing lag); the
6th is Wang–Pryadko, *Algebra of Bivariate-Bicycle Surface Codes*
(arXiv:2606.08771, submitted 2026-06-07), which cites SRB only once (on
fractal-pattern solutions of unaligned polynomials) and contains no proof or
refutation of the even-h conjecture. **None of the 6 proves or refutes the
§7 conjecture** (verifier did per-paper checks): (1) Hopkin–Albert–Williamson,
arXiv:2605.19298 (never discusses cover-degree parity); (2) Tiew–Breuckmann,
arXiv:2602.23307 (cites SRB only as a BB-generalization example);
(3) Mian–Gwilliam–Krastanov, arXiv:2601.18879 (benchmark-table examples
only); (4) Wang–Liu–Li–Kubica–Gu, arXiv:2601.15446 (weight-8 covering-graph
examples only); (5) Leverrier–Rozendaal–Zémor, arXiv:2512.20532 (discusses
the lift bound only "for odd |G|", attributing it to SRB); (6) the new
Wang–Pryadko paper. SRB itself is still at v1 (Nov 17, 2025). Hopkin et al.'s
distance results for A2BGA/BB codes are asymptotic scaling bounds only
(Thm 2 upper; Cor 1 lower, which additionally requires "no string-like
operators in all but two directions" — hypothesis restored by the verifier),
not per-instance.

**Source.** Semantic Scholar citations API for arXiv:2511.13560 (2026-06-09,
re-checked 2026-06-10); Hopkin–Albert–Williamson arXiv:2605.19298 Thm 2 /
Cor 1.

**Verified quote.**

> [Hopkin et al., Theorem 2:] Suppose 𝒞 = [[n,k,d]] is a family of abelian
> two-block group algebra codes defined by polynomials f and g with fixed
> weight w. Suppose that 𝒞 is indecomposable, and that v ≤ w−2, where v is
> the number of unique variables. Then we can map this code to one local in
> D ≤ w−2 dimensions, and the distance scaling of 𝒞 has the following upper
> bound: d ≤ O(n^{1−(1/D)}) with the parameters satisfying
> kd^{2/(D−1)} ≤ O(n).
>
> [Corollary 1:] If 𝒞 = [[n,k,d]] is a D-dimensional fracton model with no
> string-like operators in all but two directions, then it has distance
> scaling lower bounded by O(n^{1/D}) ≤ d.

**Applicability to gross.** The citing literature provides no per-instance
bound for gross. Note Hopkin et al. cite Chen et al. (arXiv:2503.04699,
PRL 135, 076603 (2025)) for BB distance scaling lower bounds O(L) via the
Bernstein–Khovanskii–Kushnirenko theorem — unfetched here, flagged as an open
question for Track A/D.

**Feeds.** Track B — confirms the conjecture window is still open as of June
2026: no published proof or counterexample of d ≤ d_h ≤ hd for even h.

### L2-hsieh-legall-phantom-citation — phantom citation confirmed (CONFIRMED)

**Claim.** "Hsieh–Le Gall 2020" as cited in the program's HANDOFF.md (lines
458 and 632–633, listed among homological/chain-complex distance-bound papers
alongside Kovalev–Pryadko 2013) **does not exist**. The arXiv author API
query (au:"Le Gall" AND au:"Hsieh") returns exactly one joint paper ever:
*NP-hardness of decoding quantum error-correction codes*, Min-Hsiu Hsieh and
François Le Gall, Phys. Rev. A 83, 052331 (2011), arXiv:1009.1319 — a
decoding-complexity result with no distance bounds, hypergraph products, or
chain-complex machinery, so it cannot be the cited paper even under a year
typo. HANDOFF.md additionally misdescribes it as working "on the chain
complex of the BB code directly", which is false of the real 2011 paper.

**Source.** arXiv:1009.1319 metadata (verifier fetched the abs page
directly, upgrading the researcher's search-level check);
HANDOFF.md:458, 632–633.

**Verified quote.**

> [arXiv:1009.1319 metadata] title "NP-hardness of decoding quantum
> error-correction codes"; authors Min-Hsiu Hsieh, Francois Le Gall; journal
> reference "Physical Review A 83, 052331 (2011)"; abstract: the paper proves
> "the general quantum decoding problem is NP-hard regardless of the quantum
> codes being degenerate or non-degenerate".
>
> [HANDOFF.md:458] "also Hsieh–Le Gall 2020; Kovalev–Pryadko 2013). These
> work on the chain complex of the BB code directly"

**Applicability to gross.** N/A — the paper that exists is about decoding
hardness, not distance.

**Feeds.** All tracks (citation hygiene): remove "Hsieh–Le Gall 2020" from
HANDOFF 6j item 1 — third citation-failure of the same kind as
"Pesah–Roffe 2025". Do not spend Phase-2 time looking for its theorems.

## Unverified / refuted

**None.** All 13 findings came back CONFIRMED (6) or
CONFIRMED-WITH-CORRECTIONS (7); no verdict was UNVERIFIABLE or REFUTED. For
the record, the substantive corrections already folded into the subsections
above (do not cite the uncorrected forms):

| finding | correction |
|---|---|
| L2-srb-thm31-cover-conditions | Thm 3.1 is sufficiency-only, not a biconditional "characterization" |
| L2-srb-odd-h-theorems | "all rigorous results are odd-h" overlooked the any-h conditional Thm 4.8; Thm 4.6 quote dropped the word "two" |
| L2-srb-thm48-weight-preserving-lift | the paper's inline σ_• direction is a typo (Q̃_•→Q_•); diagram + proof force Q_•→Q̃_•, as quoted |
| L2-guemard-zemor-prop35-transfer | "independently" overstated (documented SRB–Guémard contact; concurrent, same-day posting); π#∘τ# sentence follows, not precedes, Prop 3.5; "[Gue25]" vs "[7]" is a PDF-vs-HTML rendering difference |
| L2-kp2013-thm5-floor-bound | arXiv title differs from published PRA title (same paper); LP Statement 12 cites "Ref. 14" not [16]; descendant is Wang–**Lin**–Pryadko 2305.06890, not Wang–Pryadko 2203.17216 |
| L2-kp2013-thm8-9-even-c-over-F2 | section is IV.E not III.E; Lemma 4 forces sublattice weights 0 or ≥ **d** (the "0 or ≥ 2" dichotomy belongs to the degeneracy terms, eq. (39)) |
| L2-srb-citing-papers-no-resolution | citing-paper count now 6, not 5 (Wang–Pryadko arXiv:2606.08771, 2026-06-07, also non-resolving); Cor 1 lower bound needs the "no string-like operators" hypothesis |

## Open questions and dead ends

### Open questions (researcher, verbatim)

1. "Can the Kovalev-Pryadko 2013 Theorem 8/9 'repeated codewords' technique
   (decompose a null vector into a fully-(1+sigma)-symmetric part plus
   stabilizer degeneracy, then lower-bound the symmetric part's weight
   blockwise) be translated from hyperbicycle form to the SRB BB 2-cover
   setting? Concretely: does the (gross, [[72,12,6]]) pair satisfy a BB
   analogue of the hypothesis k_i^{(1+x)} = k_i, and what does
   d = min(d_1,d_2,d~_1,d~_2) become in BB language?"
2. "Smith-sequence weight argument for Track B: for a free Z_2 cover,
   exactness gives that a cover logical class [L~] with pr_*[L~] = 0 lies in
   Im(tr_*); tr_* doubles weight, so the dangerous case is
   Ker(tr_*) = Im(Delta) with Delta = cap product with the characteristic
   class omega of the double cover. For BB 2-covers omega is an explicit
   1-cocycle (the x-direction cut). Question: when is
   Delta : H_2(base complex) -> H_1(base complex) zero or controllable for BB
   chain complexes? (For the BB 3-term complex H_2 = ker of the first
   boundary map = the (f,g) syzygy space; on [[72,12,6]] this is
   12-dimensional.) Nobody in the literature has attempted this — searches
   for Smith theory applied to QEC covers return nothing as of June 2026."
3. "Also need the second half of the d ≥ d_base argument: when
   pr_*[L~] ≠ 0, one gets |L~| ≥ |p(L~)| ≥ d_base only if p(L~) represents a
   NONTRIVIAL base class — pr_* of a nontrivial cover class could be a
   nonzero chain in a trivial class. Verify whether SRB's Theorem 4.1
   chain-map structure already gives [p(L~)] = pr_*[L~] (it does — induced
   map on homology), so the gap is only the pr_*[L~] = 0 branch."
4. "Fetch and check Chen, Liu, Zhang, Liang, Chen, Liu, Song, 'Anyon Theory
   and Topological Frustration of High-Efficiency Quantum Low-Density
   Parity-Check Codes', arXiv:2503.04699 (PRL 135, 076603 (2025)): Hopkin et
   al. say it derives BB distance scaling lower bounds O(L) via the
   Bernstein-Khovanskii-Kushnirenko theorem. Is the bound analytic and
   per-family? Could it serve program goal (2) (nontrivial analytic lower
   bound for a class of BB codes)?"
5. "Check Leverrier-Rozendaal-Zemor arXiv:2512.20532 ('Small quantum Tanner
   codes from left-right Cayley complexes', Dec 2025): it cites SRB and uses
   lifting procedures with the GZ machinery — does it contain any even-degree
   lift distance statement, or only odd Galois lifts? (Not fetched this
   session.)" *(Write-up note: the verifier's per-paper check of the citing
   literature partially answers this — LRZ discuss the lift bound only "for
   odd |G|" — but the paper itself remains unfetched.)*
6. "Does SRB's Remark 8 rank/nullity analysis (rank H_1(tau_•) ≤ nullity
   H_1(p_•) for even h, plus the mapping-cone criterion they sketch) yield a
   usable sufficient condition for k_h ≥ k at h=2 that can be verified
   analytically for the gross chain (they say the boundary maps' block
   structure makes it 'theoretically difficult... in general' but not
   impossible for specific codes)?"
7. "The deck group of gross's 2-cover makes the gross complex a free
   F_2[Z_2]-module complex with base = [[72,12,6]] complex (GZ Remark 3.6
   generality). F_2[Z_2] = F_2[t]/(t^2) is local; standard tools (Nakayama,
   the exact functor -/t(-), minimal free resolutions) might replace
   transfer. Is there a published distance statement for codes over
   F_2[t]/(t^2) chain complexes (e.g. in the fiber-bundle code literature,
   Hastings-Haah-O'Donnell STOC 2021, where twisted Z_2-bundles appear)? Not
   searched this session beyond BE overlap remark."

### Dead ends (researcher, verbatim)

1. "'Hsieh-Le Gall 2020' as a homological distance-bound paper: does not
   exist. Searches 'Hsieh Le Gall 2020 quantum LDPC hypergraph product
   distance bound' and 'Hsieh Le Gall quantum error correction NP-hardness
   decoding 2011' establish the only Hsieh+Le Gall paper is the 2011
   NP-hardness-of-decoding paper (arXiv:1009.1319). Stop citing the 2020
   version."
2. "Smith theory / Smith exact sequence applied to quantum codes or
   stabilizer codes: extensive search ('Smith theory quantum error correcting
   code stabilizer double cover involution 2025 2026', 'Smith exact sequence
   free involution chain complex F2 transfer 1+sigma homology double cover
   code distance') found zero QEC applications — only real-algebraic-geometry
   and equivariant-topology literature. The even-h Smith route is untried,
   i.e. open, not preempted."
3. "Search for a proof or refutation of the SRB Section-7 conjecture posted
   after Nov 2025 ('bivariate bicycle cover code even h conjecture distance
   proof 2026'): nothing. SRB still v1; all 5 citing papers (Semantic
   Scholar, June 2026) are constructions/frameworks, none addresses even-h
   transfer." *(Write-up note: count corrected to 6 by the verifier; the
   conclusion stands — see L2-srb-citing-papers-no-resolution.)*
4. "Guemard 'Lifting a CSS code via its handlebody realization'
   (arXiv:2505.14327, May 2025): abstract has no distance bounds, no
   parity/characteristic-2 content — classification of lifts only."
5. "Guemard 2404.16736 (IEEE TIT 2025): no distance lower bound for lifts
   anywhere; explicitly disclaims one ('case by case analysis'). Do not mine
   it for transfer theorems — the transfer content went into Guemard-Zemor
   2502.20297 v2 instead (odd t only)."
6. "WebFetch on raw arXiv PDF URLs (2306.16400, 1212.6703, math/0004134,
   2305.06890) returns un-parseable compressed streams from the summarizer —
   but the binary is saved locally; Read tool on the saved PDF (or
   /opt/homebrew/bin/pdftotext) works. Use that workflow, not repeated fetch
   attempts."
7. "arxiv.org/html/2305.06890v4 does not exist (404) — Wang-Pryadko has only
   v1/v2 and no HTML rendering; use the PDF."
8. "Hopkin-Albert-Williamson 2605.19298 for per-instance gross bounds: their
   Theorem 2 / Corollary 1 are asymptotic scaling statements (and the lower
   bound needs a D-dimensional fracton model with no string-like operators in
   all but two directions); nothing evaluable on a fixed [[144,12,12]]
   instance."

Supporting context (researcher findings, both verified): Panteleev–Kalachev
arXiv:2012.04068 (lifted-product "almost linear distance") and
Breuckmann–Eberhardt arXiv:2012.09271 (balanced products) are
ensemble/asymptotic results — random expander constituents, growing circulant
size, family-level Θ(·) statements — with **no per-instance lower-bound
formula** that survives specialization to a fixed code like gross. "BB codes
are lifted/balanced products" imports no usable bound. Guémard's own TIT
paper (arXiv:2404.16736 §1.2) states lift parameters are "in general, hard to
determine. One can only hope to do a case by case analysis." — supporting
novelty of any even-h transfer theorem.

## Implications for Phase 2

**Preempted (already published — do not redo):**

- Any **odd-h** cover-transfer theorem. Published twice: SRB Thm 4.7 (BB
  codes) and GZ Prop 3.5 + Remark 3.6 (any chain complex of free Γ-modules,
  strictly more general). A Track-B write-up claiming odd-h content as new
  would be scooped on arrival. Moreover, A0 already showed the rigorous odd-h
  bound is **vacuous on the entire Bravyi table** (every odd-h base has
  k′ = 0), so nothing is lost.
- The bare ⌈d₀/c⌉ mechanism (KP-2013 Thm 5 → WLP St. 3 → LP St. 12). Track A
  must position itself explicitly as improving on this 13-year-old argument.

**Enabled (tools now in hand):**

- **Track B has a precise, sourced proof skeleton.** The Smith exact sequence
  for free involutions (Degtyarev–Kharlamov A.1.5 / Bredon Ch. 3) applies
  verbatim to gross's cover (free Z₂ action via GZ Lemma 3.8, F = ∅, F₂
  coefficients). The two-branch argument (pr_*[L̃] ≠ 0 ⟹ project;
  pr_*[L̃] = 0 ⟹ τ-lift + boundary) is fully set up; the residual obstruction
  is identified exactly: Δ = ∩ω : H₂(base) → H₁(base), with ω the explicit
  x-direction cut cocycle. The new mathematics needed is weight control of
  representatives, not exactness.
- **A published even-symmetry F₂ precedent exists**: KP-2013 Thms 8–9 prove
  even-c distance lower bounds via symmetric-part decomposition, with no
  transfer inversion. This both raises confidence the h=2 goal is provable
  and supplies a concrete second attack (translate the repeated-codeword
  hypothesis to BB 2-covers — open question 1).
- SRB's chain maps p_•, τ_• (Thms 4.1/4.3) are valid at h=2 and reusable
  as-is; open question 3's gap-check confirms only the pr_*[L̃] = 0 branch
  needs new work. Thm 4.8's weight-preserving lifts give the parity-free
  vocabulary for the saturation stretch goal (and a consistency check: no
  such lift can exist for (gross, [[72,12,6]])).
- The novelty window is **confirmed open as of 2026-06-10** (6 citing papers,
  none resolving; SRB still v1; zero QEC applications of Smith theory in the
  literature). Track B, if it lands, is the first proof of the h=2 case of a
  named open conjecture.
- Citation hygiene: purge "Hsieh–Le Gall 2020" from HANDOFF.md (lines 458,
  632–633) — phantom, like "Pesah–Roffe 2025".

**Killed: nothing.** Lemma 4.4 kills only the literal p∘τ-inversion route —
which the program already believed dead (HANDOFF 6k) — not the goal; SRB's
own Remark 9 and Conclusion explicitly leave room for "different tools."
The general lifted/balanced-product literature (PK, BE, Guémard TIT) yields
no shortcut but also no obstruction. No counterexample to the even-h
conjecture exists in the literature, and SRB's Tables 1–10 plus the A0 cover
chain (gross → 72 → 36 → 18, distances exactly halving) are consistent with
both d_cover ≥ d_base and saturation d_cover = 2·d_base on gross's lattice.

**Watch items for Phase 2:** Chen et al. arXiv:2503.04699 (BKK-theorem BB
distance scaling — possible overlap with program goal (2); unfetched) and
Leverrier–Rozendaal–Zémor arXiv:2512.20532 (unfetched; verifier's spot-check
says odd-|G| only). Both should be fetched before any Track A/D claims of
novelty for family-level analytic lower bounds.
