# A1/L4 — Analytically-anchored small codes and toric equivalences

Date: 2026-06-09. Lane L4 ("Analytically-anchored base codes for the
cover chains") of the Phase-1 literature sweep for the analytic-bound
program. Researcher findings adversarially verified at source; all
verifier corrections are applied inline below. Quotes are the
**verifier's** verified verbatim extracts, not the researcher's
originals.

**Lane verdict.** The gross 2-cover chain now bottoms out on a
**published, fully analytic** anchor: the chain-bottom [[18,8,2]] BB
code is verifiably (verifier recomputed from scratch) the hypergraph
product HGP(J₃,J₃) of the [3,2,2] even-weight code with itself, and
its exact d = 2 follows from three mutually consistent published
results whose hypotheses are all verified to hold — Tillich–Zémor
Theorem 15 (conditional equality, conditions satisfied),
Kovalev–Pryadko Eq. (12) (square cyclic seeds), and Lin–Pryadko
Statement 8's trivial-intersection HP specialization (with the
connectivity condition G_a·G_b = G, satisfied here). The anchor
**cannot be moved up the chain by citation**: [[36,8,4]] is the
Tiew–Breuckmann balanced-product q=2 code with only a published
*upper* bound (d ≤ 2q, distances numerical), and an original,
verifier-rechecked Griesmer/TZ argument proves **no binary HGP code
has parameters [[36,8,4]] at all**. The lane's most consequential
finding is internal: A0 baseline observation 3 ("every rigorous
odd-h base has k′ = 0") is **wrong by A0's own tables** — bb_90 and
bb_108 have odd-h rigorous bases with k′ = 8 = k, so SRB Thms 4.6+4.7
already give a fully-analytic 2 ≤ d(bb_90) ≤ 10 *today* (the upper
bound saturated: 10 = 5·2), and one analytic d ≥ 4 for [[36,8,4]]
would yield the program's first fully-analytic nontrivial bound on a
Bravyi-table instance (bb_108, h = 3 odd). For gross itself nothing
moves: c = |G_a ∩ G_b| = 8 fails every published equality hypothesis,
all its positive-k′ covers are even-h, and the prior-art clearance
survived adversarial re-search *for gross specifically* — but the
researcher's blanket "nothing exists for non-separated weight-6 BB
codes" clause was refuted by the lane's own SRB source (see
§ Unverified / refuted), so Phase 2 must state its novelty claims
with the odd-h cover transfer explicitly carved out.

## Scoreboard

12 load-bearing findings sent to the verifier:

| Finding | Verdict | Feeds |
|---|---|---|
| L4-18-8-2-is-HGP | CONFIRMED | Track B (+A) |
| L4-tz-hgp-distance-theorem | CONFIRMED | Track B |
| L4-kp-square-seed-family | CONFIRMED | Track B (Lean target) |
| L4-lp-statement-8-hgp | CONFIRMED-WITH-CORRECTIONS | Tracks A, B |
| L4-lp-statement-12-and-c1-equality | CONFIRMED-WITH-CORRECTIONS | Track A |
| L4-36-8-4-is-tiew-breuckmann-bp | CONFIRMED | Track B |
| L4-no-hgp-36-8-4 | CONFIRMED-WITH-CORRECTIONS | Track B |
| L4-tb-hgp-18q2-family | CONFIRMED-WITH-CORRECTIONS | Tracks A, B |
| L4-srb-thm-4-6-4-7 | CONFIRMED | Track B |
| L4-rigorous-odd-h-bases-exist | CONFIRMED-WITH-CORRECTIONS | Track B |
| L4-liang-twisted-tori-correspondence | CONFIRMED | Tracks B, D |
| L4-prior-art-clearance-2026 | CONFIRMED-WITH-CORRECTIONS, **verified = false** (blanket sub-claims refuted; see § Unverified / refuted) | All tracks |

Three further context-only (non-load-bearing) findings were **not**
sent to the verifier — see § Unverified / refuted.

---

## Verified findings

### L4-18-8-2-is-HGP — the chain bottom is a hypergraph-product code (CONFIRMED)

**Claim (corrections applied).** The chain-bottom [[18,8,2]] BB code
(G = Z₃ × Z₃, A = 1+y+y², B = 1+x+x²) IS a hypergraph-product code:
the HGP of the [3,2,2] even-weight code with itself, seeded by the
redundant 3×3 all-ones circulant J₃ = circ(1+x+x²). Verified
computationally this session and independently re-derived from
scratch by the verifier (different construction path: explicit
regular-representation shift matrices, own GF(2) RREF/kernel code):
A = I₃ ⊗ J₃ and B = J₃ ⊗ I₃ exactly, so the BB H_X = (I⊗J | J⊗I)
equals the HGP(J₃,J₃) H_Z block-for-block (the BB code is the CSS
ZX-dual of HGP(J₃,J₃)); both codes have n = 18, k = 8,
d_X = d_Z = 2 by exhaustive kernel enumeration. The hypothesis that
makes this work: supp(A) generates 0 × Z₃, supp(B) generates
Z₃ × 0, and the support subgroups intersect trivially
(c = |G_a ∩ G_b| = 1). Its analytic distance d = 2 then follows from
published theorems (next two findings). Verifier resolved the
bibliographic ids: Tillich–Zémor arXiv:0903.0566v2 / IEEE-IT
60(2):1193–1202 (2014) and Lin–Pryadko arXiv:2306.16400; note the
explicit 2BGA→HGP statement sits in the discussion *immediately
following* LP Statement 8 (Statement 8 proper is the more general
double-coset version).

**Source.** This session's computation (`/tmp/hgp_check.py`),
cross-checked against Tillich–Zémor Theorem 15 and Lin–Pryadko
Statement 8 (both quoted in their own findings below).

**Verified quote (verifier's reproduction of the script output).**

> BB [[18,8,2]] params: (18, 8) / BB d_Z: 2  d_X: 2 / HGP(J3,J3)
> params: (18, 8) / HGP d_Z: 2  d_X: 2 / A == I(x)J: True
> B == J(x)I: True

**Applicability to gross.** Does NOT apply to gross directly: gross
has G_a ∩ G_b of order 8 (c = 8), so the trivial-intersection
hypothesis fails. It applies exactly to the chain-bottom base code.

**Feeds.** Track B: the gross 2-cover chain
gross → [[72,12,6]] → [[36,8,4]] → [[18,8,2]] now bottoms out at a
code with a PUBLISHED ANALYTIC exact distance (d = 2), not just a
weight-1 exhaustion argument. Track A: [[18,8,2]] is the c = 1
boundary case where single-block dominance d = min(d_A^⊥, d_B^⊥) is
a theorem.

### L4-tz-hgp-distance-theorem — the published HGP distance theorem, hypotheses verified for [[18,8,2]] (CONFIRMED)

**Claim (corrections applied).** Tillich–Zémor's HGP distance
theorem: d_Q ≥ min(d₁, d₂, d₁ᵀ, d₂ᵀ) unconditionally, with EQUALITY
under explicit conditions (the min is attained by a code whose
partner on the same side is nontrivial), under the convention that
the distance of the zero code is ∞. Precision from the verifier:
the equality conditions are stated *inside Theorem 15 itself*;
Lemma 16 proves only the lower bound and **Lemma 17** proves the
upper bounds ("Lemmas 16 and 17 together prove Theorem 15"). For
[[18,8,2]]: d₁ = d₂ = d₁ᵀ = d₂ᵀ = 2 (J₃ is symmetric rank-1; all
four sector codes are [3,2,2]), the equality condition
(dᵢ = min and d₃₋ᵢ ≠ ∞) holds, so d_Q = 2 exactly, fully
analytically; Theorem 15 carries no semisimplicity/Sylow/full-rank
hypotheses. Numbering drift across versions confirmed exactly:
Kovalev–Pryadko arXiv:1212.6703 cites these results as "Theorem 7 /
Theorem 9 / Lemma 10 from Ref. [23]" (the ISIT 2009 version) —
though KP's Theorem 7 is the *dimension* formula (≈ arXiv
Proposition 14), not part of the distance theorem.

**Source.** Tillich, Zémor, *Quantum LDPC codes with positive rate
and minimum distance proportional to n^{1/2}*, arXiv:0903.0566
(IEEE-IT 60(2):1193–1202, 2014). Section 5 "Minimum distance",
Theorem 15 with Lemmas 16–17.

**Verified quote.**

> In this section, we show that the minimum distance of the quantum
> code Q(G1 × G2) has a very simple expression, when we adopt the
> convention that the minimum distance of a code reduced to the
> all-zero codeword is ∞ Theorem 15 For i ∈ {1, 2}, let di be the
> minimum distance of a code with Tanner graph Gi and let dTi denote
> the minimum distance of the code specified by the transpose Tanner
> graph GTi. The minimum distance dQ of the quantum code Q(G1 × G2)
> satisfies dQ ≥ min(d1, d2, dT1, dT2). and is given by
> dQ = min(d1, d2, dT1, dT2). in the following cases
> • di = min(d1, d2, dT1, dT2) for some i ∈ {1, 2} and d3−i 6= ∞,
> • or dTi = min(d1, d2, dT1, dT2) for some i ∈ {1, 2} and
> dT3−i 6= ∞.

**Applicability to gross.** Applies to [[18,8,2]] (all hypotheses
verified, including the equality bullet). Does not apply to gross,
[[36,8,4]], or [[72,12,6]] — none of them is an HGP code (gross/72
have c > 1; [[36,8,4]] provably has no HGP realization, see
L4-no-hgp-36-8-4).

**Feeds.** Track B: this is the published analytic theorem that
anchors the chain bottom — exactly the "HGP distance theorem with
hypotheses" requested by L4 task 4. Any Lean formalization of the
[[18,8,2]] anchor should target this statement (or the easier
rank-1-seed special case).

### L4-kp-square-seed-family — the simplest citable form of the anchor (CONFIRMED)

**Claim (corrections applied).** Kovalev–Pryadko's "square
parity-check matrix" HGP variant gives parameters
Q_square = [[2n₁n₂, 2k₁k₂, min(d₁,d₂)]] whenever the square seeds
satisfy d̃ᵢ = dᵢ (transpose code has the same distance); k̃ᵢ = kᵢ is
automatic. [[18,8,2]] is the instance n₁ = n₂ = 3, k₁ = k₂ = 2,
d₁ = d₂ = 2 with seed H = full circulant of the check polynomial
1+x+x² on Z₃; KP explicitly note that for cyclic seeds the
transposed code has the same parameters (reversed check polynomial),
so the d̃ = d hypothesis is free. Verifier caveats: [[18,8,2]] is
NOT explicitly listed as a KP example (their Sec. C examples are the
toric [[2d²,2,d]] family) — the claim correctly frames it as an
instantiation of published Eq. (12), which the verifier re-derived
computationally (rank H_X = rank H_Z = 5, k = 8, d_X = d_Z = 2).
The polynomial's palindromicity is true but *incidental* for
Eq. (12) — it matters only for KP's separate symmetric construction
(Eq. 15), which would give the smaller [[9,4,2]].

**Source.** Kovalev, Pryadko, *Improved quantum hypergraph-product
LDPC codes*, arXiv:1202.0928. Section IV-C "Code family from square
matrices", Eq. (12) and surrounding text.

**Verified quote.**

> Instead of using full-rank parity-check matrices[18], let us start
> with a pair of binary codes with square parity-check matrices Hi,
> such that d̃1 = d1, d̃2 = d2. Then, automatically, k̃i = ki =
> ni − rank Hi. The hypergraph-product ansatz (9) gives the code with
> the parameters Qsquare = [[2n1 n2, 2k1 k2, min(d1, d2)]]. (12)
> [...] Second construction assumes that CHi are cyclic LDPC codes.
> The full circulant matrices Hi are constructed from coefficients of
> check polynomials hi(x). The check polynomials of the transposed
> code, h̃i(x) = hi(x^(ni−1)) mod(x^ni − 1), are just the original
> check polynomials reversed, and the original and transposed codes
> have the same parameters.

**Applicability to gross.** Construction-level only: gross is not of
this separated-variable square-seed form (its A and B share support
directions, c = 8).

**Feeds.** Track B: simplest citable form of the [[18,8,2]] anchor —
d = min(2,2) = 2 with hypotheses trivially checkable. Also the
cleanest Lean-formalization target shape (square circulant seeds).

### L4-lp-statement-8-hgp — BB = HP exactly when supports separate (CONFIRMED-WITH-CORRECTIONS)

**Claim (corrections applied).** Lin–Pryadko Statement 8 plus the
unnumbered "In particular" paragraph following it: a 2BGA/BB code
whose support groups intersect trivially (G_a ∩ G_b = {1}) is an HP
(hypergraph-product) code built from square matrices, with
explicitly known parameters [[2nₐn_b, 2kₐk_b, min(dₐ, d_b)]].
**Correction:** Statement 8 proper addresses the *double-coset
subcode* supported on G_a·1·G_b; the headline "code = HP" needs the
additional connectivity condition G_a·G_b = G — otherwise the code
is a direct sum of equivalent HP subcodes, not a single HP code.
For [[18,8,2]] the caveat is vacuous: |G_a||G_b| = 9 = |G|, so
G_a·G_b = G and the whole code is the HP code. This is the published
"BB = HGP when supports separate" theorem, the primary source behind
the ECZoo 2BGA page's statement (dependency confirmed: the ECZoo
page cites exactly this paper, published as Phys. Rev. A 109,
022407 (2024)). For [[18,8,2]]: G_a = ⟨y⟩ and G_b = ⟨x⟩ intersect
trivially, [nₐ,kₐ,dₐ] = [3,2,2], giving [[18,8,2]] with analytic
d = 2.

**Source.** Lin, Pryadko, *Quantum two-block group algebra codes*,
arXiv:2306.16400 (PRA 109, 022407, 2024). Statement 8 and the
paragraph immediately following it (Section IV C, "Connectivity of
2BGA codes").

**Verified quote.**

> Statement 8. If the intersection subgroup N ≡ Ga ∩ Gb is abelian
> and normal in both support groups, the subcode of LP[a, b]
> supported in the double-coset Ga 1Gb is equivalent to a 2BGA code
> over a group G′ of rank |Ga 1Gb|. In particular, with disjoint
> subgroups, Ga ∩ Gb = {1}, the group in Statement 8 is just a
> direct product of the two subgroups, G′ = Ga × Gb. In this case we
> can independently choose the order of elements in each subgroup,
> and both matrices may simultaneously have the form of Kronecker
> products, A = A1 ⊗ Inb, B = Ina ⊗ B1, with nb ≡ |Gb| = ma and
> na ≡ |Ga| = mb. This is exactly the block structure of an HP
> code[13], constructed from square matrices A1 and B1. If we denote
> the parameters of classical linear codes with parity check
> matrices A1 and B1, respectively, as [na, ka, da]q and
> [nb, kb, db]q (these parameters remain the same when the
> transposed matrices are used), the parameters of the quantum HP
> code are known explicitly, [[2na nb, 2ka kb, min(da, db)]]q.

**Applicability to gross.** Hypothesis G_a ∩ G_b = {1} fails on
gross (intersection has order 8). The theorem brackets exactly where
gross lives: published equality at c = 1, published ⌈min/c⌉ lower
bound for c > 1 (Statement 12), nothing tight in between.

**Feeds.** Track A: the published c = 1 endpoint of the
single-block-dominance program (d = min(d_A^⊥, d_B^⊥) is a THEOREM
at c = 1; A0 obs. 1 seeks conditions extending it to c > 1).
Track B: certifies the [[18,8,2]] anchor from the BB side without
needing the explicit HGP reshuffle.

### L4-lp-statement-12-and-c1-equality — the program's known LP bound, and where its equality stops (CONFIRMED-WITH-CORRECTIONS)

**Claim (corrections applied).** Lin–Pryadko Statement 12 (the
program's known LP bound), quoted exactly with hypotheses, plus
LP's remark that the lower and upper bounds coincide **when** c = 1,
where d_Z = min(d_A^⊥, d_B^⊥). **Correction:** the researcher's
"iff c = 1 / equality ONLY at c = 1" gloss strengthens LP's
one-directional "when c = 1" into a biconditional LP never stated —
LP never asserts the bounds *cannot* coincide for some specific
c > 1 code. The accurate reading: LP's published statements
GUARANTEE equality only in the c = 1 case, and give only the
⌈min(d_A^⊥, d_B^⊥)/c⌉ lower bound unconditionally. On gross
(c = 8, hypotheses re-derived to hold: G_a = ⟨x³,y⟩ ≅ Z₄×Z₆,
G_b = ⟨x,y³⟩ ≅ Z₁₂×Z₂, N = ⟨x³,y³⟩ ≅ Z₄×Z₂, "rank" = group order
confirmed at two independent sites in the text) it yields
⌈12/8⌉ = 2, matching A0 — conditional on min(d_A^⊥, d_B^⊥) = 12,
which is A0's figure (independently recomputed by the L3 lane's
verifier, not re-done here). Minor location fix: the c = 1
paragraph is the second/third paragraph after Statement 13, not
immediately after it.

**Source.** Same paper, arXiv:2306.16400. Statement 12
(Section IV F) and the "upper and the lower bounds on dZ coincide
when c = 1" paragraph after Statement 13.

**Verified quote.**

> Statement 12 (Version of Theorem 5 from Ref. 14). Given elements
> a, b ∈ F[G] such that the intersection subgroup N ≡ Ga ∩ Gb of
> rank c is abelian and normal in both support groups, let d⊥A and
> d⊥B be the distances of classical F-linear group algebra codes
> with parity check matrices A = L(a) and B = R(b). Then the
> distance dZ of the code LP[a, b] satisfies
> dZ ≥ d0 ≡ ⌈min(d⊥A, d⊥B)/c⌉. [...] The upper and the lower bounds
> on dZ coincide when c = 1: in this case the subgroup N = {1} is
> trivial so that F[N] is just the field F, and the auxiliary codes
> in statements 12 and 13 coincide, which gives
> dZ = min(d⊥A, d⊥B). Of course, the same result for the distance
> can be also obtained from the map to a hypergraph-product code
> constructed from the single-block classical group algebra codes
> with groups Ga and Gb.

**Applicability to gross.** Applies to gross with c = 8, giving only
d ≥ 2. The base [[18,8,2]] sits at c = 1 where it is tight;
[[36,8,4]] has c = 2 (G_a = ⟨y⟩ order 6, G_b = ⟨y³,x⟩ order 6,
N = {1, y³}), giving d ≥ ⌈4/2⌉ = 2 — not 4.

**Feeds.** Track A: exact statement + hypotheses of the bound
Track A wants to sharpen. The c = 1 equality remark defines the open
gap (1 < c: equality not guaranteed by anything published).

### L4-36-8-4-is-tiew-breuckmann-bp — [[36,8,4]] is a known balanced-product code, with only an UPPER bound published (CONFIRMED)

**Claim (corrections applied).** The gross-chain [[36,8,4]] (A0 6×3
row: A′ = y+y²+x³, B′ = 1+x+x² over Z₆ × Z₃) is the q = 2 member of
Tiew–Breuckmann's balanced-product cyclic family [[18q, 8, ≤ 2q]]
with p₁ = p₂ = 1+x+x² (their Table I lists q = 2: [[36,8,4]]).
Hand-verified equivalence this session, independently re-derived by
the verifier: TB's isomorphism f: F₂C₆ ⊗_{C₂} F₂C₆ → F₂[C₃ × C₆]
(their Eq. (54), valid for q mod 3 ≠ 0) sends p₁ to 1+y+x³y² and
p₂ to 1+x+x²; and y²·(y+y²+x³) = 1+y+x³y², so the codes agree up to
multiplication of A by the unit monomial y² (a valid BB equivalence
for abelian groups — relabel right-block qubits by P_u and X-check
rows by P_u⁻¹). CRITICAL NEGATIVE: TB prove only the UPPER bound
d ≤ 2q for this family (via a weight-2q logical that survives the
quotient); Table I distances are from numerical search (ILP-exact),
and the same-polynomial family does NOT keep d = 2q (their q = 3
entry with p₁ = p₂ = 1+x+x² is [[54,8,4]], not 6). So [[36,8,4]] has
no analytic lower bound *in this source* (the universal absence
claim is supported but inherently unfalsifiable from one source).
Cosmetic fixes: the section is subsection VI.B (Section VI is
"Balanced Product Cyclic Codes"); the paper hyphenates
"upper-bounds".

**Source.** Tiew, Breuckmann, *Low-Overhead Entangling Gates from
Generalised Dehn Twists*, arXiv:2411.03302. Subsection VI.B
("Constructing a [[18q, 8, ≤ 2q]] Balanced Product Cyclic Code"),
Eq. (54), and Table I.

**Verified quote.**

> The hypergraph product code distance of 2q upper-bounds the
> distance of this construction as the basis of logical operators
> from Eq. (30) is still valid. However, the minimum-weight logical
> operators of the balanced product code now depend on
> representative polynomials p1(x), p2(x) used in the construction.
> [...] TABLE I. Highest-distance codes from a numerical search
> using weight 3 polynomials in the construction of [[18q, 8, ≤ 2q]]
> balanced product cyclic codes for q ≤ 10. Codes that saturate the
> upper bound of 2q are highlighted in yellow. [Rows: 1 [[18,8,2]] 2
> el+x+x2 el+x+x2 | 2 [[36,8,4]] 4 el+x+x2 el+x+x2 | 3 [[54,8,4]] 6
> el+x+x2 el+x+x2] [...] For q mod 3 ≠ 0, there is a simple
> isomorphism: letting C3 = ⟨y⟩, we can define
> f : F2Cl ⊗H F2Cl → F2[C3 × Cl] (54a); f(x^q ⊗H el) ↦ y ⊗ el (54b);
> f(el ⊗H x) ↦ e3 ⊗ x (54c). [...] Distances quoted are exact
> distances found by formulating distance-finding as a problem in
> linear integer programming.

**Applicability to gross.** Indirect: [[36,8,4]] is two conjectural
h = 2 transfer steps below gross. Also note bb_108 covers [[36,8,4]]
with h = 3 ODD and k preserved, so SRB Thm 4.7 rigorously gives
d(bb_108) ≥ d([[36,8,4]]) — an analytic d ≥ 4 for [[36,8,4]] would
yield the first fully-analytic nontrivial bound on a Bravyi-table
instance.

**Feeds.** Track B: identifies [[36,8,4]] as a known
(Tiew–Breuckmann balanced-product) code BUT with only an
upper-bound theorem — the chain's analytic floor cannot currently be
moved up from [[18,8,2]] to [[36,8,4]] by citation. A new analytic
lower bound d([[36,8,4]]) ≥ 4 (e.g. via balanced-product distance
theory) would lift the whole chain one rung.

### L4-no-hgp-36-8-4 — no binary HGP code has parameters [[36,8,4]] (CONFIRMED-WITH-CORRECTIONS; original derivation, verifier re-checked)

**Claim (corrections applied).** ORIGINAL DERIVATION (not
literature): no binary HGP code has parameters [[36,8,4]]. Proof
shape, with the verifier's two precision fixes applied: by TZ
**Lemma 17** (the upper-bound half of Theorem 15 — Theorem 15's bare
equality bullets alone leave one degenerate corner that Lemma 17
covers), d_Q ≤ dᵢ whenever the same-side partner kernel is
nontrivial; so any HGP with d_Q = 4 and k = k₁k₂ + k₁ᵀk₂ᵀ = 8 needs
**every sector code whose same-side partner is nontrivial** (not
literally "all nontrivial sector codes") to have distance ≥ 4 — and
those are exactly the sectors entering the count. The Griesmer bound
([n,k,4]₂ needs n ≥ 4,6,7,8,9,10,11,12 for k = 1..8 — values
re-verified) then forces n₁n₂ + r₁r₂ ≥ 48 in every factorization of
8 (pure-sector cases: min(4·12, 6·8) = 48; mixed splits ≥ 60),
exceeding 36. Hence the cover chain's HGP anchor is exactly
[[18,8,2]] and cannot be relocated to [[36,8,4]]; consistent with TB
needing a balanced product (a quotient of HGP(6,6) by C₂) to realize
n = 36 (this last remark is session-internal context, not
literature-verified).

**Source.** This session's derivation from Tillich–Zémor Theorem 15
+ Lemma 17 + the Griesmer bound (case analysis over
k₁k₂ + k₁ᵀk₂ᵀ = 8). Independently re-derived by the verifier.

**Verified quote (the TZ inputs, verbatim).**

> Lemma 17: "Let i belong to {1,2}. Assume that d_{3−i} ≠ ∞. Then
> d_Q ≤ d_i. If d_{3−i}^T ≠ ∞ then d_Q ≤ d_i^T." Proposition 14:
> "The quantum dimension k_Q of Q(G_1 × G_2) is given by
> k_Q = k_1 k_2 + k_1^T k_2^T."

**Applicability to gross.** Same Griesmer-style argument scales:
gross [[144,12,12]] as an HGP would need all relevant sector
distances ≥ 12 with k-products summing to 12; not checked
exhaustively here, but gross is anyway not HGP since c = 8 ≠ 1
obstructs the separated-variable form.

**Feeds.** Track B: closes the question "is [[36,8,4]] secretly an
HGP code with free analytic distance?" — NO. Any analytic d ≥ 4 for
[[36,8,4]] must come from balanced-product/quotient or BB-specific
arguments, not from the HGP theorem.

### L4-tb-hgp-18q2-family — the only weight-6 separated-support family with analytic exact distance at all sizes (CONFIRMED-WITH-CORRECTIONS)

**Claim (corrections applied).** Tiew–Breuckmann's [[18q², 8, 2q]]
hypergraph-product family is a weight-6 (two 3-term polynomials),
separated-support family with fully analytic exact distance for all
q: the seed is the cyclic code on Z_{3q} with check polynomial
1+x+x², whose classical distance 2q they cite to
MacWilliams–Sloane (ref [24] confirmed), and the paper asserts the
exact quantum distance 2q for all q. **Corrections:** (i) the first
quoted sentence is from the *Introduction*, not the Abstract;
(ii) the paper calls this family a hypergraph-product code
throughout and never labels it "BB-type" — the BB-form reading is
the researcher's mathematically faithful reframing (Eq. (29a) gives
H_X = [A(y) | B(x)] with separated supports over F₂[C_{3q} × C_{3q}],
check weight 6 stated explicitly); (iii) the derivation route "the
quantum distance follows from the HGP min formula" is the
researcher's *sound* reconstruction, not the paper's explicit
argument — the paper supplies the needed hypothesis (pᵀ(x) and p(x)
describe the same classical code) and the verifier independently
confirmed the classical seed code has distance exactly 2q. This
answers L4 task 3 in the affirmative for SEPARATED supports:
analytic d results for weight-6 BB-shaped codes exist and scale as
Θ(√n). [[18,8,2]] is the q = 1 member. No member beyond q = 1 lies
in gross's cover lattice ([[72,8,4]] at q = 2 differs from the
chain's [[72,12,6]] — arithmetic verified).

**Source.** Same paper, arXiv:2411.03302. Introduction; Section V.1
(journal-style V.A) "Description of the [[18q², 8, 2q]] Code",
Eq. (37).

**Verified quote.**

> The code families have parameters [[18q²,8,2q]]_{q∈ℕ} and
> [[18q,8,≤ 2q]]_{q∈ℕ} respectively. They are constructed by taking
> a product of the simplest cyclic code after the repetition code,
> and in a sense are the simplest extensions of the toric code.
> [...] The check weight in this construction is 6, for both X- and
> Z-checks. [...] This code can be thought of as the simplest
> extension of the toric code, as it uses the check polynomial
> p(x) = e_l + x + x² (37) This polynomial is an irreducible
> polynomial for cyclic groups of order 3q, q ∈ ℕ, and is the
> simplest polynomial with higher degree than that for the
> repetition code. The polynomial describes a general BCH code
> [24, Chapter 3], a type of cyclic code, which guarantees a
> classical code distance of 2q [24, Ch. 7. § 6. Theorem 8].

**Applicability to gross.** Not applicable to gross (separated
supports, c = 1 family). Useful as the control family for any
conjectured c-aware bound: a candidate bound should reproduce
d = 2q here.

**Feeds.** Tracks B/A: the only weight-6 BB-adjacent family found
with analytic exact distance at all sizes. Defines the published
frontier for L4 task 3: analytic d for weight-6 codes exists exactly
when supports separate (c = 1); no analytic lower bound found
anywhere for non-separated weight-6 BB codes (gross-type) — but see
the SRB odd-h carve-out under L4-prior-art-clearance-2026.

### L4-srb-thm-4-6-4-7 — the only published rigorous cover transfer: odd h, k preserved (CONFIRMED)

**Claim.** Symons–Rajput–Browne's rigorous cover-transfer theorems,
quoted exactly: Thm 4.6 (h odd ⟹ d_h ≤ hd) and Thm 4.7 (h odd AND
k_h = k ⟹ d ≤ d_h ≤ hd). The lower-bound direction d_h ≥ d is
exactly the transfer Track B wants, but published only for ODD h
with k preserved; their Remark 9 concedes the even-h / k-changing
cases need injectivity/surjectivity that "are clearly not guaranteed
in general". Verifier's adversarial cross-check passed: Theorem 4.7
is the paper's *only* rigorous lower bound (Theorem 4.8 gives the
opposite direction d_h ≤ d under a weight-preserving-lift
hypothesis; the abstract/conclusion explicitly leave the even-h
lower bound as an empirical conjecture). The reported Remark 9 quote
omitted its final two sentences, which reinforce rather than weaken
the claim (restored below).

**Source.** Symons, Rajput, Browne, *Sequences of Bivariate Bicycle
Codes from Covering Graphs*, arXiv:2511.13560. Theorems 4.6 and 4.7
and Remark 9 (Section 4.3).

**Verified quote.**

> Theorem 4.6. Let Q(A, B, l, m) and Q̃(Ã, B̃, l̃, m̃) be two BB codes
> with parameters [[n, k, d]] and [[nh = hn, kh, dh]] respectively
> that satisfy the conditions of Theorem 3.1 so that Q̃ is an h-cover
> code of Q. If h is odd, dh ≤ hd. [...] Theorem 4.7. With the same
> conditions as in the preceding theorem, suppose h is odd and
> kh = k. Then d ≤ dh ≤ hd. [...] Remark 9. When attempting to
> generalize these arguments to situations where h is even or
> k ≠ kh, we arrive at points in the proof where the injectivity or
> surjectivity of pi or τi respectively or their corresponding
> induced maps in homology are needed. These are clearly not
> guaranteed in general. While it may be possible to prove general
> upper and lower bounds for these cover codes, this may require
> either more specific information about the codes or other kinds of
> arguments entirely.

**Applicability to gross.** Gross's only covers in the A0 lattice
with k′ > 0 are even-h (h = 2, 4, 8), so Thm 4.7 never applies to
gross — its hypotheses are exactly what Section 6k identified as the
2-divisibility wall.

**Feeds.** Track B: the exact statement and hypotheses of the only
published rigorous transfer. Composing with this lane's base
anchors: bb_90 = 5-cover of [[18,8,2]] (h odd, k = 8 preserved)
gives the FULLY-ANALYTIC chain 2 = d([[18,8,2]]) ≤ d(bb_90) ≤ 10
available today; bb_108 = 3-cover of [[36,8,4]] (h odd, k = 8
preserved) gives d(bb_108) ≥ d([[36,8,4]]) pending an analytic bound
on the base.

### L4-rigorous-odd-h-bases-exist — A0 observation 3 is wrong; bb_90 and bb_108 have rigorous odd-h bases with k′ = 8 (CONFIRMED-WITH-CORRECTIONS)

**Claim (corrections applied).** `A0_baseline.md` is internally
inconsistent: headline observation 3 claims "Every rigorous (odd-h)
base of every Bravyi instance has k′ = 0", but A0's own tables list
bb_90's 3×3 base (h = 5, odd, rigorous, A′ = 1+y+y², B′ = 1+x+x²,
n′ = 18, k′ = 8, d′ = 2) and bb_108's 3×6 base (h = 3, odd,
rigorous, A′ = 1+y+y², B′ = y³+x+x², n′ = 36, k′ = 8, d′ = 4). Both
have k′ = 8 with k preserved. The verifier independently re-derived
applicability: SRB Thm 3.1's monomial-reduction conditions hold by
direct computation for both covers (bb_90: A = x⁹+y+y² → 1+y+y²
mod x³, B = 1+x²+x⁷ → 1+x+x², all monomials distinct; bb_108: the
x³ → 1 reductions check out). Consequences: SRB Thms 4.6 + 4.7
apply RIGOROUSLY to bb_90 — giving 2 ≤ d ≤ 10, with
d(bb_90) = 10 SATURATING the odd-h upper bound 5·2 — and to bb_108
(giving d ≥ d([[36,8,4]])). **Two corrections:** (i) the interval
2 ≤ d ≤ 10 needs *both* Thm 4.6 (upper) and Thm 4.7 (lower), not
"Thm 4.7" alone; (ii) the sub-claim "gross remains the only
flagship with no odd-h base of positive k′" is **REFUTED by the
same file** — bb_72's and bb_288's odd-h rows ALL have k′ = 0 too,
so three of the five instances (bb_72, gross, bb_288) lack odd-h
positive-k′ bases; only bb_90 and bb_108 have them.

**Source.** `experiments/bb_lab/notes/A0_baseline.md` — headline
obs. 3 (lines 37–41) vs. the bb_90 table row at line 93 and the
bb_108 table row at line 112 (quotes verified verbatim against the
file).

**Verified quote.**

> [lines 37–41] "3. **Every rigorous (odd-h) base of every Bravyi
> instance has k′ = 0** — the rigorous SRB bound is vacuous on the
> whole table, confirming §6k's narrow claim. ..." [line 93, bb_90
> §Cover lattice] "| 3×3 | 5 | odd (rigorous) | `1 + y + y^2` |
> `1 + x + x^2` | 18 | 8 | 2 (sat) |" [line 112, bb_108 §Cover
> lattice] "| 3×6 | 3 | odd (rigorous) | `1 + y + y^2` |
> `y^3 + x + x^2` | 36 | 8 | 4 (sat) |"

**Applicability to gross.** Does not directly bound gross (gross has
no odd-h positive-k′ base — that much of obs. 3 survives, though it
is not unique in this), but provides the program's first realistic
fully-analytic milestones on sibling instances.

**Feeds.** Track B: changes the target list. Phase 2 must not
propagate obs. 3's claim. bb_108 becomes the highest-value
intermediate target: one analytic lower bound on [[36,8,4]] plus the
already-published SRB Thm 4.7 yields a fully analytic d ≥ 4 on a
Bravyi-table instance with NO conjectural ingredient.

### L4-liang-twisted-tori-correspondence — twisted-tori geometry for gross, but zero analytic distance content (CONFIRMED)

**Claim.** Liang–Liu–Song–Chen establish the "generalized toric
codes on twisted tori" framework and state it "naturally applies to
bivariate bicycle codes"; the gross stabilizers are the
(−1,3,3,−1)-generalized toric code (f = 1+x+x⁻¹y³, g = 1+y+x³y⁻¹,
their Example 3 — polynomials verified exact, and the paper itself
identifies them with the gross code of Bravyi et al.), and the SAME
stabilizers on different twisted-torus lattices produce a family
including [[72,8,8]], [[108,8,10]], [[144,12,12]], [[162,8,14]], …,
[[360,12,≤24]]. CRITICAL for L4: all their distances are
COMPUTATIONAL, not analytic (integer programming, exact for d ≤ 20;
probabilistic upper bounds beyond — verifier grepped the full text
and found no analytic distance lower bound or proof anywhere). So
the twisted-tori literature supplies geometry/equivalences for
weight-6 BB codes but NO analytic distance proof — it does not
preempt the program's goals, and it does not anchor any chain member
analytically.

**Source.** Liang, Liu, Song, Chen, *Generalized toric codes on
twisted tori for quantum error correction*, arXiv:2503.03827
(PRX Quantum 6, 020357, 2025 — journal ref confirmed). Fig. 2
caption; Table I caption; main text; Example 3.

**Verified quote.**

> [Fig. 2 caption] Even when the stabilizers are identical, their
> implementation on different lattices yields various quantum LDPC
> codes. For instance, we later demonstrate that the
> (−1, 3, 3, −1)-generalized toric code (Example 3), also known as
> the (3, 3)-bivariate bicycle (BB) code [18, 83], produces the
> [[72, 8, 8]], [[108, 8, 10]], [[144, 12, 12]], [[162, 8, 14]],
> [[180, 8, 16]], [[192, 8, 16]], [[234, 8, 18]], [[270, 8, 20]],
> [[282, 4, ≤ 24]], and [[360, 12, ≤ 24]] quantum LDPC codes.
> [Table I caption] Code distances are computed exactly from the
> integer programming approach [18, 92]. [Main text] For codes with
> d ≤ 20, the code distance can be computed exactly; for codes with
> larger d, we employed a probabilistic algorithm with sufficient
> runtime to obtain an upper bound that we believe to be tight.
> [Example 3] This corresponds to the stabilizers of the gross code
> in Ref. [18] and the (3, 3)-BB code in Ref. [83], described by the
> following polynomials: f(x, y) = 1 + x + x⁻¹y³,
> g(x, y) = 1 + y + x³y⁻¹

**Applicability to gross.** Directly about gross: gross = the
(3,3)-BB stabilizers on the Z₁₂ × Z₆ torus; the framework applies as
stated, but contributes no distance lower bound.

**Feeds.** Tracks B/D: prior-art clearance (no analytic d for gross
or its family in the twisted-tori line) plus a geometric reframing
of gross that any anyon/Gröbner-basis attack would start from. Their
Gröbner machinery is analytic for k but not for d.

### L4-prior-art-clearance-2026 — gross-specific clearance survives; blanket clause does NOT (CONFIRMED-WITH-CORRECTIONS, verifier flag: not fully verified)

**Claim (corrections applied — read § Unverified / refuted for the
refuted sub-claims).** Prior-art check for 2024–2026, as corrected:
**no paper found claiming an analytic lower bound on gross's d** —
this half survived the verifier's adversarial re-search. The
researcher's *blanket* clauses ("no paper … on non-separated
weight-6 BB codes"; "searches returned nothing else") are
contradicted by arXiv:2511.13560 (SRB, Nov 2025, missed by the
clearance searches despite being this very lane's own source):
its Thm 4.7 IS a conditional analytic lower bound applicable to
non-separated weight-6 BB codes (its Example 5 treats exactly the
gross polynomials). The verifier re-derived the scope boundary:
gross is an h = 2 (EVEN) cover of [[72,12,6]], so the theorem does
not apply to gross itself — the gross-specific clearance stands.
Per-source characterizations verified: (a) arXiv:2605.14173
(Rabeti & Mahdavifar, 13 May 2026) introduces univariate-bicycle
codes and derives UPPER bounds on distance only;
(b) arXiv:2502.17052 (Postema & Kokkelmans) addresses dimension k
and existence, not d lower bounds. (c) The researcher's unread flag
arXiv:2508.09082 was **followed up by the verifier**: full title is
"Generalized Bicycle Codes with Low Connectivity: Minimum Distance
Bounds and Hook Errors" (Dastbasteh et al., 12 Aug 2025); it proves
upper AND lower distance bounds but only for univariate GB codes
with weight-4 check connectivity ([[d²+1,2,d]] / [[d²,2,d]]
families); no mention of gross, [[144,12,12]], bivariate, or
weight-6 — it does not breach the clearance, and it even asserts
such two-sided GB distance bounds are otherwise absent from the
literature. (d) Verifier's lower-confidence addendum: a search
snippet of arXiv:2510.05211 (Liang & Chen) states weight-6
SELF-DUAL BB codes reduce to color codes (known distances for that
subclass); gross is not self-dual and the paper's main enumeration
is weight-8, so this likely does not breach the clearance, but it
should be audited and cited in any final prior-art statement.

**Source.** arXiv:2605.14173 and arXiv:2502.17052 (abstracts);
verifier follow-ups on arXiv:2511.13560, arXiv:2508.09082,
arXiv:2510.05211.

**Verified quote.**

> [arXiv:2605.14173 abstract] We introduce univariate bicycle (UB)
> codes, a structured subclass of generalized bicycle (GB) quantum
> low-density parity-check (LDPC) codes obtained via a Frobenius
> relation. … Leveraging this structure, we derive upper bounds on
> the minimum distance by relating structured logical
> representatives to cycle-density properties of associated
> circulant matrices. [arXiv:2502.17052 abstract] …though the exact
> tradeoff of the code parameters [[n,k,d]] remained unknown. In
> this Article, we explore these codes by leveraging their ring
> structure, and predict their dimension as well as conditions on
> their existence. Finally, we highlight asymptotic badness.

**Applicability to gross.** Nothing found that applies to gross as
stated; UB/GB results are cyclic-group-scoped (gross's group is
non-cyclic with non-cyclic 2-Sylow), and the SRB lower bound needs
odd h, which gross's positive-k′ covers all lack.

**Feeds.** All tracks: clearance that Phase 2's planned theorems
(analytic gross bound, c-aware single-block dominance, even-h
transfer) are not preempted as of 2026-06 — **provided** every
novelty claim is phrased with the SRB odd-h transfer explicitly
carved out. Caveat stands: 2605.14173 / 2502.17052 were read at
abstract level only.

---

## Unverified / refuted

**No finding received a flat REFUTED or UNVERIFIABLE verdict**, but
one verified finding contains refuted sub-claims and one finding was
returned with `verified = false`; neither may be cited in its
original form.

**Refuted sub-claims (must not be propagated):**

| Where | Refuted sub-claim | Discrepancy |
|---|---|---|
| L4-prior-art-clearance-2026 (`verified = false`) | "Searches … returned nothing else"; "no paper claiming an analytic lower bound … on non-separated weight-6 BB codes" | arXiv:2511.13560 (SRB, Nov 2025 — inside the window, and this lane's own source) proves a conditional analytic lower bound d_h ≥ d for odd-h cover BB codes, applicable to non-separated weight-6 BB codes (its Example 5 treats the gross polynomials). Inapplicable to gross only because gross is an even 2-cover. The gross-specific half of the clearance survived; the blanket half did not. Also: 2508.09082's title was truncated in the finding (full: "…: Minimum Distance Bounds and Hook Errors"). |
| L4-rigorous-odd-h-bases-exist | "Gross remains the only flagship with no odd-h base of positive k′" | Refuted by `A0_baseline.md` itself: bb_72's odd-h rows (2×6 h=3, 6×2 h=3, 2×2 h=9) and bb_288's odd-h rows (4×12 h=3, 12×4 h=3, 4×4 h=9) all have k′ = 0, like gross's. Three of five instances lack odd-h positive-k′ bases; gross is not unique. ("Flagship" is the finding's own term, appearing nowhere in the bb_lab notes.) |

**Not verified (context-only findings, never sent to the
verifier).** These rest on the researcher's fetched quotes alone and
must go through verification before any of them becomes
load-bearing:

| Finding | Researcher claim (unverified) |
|---|---|
| L4-srb-cover-identifications | SRB explicitly identify the gross chain in their framework: gross is a double cover of [[72,12,6]] (Example 5); the [[36,8,4]] codes are 2-covers of [[18,8,2]] (Examples 6, 7 — A0's 6×3 and, up to presentation, 3×6 rows); [[54,8,6]] is a triple cover of [[18,8,2]]; their k = 8 cover sequences "appear to match" the Tiew–Breuckmann [[18h, 8, ≤ 2h]] balanced-product cyclic codes; "in principle" all generalised toric codes of Liang et al. arise as cover sequences. arXiv:2511.13560, Intro (p.3), Examples 5–7, Section 7. |
| L4-lp-weight4-classification | Lin–Pryadko classify ALL row-weight W = 4 2BGA codes: equivalent to direct sums of abelian-group codes mappable to rotated surface codes; with g = 1 and trivially-intersecting cyclic supports one gets a toric code. So weight-4 BB codes are completely toric/surface-classified analytically; weight-6 has no analogous published classification outside c = 1/HGP. arXiv:2306.16400, Section V A. |
| L4-eczoo-hgp-and-2bga-statements | ECZoo distance statements: HGP page states the min(d₁,d₂,d₁ᵀ,d₂ᵀ) parameter formula UNconditionally (stronger than TZ Thm 15's conditional equality — do not cite the zoo's version as a theorem); 2BGA page states the trivial-intersection HGP equivalence citing Lin–Pryadko; BB page (/c/qcga) makes NO analytic distance statements; GB page quotes the Wang–Pryadko analytic GB lower bound d ≥ d₀ citing arXiv:2203.17216. 2BGA/GB quotes passed through WebFetch summarization (primary-source version of the 2BGA statement is verified in L4-lp-statement-8-hgp). |

---

## Open questions and dead ends

### Open questions (researcher, verbatim)

1. "Does an analytic lower bound d >= 4 exist or seem provable for
   [[36,8,4]] (= Tiew-Breuckmann balanced-product q=2, = 2-cover of
   [[18,8,2]])? TB prove only d <= 2q. Balanced-product distance
   theory (Breuckmann-Eberhardt arXiv:2012.09271) was not examined
   this session — it is the obvious next place to look, and success
   would (via SRB Thm 4.7 with h=3 odd) immediately give a
   fully-analytic d >= 4 for bb_108 [[108,8,10]]."
2. "A0_baseline.md observation 3 ('every rigorous odd-h base has
   k' = 0') contradicts A0's own bb_90 (3x3, h=5, k'=8) and bb_108
   (3x6, h=3, k'=8) table rows. Which is wrong — the observation or
   the parity/k' columns? If the tables are right, do these covers
   actually satisfy SRB Theorem 3.1's conditions (required for
   Thm 4.7)? This must be settled before Phase 2 relies on either."
   - *Verifier update (this lane): settled in the tables' favor —
     the observation is wrong, and the verifier re-derived SRB
     Thm 3.1's monomial-reduction conditions to hold for both covers
     by direct computation (see L4-rigorous-odd-h-bases-exist).*
3. "The task statement's claim that the gross chain 'saturates
   d_cover = 2*d_base at every step' fails at the [[72,12,6]] ->
   [[36,8,4]] step (6 != 2*4); only gross->72 (12=2*6) and 36->18
   (4=2*2) saturate. Does Phase 2's Track B target the right
   transfer inequality (d_cover >= d_base, not >= 2*d_base, since
   the latter is empirically false at one step)?"
4. "The ECZoo HGP page states d = min(d1,d2,d1T,d2T)
   UNconditionally, but TZ Theorem 15 proves equality only under
   conditions. Is the unconditional equality proven somewhere
   (candidate: Zeng-Pryadko, 'Minimal distances for certain quantum
   product codes and tensor products of chain complexes')? Matters
   only for corner cases with trivial sector codes; the [[18,8,2]]
   instance is safely inside TZ's equality conditions either way."
5. "arXiv:2508.09082 'Generalized Bicycle Codes with Low
   Connectivity: Minimum Distance' was found but not read — check
   whether its GB minimum-distance techniques extend beyond cyclic
   groups."
   - *Verifier update (this lane): follow-up completed — full title
     "…: Minimum Distance Bounds and Hook Errors"; two-sided bounds
     but only for univariate weight-4-connectivity GB families
     ([[d²+1,2,d]], [[d²,2,d]]); no bivariate/weight-6/gross
     content; does not breach the clearance.*
6. "Wang-Mueller 'Coprime bivariate bicycle codes'
   (arXiv:2408.10001) maps coprime-(l,m) BB codes to cyclic GB codes
   where Wang-Pryadko analytic GB bounds apply. None of the
   gross-chain groups is coprime (gcd(12,6), gcd(6,6), gcd(3,6),
   gcd(3,3) all > 1), but does ANY Bravyi-adjacent instance admit a
   coprime presentation that would give an analytic anchor?"
7. "Is [[72,12,6]] (Z_6 x Z_6) a known code in any analytic family?
   This session found it only as: SRB Example 5's base of gross, and
   a generalized-toric-on-twisted-torus instance (numerical d). It
   is not HGP (c=4), not in the TB families (k=12). Its analytic
   status is the single biggest gap between the
   [[18,8,2]]/[[36,8,4]] anchors and gross."

### Dead ends (researcher, verbatim)

- "Search '[[18,8,2]] quantum code': no named Error Correction Zoo
  entry and no dedicated paper exists for this code; it appears only
  as Tiew-Breuckmann's q=1 family member and SRB's Example 6 base
  code. Don't search for an eponymous '[[18,8,2]] code' page."
- "https://errorcorrectionzoo.org/c/bivariate_bicycle is a 404 — the
  BB page lives at /c/qcga (and the gross code at /c/gross)."
- "The ECZoo gross page (/c/gross) contains nothing about how d=12
  was established and no construction details — not a useful source
  for distance provenance."
- "The ECZoo BB page (/c/qcga) contains NO analytic distance
  statements for BB codes (only circuit-distance d_circ <= 10
  remarks for depth-7 schedules) — don't mine it for distance
  theory."
- "arXiv:1212.6703 is the 'hyperbicycle' paper, NOT the source of an
  unconditional exact HGP distance formula; it explicitly attributes
  the HGP lower bound and conditional upper bounds to Tillich-Zemor
  (Thm 9 / Lemma 10 of the ISIT version). Searching it for 'Theorem
  giving exact HGP distance' is a dead end; its own Theorems 5/6 are
  for hyperbicycle c >= 1 with floor(d/c) lower bound."
- "WebFetch on arxiv.org/pdf/<id> returns unreadable binary for
  these papers; the working pattern is curl + pdftotext locally
  (used for 0903.0566, 1202.0928, 1212.6703, 2411.03302, 2306.16400,
  2511.13560, 2503.03827)."
- "arXiv:2306.16400v4 does not exist (fetch returns HTML error
  page); use /pdf/2306.16400 unversioned."
- "grep of local catalog/zoo.yaml for '18,8,2' / '36,8,4': no
  entries — the repo's 267-code catalog does not contain the chain's
  base codes as standalone codes."
- "Searches 'bivariate bicycle distance lower bound analytic proof
  2025 2026 gross code' and 'arxiv 2026 bivariate bicycle minimum
  distance theorem proven analytic bound group algebra': no paper
  proving an analytic lower bound for gross or for non-separated
  weight-6 BB codes (only k/existence results, UB upper bounds, and
  the SRB odd-h transfer already known to the program)."
  - *Verifier caveat: as a blanket negative this is the clause
    contradicted by SRB itself (see § Unverified / refuted); the
    gross-specific half stands.*
- "Liang et al 2503.03827 abstract/tables do not contain
  [[144,12,12]]'s chain relatives [[18,8,2]], [[36,8,4]],
  [[72,12,6]] as named instances, and the paper's distances are all
  integer-programming/probabilistic — no analytic distance content
  to extract beyond the correspondence itself."

---

## Implications for Phase 2

**Nothing planned is preempted.**

- No source proves an analytic lower bound on gross's d
  (L4-prior-art-clearance-2026, gross-specific half, adversarially
  re-searched); the twisted-tori line is computational-only
  (L4-liang-twisted-tori-correspondence); the only published
  rigorous transfer is odd-h with k preserved (L4-srb-thm-4-6-4-7),
  which never reaches gross.
- One scoping requirement: every Phase-2 novelty claim about
  "analytic lower bounds for non-separated weight-6 BB codes" must
  carve out SRB Thm 4.7 (odd-h covers) explicitly — the blanket
  version of the claim is already false in the literature.

**Enabled.**

- **Track B (chain anchor upgraded):** the [[18,8,2]] chain bottom
  now rests on three published, hypothesis-verified analytic routes
  (TZ Thm 15; KP Eq. (12); LP Statement 8 + connectivity) instead of
  a weight-1 exhaustion argument. The cleanest Lean target is the KP
  square-circulant-seed special case; the fullest is TZ Thm 15 with
  its equality bullets (formalize Lemma 17, not just the equality
  cases, if the [[36,8,4]] impossibility argument is ever
  formalized too).
- **Track B (new fully-analytic milestones, available today):**
  correcting A0 obs. 3 unlocks two rigorous compositions —
  2 ≤ d(bb_90) ≤ 10 (both bounds published: Thm 4.7 + Thm 4.6 over
  the h = 5 cover of [[18,8,2]]; the upper bound is saturated,
  10 = 5·2) and d(bb_108) ≥ d([[36,8,4]]) (h = 3). The
  highest-leverage single open problem produced by this lane:
  **an analytic d ≥ 4 for [[36,8,4]]** (open question 1 —
  Breuckmann–Eberhardt balanced-product distance theory,
  arXiv:2012.09271, is the unexamined candidate tool), which would
  give the program's first fully-analytic nontrivial bound on a
  Bravyi-table instance with no conjectural ingredient.
- **Track A (bracket sharpened):** the published machinery now
  brackets the gap exactly — equality d_Z = min(d_A^⊥, d_B^⊥)
  guaranteed at c = 1 (LP Statement 8 / the c = 1 remark), only
  ⌈min/c⌉ for c > 1 (Statement 12), with [[36,8,4]] (c = 2, bound 2
  vs. true 4) as the smallest concrete instance of the gap and the
  TB [[18q²,8,2q]] family as the c = 1 control any candidate
  c-aware bound must reproduce.
- **Track D:** the twisted-tori reframing of gross (Example 3
  polynomials verified) is the published geometric starting point
  for any anyon/Gröbner attack; its machinery is analytic for k but
  not d — the d-slot is open.

**Killed / blocked (paths, not tracks).**

- "Maybe [[36,8,4]] is secretly an HGP code with free analytic
  distance" is dead: no binary HGP code has parameters [[36,8,4]]
  (L4-no-hgp-36-8-4, original derivation, verifier re-checked). Any
  analytic d ≥ 4 there must come from balanced-product/quotient or
  BB-specific arguments.
- "Relocate the chain anchor upward by citation" is dead for every
  rung above [[18,8,2]]: [[36,8,4]] has only TB's upper bound;
  [[72,12,6]] is in no known analytic family at all (open
  question 7 — the single biggest gap between the anchors and
  gross).
- The ECZoo's unconditional HGP min-formula must not be cited as a
  theorem (it is stronger than what TZ proves); cite TZ Thm 15's
  conditional version or first verify the Zeng–Pryadko candidate
  (open question 4).

**Action items emitted by this lane.**

1. **Fix `A0_baseline.md` observation 3** (it is contradicted by the
   file's own bb_90/bb_108 rows, verifier-settled in the tables'
   favor) — and do not replace it with "gross is the only instance
   lacking odd-h positive-k′ bases", which is also false (bb_72 and
   bb_288 lack them too). The correct statement: only bb_90 and
   bb_108 have rigorous odd-h bases with k′ > 0.
2. Examine Breuckmann–Eberhardt arXiv:2012.09271 for a
   balanced-product route to d([[36,8,4]]) ≥ 4 (open question 1) —
   the lane's highest-value follow-up.
3. Settle [[72,12,6]]'s analytic status (open question 7) before
   Track B commits to the full-chain strategy.
4. Verify L4-srb-cover-identifications (currently unverified) before
   any Phase-2 text asserts the SRB Examples 5–7 identifications.
5. In any prior-art statement: cite SRB Thm 4.7 as the existing
   conditional analytic lower bound for (odd-h-cover) weight-6 BB
   codes, and audit arXiv:2510.05211 (self-dual weight-6 → color
   codes) before final wording.
