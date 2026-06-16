# A1/L3 — Publication frontier: gross d=12 + BB logical-operator structure

Date: 2026-06-09. Lane L3 of the Phase-1 literature sweep for the
analytic-bound program. Researcher findings adversarially verified;
quotes below are the **verifier's** verbatim extractions, and all
verifier corrections are applied to the claims.

**Lane verdict.** The program's premise survives adversarial
verification intact: as of 2026-06-09 there is **no published analytic
proof or analytic lower bound** for the gross code's d = 12 — Bravyi et
al. certify it only by ILP, the strongest published applicable lower
bound (Lin–Pryadko Statement 12, a version of Kovalev–Pryadko 2013
Thm 5) gives only d ≥ 2 on gross (verifier independently recomputed
c = |N| = 8 and d_A^⊥ = d_B^⊥ = 12), and the SRB even-h cover
conjecture that governs gross's entire 2-cover chain is explicitly
open with the authors' own toolkit declared insufficient (no
proving follow-up among all six citing papers as of 2026-06-09). The
published structural toolkit Tracks A/B need does exist — the
Eberhardt–Steffan fundamental exact sequence applies verbatim to gross
with no semisimplicity hypothesis — but ES's own Table 1 marks gross
non-pure/non-principal/non-symmetric, so no published explicit logical
basis covers it, and nobody has computed the four exact-sequence terms
for gross or converted any explicit-basis machinery into a lower
bound. One citation in the lab's prior notes is corrected here: the
"Otjens 2025" attribution and its "no closed-form analytical formula"
quote are apocryphal (third citation failure of the known genre).

Verification scoreboard (8 load-bearing findings sent to the verifier):

| finding | verdict |
|---|---|
| L3-bravyi-mip-distance | CONFIRMED-WITH-CORRECTIONS |
| L3-bravyi-lemma1-dxdz | CONFIRMED |
| L3-es-fundamental-exact-sequence | CONFIRMED |
| L3-es-gross-nonprincipal | CONFIRMED |
| L3-lp-statement12 | CONFIRMED-WITH-CORRECTIONS |
| L3-srb-odd-h-theorem | CONFIRMED |
| L3-srb-even-h-explicitly-open | CONFIRMED |
| L3-otjens-citation-correction | CONFIRMED |

Seven further context-only (non-load-bearing) findings were **not**
verified — see § Unverified / refuted.

---

## Verified findings

### L3-bravyi-mip-distance — gross d=12 is ILP-computed, not proven (CONFIRMED-WITH-CORRECTIONS)

**Claim (corrections applied).** Bravyi et al. establish exact
distances for **5 of the 7** BB codes in their Table 3 — including
gross [[144,12,12]] — purely computationally, via the
integer-linear-programming method of Landahl–Anderson–Rice
(arXiv:1108.5738, ref [55]); the remaining two entries
([[360,12,≤24]] and [[756,16,≤34]]) carry the caption's "≤ d"
notation, i.e. only upper bounds were known at the time of writing.
BP-OSD was used as an efficient upper-bound proxy (d_BP) during code
search (and also to upper-bound the distinct circuit-level distance
d_circ). The paper contains **no analytic distance proof and no
analytic lower bound on d** for any of its codes — the string "lower
bound" (analytic) never appears, and the only analytic distance
content is Lemma 1's characterization.

> The researcher's original "establish d for **all** BB codes in
> Table 3 ... exact distances" was the over-claim; the gross code IS
> among the exact five, so the lane premise is unaffected.

**Source.** Bravyi, Cross, Gambetta, Maslov, Rall, Yoder,
*High-threshold and low-overhead fault-tolerant quantum memory*,
arXiv:2308.07915 (Nature 627, 778–782, 2024). Table 3 caption;
BP-OSD appendix (pdftotext lines 1677–1724 of arXiv v2);
bibliography entry [55].

**Verified quote.**

> Table 3: Small examples of Bivariate Bicycle LDPC codes and their
> parameters. All codes have weight-6 checks, thickness-2 Tanner
> graph, and a depth-7 syndrome measurement circuit. Code distance
> was computed by the mixed integer programming approach of
> Ref. [55]. Notation ≤ d indicates that only an upper bound on the
> code distance is known at the time of this writing. || The actual
> distance of each candidate code was computed using the integer
> linear programming method [55]. || [55] Andrew J. Landahl, Jonas
> T. Anderson, and Patrick R. Rice. Fault-tolerant quantum computing
> with color codes. arXiv preprint arXiv:1108.5738, 2011. || We also
> employed BP-OSD to compute an upper bound on the code distance d.
> || Using the quantity dBP as an efficiently computable proxy for
> the code distance enabled us to search over a large number of
> candidate BB codes with n = O(100) qubits.

**Applicability to gross.** Direct: gross's d = 12 is one of the five
ILP-exact entries — a computational certificate, not an analytic
proof. This is the definition of the program's target.

**Feeds.** All tracks — verifies the whole-program premise (goal 1,
analytic proof of gross d = 12, is unclaimed in the source paper).

### L3-bravyi-lemma1-dxdz — Lemma 1 characterizes but does not bound d; d_X = d_Z (CONFIRMED)

**Claim.** Bravyi et al. Lemma 1 gives the only analytic structural
facts about BB code parameters in the paper: n = 2ℓm,
k = 2·dim(ker A ∩ ker B), d = min weight over ker(H_X) \ rs(H_Z),
and d_X = d_Z (proven via the self-inverse permutation C = C_ℓ ⊗ C_m
conjugating A^T = CAC, B^T = CBC). It characterizes d but does not
bound it. The verifier exhaustively scanned the paper's other lemmas
(Lemma 2 thickness, Lemma 3 connectivity, Lemma 4 toric layout,
appendix Sec. 9 logical/automorphism lemmas) and confirmed none
states parameter formulas or bounds d.

**Source.** Same paper, arXiv:2308.07915. Lemma 1, main text
(pdftotext lines 573–583; the "equal distance" sentence at 583 and
Eq. 13 at 590–592) and appendix proof (lines 1763–1790).

**Verified quote.**

> Lemma 1. The code QC(A, B) has parameters [[n, k, d]], where
> n = 2ℓm, k = 2 · dim (ker(A) ∩ ker(B)), and d = min |v|: v ∈
> ker(H X )\rs(H Z ). The code offers equal distance for X-type and
> Z-type errors. [Proof:] We claim that rk(H X ) = rk(H Z ). Indeed,
> define a self-inverse permutation matrix Cℓ of size ℓ × ℓ ... let
> C = Cℓ ⊗ Cm . ... one gets AT = CAC and B T = CBC. ... dZ ≤ |h| =
> |Cβ| + |Cα| = |β| + |α| = |f | = dX . ... Similar argument shows
> that dX ≤ dZ , that is, dX = dZ .

**Applicability to gross.** Unconditional — Lemma 1 carries no
semisimplicity or cyclic-Sylow hypotheses, and gross is one of the
paper's own Table 3 codes.

**Feeds.** All tracks: any Phase-2 theorem only needs to bound d_Z
(or d_X). Also the k-formula underlying the §6h k-vs-d invariant
distinction.

### L3-es-fundamental-exact-sequence — the published logical-space decomposition, hypothesis-free for gross (CONFIRMED)

**Claim.** Eberhardt–Steffan Theorem 2.3 gives a fully general
exact-sequence description (induced by the Künneth spectral
sequence, their Remark 2.4) of the logical space of any two-block
code over a **commutative** group algebra: with R the group algebra,
Z = {(f,g) ∈ R_h ⊕ R_v | cf = dg}, B = {(dr,cr) | r ∈ R}, H = Z/B,
there is an exact sequence
0 → ann(cd)/M → ann(c)/ann(c)(d) ⊕ ann(d)/(c)ann(d) → H →
((c)∩(d))/(cd) → 0, where M = {r ∈ ann(cd) | ∃f ∈ ann(c),
g ∈ ann(d) with rd = fd and rc = gc}. The image of the middle map β
is the pure part H_h + H_v; the last term measures non-pure
logicals. The only standing hypotheses are R commutative plus
finite-dimensional F_2-algebra — **no semisimplicity, coprimality,
or Sylow hypothesis** — so it applies verbatim to gross's
non-semisimple R = F_2[Z_12 × Z_6]. (Verifier note: non-abelian 2BGA
would need the bimodule generalization in their Appendix C —
immaterial for gross, whose group is abelian.)

**Source.** Eberhardt, Steffan, *Logical Operators and
Fold-Transversal Gates of Bivariate Bicycle Codes*, arXiv:2407.03973
(IEEE Trans. Inform. Theory 71(2), 1140–1152, 2025, DOI
10.1109/TIT.2024.3521638). Theorem 2.3 and §2.2–2.3 (HTML v1).

**Verified quote.**

> Theorem 2.3. The following maps yield an exact sequence, which we
> call the fundamental exact sequence, 0 → ann(cd)/M →
> ann(c)/ann(c)(d) ⊕ ann(d)/(c)ann(d) → H=Z/B → (c)∩(d)/(cd) → 0
> [maps labeled α, β, γ: [r] ↦ ([dr],[cr]); ([f],[g]) ↦ [f,g];
> [f,g] ↦ [cf]=[dg]] (3) where M is defined by M = {r ∈ ann(cd) |
> ∃f ∈ ann(c), g ∈ ann(d) such that rd = fd and rc = gc}. ... The
> image of β is the pure part H_h + H_v ⊂ H. || Z = {(f,g) ∈ R_h ⊕
> R_v | cf = dg} and B = {(dr,cr) | r ∈ R} so that H = H(c,b) = Z/B.
> [sic — "H(c,b)" is a typo in the paper itself; should be H(c,d)]

**Applicability to gross.** Applies as stated. For gross the
obstruction term ((c)∩(d))/(cd) is nonzero (see next finding), so
the pure part does not exhaust H.

**Feeds.** Tracks A and B — this is the published explicit
description of the BB logical space, the input any by-hand
minimum-weight argument needs. A weight-aware analysis of the four
terms over F_2[Z_12 × Z_6] is an unexplored route to a lower bound
on gross (no surveyed paper does this).

### L3-es-gross-nonprincipal — ES's own table excludes gross from the nice-basis machinery (CONFIRMED)

**Claim.** Eberhardt–Steffan's "nice basis" machinery does NOT cover
gross: their Table 1 explicitly marks the [[144,12,12]] code
(c = x³+y+y², d = y³+x+x², ℓ,m = 6,12 in their transposed
convention) as not pure, not principal, and not symmetric (× in all
three columns — verifier confirmed by parsing the raw HTML table,
row S1.T1.15.15, after a fast-model summary had wrongly claimed the
row absent). Their principality guarantee (§1.2, Cor 4.4) requires ℓ
and m odd; gross has both even (under either ordering convention).
Purity criterion: H pure iff (c)∩(d) = (cd) (Corollary 2.5); the
explicit basis surjection R/(c,d) ⊕ R/(c,d) → H, ([f],[g]) ↦
[fP, gQ] (Corollary 2.11) is defined only under principality, since
the generators P, Q exist only when ann(c), ann(d) are principal.

**Source.** Same paper, arXiv:2407.03973 (IEEE TIT 71(2), 2025).
Table 1 (§1.2), §1.2 intro, Corollary 2.5 (§2.3), Definition 2.10
and Corollary 2.11 (§2.4), Corollary 4.4.

**Verified quote.**

> We show that if ℓ and m are odd, all BB codes are principal. ||
> Table 1, row 2 (headers: c | d | l,m | [[n,k,d]] | Pure | Prin. |
> Sym.): x^{3}+y+y^{2} | y^{3}+x+x^{2} | 6,12 | [[144,12,12]] | × |
> × | × || Corollary 2.5. The homology H is pure, that is
> H=H_{h}+H_{v}, if and only if (c)∩(d)=(cd). Moreover,
> H=H_{h}⊕H_{v} if and only if (c)∩(d)=(cd) and ann(cd)=M. ||
> Definition 2.10: We call C(c,d) principal if it is pure and the
> ideals ann(c) and ann(d) are principal, that is, generated by
> single elements P,Q ∈ R. || Corollary 2.11. Assume that C(c,d) is
> principal. Write ann(c)=(P) and ann(d)=(Q). Then there is a
> surjection R/(c,d)⊕R/(c,d) → H, ([f],[g]) ↦ [fP,gQ]. (4) If,
> moreover, ann(P)=(c) and ann(Q)=(d), then the map is an
> isomorphism. || Corollary 4.4. Let ℓ and m be odd. Then, the code
> C(c,d) is pure and principal.

**Applicability to gross.** Negative, by the source's own table:
gross fails purity, principality, and symmetry; the odd-ℓ,m theorem
cannot be invoked. Consistent with the program's 2-divisibility wall
(ℓ, m even is exactly the parity obstruction again).

**Feeds.** Tracks A/B — blocks the easy path: gross admits no
published explicit toric-style logical basis, so any by-hand
minimum-weight argument must handle the non-pure obstruction term.

### L3-lp-statement12 — the identified published lower bound; gives only d ≥ 2 on gross (CONFIRMED-WITH-CORRECTIONS)

**Claim (corrections applied).** Lin–Pryadko Statement 12 is **the
published rigorous lower bound on BB/2BGA distance that the lab has
identified** as applicable to gross — *not* provably "the only" one;
it is explicitly a version of the already-published Kovalev–Pryadko
PRA 88, 012311 (2013) Theorem 5 (their Ref. [14]), which is a
published rigorous lower bound of the same form. The bound:
d_Z ≥ ⌈min(d_A^⊥, d_B^⊥)/c⌉ where c is the "rank" of the
intersection subgroup N = G_a ∩ G_b (required abelian and normal in
both support groups). The verifier confirmed that "rank" is the
paper's own established terminology for **group order** (used
throughout: "group rank ℓ", "abelian groups of ranks ℓ ≤ 50"), so
the lab's reading c = |N| is correct, not an interpretive stretch.
Verifier independently recomputed everything on gross: N = ⟨x³⟩×⟨y³⟩
≅ Z_4 × Z_2, abelian and normal, |N| = 8; min(d_A^⊥, d_B^⊥) = 12 by
exact kernel enumeration (both classical codes are [72,12,12]);
⌈12/8⌉ = 2. Statement 12 bounds d_Z only; d ≥ 2 on gross then
follows from the X↔Z symmetry of the construction (which holds — the
two classical codes match).

**Source.** Lin, Pryadko, *Quantum two-block group algebra codes*,
arXiv:2306.16400 (Phys. Rev. A 109, 022407, 2024). Statement 12
(HTML version), "Version of Theorem 5 from Ref. [14]"
(Kovalev–Pryadko PRA 88, 012311, 2013).

**Verified quote.**

> Statement 12 (Version of Theorem 5 from Ref. [14]). Given elements
> a, b ∈ F[G] such that the intersection subgroup N ≡ G_a ∩ G_b of
> rank c is abelian and normal in both support groups, let d_A^⊥ and
> d_B^⊥ be the distances of classical F-linear group algebra codes
> with parity check matrices A = L(a) and B = R(b). Then the
> distance d_Z of the code LP[a,b] satisfies d_Z ≥ d_0 ≡
> ⌈min(d_A^⊥, d_B^⊥)/c⌉. [Following paragraph, outside the theorem
> block:] To get a matching upper bound, we need an additional
> condition to ensure that, e.g., vectors in C_A^⊥ have vectors
> matching by symmetry in C_B^⊥ to form non-trivial GB codes, see
> Eq. (53) in the proof of Statement 9.

**Applicability to gross.** Applies (hypotheses hold; no
semisimplicity or cyclic-Sylow condition appears, so non-semisimple
F_2[G] is irrelevant). Gives only d ≥ 2 — the headroom Track A
targets. Matches A0 baseline obs. 1 exactly.

**Feeds.** Track A's published baseline and composition target
(improve the numerator via radical-multiplicative classical bounds;
the quantum step stays Statement 12). Add Kovalev–Pryadko 2013
Thm 5 to the baseline citation list alongside Statement 12.

### L3-srb-odd-h-theorem — cover-code parameter bounds proven only for odd h (CONFIRMED)

**Claim (precision applied).** Symons–Rajput–Browne prove cover-code
parameter bounds only for odd cover degree h: k_h ≥ k (Theorem 4.5)
and d_h ≤ h·d (Theorem 4.6) when h is odd, and d ≤ d_h ≤ h·d when h
is odd and k_h = k (Theorem 4.7). They conjecture the same parameter
bounds for all h. (Verifier nuance: the paper also proves one
additional conditional distance bound valid for ANY h — Theorem 4.8
gives d_h ≤ d when a weight-preserving-lift chain map exists, framed
by the authors as a numerical tool for ruling out
non-distance-growing covers, not a parameter theorem; it is an upper
bound, so it does not touch Track B's target direction.)

**Source.** Symons, Rajput, Browne, *Sequences of Bivariate Bicycle
Codes from Covering Graphs*, arXiv:2511.13560 (submitted
2025-11-17). Abstract; Theorems 4.5–4.7 (HTML v1).

**Verified quote.**

> For an h-cover code of an [[n,k,d]] BB code with parameters
> [[n_h=hn,k_h,d_h]], we prove that k_h≥k and d_h≤hd when h is odd.
> Furthermore if h is odd and k_h=k, we prove the lower bound
> d≤d_h. We conjecture it is always true that an h-cover BB code of
> a base [[n,k,d]] BB code has parameters [[n_h=hn, k_h≥k,
> d≤d_h≤hd]]. || Theorem 4.5. With the same conditions as in the
> preceding lemma, if h is odd then k_h≥k. || Theorem 4.6. ... If h
> is odd, d_h≤hd. || Theorem 4.7. With the same conditions as in the
> preceding theorem, suppose h is odd and k_h=k. Then d≤d_h≤hd.

**Applicability to gross.** Gross is an h=2 cover of [[72,12,6]]; h
even, so the proven theorems do NOT apply — only the conjecture
covers gross. The rigorous (odd-h) version is moreover vacuous on
the whole Bravyi table: every odd-h base has k′ = 0 (A0 baseline
obs. 3).

**Feeds.** Track B's launching point — all the value sits in the
conjectural even-h case.

### L3-srb-even-h-explicitly-open — Track B's target is open; no follow-up proves it (CONFIRMED)

**Claim.** SRB explicitly state the even-h case (Track B's exact
target, h=2 with char F_2 | h) is one of "several outstanding open
questions" and that their proof technique breaks; they say proving
it rigorously "may require different tools from those employed
here". The breaking mechanism is verified: Lemma 4.4 gives the
transfer map p∘τ = h·I, which is I for odd h and **0** for even h
over F_2 — matching the HANDOFF §6k correction that only the h·I
transfer map is blocked. Preemption check as of 2026-06-09: only v1
of SRB exists; all 6 papers citing arXiv:2511.13560 (2606.08771,
2605.19298, 2602.23307, 2601.18879, 2601.15446, 2512.20532) were
checked and none proves the even-h bounds; web searches found no
other follow-up. (The footnoted V. Guemard talk only identifies
gross as a double cover; it proves no parameter bounds.) Track B is
NOT preempted — a proof of d ≤ d_h for h=2 would be a new result.

**Source.** Same paper, arXiv:2511.13560. Discussion /
open-questions section (end of paper, HTML). The two quoted
passages appear in the opposite order in the paper (summary
paragraph first); no meaning is distorted.

**Verified quote.**

> This work raises several outstanding open questions. Our proof
> techniques for establishing bounds on k and d break down when h is
> even as then the characteristic of F_2 divides h (see for example
> Lemma 4.4). While we have numerical evidence that all h-cover BB
> codes obey the conjectured bounds k_h ≥ k and d ≤ d_h ≤ hd
> regardless of h, establishing this rigorously may require
> different tools from those employed here. || We have empirically
> observed the same behaviour for codes with even h and conjecture
> that the parameters of a h-cover code satisfy [[n_h = hn, k_h ≥ k,
> d ≤ d_h ≤ hd]] for any h. All the numerical evidence we have
> gathered to date supports this conjecture.

**Applicability to gross.** Direct: gross's entire even-h cover
chain (gross → [[72,12,6]] → [[36,8,4]] → [[18,8,2]], the A0
obs. 2 lattice) is governed only by this open conjecture.

**Feeds.** Track B — confirms Candidate B1 (d_cover ≥ d_base for
h=2) is open in the literature and that the original authors see
their own toolkit as insufficient.

### L3-otjens-citation-correction — "Otjens 2025" is a misattribution; the quoted abstract line is apocryphal (CONFIRMED)

**Claim.** The HANDOFF's "Otjens 2025 (arXiv:2502.17052)" is a
misattribution. arXiv:2502.17052 is by Jasper J. Postema and
Servaas J.J.M.F. Kokkelmans, *Existence and Characterisation of
Bivariate Bicycle Codes* (v1 2025-02-24 ... v4 2026-04-30); Pascal
Otjens appears only in its acknowledgments. "Otjens" is a separate
June-2024 TU/e BSc thesis (*Algebraic Characterisation of Bivariate
Bicycle Codes*, supervised by Postema and Kokkelmans) whose
algebraic result is a lower bound on the **dimension k**, not on d.
The alleged abstract quote "no closed-form analytical formula"
appears in NEITHER source: verifier independently re-ran the greps
— 0 hits for closed-form / closed form / analytic* in PK v4 full
text, absent from the v1 abstract, 0 hits for closed-form /
analytical formula / open problem (and zero analytic* hits at all)
in the thesis pdftotext. The defensible open-problem support is the
PK abstract sentence quoted below. This is the third citation
failure of the program's known genre.

**Source.** Postema, Kokkelmans, arXiv:2502.17052 (v4 abstract +
acknowledgments) / P.A.S. Otjens, TU Eindhoven BSc thesis, June 2024
(title page and abstract; no arXiv id).

**Verified quote.**

> Recently, bivariate bicycle (BB) codes have emerged as a promising
> candidate for such compact memory, though the exact tradeoff of
> the code parameters [[n,k,d]] remained unknown. || Acknowledgments:
> We thank Fabrizio Conca, Pascal Otjens, Jyrki Lahtonen and Raul
> Parcelas Resina dos Santos for fruitful discussions. || Thesis:
> Algebraic Characterisation of Bivariate Bicycle Codes ... P.A.S.
> Otjens ... Supervisors: Jasper Postema, Servaas Kokkelmans ...
> June 2024 ... In this way, a lower bound for the dimension k is
> established, demonstrating the potential of this approach.

**Applicability to gross.** The PK paper studies the same BB class
as gross; its open-problem framing supports (but does not prove)
that no analytic d formula exists. Its own theorems are
upper/asymptotic bounds and k-predictions only.

**Feeds.** All tracks / verification hygiene: HANDOFF §6j's closing
line ("consistent with Otjens 2025's stated open problem") rests on
a quote that does not exist as stated. **Action: replace the
citation with Postema–Kokkelmans arXiv:2502.17052 and the verbatim
"exact tradeoff ... remained unknown" sentence**, and fix
`notes/T2.3_literature_survey.md` "Conjectures" item 1, which
records the apocryphal quote.

---

## Unverified / refuted

**No finding was REFUTED or judged UNVERIFIABLE by the verifier.**
However, the verifier checked only the eight load-bearing findings
above. The following seven context-only findings were **not
independently verified** — they rest on the researcher's fetched
quotes alone and must not be treated as verified prior art if any of
them later becomes load-bearing:

| finding | researcher claim (unverified) |
|---|---|
| L3-lp-tables-computational | All distances in the Lin–Pryadko 2BGA enumeration tables are computational (randomized GAP/QDistRnd at UCR HPCC), not analytic. arXiv:2306.16400, methods text near refs [45],[46]. |
| L3-pk-generalised-bravyi-terhal | Postema–Kokkelmans' only "analytic" distance results are upper bounds imported from Arnault et al. (their Thm 2.18, generalised Bravyi–Terhal); PK themselves note the bound only applies for n ≥ 8192 and is trivial until n ≈ 4·10^5 — vacuous at gross's n = 144. arXiv:2502.17052 v4, §2 and §3. |
| L3-arnault-bt-variant | Arnault–Gaborit–Rozendaal–Saussay–Zémor prove the lattice-quotient Bravyi–Terhal variant (upper bound d ≤ m√γ_D(√D+4ρ)n^{(D−1)/D} for n^{1/D} ≥ 8ρ√γ_D) applied to abelian 2BGA codes. arXiv:2502.04995 (IEEE TIT 72(1), 437–446, 2026). Upper bound only. |
| L3-liang-twisted-tori-groebner | Liang–Liu–Song–Chen (PRX Quantum 6, 020357, 2025; arXiv:2503.03827): Gröbner-basis / anyon-periodicity framework on twisted tori computes k without parity-check matrices; BB codes are a special case; table distances algorithmic, some only upper-bounded; no analytic lower-bound theorem claimed. |
| L3-qdistrnd-frontier | QDistRnd (arXiv:2308.15140, JOSS 2022) is a randomized upper-bound algorithm with no performance guarantee — literature d-values sourced from it are randomized upper bounds. |
| L3-rabeti-univariate-bicycle | Rabeti–Mahdavifar (arXiv:2605.14173, 2026-05-13): complete logical parametrization for univariate bicycle (cyclic-group) codes yields only UPPER distance bounds; does not cover BB over Z_ℓ × Z_m. |
| L3-wang-mueller-coprime | Wang–Mueller coprime-BB subclass (arXiv:2408.10001): k predictable in advance, d still numerical; requires gcd(ℓ,m) = 1, which gross (gcd(12,6) = 6) violates. |

None of these is load-bearing for Phase 2 as planned; all are
frontier-context. If Track A/B later cites any of them (e.g. the
Arnault upper bound as a sanity ceiling, or Liang et al. as the
generalization target), send that finding through verification
first.

---

## Open questions and dead ends

### Open questions (researcher, verbatim)

1. "In Lin-Pryadko Statement 12, does 'the intersection subgroup
   N ≡ G_a ∩ G_b of rank c' mean c = |N| (lab's reading, c = 8 on
   gross, bound 2) or c = minimal number of generators of N
   (N ≅ Z_4 x Z_2 would give c = 2 and bound ⌈12/2⌉ = 6)? The lab's
   A0 baseline assumes |N|; verify against the proof of Statement
   12 / Kovalev-Pryadko 2013 Theorem 5 before Track A builds on the
   denominator. If the generator-rank reading were correct the
   published bound would already give d ≥ 6 on gross — too good to
   be plausible, but it must be settled from the proof, not
   assumed."
   - *Verifier update (this lane): largely settled — the paper's own
     terminology uses "rank" for group order throughout, so c = |N|
     = 8 is correct. The residual check against the KP13 Theorem 5
     proof remains cheap insurance before Track A invests.*
2. "Compute the four terms of the Eberhardt-Steffan fundamental
   exact sequence (Thm 2.3) explicitly for gross over
   F_2[Z_12 x Z_6]: dim ann(c)/ann(c)(d), dim ann(d)/(c)ann(d),
   dim ((c)∩(d))/(cd), dim ann(cd)/M. This quantifies how much of
   gross's 12-dimensional logical space is pure vs obstruction — the
   literature marks gross non-pure but never computes the split; it
   is the natural starting point for a weight analysis of logicals
   (Tracks A/B)."
3. "Does the ILP certificate from the Landahl-Anderson-Rice method
   as run by Bravyi et al. include a dual/optimality certificate
   that could in principle be transcribed into a verifiable (if
   inelegant) proof of d = 12, and would the program count that as
   'analytic'? (Currently excluded by the no-IP rule, but worth a
   policy decision.)"
4. "Postema-Kokkelmans v2/v3 abstracts were not checked for the 'no
   closed-form analytical formula' phrasing (v1 and v4 checked:
   absent). Low priority — even if present in an intermediate
   version it was removed, and the thesis lacks it too."
5. "Do Eberhardt's adjacent papers (Pruning, arXiv:2412.04181;
   Liang-Eberhardt-Chen, PRX Quantum 6, 040330 (2025) planar
   open-boundary codes) contain distance lower-bound machinery for
   the closed-torus case? Only abstracts were checked; the pruning
   paper proves properties for hypergraph-product-like BB codes, a
   class that may exclude gross."
6. "Re-check shortly before any publication whether a post-2025-11
   preprint proves the SRB even-h cover conjecture (none found as of
   2026-06-09; the field moves fast and Track B's value collapses if
   someone proves h=2 transfer first)."

### Dead ends (researcher, verbatim)

- "'Eberhardt + Wein' BB-code collaboration: does not exist. Search
  returned only Eberhardt's actual collaborators (Breuckmann on
  balanced products, Steffan, Pereira, Liang/Chen). The lane
  prompt's 'with Wein?' is a phantom."
- "2024-2026 analytic LOWER bounds on BB code distance beyond
  Lin-Pryadko Statement 12 and SRB odd-h: none found. Queries:
  '\"bivariate bicycle\" code distance \"lower bound\" analytic
  proof 2025', '\"gross code\" [[144,12,12]] distance proof analytic
  theorem 2025 2026', '\"bivariate bicycle\" \"minimum distance\"
  \"we prove\" 2026 arXiv quantum code'. Everything that 'proves'
  distance facts for gross is about CIRCUIT distance (e.g.
  arXiv:2603.05481 proves no depth-7 circuit achieves d_circ = 12),
  taking code distance 12 as a computational given."
- "Trapezoid/coset combinatorial analytic distance lower bounds for
  twisted toric / quotient-lattice codes: nothing BB-applicable
  found. Query 'toric code distance proof coset trapezoid
  combinatorial \"twisted boundary\" OR \"quotient lattice\" lower
  bound stabilizer' returned only standard toric d=L pedagogy (REU
  notes), the EC Zoo D-dimensional twisted toric entry, and generic
  coset-weight definitions. The d=L-style argument has not been
  published for twisted-torus BB codes; Liang et al. 2503.03827 is
  the closest framework and stops at algorithmic computation."
- "The alleged 'Otjens 2025 abstract' quote 'no closed-form
  analytical formula': absent from arXiv:2502.17052 v1 abstract,
  absent from the full v4 text (zero grep hits for
  closed-form/analytical/analytic), absent from the Otjens BSc
  thesis text (pdftotext + grep). The quote as recorded in
  notes/T2.3_literature_survey.md item 1 of 'Conjectures' is
  unverifiable — treat as apocryphal."
- "Error Correction Zoo BB entry (errorcorrectionzoo.org/c/qcga):
  cites no analytic distance results or bounds for BB codes; only
  circuit-distance facts for [[144,12,12]]."
- "Post-SRB (after 2025-11) follow-up proving even-h cover-distance
  bounds: none found (query: '\"cover\" OR \"covering graph\"
  bivariate bicycle code distance bound \"even\" 2026 Smith theory
  chain complex' returns only SRB itself)."
- "Nature.com Methods section direct fetch: paywalled/redirect loop
  — use the PMC mirror (PMC10972743) or arXiv v2 PDF instead (both
  successfully fetched and consistent)."

---

## Implications for Phase 2

**Nothing is preempted.**

- Goal 1 (analytic proof of gross d = 12) is unclaimed: the source
  paper's certificate is ILP-only (L3-bravyi-mip-distance), the EC
  Zoo cites nothing analytic, and targeted searches for 2024–2026
  analytic lower bounds beyond LP Statement 12 / SRB odd-h came up
  empty (dead ends 2, 5).
- Track B's target theorem (even-h, h=2 cover transfer d ≤ d_h) is
  explicitly open per the SRB authors, with no proving follow-up
  among all six citing papers as of 2026-06-09
  (L3-srb-even-h-explicitly-open). Re-check before publication
  (open question 6) — this is the lane's biggest scoop-risk.

**Enabled.**

- **Track A/B (logical-space anatomy):** ES Theorem 2.3 applies
  verbatim to gross — no semisimplicity hypothesis — and gives the
  exact four-term decomposition of H any weight argument needs
  (L3-es-fundamental-exact-sequence). Computing the four terms for
  gross (open question 2) is unpublished and is the natural next
  concrete step; the literature marks gross non-pure but never
  quantifies the pure/obstruction split.
- **All tracks:** Bravyi Lemma 1's d_X = d_Z (L3-bravyi-lemma1-dxdz)
  halves the work — any Phase-2 theorem need only bound d_Z.
- **Track A (baseline secured):** Statement 12's c = |N| reading is
  confirmed from the paper's own terminology, and the verifier
  independently recomputed the gross numbers (c = 8,
  d_A^⊥ = d_B^⊥ = 12, bound 2), so the A0 baseline scoreboard rests
  on verified ground. Citation hygiene: pair Statement 12 with its
  parent, Kovalev–Pryadko PRA 88, 012311 (2013) Theorem 5.

**Killed / blocked (paths, not tracks).**

- The "borrow a published explicit logical basis for gross" shortcut
  is dead: ES's own Table 1 marks gross non-pure, non-principal,
  non-symmetric, and the principality guarantee needs ℓ, m odd
  (L3-es-gross-nonprincipal). Any by-hand minimum-weight argument
  must engage the non-pure obstruction term ((c)∩(d))/(cd) — the
  2-divisibility wall in yet another costume. No track dies, but
  Track A/B plans assuming a toric-style basis must be revised.
- The "someone must have done d=L for twisted tori" hope is dead
  (dead end 3): Liang et al. stop at algorithmic computation; the
  lower-bound generalization slot is open — which is also the
  opportunity.

**Action items emitted by this lane.**

1. Fix the HANDOFF §6j citation and
   `notes/T2.3_literature_survey.md` Conjectures item 1: replace
   "Otjens 2025" + apocryphal quote with Postema–Kokkelmans
   arXiv:2502.17052 and the verbatim "exact tradeoff ... remained
   unknown" sentence (L3-otjens-citation-correction).
2. Before Track A builds on the LP denominator: one cheap pass over
   the KP13 Theorem 5 proof to close open question 1's residue.
3. Before Track B write-up / any publication: re-run the
   even-h-preemption search (open question 6).
