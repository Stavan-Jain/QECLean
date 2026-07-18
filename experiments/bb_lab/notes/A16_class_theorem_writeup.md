# A16 — The class small-cycle theorem (statement and proof of record)

> **STATUS: UNCONDITIONAL.** Consolidates `A5_goal2_log.md` Entries
> 8–13 into one document; the three polish items flagged at Entry 11.4
> (P1 general embeddings, P2 the 2-torsion-u sub-case, P3 the
> relation-type table) are discharged here (§5.3, §6.3), so the
> theorem carries no caveats. Every finite verification cited below is
> *confirmation of a hand argument, never an ingredient* (A_HANDOFF
> §1); the two fixed censuses that ARE load-bearing (§6.3: Z₅² and
> Z₁₅², both complete by torsion factoring) are instance-independent,
> checked once, and of d₃-dictionary epistemic grade — surveyable in
> principle, machine-checked in `a16_polish_checks.py`.

---

## 0. Results

**Theorem (class small cycles).** Let G = Z_ℓ × Z_m with
4 ∤ ℓ and 4 ∤ m (equivalently: 2-part of G ∈ {1, Z₂, Z₂²}), and let
A, B ∈ F₂[G] with |A| = |B| = 3 satisfy

  (D1) dA and dB are multiplicity-free (Sidon; each nonzero
       difference from exactly one ordered pair),
  (D2) dA ∩ dB = ∅,
  (iii) the mirrored projection pattern: A is monomial in exactly one
       coordinate axis under the parity-collapsing projections
       π_x, π_y, B in exactly the other,
  (a)  Ann(A) ≠ 0 ≠ Ann(B), and the one-sided floor holds:
       μ(Ann A), μ(Ann B) ≥ 6.

Then the BB code (G, A, B) has **no nonzero 1-cycle of weight ≤ 5**:
d ≥ 6, μ_Z = μ_X ≥ 6, and every free-Z₂ cover with the same
polynomials has d ≥ 6 (Theorem-B transfer, A4 §5).

**Hypothesis accounting.** The full floor μ ≥ 6 of (a) is consumed
only by the one-sided splits (§3). The two-sided analysis (§§5–6)
uses only D1 ∧ D2 ∧ (iii) ∧ Ann ≠ 0 ∧ (no period) ∧ 4∤ℓ ∧ 4∤m — and
"no period" is itself a consequence of D1 at weight 3 (§4).

**Corollaries.**
1. The 58-member corpus class (A5 Entries 1–5) is certified at d ≥ 6
   analytically, as is every member of the 111,840-member hunt
   battery, and every future instance passing the certifier gates
   (`a15_class_certify.py`) — with no per-instance census of any
   kind.
2. bb_72 (= the gross base), bb_108, bb_90 are instances (their
   original per-instance proofs, A4 §4 / A5 E2 / A5 E4, are
   subsumed).
3. Z₆×Z₁₄ [[168,12,6]] (A = 1+y+x³y³, B = 1+x+x²y⁷) is an instance —
   the first with odd part off Z₃² (components F₂·F₄·F₈²·F₆₄²) — and
   its two n = 336 free-Z₂ covers have d ≥ 6.
4. On instances where a weight-6 annihilator element exists (all
   corpus d = 6 members), d = 6 exactly, with the element as witness.

**What the theorem does not give** (§8): anything past d ≥ 6; any
verdict on non-mirrored pairs (the Z₃×Z₅ d = 4 family and the
Frobenius squares live exactly there); any verdict on 4 | ℓ frames
(gross-as-base, bb_288-base — the Z₄ wall, A15 track T3c).

---

## 1. Setup and conventions

Chain conventions, PAR, and difference sets as in A4 §1. For a 3-set
S we write its six ordered differences dS = {±p, ±q, ±r} with
positive representatives p = S₁−S₂, q = S₂−S₃, r = p + q = S₁−S₃
(any labeling; D1 says these are six distinct nonzero elements).
Two immediate D1 consequences used throughout:

* **no 2-torsion differences**: 2v = 0 with v ∈ dS would make v = −v
  arise from two ordered pairs;
* **no periods**: S + g = S (g ≠ 0) forces S to be an ⟨g⟩-coset with
  ord(g) = 3 and dS = {±g} with multiplicity 3.

Under (iii), up to the x↔y relabeling we take A monomial-in-x and B
monomial-in-y, and each has exactly two shapes:

* **A1** (spike + pair): A = {(α₁,β₁), (α₂,β₂), (α₂,β₃)}, u :=
  α₁−α₂ ≠ 0, w := β₂−β₃ ≠ 0, s := β₁−β₂, s′ := β₁−β₃ = s+w with
  s, s′ ≠ 0 (a zero would collapse π_y to a singleton, making A
  monomial in both axes). Then
  dA = {±(0,w), ±(u,s), ±(u,s′)}: x-profile {0², u², (−u)²}, **no
  y = 0 elements**.
* **A2** (vertical): all three x-coordinates equal;
  dA ⊂ {x = 0} with three distinct nonzero y-differences.

Mirror shapes **B1** (y-pair (p,0)-difference + slants (q,h),
(p+q,h), all x-parts nonzero, h ≠ 0) and **B2** (horizontal;
dB ⊂ {y = 0}, x-parts nonzero).

A (2,2)-match is A·{0,δ_L} = t + B·{0,δ_R} with δ_L, δ_R ≠ 0; we
write σ_L = A ⊕ (A+δ_L), σ_R likewise; |σ_L| = 6 − 2·[δ_L ∈ dA]·2
∈ {6, 4} (D1; size 2 needs a 2-torsion δ_L ∈ dA — vacuous). A
(1,3)-candidate is B·T = t + A for a 3-set T with |B·T| = 3, which
by D1 inclusion–exclusion forces T to be a dB-triangle
({0, a, b} with a, b, b−a ∈ dB, up to translation; A4 §4.3).

d(S) denotes the multiset of ordered differences of a set S;
matches force d(σ_L) = d(σ_R) and d(B·T) = dA (translation
invariance).

---

## 2. Proof map

| split (weight ≤ 5) | mechanism | proved in |
|---|---|---|
| mixed parity | PAR (augmentation) | A4 §4 (generic) |
| (k,0), (0,k) | one-sided floor, hypothesis (a) | §3 |
| (1,1) | D2 | §4 |
| (1,3), (3,1) | chirality identities + Frobenius exclusion + O3/PROG | §5 |
| (2,2) size 6 | atoms → translate rigidity → S2 funnel | §6.1–6.2 |
| (2,2) size 4 | exact rigidity → matching dichotomy → family collapse | §6.3 |
| (2,2) size 2 | vacuous under D1 | §1 |

---

## 3. The one-sided floor (hypothesis (a) and its engines)

The floor μ(Ann A), μ(Ann B) ≥ 6 is hypothesis (a); the theorem
consumes it as stated. The per-frame analytic engines that discharge
it (and make the certifier's FLR-route analytic rather than merely
finite) are:

**Lemma 3.1 (field-generic Z₂²-engine; A5 E8.1b).** Let K be any
field of characteristic 2, R = K[Z₂²] = K[U,V]/(U²,V²), and
D = aU + bV + cUV with (a,b) ≠ 0. Then x·D = x₀D + (x₁b + x₂a)UV,
so D² = 0 and Ann(D) = K·(aU+bV) ⊕ K·UV = (D); and a nonzero element
α(aU+bV) + β′UV has slot vector (α(a+b)+β′, αa+β′, αb+β′, β′), which
has ≥ 3 nonzero slots for every (α, β′) ≠ 0 **iff {0, a, b, a+b} are
pairwise distinct iff D's own four slot values are pairwise
distinct**. ∎ (Swept exhaustively over F₄/F₈/F₁₆/F₆₄,
`a15_field_generic_engine_check.py` E1/E2/E2′.)

**Corollary 3.2 (widened engine floor).** If G has 2-part Z₂², |A|
odd, and every CRT component of Â is a unit or a radical satisfying
the distinctness condition (no zero components), then every nonzero
z ∈ Ann(A) has ≥ 3 nonzero layers, each of even weight (Â₀ is a
unit), so μ(Ann A) ≥ 6. ∎ — This is A4 §4.1 with the F₄-specific
hypothesis removed; no |F₄ˣ| = 3 input anywhere. It covers bb_72 and
Z₆×Z₁₄ (heterogeneous F₈/F₆₄ components).

Z₂-frames: Ann(A) = (1+s) ⊗ I(W_A) with floor 2·d_H(W) (A5 E2,
bb_108); semisimple frames: Ann(A) = I(V_A) with floor d_H(V)
(A5 E4, bb_90). What remains F₄-locked is only the VALUE-rigidity
layer (co-point C-ratios, Prop-10 classification, the gross Part-II
machinery) — supports port, classifications don't.

---

## 4. Parity, (1,1), and no-period

PAR kills all splits with |u_L| ≢ |u_R| (mod 2) since ε(A) = ε(B)
= 1. The (1,1) split A·g = B·r forces dA = dB, contradicting D2 with
dA ≠ ∅. Periods are excluded by D1 (§1), which retires the standing
"no-period" side condition. ∎

---

## 5. The (1,3)/(3,1) kill

### 5.1 Chirality structure (Lemma I, E11.1)

Char-2 polynomial identities: **B·B = B²** (Frobenius squaring —
three distinct cells by no-2-torsion) and **B·(−B) = {0} ∪ dB**
(weight 7 under D1). The two generically-existing dB-triangle
translate classes are T ~ B − B_i (same-chirality) and T ~ B_i − B
(reflection), with images

    B·(B − B_i) = B² − B_i   (weight 3, the Frobenius square),
    B·(B_i − B) = ({0} ∪ dB) + B_i   (weight 7 — never a candidate).

∎ (24,000/24,000 image identities verified, `a15_e11_iv_kill.py` X1;
A4 §4.3's T₊/T₋ are these two classes, its "constant-y image" is
2B + (0,3) verbatim.)

### 5.2 The Frobenius exclusion (Theorem J, E11.2)

**Under D1 ∧ (iii) alone**: no weight-3 same-chirality image is a
translate of the partner, in either direction. *Proof.* A match
forces dA = d(B²) = 2·dB. B1-shape dB contains (p, 0) with 2p ≠ 0
(no-2-torsion), so 2·dB contains the nonzero y = 0 element (2p, 0);
dA (A1 or A2) has no y = 0 elements. Mirror: dB = 2·dA needs
(0, 2w) ∈ dB — impossible for B1 (x-parts nonzero) and for B2
(forces 2w = 0). ∎

This subsumes the `is_frobenius_related` gate on class members and
closes the extensibility-§6 arc there: A ~ B² and all its spread
variants (the Z₈² hole) are non-mirrored.

### 5.3 Coincidence classes: the complete table (Lemma K′; P3 + P2)

**Lemma 5.3.1 (completeness).** Under D1, every dB-triangle
translate class beyond the two chirality classes is one of:

* **O3**: T = a coset of ⟨s⟩ for an order-3 element s ∈ dB (the
  relation 2s = −s ∈ dB is free by symmetry);
* **PROG**: T ~ {0, c, 2c} where dB = ±{c, 2c, 3c} (B is a translate
  of {0, c, 3c}-type "progression" set).

*Proof.* A triangle is an ordered pair (a, b) ∈ dB² with b − a ∈ dB.
Of the 30 ordered pairs, 12 satisfy b − a ∈ dB identically (the two
chirality classes). The remaining 18 fall into four relation types:
(s, −s)-pairs need 2s ∈ dB; {p,q}-mixed need q − p ∈ dB; {p,r}-mixed
need 2p + q ∈ dB; {q,r}-mixed need p + 2q ∈ dB. Resolving each
against dB = {±p, ±q, ±r} and discarding the D1-dead options
(2-torsion, p = q, degenerate) leaves exactly: 3s = 0 (→ O3), and
the linear relations q = 2p, p = 2q, q = −2p (|dB| < 6, dead),
q = −3p, 3p + 2q = 0, and their p↔q mirrors — **each of which forces
dB = ±{c, 2c, 3c}** (e.g. 3p + 2q = 0 gives p = −2r, q = 3r with
c = r). Under D1 a PROG dB carries no further coincidences (4c ∈ dB
forces 5c = 0 or 3c = 0 or 2-torsion, each degenerating |dB|), and
its extra translate class is exactly the AP {0, c, 2c}. ∎
(Exhaustive: 7,674 extra classes over 23,028 D1-sets across ~40
ambient groups, all O3 or PROG — `a16_polish_checks.py` Y1.)

**Lemma 5.3.2 (kills).** (O3) The image of an O3 triangle is a
single ⟨s⟩-coset line (the two B-cells differing by s ∈ dB
contribute the same coset twice and cancel), whose difference
multiset is {±s} with multiplicity 3; a translate of A would violate
D1. (PROG) The image of the AP-triangle is
B·{0, c, 2c} = {0, 4c, 5c} + t′ (direct expansion; weight 3 since
D1 kills 4c = 0, 5c = 0, 5c = 4c), and
d({0, 4c, 5c}) ∋ ±c ∈ dB — so a translate of A would put
c ∈ dA ∩ dB, violating **D2**. ∎ (Y1/Y2: 4,536 O3 images all
AP-lines; 3,138 PROG images all carry c ∈ d(σ) ∩ ±dB.)

Both kills need only D1 ∧ D2 — no coordinates, no frame condition.
This discharges P2 (the old coordinate route through the doubling
family is obsolete) and P3 (the table is complete). With §5.1–5.2,
**no weight-3 triangle image is ever a translate of the partner**,
killing (1,3) and (3,1). ∎

---

## 6. The (2,2) kill

### 6.1 Multiset formulas (E9)

For δ ∉ dA (size 6): d(σ_L) = 2·dA ⊎ (dA + δ) ⊎ (dA − δ) ⊎ {δ}³ ⊎
{−δ}³ (with the two atom piles merging to {δ}⁶ when 2δ = 0). For
δ ∈ dA (size 4), with (a_i, a_j) the Sidon-unique pair a_i − a_j =
δ and e := a_j − a_k: d(σ_L) = ±{δ, 2δ, e, e−δ, e+δ, e+2δ}.
(Formula-validated on 86,400+ rows; `a15_e9_residue_lemma_checks.py`
V1.)

### 6.2 Size 6 (E9 Lemma A / Theorem D; E10 Theorem G)

**Atoms (Lemma A).** mult_{d(σ_L)}(δ_L) = 3 + [2δ_L ∈ dA] +
3·[2δ_L = 0] ≥ 3, while mult_{d(σ_R)}(δ_L) ≤ 2 unless δ_L = ±δ_R or
δ_L ∈ dB. With the mirror count at δ_R: any match has **δ_L = ±δ_R,
or (δ_L ∈ dB ∧ δ_R ∈ dA)**. (Branch tally over 1.77M rows: atoms
kill 94.7% outright.)

**Branch 2a (Theorem D).** For δ := δ_L = ±δ_R (wlog =, since
σ_R(−δ) is a translate of σ_R(δ)): counting d(σ_L) = d(σ_R) over dA
forces dB = dA + δ = dA − δ. Under (iii) this is impossible on
floor-bearing frames: dA's x-profile is {0², u², (−u)²} (A1) or
{0⁶} (A2), while a translate-invariant profile comparison shows the
B-side x-profile {±p, ±q, ±(p+q)} attains the 3-values-×-2 shape
only when an order-4 x-element exists (**profile-shape lemma**,
verified: the shape occurs ⟺ 4 | ℓ) and never attains 1-value-×-6.
4 ∤ ℓ kills. ∎ (Corpus-wide: no member has dB in dA's translate
class at all — V3, 44,064/44,064.)

**Branch 2b (Theorem G, the S2 funnel).** For δ_L ∈ dB ∧ δ_R ∈ dA:
the Σ-count over dA (the S2 atom terms contribute +6) forces
|dA ∩ (dB ± δ_R)| ≥ 6; the projection weight lemma (E7.3, both
axes) pins b(x) = AP(δ_Rx) with δ_Rx = ±u, making x(dB) =
{±u², ±2u}; the x-fiber caps then force equality, pinning
{δ_Ry, δ_Ry ∓ h} = {±w}, hence h = ±2w and {s, s′} = {w, 2w} (up to
mirror), i.e. a(y) = AP(w). The pinning also demands a(y) =
AP(±h) = AP(2w); a 3-set that is an AP for both w and 2w forces
3w = 0, upon which dA's slant set becomes all four (±u, ±w) — and dB
always carries a slant with x-part ±u and y-part ±h = ∓w, which lies
in dA: **dA ∩ dB ≠ ∅, contradicting D2**. Sub-branches: 3u = 0
reruns the count with per-fiber caps 2 and lands in the same clash;
b-side orbit-pair dies by the fiber count (≤ 4 < 6); a-side
orbit-pair forces 4w = 0 ⟹ 2w = 0, D1-dead. ∎ (W3: 0 funnel-
condition rows among all pinned S2 rows; all AP/AP.)

### 6.3 Size 4 (E10 Lemmas E/F/H; F-tri-5 discharged here — P1)

**Exact rigidity (Lemma E).** A size-4 match forces
dB = {±2δ, ±(e−δ), ±(e+2δ)} and dA = {±2δ′, ±(f−δ′), ±(f+2δ′)},
all six values distinct on each side (Σ-count over dA/dB with
per-element equality). ∎

**Matching dichotomy (Lemma F).** σ_L's pair decomposition (gaps
{δ, 2δ}) and σ_R's ({δ′, 2δ′}) are matchings of one 4-set, so one
of: *aligned* (δ = ±δ′ — D2-dead); *crossed* (δ = ±2δ′ ∧ 2δ = ∓δ′ ⟹
3δ′ = 0, whence δ = ∓δ′, D2-dead — or 5δ′ = 0, the **pentagonal**
family); *M₂* ({±e, ±(e+δ)} = {±δ′, ±2δ′} ⟹ some dA element ∈ ±dB,
D2-dead); *M₃* (the **triangular** families, resolved by the closure
constraint that dB must itself be a 3-set difference set). ∎

**Pentagonal (Lemma H).** The crossed-5-torsion relations under
(iii) confine all data to the 5-torsion subgroup: δ′ ∈ dB has
nonzero x-part (B1) — and B2, A2, and mixed shape cases die
immediately on zero-coordinate grounds — so 5δ′ = 0 puts 5-torsion
in both axes; the Lemma-E memberships then walk e and f into the
same subgroup. Hence dA ⊂ T₅ := (5-torsion of G) and A lies in a
single T₅-coset. **In char 2 there are no vanishing weight-3 sums of
5th roots of unity** ((1+ζ)⁵ = ζ + ζ⁴ ≠ 1 for ζ ∈ μ₅ ∖ {1}), so
every CRT component of Â is a unit and Ann(A) = 0, violating (a). ∎
Since any embedding's 5-torsion factors through Z₅×Z₅, the Z₅²
census is **embedding-complete**: the family is genuinely live at
the difference-set level (960 D1∧D2 σ-shape matches on Z₅², all
realizable) and every realization has all-unit components
(276/276 — `a15_e10_size4_s2_kills.py` W4/W4b).

**Triangular families (Prop. 6.3.1; discharges P1).** The M₃
closure options force one of:

* **T₃-confined** (3δ = 3τ = 0): dA ⊎ dB would need 12 distinct
  nonzero 3-torsion elements, but |Z₃² ∖ 0| = 8. Dead (counting).
* **T9** (τ = 3δ, 9δ = 0): dB acquires 2δ twice. Dead (D1).
* **15-torsion cyclic** (τ = 5δ, 15δ = 0): dA = ±{δ, 5δ, 6δ} forces
  dB = ±{2δ, 4δ, 7δ}, which is not a 3-set difference set: signed
  closure ±a ± b = ±c over {2, 4, 7} has no integer solution besides
  the duplicate-producing one, and modular coincidences require
  n ≤ 17, each dying by D1/D2/duplicate (finite table). Dead.
* **F-tri-5** (ord δ = 5, ord τ = 3; dA = {±δ, ±τ, ±(τ+δ)},
  dB = {±2δ, ±(τ−δ), ±(τ+2δ)} — live at the difference-set level:
  all 192 Z₁₅² data pass D1 ∧ D2): under (iii), assign dA's three
  positive representatives to the A-shape slots. If the x = 0 slot
  is δ: dB ∋ 2δ = (0, 2δ_y) with x = 0 — impossible for B1, and B2
  forces 2δ_y = 0 ⟹ δ = 0. If it is τ: the slants give 5u = 5s = 0,
  and dB's y-parts {±2s, ±(w−s), ±(w+2s)} can never produce B1's
  zero-pair (each vanishing condition forces an element of coprime
  3·5-torsion to vanish) nor B2's all-zero row. If it is τ + δ: the
  two slants must carry x-parts ±u with 3u = 0 = 5u ⟹ u = 0. All
  dead; A2 variants die inside the same case split (dA ⊂ {x = 0}
  forces the partner data onto a zero coordinate). ∎ Any embedding
  factors through the 15-torsion subgroup ⊆ Z₁₅×Z₁₅, so the Z₁₅²
  sweep of all 192 (δ, τ) data — none admitting an (iii)-mirrored
  shape pair — is **embedding-complete** (`a16_polish_checks.py`
  Y3).

Size-4 matches are therefore impossible; with §6.2 and the size-2
vacuity, **the (2,2) split is dead**. ∎

---

## 7. Assembly

Let u = (u_L, u_R) be a nonzero cycle of weight ≤ 5. PAR leaves the
splits (k,0), (0,k), (1,1), (1,3), (3,1), (2,2). One-sided splits
die by hypothesis (a) (§3); (1,1) by D2 (§4); (1,3)/(3,1) by §5;
(2,2) by §6. Hence no such cycle exists; d ≥ 6 and μ_Z ≥ 6 follow,
d_X = d_Z by the inversion duality (A4 Lemma 2.1), and the
Theorem-B transfer extends the floor to every free-Z₂ cover. **∎**

---

## 8. Scope, and what lies outside

* **Non-mirrored pairs**: the Z₃×Z₅ d = 4 family (A5 E6) and the
  Frobenius squares are (iii)-violating; the theorem says nothing
  about them, and they are genuine d < 6 codes — (iii) is
  load-bearing, not cosmetic.
* **Deep frames** (4 | ℓ or 4 | m): outside; the Z₄ chain-ring
  engine is A15 track T3c.
* **d > 6**: the class theorem is a floor at 2w = 6; corpus members
  with true d ∈ {8, 10} need the depth program (A15 T5) or covers.
* **k, exact d**: k > 0 is not implied (Ann ≠ 0 is weaker); exact
  d = 6 needs a weight-6 witness per instance.

## Appendix A. Verification map (confirmation only)

| claim | script / check |
|---|---|
| Lemma 3.1 sweeps (E1/E2/E2′, 4 fields) + instance checks | `a15_field_generic_engine_check.py` |
| §6.1 formulas; atoms; branch tallies; 2a translate check; profile-shape lemma | `a15_e9_residue_lemma_checks.py` V1–V6 |
| Theorem G pinning + funnel; Lemmas E/F; pentagonal census + μ₅; ambient sweeps | `a15_e10_size4_s2_kills.py` W1–W5b |
| Lemma I identities; Theorem J; coincidence classes on the battery | `a15_e11_iv_kill.py` X1–X3 |
| Lemma 5.3.1/5.3.2 completeness + kills; F-tri-5 over Z₁₅² | `a16_polish_checks.py` Y1–Y3 |
| the hunt batteries (111,840 members, 8 frames, 0 violations) | `a15_t11_residue_hunt.py` + `data/a15/` |
| per-instance certificates | `a15_class_certify.py` |

## Appendix B. The two load-bearing fixed censuses

* **Z₅² (pentagonal)**: all 276 weight-3 polynomials on Z₅×Z₅ have
  all-unit CRT components (no vanishing weight-3 sums of 5th roots —
  the hand proof is the (1+ζ)⁵ computation; the census is its
  exhaustive confirmation). Complete for all frames by 5-torsion
  factoring.
* **Z₁₅² (F-tri-5)**: all 192 (δ, τ) ∈ ord-5 × ord-3 data satisfy
  D1 ∧ D2, and none admits an (iii)-mirrored shape assignment (the
  §6.3 case analysis is the hand proof). Complete for all frames by
  15-torsion factoring.
