# A fully analytic distance bound for the gross code: d ≥ 6

> **STATUS: REVIEW-CLEARED.** The Entry-15 adversarial re-review (fresh
> session; every machine check re-implemented independently —
> `a3_adv15_recheck.py`, 49/49 — and every prose argument re-derived by
> hand) found **all links HOLD**; its two presentational notes are folded
> in below (§3 d₃ remark; §6.3 (1,1,1,1) bullet). Every numerical
> statement in this note is *confirmation* of a hand proof, never an
> ingredient; the verification scripts are listed in Appendix A. Source of
> record for the proofs: `notes/A3_track1p1_log.md`, Entries 5 and 10–15.
> The post-review goal-1 closure (Entries 16–26: (R), the flux
> characterization, the (M-im) confined-floor program — **d(gross) = 12**,
> review-cleared by Entry 27 at the grade "analytic spine + two
> machine-certified residues") is NOT yet part of this note; the A4
> extension covering it is the open write-up debt (Entry 27).

---

## 0. Results

Throughout, "analytic" means: no SAT, no kernel-`decide`, no exhaustive
enumeration is load-bearing; every finite case split is small enough to
survey by hand (the largest below has nine cases).

**Theorem A (small cycles).** The bivariate-bicycle code
`base = [[72,12,6]]` (group Z₆×Z₆, A = x³+y+y², B = y³+x+x²) has no
nonzero X-type or Z-type 1-cycle of weight ≤ 5. In particular
d(base) ≥ 6, and the minimum nonzero Z-stabilizer weight μ_Z and
X-stabilizer weight μ_X are ≥ 6.

**Corollary A′.** d(base) = 6, exhibited analytically: the weight-6
element z\* = 1 + y + y² + y⁵ + x³ + x³y⁴ ∈ Ann(A) gives the Z-logical
(z\*, 0) (§4.6).

**Theorem B (gross, minimal form).** The gross code `[[144,12,12]]`
(group Z₁₂×Z₆, same A, B — the free-Z₂ double cover of the base in the
x-direction) satisfies **d(gross) ≥ 6**. This triples the best published
analytic floor, d ≥ 2 (Lin–Pryadko Statement 12 with degeneracy c = 8:
⌈12/8⌉ = 2).

**Theorem C (dangerous sector, tight).** Every nontrivial Z-logical of
gross whose class lies in ker(pr_*: H₁(gross) → H₁(base)) has weight
≥ 12 = 2·d(base); weight 12 is attained. (The factor-2 lemma **(M)**, with
no hypothesis.)

To our knowledge (four-lane literature sweep, `A1_literature_*.md`), these
are the first analytic distance results matching the true parameters for
codes in the Bravyi–Cross–Gambetta–Maslov–Rall–Yoder BB family; the
previously available analytic route (Lin–Pryadko) is provably capped at 2
on gross by an arithmetic wall (`A2_scouting.md`).

---

## 1. Setup and conventions

A BB code over an abelian group G with polynomials A, B ∈ F₂[G] has
qubits L ⊔ R, each block a copy of F₂[G], and check matrices
H_X = (M_A | M_B), H_Z = (M_Bᵀ | M_Aᵀ), where M_P is the group-algebra
multiplication operator. We use the chain complex
C₂ →∂₂ C₁ →∂₁ C₀ with ∂₁ = H_X and ∂₂ = H_Zᵀ, so that for z ∈ F₂[G]

    ∂₂ z = (B·z, A·z)        (left block B·z, right block A·z),

Z-stabilizers are im ∂₂, Z-logical operators are ker ∂₁ ∖ im ∂₂, and
d_Z = min weight over nontrivial classes of H₁ = ker ∂₁ / im ∂₂. A
1-chain is written u = (u_L, u_R); the cycle condition is
A·u_L = B·u_R (=: σ, "the matched syndrome").

The augmentation ε: F₂[G] → F₂ (sum of coefficients) is a ring
homomorphism with ε(A) = ε(B) = 1, and weight ≡ augmentation (mod 2);
hence

    |A·f| ≡ |f|  and  |B·f| ≡ |f|   (mod 2).                    (PAR)

**Difference sets.** dA = {g·h⁻¹ : g ≠ h ∈ supp A} =
{(0,±1), (3,±1), (3,±2)} and dB = {(±1,0), (±1,3), (±2,3)} (coordinates
(x,y)). Both are multiplicity-free (each element arises from exactly one
ordered pair), they are disjoint, and they are disjoint **in both
coordinates**: x(dA) ⊆ {0,3}, x(dB) ⊆ {1,2,4,5}; y(dA) ⊆ {1,2,4,5},
y(dB) ⊆ {0,3}. Consequently two columns of M_A (or two of M_B) intersect
in ≤ 1 cell ("ov ≤ 1"), with equality exactly on dA (resp. dB).

---

## 2. The X–Z inversion duality

**Lemma 2.1.** For any BB code (any abelian G, any A, B), the map
Φ(w_L, w_R) := (ι(w_R), ι(w_L)), with ι the inversion g ↦ g⁻¹ extended
linearly, is a weight-preserving bijection carrying ker H_Z onto
ker H_X and the X-stabilizer space im H_Xᵀ onto the Z-stabilizer space
im H_Zᵀ. Hence **d_X = d_Z**.

*Proof.* ι is an algebra automorphism of F₂[G] (G abelian), and
M_Pᵀ = M_{ι(P)}. A vector (w_L, w_R) ∈ ker H_Z satisfies
ι(B)·w_L + ι(A)·w_R = 0; applying ι gives B·ι(w_L) + A·ι(w_R) = 0, i.e.
Φ(w) ∈ ker H_X. The row of H_X at check g is (ι(A)·δ_g, ι(B)·δ_g), and
Φ of it is (B·δ_{g⁻¹}, A·δ_{g⁻¹}) = ∂₂δ_{g⁻¹}; spans map onto spans, and
Φ² = id. ∎

This applies to the base and to gross (inversion needs no symmetry
between the x- and y-directions). All statements below are therefore
proved on the Z side only.

---

## 3. The CRT layer frame for the base

Z₆ = Z₂ × Z₃ via x = s_x t_x (s_x = x³, t_x = x⁴), same in y. Cells of
Z₆² are pairs (s, t), s ∈ Z₂² ("layers"), t ∈ Z₃². Over F₄ the 3-part
characters fall into five Frobenius orbits, giving

    R = F₂[Z₆²] ≅ R₀ × R₁ × R₂ × R₃ × R₄,
    R₀ = F₂[Z₂²],  R_j = F₄[Z₂²] (j = 1..4),

with component characters (as functions of t = (t_x, t_y))

    ψ₁ = ω^{t_y},  ψ₂ = ω^{t_x},  ψ₃ = ω^{t_x+t_y},  ψ₄ = ω^{t_x+2t_y};
    relations  ψ₃ = ψ₁ψ₂,  ψ₄ = ψ₁ψ₃;
    kernels    ker ψ₁ = span(1,0),  ker ψ₂ = span(0,1),
               ker ψ₃ = span(1,2),  ker ψ₄ = span(1,1).

Writing u = 1+s_x, v = 1+s_y (u² = v² = 0) and (ξ_j, η_j) =
(ψ_j(t_x-unit), ψ_j(t_y-unit)):

    Â_j = (1+η+η²) + u + ηv,      B̂_j = (1+ξ+ξ²) + v + ξu.

| j | (ξ,η) | Â_j | B̂_j |
|---|-------|------|------|
| 0 | (1,1) | 1+u+v (unit) | 1+u+v (unit) |
| 1 | (1,ω) | u+ωv (radical) | 1+u+v (unit) |
| 2 | (ω,1) | 1+u+v (unit) | ωu+v (radical) |
| 3 | (ω,ω) | u+ωv | ωu+v |
| 4 | (ω,ω²)| u+ω²v | ωu+v = ω·Â₄ |

For f ∈ F₂[Z₆²], the layer s of block f is its restriction f_s ∈ F₂[Z₃²],
and the component transform is the vector V_j(f) ∈ F₄^{Z₂²},
V_j(f)[s] = Σ_{t ∈ f_s} ψ_j(t); multiplicativity reads
V_j(A·z) = Â_j·ẑ_j (product in F₄[Z₂²]). V₀[s] is the parity of layer s.

**Engine lemma.** Let D be any of the six radical multipliers. Then
(i) Ann(D) = (D) = {αD + β·uv : α, β ∈ F₄}, a 2-dimensional ideal
(D² = 0, D·uv = 0, dimension count);
(ii) the value vector of D over the layers (1, s_x, s_y, s_xs_y) is
(1+η, 1, η, 0) — three pairwise-distinct nonzero values and one zero — so
a nonzero ideal element αD + β·uv has support either **full** (α = 0:
a constant vector β·1⃗, since uv = 1+s_x+s_y+s_xs_y has all-ones
coefficient vector) or a **co-point** Z₂²∖{s₄} (α ≠ 0, s₄ the unique
layer where αD = β), with value vector α·C(s₄), C(s₄) := D + D[s₄]·1⃗,
rigid up to the scalar.
(iii) **C-table.** With η² = 1+η (η ∈ {ω, ω²}): C_j([1]) = (0, η_j, 1,
η_j²) over (1, s_x, s_y, s_xs_y), and in general C_j(s₄)[s] = η_j^{e(s₄,s)}
with exponents e **independent of j**. Hence every cross-layer C-ratio is
a power of η_j with a j-independent exponent; since ψ₄ = ψ₁ψ₃ and
η₄ = η₁η₃, any ratio system "ψ_j(τ) = C-ratio_j (j ∈ {1,3,4})" is
automatically consistent and pins τ to a multiple of (0,1) (ψ₃, ψ₄
separate Z₃²).

**Layer dictionary d₃.** For nonzero f ∈ F₂[Z₃²] with Fourier support
inside orbit set W, the minimum weight depends only on
(n, ε) = (#nontrivial orbits in W, trivial ∈ W):

    (0,T)→9, (1,F)→6, (1,T)→3, (2,F)→4, (2,T)→3, (3,·)→2, (4,F)→2, (4,T)→1.

(Hand proof of each row: `A3` Entry 10, "Dictionary lemma". **Convention,
per the Entry-15 review:** d₃(W) is the minimum weight over nonzero f with
Fourier support *contained in* W — not exactly W; the two differ (e.g. the
exact-support minimum at (2,T) is 5, while d₃(2,T) = 3, attained by a line
whose support is a proper subset). Every use below is of the safe form
"supp ⊆ W ⟹ |f| ≥ d₃(W)". Below we use only: weight-1 layers are δ-points
with full Fourier support and values ψ_j(t); d₃({1}) = d₃({3}) = 6;
d₃({1,3}) = 4.)

---

## 4. Theorem A: no small cycles

Let u = (u_L, u_R) be a nonzero cycle, A·u_L = B·u_R = σ, with
|u| = |u_L| + |u_R| ≤ 5. By (PAR), |u_L| ≡ |u_R| (mod 2), which kills the
splits (1,2), (2,1), (2,3), (3,2), (1,4), (4,1). The remaining splits:

### 4.1 One-sided: (k,0) and (0,k), k ≤ 5

Here u_L ∈ Ann(A) (resp. u_R ∈ Ann(B)) is nonzero. By the engine, the
unit components force ẑ₀ = ẑ₂ = 0 (Ann side A; mirror for B), and the
radical components lie in the self-annihilating ideals; a nonzero element
therefore has some V_j ≠ 0 with co-point-or-full support, i.e. **≥ 3
nonzero layers**, while ẑ₀ = 0 makes every layer weight even. Hence
**min weight of Ann(A), Ann(B) ≥ 6** — kills all one-sided splits. ∎

### 4.2 Split (1,1)

A·g = B·r forces two translate 3-sets to coincide, hence their difference
sets: dA = dB. They are disjoint and nonempty. ∎

### 4.3 Splits (1,3) and (3,1)

|A·g| = 3 exactly, so |B·z| = 3 is required for the 3-set z = supp u_R.
Inclusion–exclusion with ov ≤ 1: |B·z| = 9 − 2p + 4T, where p ≤ 3 is the
number of overlapping column pairs and T ≤ 1 the common triple cells; the
only solution of 9 − 2p + 4T = 3 is (p,T) = (3,0): **z is a dB-triangle
{z₀, z₀+a, z₀+b} with a, b, b−a ∈ dB and the three overlap cells
distinct.** Enumerating a, b ∈ dB with b−a ∈ dB (six elements, a dozen
candidate pairs) yields exactly one class up to translation and
reflection, represented by

    T₊ = {0, (1,0), (2,3)}:  the three overlaps coincide, |B·z| = 7;  ✗
    T₋ = {0, (1,0), (5,3)}:  |B·z| = 3 with B·z a translate of
                              y³(1 + x² + x⁴) — constant y-coordinate.

But A·g has y-coordinates g_y + {0,1,2}, pairwise distinct: σ cannot be
constant-y. ✗ The mirror split (3,1) is identical with dA-triangles
(constant-x images vs. the three distinct x-coordinates of B·r). ∎

### 4.4 Split (2,2)

u_L = {ℓ₁, ℓ₂}, u_R = {r₁, r₂}. Write π_x, π_y for the coordinate
projections F₂[Z₆²] → F₂[Z₆] (sum over the other coordinate) — ring
homomorphisms with

    π_y(A) = 1+y+y²,  π_y(B) = y³,  π_x(A) = x³,  π_x(B) = 1+x+x².

|σ| ∈ {4, 6} on each side (ov ≤ 1), and the sides must agree.

**|σ| = 4** — both pairs overlapping: ℓ₁−ℓ₂ ∈ dA, r₁−r₂ ∈ dB.
Matching |π_y(σ)|: the left side is (1+y+y²)(δ + δ′) with y-gap 1 or 2,
of weight 2 resp. 4; the right side is y³(δ + δ′) with y-gap 0 or 3, of
weight 0 resp. 2. The only match is weight 2: **ℓ-diff has y-gap 1**
(i.e. (0,±1) or (3,±1)) and **r-diff has y-gap 3**.
- ℓ-diff = (0,±1): π_x(u_L) = 0, so (1+x+x²)·π_x(u_R) = 0 with
  |π_x(u_R)| ≤ 2. But Ann(1+x+x²) in F₂[Z₆] is the ideal generated by
  (1+x)(1+x³) = 1+x+x³+x⁴, of minimum weight 4: π_x(u_R) = 0, so
  r-diff = (0,3) ∉ dB. ✗
- ℓ-diff = ±(3,1): |π_x| matching (weight 2 on the left) forces the
  r-pair's x-gap to be ±1, i.e. r-diff = ±(1,3). Up to translation this
  is ONE configuration on each side: σ = A(1+x³y)·t, with x-coordinate
  multiplicity multiset **{3,1}** (cells x³, y², x³y², x³y³), versus
  B(1+xy³)·t′ with multiset **{2,1,1}** (cells y³, x², x²y³, x³y³).
  The multiset is translation-invariant. ✗

**|σ| = 6** — both pairs disjoint: ℓ-diff ∉ dA, r-diff ∉ dB.
- ℓ y-gap 0 (so ℓ x-gap ≠ 0): π_y(u_R) = 0 forces r y-gap 0, hence
  r x-gap ≠ 0; matching |π_x| = 2 forces r x-gap ±1 — but then
  r-diff = (±1,0) ∈ dB. ✗
- ℓ y-gap ±1: ℓ-diff = (e,±1) with e ∈ {1,2,4,5}; |π_y| = 2 forces
  r y-gap 3, so r-diff = (f,3) with f ∈ {0,3} (else ∈ dB). Then
  |π_x(σ)|: left x³(gap e) has weight 2; right (1+x+x²)(gap f) has
  weight 0 (f=0) or 6 (f=3). ✗
- ℓ y-gap ±2 or 3: |π_y(σ)| = 4 or 6 from the left, ≤ 2 from the right. ✗

All splits are dead; nonzero cycles have weight ≥ 6. By Lemma 2.1 the
ker H_Z statement follows (and was verified independently). **∎ Theorem A**

### 4.5 Corollaries

- **(H0) discharged:** d_Z(base) ≥ 6 (a nontrivial logical is a nonzero
  cycle); d_X = d_Z (Lemma 2.1). μ_Z, μ_X ≥ 6 (stabilizers are cycles).
- **Sharp annihilator minima:** Ann(A), Ann(B) have minimum weight
  exactly 6 (§4.6 exhibits an element).

### 4.6 The exhibit: d(base) = 6

Let z\* = 1 + y + y² + y⁵ + x³ + x³y⁴ = (1+y+y²+y⁵) + x³(1+y⁴). Then
A·z\* = 0: expanding (x³+y+y²)·z\* gives 18 monomials that cancel in
pairs —

    x³·z* = x³ + x³y + x³y² + x³y⁵ + 1 + y⁴
    y ·z* = y + y² + y³ + 1 + x³y + x³y⁵
    y²·z* = y² + y³ + y⁴ + y + x³y² + x³

(each of the nine distinct monomials 1, y, y², y³, y⁴, x³, x³y, x³y²,
x³y⁵ appears exactly twice). So u\* := (z\*, 0) is a weight-6 cycle. It is
not a stabilizer: a stabilizer (B·w, A·w) with zero right block has
w ∈ Ann(A), and if nonzero in im ∂₂ then w ∉ ker ∂₂, so |B·w| ≥ 16 by the
one-block lemma (§6.3) — no weight-6 stabilizer has a zero block. Hence
u\* is a nontrivial Z-logical of weight 6: **d(base) = 6**. ∎

---

## 5. The double cover and Theorem B

Gross is the x-direction free-Z₂ double cover of the base: deck
transformation σ: x ↦ x+6 (additively), sheets indexed by x ≥ 6. In sheet
coordinates a cover chain is a pair of base chains v = (v₀, v₁), and for
every seam position the cover boundaries take the block form
[[∂_nc, ∂_c], [∂_c, ∂_nc]] with ∂ = ∂_nc + ∂_c the base boundary
(verified structurally in `a3_cut_decomposition.py`; the split is
entrywise on ∂). Two consequences used here:

1. **p is a chain map.** p(v) := v₀ + v₁ satisfies
   ∂₁(p(v)) = sum of the two block rows of ∂₁^cov v; in particular
   v ∈ ker ∂₁^cov ⟹ p(v) ∈ ker ∂₁^base. And |v| ≥ |p(v)|.
2. **p(v) = 0 means v is diagonal:** v = (v₀, v₀), and the block
   equations reduce to ∂₁v₀ = 0.

**Proof of Theorem B.** Let v ≠ 0 be any cover Z-cycle (logical or not).
- If p(v) ≠ 0: p(v) is a nonzero base cycle, so
  |v| ≥ |p(v)| ≥ 6 (Theorem A).
- If p(v) = 0: v = (v₀, v₀) with v₀ ≠ 0 a base cycle, so
  |v| = 2|v₀| ≥ 12.

Hence every nonzero cover cycle has weight ≥ 6 — in particular
d_Z(gross) ≥ 6 — and d_X = d_Z by Lemma 2.1. **∎**

Remark (Fork B resurrected). This is the Entry-4 "projection bound"
d ≥ min(d_base, μ_Z), which was a dead end only because its inputs were
SAT facts; Theorem A supplies both analytically, with no recursion down a
cover tower. Note that Theorem B uses nothing from §6.

---

## 6. Theorem C: the dangerous sector is ≥ 12, tight

Theorem B caps at 6 because the safe sector does; the deeper result —
and the asset for the d = 12 program — is that the **dangerous sector**
(classes in ker pr_*) is bounded by 12 = 2·d(base). This needs the full
machinery: the slice reduction and the light-stabilizer classification.

### 6.1 The slice identity (Entry 5)

For each seam position j, write ∂₂ = d2nc_j + d2c_j. Dangerous cycles are
exactly τ(Z₁) + im ∂₂^cov (τ(u) = (u,u)), and v = τ(u) + ∂₂^cov w is a
nontrivial logical iff [u] ∉ imΔ, where Δ[ζ] = [d2c_j ζ] is the Smith
connecting map (im Δ = ker tr_*, cut-independent). Fixing
b := p(v) = ∂₂ p(w) ∈ Stab_Z(base) and a preimage z_b, the sheets satisfy
v₀ = u + d2c_j z_b + ∂₂w₀ (mod relabeling) and v₁ = v₀ + b, so the
boolean identity |x| + |x+b| = |b| + 2|x off supp b| gives, for every j,

    |v| = |b| + 2·|v₀ off supp b| ≥ |b| + 2·m(b),
    m(b) := min{ |(d2c_j z_b + u′) off supp b| : u′ ∈ Z₁, [u′] ∉ imΔ }.

(Full derivation and the exactness of the range: `A3` Entry 5; verified
in `a3_mb_foundations.py` V1–V8.) Theorem C is then exactly

    (M):  |b| + 2·m(b) ≥ 12  for every b ∈ Stab_Z(base).

### 6.2 Structure lemmas for the classification

Throughout, b = ∂₂z = (B·z, A·z) with blocks decomposed into layers.

- **Parity.** Â₀ = B̂₀ (A and B have the same s-part multiset
  {1, s_x, s_y}), so the two blocks have identical layer parities; and
  |b| = |B·z| + |A·z| ≡ 2|z| ≡ 0: **|b| is even**.
- **Floor.** If b ≠ 0 and |b| ≤ 10 then **both blocks have ≥ 3 nonzero
  layers**. (Engine support analysis on the radical components; `A3`
  Entry 10, "Floor lemma" — uses the one-block lemma below for the
  one-block-zero branch.)
- **One-block lemma (sharp form).** If z′ ∈ Ann(A) ∖ ker ∂₂ then
  |B·z′| ≥ 16 (mirror: Ann(B), |A·z′| ≥ 16). *Proof.* ẑ′₀ = ẑ′₂ = 0
  (units), ẑ′_j ∈ (Â_j) for j ∈ {1,3,4}. Then V₄^B = ωÂ₄ẑ′₄ = 0;
  V₃^B = B̂₃ẑ′₃ ∈ F₄·uv (socle): a constant vector; V₁^B ∈ (Â₁). The
  parity component is dead, so every layer's Fourier support ⊆ {1,3},
  with d₃-costs: {1} → 6, {3} → 6, {1,3} → 4. Cases: V₃ ≠ 0 constant ⟹
  all four layers alive; V₁ full ⟹ 4 layers at cost 4 = **16**; V₁
  co-point ⟹ 3·4 + 6 = 18; V₁ = 0 ⟹ 4·6 = 24. V₃ = 0 ⟹ V₁ ≠ 0 with
  ≥ 3 layers at cost 6 ⟹ ≥ 18. Minimum 16 (attained). ∎
- **Direction forcing.** If f ∈ im(A·) has a zero layer and a weight-2
  layer {p, p+δ} (and some δ-point layer), each radical V_j is a nonzero
  co-point vector, so V_j[s_pair] = ψ_j(p)(1+ψ_j(δ)) ≠ 0 for
  j ∈ {1,3,4}: δ avoids ker ψ₁, ker ψ₃, ker ψ₄, leaving **δ ∈ the t_y
  direction** (mirror on the B side: t_x).

### 6.3 The classification

**Theorem (light stabilizers).** Every b ∈ Stab_Z(base) with
0 < |b| ≤ 11 is one of the 36 **hexagons** ∂₂δ_g (|b| = 6) or the 216
**D-pairs** ∂₂(δ_g + δ_{gd}), d ∈ dA ∪ dB (|b| = 10). In particular
there are no stabilizers of weight 8, and μ_Z = 6.

*Proof.* |b| ≤ 10 by evenness; both blocks have ≥ 3 nonzero layers
(floor), so the lighter block (WLOG the A-block, by the x↔y swap
automorphism A(y,x) = B(x,y), which exchanges the blocks) has weight
3, 4 or 5 with layer profile among

    (1,1,1) | (1,1,1,1), (2,1,1) | (2,1,1,1), (2,2,1), (3,1,1).

Each shape is resolved by the engine; in every surviving case f = A·z is
pinned inside a **single t_y-fibre**, and an endgame transfers the
classification from the block to b itself:

- **(1,1,1) [R1]:** three δ-point layers; the radical V_j are co-points
  with C-ratios = η-powers; ψ₃, ψ₄ separation pins the three cells to the
  difference pattern of A·δ_g. Endgame: z − δ_g ∈ Ann(A) with
  |B(z − δ_g)| ≤ 7 + 3 < 16 ⟹ z ≡ δ_g mod ker ∂₂: **b is a hexagon**.
- **(1,1,1,1):** all V_j full ⟹ constant ⟹ the four cells coincide
  (δ-column at t\*). Completions die: the B-block would be all-odd of
  weight ≤ 6, i.e. (1,1,1,1) or (3,1,1,1) — and one comp-2 transfer kills
  both at once (the Entry-15 reviewer's simplification of the Entry-10
  kill): the A-side pins ẑ₂ = Â₂⁻¹·ψ₂(t\*)·uv = ψ₂(t\*)·uv (units fix
  the socle: u₀·uv = ε(u₀)·uv = uv), so V₂ᴮ = B̂₂·ψ₂(t\*)uv = 0 since the
  radical B̂₂ kills the socle — but either B-shape has a δ-point layer,
  where V₂ᴮ takes the nonzero value ψ₂(t-cell). ✗ **No light b.**
  (The original Entry-10 route — socle-transfer constants forcing the
  B-cells to coincide, then the comp-1 and Q-dictionary kills — remains
  valid; `A3` Entry 15, Note 1 spells out its compressed steps.)
- **(2,1,1) [the D-pair lemma]:** direction forcing puts the pair in the
  t_y direction; with 1 + η = η², the C-ratio system has exactly one
  solution per pair-layer position — the three single-fibre patterns
  realized by A·(δ_g + δ_{gd}), d = y, x³y², x³y (108 elements, 3
  translation classes; machine-confirmed equal to the enumerated set).
  Since dA ∩ dB = ∅, the dA-pair has block weights (4, 6). Endgame: a
  completion with |b| ≤ 10 has |B·z| ≤ 6, so |B(z − pair)| ≤ 6 + 6 =
  12 < 16 (sharp one-block!) ⟹ z ≡ pair mod ker: **b is the D-pair,
  |b| = 10.** (This is where the sharp 16 is genuinely needed: the old
  ≥ 12 bound left a gap at exactly 12.)
- **(3,1,1):** the weight-3 layer is a line or a triangle. A line kills
  ≥ 2 of the three radical components at its layer (only the orthogonal
  orbit survives a line) — contradicting co-point support. A triangle
  {p, p+g, p+h} has κ_j := 1 + ψ_j(g) + ψ_j(h) = 0 for **exactly one**
  orbit class (j ↦ (j·g, j·h) is a bijection; κ = 0 ⟺ (j·g, j·h) =
  ±(1,2)); if that class is radical, support kill; if it is the A-unit
  comp 2, the ratio system is solvable only if κ₄ = κ₁κ₃ (from ψ₄ = ψ₁ψ₃
  and the j-independent C-exponents), and the six dead-orbit-2 triangle
  shapes all violate it:

      (g_y,h_y) ∈ {(0,1),(0,2),(1,0),(1,1),(2,0),(2,2)} (g_x=1, h_x=2):
      κ₁κ₃ ∈ {ω², ω², ω, ω², ω, ω}  vs  κ₄ ∈ {1, ω, ω², ω, 1, ω²}.

  **im(A·) has no (3,1,1) element** (machine cross-check: none on either
  side).
- **(2,1,1,1):** all four layers alive. If the pair direction avoids all
  radical kernels (t_y), all three radical V_j are full ⟹ constant ⟹
  δ-cells coincide at t\* and the pair is {t\*+e, t\*+2e}: one class. If
  the direction lies in one radical kernel, that V_j is co-point while
  the other two force the δ-cells equal — but a co-point takes three
  *distinct* values on its support. ✗ Kill of the surviving class: a
  completion needs |B·z| = 5 with three odd layers, so the B-block is
  (3,1,1) — impossible by the mirror of the previous item — or
  (2,1,1,1), pinned by the mirror classification to δ-cells at a common
  t₀ and a t_x pair. The **comp-1 transfer operator**
  T := Â₁·B̂₁⁻¹ = Â₁(1+u+v) = u + ωv + (1+ω)uv (B̂₁ is a self-inverse
  unit) has value vector C₁([1]) and T·1⃗ = 0; since ψ₁ kills t_x pairs,
  V₁^B = ψ₁(t₀)(1⃗ + δ_{s_P}), so V₁^A = T·V₁^B = ψ₁(t₀)·shift_{s_P}(T)
  is a co-point vanishing at s_P — but the A-side says V₁^A is a nonzero
  constant. ✗ **No light b.**
- **(2,2,1):** direction forcing puts both pairs in t_y; the C-ratio
  bookkeeping pins the three layers to {t}, {t, t+e}, {t, t+2e} (three
  classes, single fibre). Kill: a completion needs |B·z| = 5 with exactly
  one odd layer at s_δ; the only such profile with ≥ 3 layers is
  {1,2,2}, so the B-block is a mirror-(2,2,1) with t_x pairs:
  V₁^B = ψ₁(t′)·δ_{s_δ} and V₁^A = T·V₁^B is a co-point vanishing at
  s_δ — but the A-side co-point vanishes at s₄ ≠ s_δ and is nonzero at
  s_δ. ✗ **No light b.** ∎

### 6.4 The m-rungs

- **m(hexagon) ≥ 3.** supp(d2c_j δ_g) ⊆ h(g) (the seam split is
  entrywise), so m = min |u′ off h(g)| over cycles with [u′] ∉ imΔ. If
  |u′ off h| ≤ 2, replace u′ by u′ + b if needed so |u′ ∩ h| ≤ 3: a
  cycle of weight ≤ 5, hence 0 (Theorem A) — but then [u′] = 0 ∈ imΔ. ✗
- **m(D-pair) ≥ 1.** supp(d2c_j z_b) ⊆ h ∪ h′ = supp b ∪ {q\*}. If
  m = 0, some cycle u′ with [u′] ∉ imΔ is supported in the 11-qubit
  union; the four coset reps u′ + {0, b₁, b₂, b₁+b₂} have weights
  summing to 5+5+5+5+2 = 22 < 4·6, so one rep has weight ≤ 5, hence is
  0 — then u′ ∈ span{b₁, b₂} and [u′] = 0. ✗

### 6.5 Assembly

(M) holds on every rung: b = 0 (m(0) ≥ 6: a non-imΔ class is a nonzero
cycle, Theorem A); hexagons (6 + 2·3); D-pairs (10 + 2·1); |b| ≥ 12
(trivial); and no other b with |b| ≤ 11 exists (§6.3). With §6.1,
**every nontrivial dangerous Z-logical has weight ≥ |b| + 2m(b) ≥ 12**.
Tightness: the diagonal reps τ(u) over weight-6 base logicals u with
[u] ∉ imΔ have weight 12 (such u exist; verified — e.g. all 84 weight-6
logicals are non-imΔ). **∎ Theorem C**

---

## 7. Discussion

**Why this route beat the floor.** The published analytic route on gross
(Lin–Pryadko) divides by the degeneracy c = 8 and is capped at
⌈12/8⌉ = 2 regardless of its numerator. The cover route instead splits
H₁(gross) along pr_*: the safe part inherits d(base) via the projection,
and the dangerous part — where all the true minimum-weight logicals live —
is controlled by the base's *stabilizer* structure through (M). The
binding constraint of Theorem B is now the safe sector, not the floor.

**What was discovered along the way.**
- Light base stabilizers are **single-fibre objects**: every stabilizer
  of weight ≤ 11 lives, per layer, inside one t_y-line of one x-residue
  class. This rigidity is what makes the classification small.
- The **chirality phenomenon**: dB-triangles come in two reflection
  classes with different image weights (7 vs 3) — the reason the (1,3)
  split nearly survives and the difference-set disjointness in *both
  coordinates* matters.
- The **comp-1 transfer operator** T = Â₁B̂₁⁻¹, which locks the two
  blocks of a stabilizer together through the one component where A is
  radical and B is a unit. Both weight-5 kills are one application each.

**The road to d = 12 (goal 1).** Pointwise
|v| = |p(v)| + 2|v₀ ∧ v₁|, so with the dangerous sector tight at 12, the
remaining gap is exactly the **safe-sector analogue of (M)**: for w a
nontrivial base logical cycle, every cover cycle v with p(v) = w
satisfies |w| + 2|v₀ ∧ v₁| ≥ 12. Here v₀ ranges over the solutions of
∂₁v₀ = ∂_c w (a syndrome-shifted coset — the "s ≠ 0" data of the early
entries, in its correct home), and the quantity to bound is the sheet
overlap. SAT says the safe minimum is ≥ 12, so the statement is true
with structure to find.

**Generalization (goal 2).** Theorem A's proof consumed only: (i) the
CRT component structure of F₂[G_base] (units/radicals of Â_j, B̂_j),
(ii) multiplicity-free difference sets with dA ∩ dB = ∅ disjoint in both
coordinates, (iii) the coordinate projections. Each is a checkable
hypothesis per BB instance; instances that pass get
d ≥ min(d_small-cycle-bound, …) by the same case grid, and any free-Z₂
cover of such an instance gets Theorem B's transfer for free. Candidate
next targets: the other Bravyi-instance bases and the odd-h SRB covers
(bb_90, bb_108 with k′ = 8).

**Direct attack on d(gross) = 12 by small cycles?** Running §4 on
F₂[Z₁₂×Z₆] directly (weights ≤ 11) is conceivable but the 2-part is
Z₄×Z₂: the layer ring becomes F₄[Z₄×Z₂] with radical filtration depth 4,
and the case grid grows accordingly. Not attempted; the safe-sector
(M)-analogue looks cheaper.

---

## Appendix A. Verification map (confirmation only)

| claim | script / check |
|---|---|
| Theorem A splits, triangles, multisets | `a3_small_cycles.py` W1–W5 |
| Theorem A exhaustive (both sides) | W6 (zero cycles of weight ≤ 5) |
| weight-6 census = 120 = 36 + 84 | W7 (matches `a3_mb_structure.py` T4) |
| seam containment, D-pair overlap | W8 |
| inversion duality (base AND gross) | W9 |
| engine / C-table / ideal rigidity | `a3_mb_rigidity.py` G1; `a3_shape_lemmas.py` V1 |
| one-block exact minima (16) + case split | G2; V4 |
| direction forcing | V2 |
| R1, R-(2,1,1) classifications | G3; V3 (= 108 dA-pairs) |
| D-pair endgame | V5 |
| R-(3,1,1) κ-table; no elements either side | V6 |
| R-(2,1,1,1), R-(2,2,1) class + kill + T-identity | V7, V8 |
| shape master table (all profiles, μ_B) | G4 |
| slice identity foundations | `a3_mb_foundations.py` V1–V8 |
| independent re-implementation of the whole chain | `a3_adv15_recheck.py` (Entry-15 review, 49 checks) |
| light-b enumeration; m-values | `a3_mb_scan.py` |
| end-to-end SAT crosschecks | `a3_mb_crosscheck.py` C1 (b≠0 dangerous min 14), C2 (imΔ-distance 12) |

Consistency with the (never-load-bearing) SAT ground truth: d(gross) = 12
≥ 6 ✓; the dangerous bound 12 is attained ✓; the b ≠ 0 dangerous minimum
14 = 6 + 2·4 matches the hexagon slice ✓.

## Appendix B. Surveyable tables

**C-table** (engine, §3): C_j([1]) = (0, η_j, 1, η_j²) over
(1, s_x, s_y, s_xs_y); other s₄ by layer translation, exponents
j-independent.

**d₃ dictionary** (§3): (0,T)→9, (1,F)→6, (1,T)→3, (2,F)→4, (2,T)→3,
(3,·)→2, (4,F)→2, (4,T)→1.

**dB-triangles** (§4.3): one chirality pair; T₊ = {0,(1,0),(2,3)} → image
weight 7; T₋ = {0,(1,0),(5,3)} → image y³(1+x²+x⁴), constant-y. Mirror
for dA with constant-x.

**κ-table** (§6.3, R-(3,1,1), dead orbit = comp 2; F₄ written 1, ω, ω²):

| (g_y, h_y) | κ₁ | κ₃ | κ₄ | κ₁κ₃ |
|---|---|---|---|---|
| (0,1) | ω  | ω  | 1  | ω² |
| (0,2) | ω² | 1  | ω  | ω² |
| (1,0) | ω  | 1  | ω² | ω  |
| (1,1) | 1  | ω² | ω  | ω² |
| (2,0) | ω² | ω² | 1  | ω  |
| (2,2) | 1  | ω  | ω² | ω  |

(κ₄ ≠ κ₁κ₃ in every row.)

**One-block case minima** (§6.2): (V₃ alive, V₁ full) → 16;
(V₃ alive, V₁ co-point) → 18; (V₃ alive, V₁ = 0) → 24;
(V₃ = 0, V₁ co-point) → 18; (V₃ = 0, V₁ full) → 24.
