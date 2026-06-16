# A fully analytic distance bound for the gross code: d ≥ 6, and d = 12

> **STATUS: PART I REVIEW-CLEARED; PART II IS THE ENTRY-27 EXTENSION.**
> Part I (§§1–7, Theorems A–C): the Entry-15 adversarial re-review (fresh
> session; every machine check re-implemented independently —
> `a3_adv15_recheck.py`, 49/49 — and every prose argument re-derived by
> hand) found **all links HOLD**; its two presentational notes are folded
> in below (§3 d₃ remark; §6.3 (1,1,1,1) bullet). Part II (§§8–14,
> Theorem D: **d(gross) = 12**) is the A4 extension owed by Entry 27: it
> walks the goal-1 chain (Entries 16–26, review-cleared by Entry 27) with
> the two machine-certified residues replaced by compressed, hand-walkable
> case tables — the standard-form bucket walk (§11) for the wt-24
> C-tables and the locus tables (§12–13) for the floor-10 achiever lists.
> Entry 27's two sharpenings (off₀ = off₂ = 0; the comp-2 one-liner) and
> its owed H₀ paragraph are folded in. Every numerical statement in this
> note is *confirmation* of a hand proof, never an ingredient; the
> verification scripts are listed in Appendices A and D. Source of record
> for the proofs: `notes/A3_track1p1_log.md`, Entries 5, 10–15 (Part I)
> and 16–28 (Part II).

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

---
---

# Part II. d(gross) = 12

## 8. Results and route

**Theorem D.** The gross code `[[144,12,12]]` satisfies **d(gross) = 12**,
analytically: every reduction below is hand-proven, and every finite case
split is a surveyable table (§11: 33 bucket rows; §12: per-cell locus tables of
1–4 rows each; §13: 118 one-line field evaluations organized into
families). No SAT, kernel-`decide`, or machine enumeration is
load-bearing; the scripts of Appendix D re-verify every table.

The route (Entries 16–26, review-cleared by Entry 27):

1. **Dichotomy.** For a nontrivial cover Z-logical v, either
   [p(v)] = 0 in H₁(base) (*dangerous*) or not (*safe*). The dangerous
   sector is ≥ 12 by Theorem C.
2. **(R)** (§9.1): the safe sector sees only the Smith classes:
   [p(v)] ∈ im Δ ∖ 0.
3. **(M-im)** (§§10–13): every base 1-cycle in a nonzero imΔ class has
   weight ≥ 12. Hence |v| ≥ |p(v)| ≥ 12.
4. **Duality** (Lemma 2.1): d_X = d_Z. **Tightness** (§14): τ(u\*) is a
   weight-12 logical.

(M-im) is where the work lives. Its proof has three stages: the CRT
confined frame (§9.3–§9.4), which parametrizes each Smith coset by a
shared 16-element block-diagonal comp-0 datum V₀, a shared spine
(a₃, a₄) ∈ F₄², a shared twisted shift γ, and per-block confined/free
data; the **C-table floor** (§§11–12): every coset element has weight
≥ 12 on the two wt-24 orbits and ≥ 10 on the three wt-16/18 orbits; and
the **weight-10 kill** (§13): the floor-10 achievers all violate one of
the two ρ-links that the floor relaxes. Translation transport (§9.3)
carries the five orbit representatives to all 63 nonzero Smith classes.

## 9. The safe-sector reduction

### 9.1 The sector dichotomy and (R)

Cover 1-chains are pairs of base chains v = (v₀, v₁) (sheet
coordinates); p(v) = v₀ + v₁ is a chain map, |v| ≥ |p(v)|, and the
deck transformation σ: x ↦ x+6 satisfies (1+σ)v = τ(p(v)) for cycles,
where τ(u) = (u, u) (§5). The connecting map Δ[ζ] = [d2c_j ζ] on
H₂(base) = ker ∂₂ is injective with cut-independent image; im Δ =
ker τ_\* inside H₁(cover).

**Theorem (R).** Every cover cycle v has [p(v)] ∈ im Δ; equivalently
σ_\* = id on H₁(gross).

*Proof.* Over F₂[Z₁₂×Z₆], squaring B kills its y-dependence (y⁶ = 1):
B² = 1 + x² + x⁴, so (1+x²)B² = 1+x⁶. For a cover cycle
v = (v_L, v_R) (A v_L = B v_R), set z := (1+x²)·B·v_L. Then
∂₂z = ((1+x²)B²v_L, (1+x²)B·A v_L) = ((1+x⁶)v_L, (1+x⁶)v_R) = v + σv.
So (1+σ) is null-homotopic on cycles, σ_\* = id, and
τ_\*∘p_\* = (1+σ)_\* = 0: im p_\* ⊆ ker τ_\* = im Δ. ∎

Only this **inclusion** is load-bearing (Entry 27, Link 2): the lower
bound needs [p(v)] ∈ im Δ ∖ 0, and [p(v)] ≠ 0 is the definition of the
safe sector. Neither direction of Theorem D uses k = 12 or the equality
leg of (R).

### 9.2 No double wrap; the seam-flux functionals

**Lemma (no double wrap).** For every cut j: d1c_j·d2c_j = 0,
d1nc_j·d2nc_j = 0, and d1nc_j·d2c_j = d1c_j·d2nc_j.

*Proof.* An entry of ∂₁∂₂ at (check c, face f) sums over two-step paths
f → qubit → c, one per factorization c·f⁻¹ = a·b per route (left block:
B-step then A-step; right block: A-step then B-step) — an even number
in total since AB = BA. The total x-advance of a path is
D = sx(a) + sx(b) ≤ 3 + 2 = 5 < 6, and D ≡ (c−f)_x (mod 6) with
0 ≤ D ≤ 5, so **D is the same integer for every path at the entry**.
A monotone path of advance D < 6 starting at x_f crosses the cut at
most once, and whether it crosses is determined by (x_f, D) alone.
Hence all paths at an entry have equal crossing count: if 0 they cancel
inside d1nc·d2nc; if 1, each crosses in exactly one of its two steps,
d1c·d2c and d1nc·d2nc receive nothing, and the paths distribute between
d1nc·d2c and d1c·d2nc with even total, forcing those entries equal. ∎

**Corollary (flux).** P[ξ, ζ] = ξᵀ(d1c_j d2c_j)ζ = 0 identically, so
each ξ ∈ ker H_Xᵀ gives a class functional ℓ_ξ(w) = ξᵀ d1c_j w
(well-defined: ξᵀ d1c ∂₂ = 0 needs the lemma plus ξᵀd1nc = ξᵀd1c, which
follows from ξᵀ∂₁ = 0), vanishing on im Δ. Only the **easy inclusion**
im Δ ⊆ ker flux is load-bearing (it feeds the tightness argument, §14).

*Remark (the H₀ paragraph owed by Entry 27, Link 3).* The
characterization **equality** im Δ^X = (im Δ^Z)^⊥ — decorative for
Theorem D, used only by the Entry-21 census cross-check — needs
dim im Δ = 6 on both sides, which the Gysin sequence reduces to
dim H₀(base) = dim F₂[Z₆²]/(A, B) = 6. By the CRT frame (§3): the
component quotient dimensions are (0, 0, 0, 2, 4) — components 0–2
contain a unit among {Â_j, B̂_j}; at component 3 the two radicals
Â₃ = u+ωv, B̂₃ = ωu+v generate the maximal ideal (u, v) of F₄[Z₂²]
(their span contains u and v), leaving F₄[Z₂²]/(u,v) ≅ F₄, dimension 2
over F₂; at component 4, B̂₄ = ωÂ₄ makes the ideal span{Â₄, uv}, of
F₄-codimension 2, dimension 4 over F₂. Total 0+0+0+2+4 = 6. ∎

### 9.3 The Smith cosets: transport and parity

ker ∂₂ ∖ 0 has five translation orbits, of (size, weight) = (9, 16),
(12, 18), (36, 18), (3, 24), (3, 24) — written wt-16, wt-18a, wt-18b,
wt-24a, wt-24b. The transport identities d2c_j∘T_x = T_x∘d2c_{j−1} and
d2c_j∘T_y = T_y∘d2c_j (exact matrix identities, all cuts), with
cut-independence of Δ, give class(Tζ) = T·class(ζ): the five orbit
representatives cover all 63 nonzero Smith classes, and any
translation-covariant bound transports. Fix the cut j = 0 and the five
canonical cosets C(ζ) = d2c₀ζ + im ∂₂.

**Parity (Entry 22, V1–V3).** (i) For a layer f ∈ F₂[Z₃²]:
wt(f) ≡ f̂(triv) (mod 2). (ii) Every ζ ∈ ker ∂₂ has even columns
(Aζ = 0 gives c_{i+3} = (y+y²)c_i columnwise, and aug(y+y²) = 0; rows
mirror via B). (iii) Every element of every Smith coset has even weight
and even value-cost. So sub-12 weights are 6, 8, 10, and by §13's floor
the only live possibility is weight exactly 10.

### 9.4 Components 0–2: off₀ = off₂ = 0 and the unpinned links

For w = d2c₀ζ + ∂₂t, the CRT component data is
V_j(w) = off_j + (B̂_j t̂_j, Â_j t̂_j), off_j = comp_j(d2c₀ζ), with the
five components independent.

**Sharpening 1 (Entry 27): off₀ = off₂ = 0 identically.** At components
0 and 2 the A-relation multiplier comp(y+y²) equals Y := 1+s_y (the
component characters are trivial on t_y at j ∈ {0, 2}... at j = 0 both
characters are trivial; at j = 2 the character is trivial on t_y). The
column-collapse of ζ at such a component satisfies v_i = Y v_{i+3} =
Y² v_i = 0, and the cut-marked sums building off₀, off₂ are sums of
these zero collapses. Hence comp-0 data of any coset element is the
diagonal pair (V₀, V₀), V₀ = B̂₀t̂₀ ranging over all 16 of F₂[Z₂²] (B̂₀
is a unit), and comp 2 is a free graph: V₂L = ρ₂·V₂R,
ρ₂ := B̂₂Â₂⁻¹.

**c₁ = 0 (Entry 26, comp 1 in full).** Write ζ's columns c₀..c₅ and
their comp-1 transforms û_i ∈ F₄[s_y]. The crossing bookkeeping at cut
0 gives off₁L = û₄ + û₅ + s_xû₅, off₁R = û₃ + s_xû₄ + û₅. The cycle
relations transform to û_{i+3} = τû_i (τ = ω² + ωs_y, a unit) and
û_{i−1} + û_{i−2} = s_yû_i, giving û₀ = û₁ + s_yû₂ and
**Yû₁ = ω²Yû₂** (D1). Then c₁ := off₁R + ρ₁⁻¹-normalized off₁L
vanishes: the claim reduces (group coefficients; B̂₁X = s_yX,
B̂₁Y = s_xY) to Y[(X+ω)û₁ + (ω + ω²s_x)û₂] = 0, which D1 collapses to
Y(ω² + ω + 1)û₂ = 0 — identically zero. ∎

**Sharpening 2 (Entry 27): c₂ = 0 is a one-liner** — off₂ = 0
(Sharpening 1), so the comp-2 graph passes through the origin; the
Entry-26 mirror chain is unnecessary.

Hence on every coset, the comp-1/2 data satisfies the two **ρ-links**

    V₁R = ρ₁·V₁L,    V₂L = ρ₂·V₂R,

and the **confined sets** (the dependent sides, with the free sides
relaxed) are exactly im ρ₁, im ρ₂ — 16 elements each, since
ρ_i² = aug(ρ_i)²·1 = 0 (squaring in F₄[Z₂²] is Frobenius-linear and
g² = e for g ∈ Z₂²) and ρ_i ∉ F₄·ΣG.

## 10. The slot frame

All five orbits are now analyzed in one coordinate system.

### 10.1 Slots, labelings, lines

Slots are the four elements of Z₂² = {e, x, y, xy} (the 2-part layers);
component data live in R = F₄[Z₂²], identified with functions
slots → F₄ (slot values). Write X = 1+s_x, Y = 1+s_y, XY = ΣG; the
slot values of a·1 + αX + βY + δXY are (a+α+β+δ, α+δ, β+δ, δ) over
(e, x, y, xy). The **kill vector** κ(v) := (a+α+β, α, β, 0) is the slot
function modulo the constant shift δ: as the free shift varies, the
zero set of v + δ′XY is a fibre of κ(v). Define

    m  := κ(B̂)  = (ω², ω, 1, 0)      (B̂ := B̂₂ = B̂₃ = B̂₄ = ωX + Y)
    m′ := κ(Â₃) = (ω², 1, ω, 0) = m∘(x↔y)     (Â₁ = Â₃ = X + ωY)
    θ  := (1, 0, 1, 0),   θ̃ := (1, 1, 0, 0).

Facts (each a one-line check): m, m′ are bijections slots → F₄;
m̃ := m + ω² is an additive isomorphism Z₂² ≅ (F₄, +);
**κ(Â₄) = m′² = ω²·m** and m² = ω²m′ (entrywise Frobenius);
κ(ρ₂) = m, κ(ρ₁) = m′; θ = 1 + Tr(ω²m̃), θ̃ = 1 + Tr(m̃).

Consequently (machine cross-check F1–F2):

- **conf lines**: slot values of im ρ₂ = {p·m + c : p, c ∈ F₄}; of
  im ρ₁ = {p·m′ + c} — the full affine line of the labeling.
- **comp 3**: V₃L = off₃L + a₃B̂ + βXY has slot values
  κ₃L + a₃m + c₃ with c₃ ∈ F₄ free (β absorbs the offset's XY part) and
  κ₃L := κ(off₃L); mirror on R with m′ and κ₃R. The spine coordinate a₃
  is **shared** between blocks; the constants are free and independent.
- **comp 4**: the Γ₄ ideal is one-dimensional (B̂₄ = ωÂ₄), giving the
  **tie** V₄L = ω·V₄R + w₄ with w₄ := off₄L + ω·off₄R a fixed vector
  per orbit (machine check F3). In slot values: directions
  k₄L = κ₄L + a₄m (the ω-twist absorbs into ωa₄m′² = a₄m) and
  k₄R = κ₄R + ω²a₄m, with constants tied through the shared γ:
  d₄L = ωγ + e_L, d₄R = γ + e_R, where e is the XY-coefficient of the
  block's comp-4 offset and e_L = ωe_R + (XY-coeff of w₄).

Per-orbit data (offsets as kill vectors; verified F4):

| orbit | κ₃L | κ₃R | κ₄L | κ₄R | e_L | e_R |
|---|---|---|---|---|---|---|
| wt-16  | ωθ = (ω,0,ω,0) | θ | ωθ | θ | ω | ω |
| wt-18a | m | m′ | (0,ω,ω²,0) | (ω²,ω²,ω²,0) | ω² | ω² |
| wt-18b | (1,ω,ω²,0) | ω²m | (ω,ω,1,0) | (ω,ω²,ω,0) | 1 | 1 |
| wt-24a | 0 | 0 | ωθ | θ | ω² | 1 |
| wt-24b | ωθ | θ | 0 | 0 | 1 | ω² |

(wt-24b is wt-24a with the comp-3 and comp-4 offsets exchanged.)

### 10.2 The slot-cost rules (Entry 23, recap)

Per slot s, the layer cost given (v₀; v_conf, v₃, v₄)(s), with the
block's other unit-side component free, is (proven via ψ₂² = ψ₃ψ₄,
ψ₄ = ψ₁ψ₃, and the E ≤ 2 value rigidity):

    v₀ = 0:  0 alive → 0;  1 alive → 4;  2 alive → 2;
             3 alive → 2 if T = 1 else 4
    v₀ = 1:  3 alive with T = 1 → 1 (δ-point);  else → 3

with T_L = v₂²(v₃v₄)⁻¹, T_R = v₄(v₁v₃)⁻¹ ("alive" counts nonzero
values among the block's three constrained components). The v₀-free
cost is the minimum over v₀: (0, 3, 2, 1 if cheap else 3) by alive
count. **Slot parity**: every cost ≡ v₀ (mod 2), so a block's cost
≡ |V₀| and any two blocks sharing V₀ have costs of equal parity; in
particular per-(V₀, γ) cost sums are even.

### 10.3 Fibres of affine pencils (the pair-ratio lemma)

**Lemma.** Let k = κ + λu with u: slots → F₄ a bijection. For each of
the six unordered slot pairs P = {s, s′}, k(s) = k(s′) at exactly one
pencil parameter λ_P = (κ(s)+κ(s′))·(u(s)+u(s′))⁻¹. The fibre
partition of k at a given λ is read off from {P : λ_P = λ}. ∎

For the S-form direction k = bm + ωθ (κ = ωθ, u = m): λ_P = 0 on the
two θ-constant pairs {e,y}, {x,xy}; on the four θ-split pairs
λ_P = ω·Δm(P)⁻¹, giving λ = ω on {e,x}, {y,xy} and λ = ω² on {e,xy},
{x,y}. Hence the **comp-4 trichotomy**: b ∈ {0, ω, ω²} ⟹ k is
double-paired (fibres = one of the three pair-partitions of the slots;
alive sets of size 2 or 4); b = 1 ⟹ k = (1, ω, ω², 0), a bijection
(alive sets of size 3, any dead slot). The same computation drives
every fibre-type entry in the §12 tables.

### 10.4 The chord-slope lemma and hyperbolic quadruples

**Lemma (chord slope).** Let u, k: slots → F₄ with u bijective, fix a
slot z, and consider g(s) = (u(s)+u(z))·(k(s)+k(z))⁻¹ on the three
slots s ≠ z (defined when k is injective off z's fibre). Then
g(s) = g(s′) iff the three points (u(s), k(s)), (u(s′), k(s′)),
(u(z), k(z)) of AG(2, F₄) are collinear. In particular, if no three of
the four points (u(s), k(s)) are collinear, g is injective for every z.

**Lemma (hyperbolic quadruple).** For c ∈ F₄ˣ, the four points
H_c = {(t, c·t⁻¹) : t ∈ F₄ˣ} ∪ {(0,0)} have no three collinear: a line
through the origin v = λu meets the hyperbola where λu² = c, i.e. in
exactly one point (squaring is bijective); a line v = λu + c′ with
c′ ≠ 0 meets it where λu² + c′u + c = 0, at most twice. Moreover every
chord of H_c satisfies Δu·Δv = c. ∎

The deepest slope case of the §11 walk uses exactly one instance:
(m, m + ωθ) is the quadruple {(ω²,1), (ω,ω), (1,ω²), (0,0)} = H_{ω²}
(the four products m·(m+ωθ) are ω², ω², ω², 0).

### 10.5 Cost-preserving moves and the standard form

The block cost is invariant under (each one line, machine check W1):

1. **slot relabelings** applied simultaneously to all components and V₀
   (the cost is a sum over slots);
2. **translation scalings** (v_conf, v₃, v₄) ↦ (s₂v₂, s₃v₃, s₄v₄) with
   s₂² = s₃s₄ (the nine cell symmetries of the M-table); the conf line
   is scale-invariant;
3. **Frobenius** on all values (M-table symmetry); and M₂(v₀, ·, ·, v₄)
   = M₁(v₀, ·, ·, v₄²), so an R block is an M₁-type (L-type) problem
   after Frobenius on its comp-4 values.

**Standard form.** S(a, b) := the v₀-free block problem with conf line
⟨m⟩, v₃ = am + c₃, v₄ = bm + ωθ + c₄ (c₃, c₄ free). Then:

    L(24a) at (a₃,a₄) = S(a₃, a₄)          L(24b) = S(a₄, a₃)
    R(24a) at (a₃,a₄) ≅ S(a₃, a₄²)         R(24b) ≅ S(a₄², a₃)

For L(24a) this is the definition (κ₃L = 0, κ₄L = ωθ). For L(24b)
use the v₃ ↔ v₄ symmetry of T_L. For R(24a): apply Frobenius to comp 4
(move 3): (m′; a₃m′; a₄²m′ + θ, since θ² = θ and (ω²a₄m)² = a₄²m′);
apply the slot swap x↔y (move 1): (m; a₃m; a₄²m + θ̃); apply the slot
map σ induced by m̃ ↦ ω²m̃ (move 1; it sends θ̃ ↦ θ and m ↦ ω²m + 1);
finally scale by (ω, ω, ω) (move 2). R(24b) mirrors. ∎

### 10.6 The achiever-structure lemma

Fix an orbit and a spine cell. For shared (V₀, γ) let min_L(V₀, γ),
min_R(V₀, γ) be the per-block linked minima (over the block's own
knobs: conf point on its line, c₃, and the free side of its slot
minimizations). By §10.2 both minima ≡ |V₀| (mod 2), so their sum is
even. The cell value is m(cell) = min over (V₀, γ) of the sum.

**Lemma.** Suppose m(cell) ≥ 10 for every cell of the orbit. Then a
weight-10 coset element must sit at some cell with a configuration of
cost exactly 10, every slot at its M-value, free sides in the per-slot
argmin sets, and both ρ-links satisfied; and the set of cost-10
configurations is exactly

    ⋃ {(V₀,γ) : min_L + min_R = 10}  Argmin_L(V₀,γ) × Argmin_R(V₀,γ).

*Proof.* Weight 10 with cost ≥ 10 forces slot-exactness (cost = weight
means every layer is a minimum-weight layer for its slot data). A
cost-10 pair (cost_L, cost_R) with cost_i ≥ min_i and
min_L + min_R ≥ 10 forces cost_i = min_i and min_L + min_R = 10. ∎

So §12 must produce, per cell: (i) min_L + min_R ≥ 10 for all (V₀, γ)
(the **cost-8 kill**; by parity only the splits (4,4), (3,5), (5,3)
can occur, given the §12 floors min ≥ 3), and (ii) the **loci**
{(V₀,γ) : min_L + min_R = 10} with their argmins — the achiever lists.
§13 then kills every achiever against the ρ-links.

## 11. O1 on the wt-24 orbits: the standard-form walk

**Theorem (wt-24 closure).** S(a, b) ≥ 6 for all (a, b) ∈ F₄², in the
v₀-free cost. Hence by §10.5 all four wt-24 block tables are ≥ 6
everywhere, and since the v₀-free cost lower-bounds every fixed-V₀
cost, every wt-24 spine cell has linked value ≥ 6 + 6 = 12:
**(M-im) holds on the six wt-24 Smith classes.**

*Proof.* Write the conf value as v₂ = pm + c₂ (dead: p = c₂ = 0; full
constant: p = 0 ≠ c₂; co-point at z₂: p ≠ 0, v₂ = p(m + m(z₂))). Comp
3: dead (a = c₃ = 0), full (a = 0 ≠ c₃), or co-point at z₃ (a ≠ 0).
Comp 4: alive set S₄ with |S₄| ∈ {2, 4} (b ≠ 1, double-paired; v₄ is
constant on S₄ when |S₄| = 2 and two-valued, constant on the pairs,
when |S₄| = 4) or |S₄| = 3 with v₄ injective on S₄ (b = 1, dead slot
z₄ free). Costs per slot: (0, 3, 2, 1/3) by alive count, cheap ⟺
T = v₂²(v₃v₄)⁻¹ = 1. The walk (bucket minima in brackets are the
machine-exact values; the derivations give the ≥ 6 bound):

**A. a = 0.**
- A1 (3 dead, conf dead): cost = 3|S₄| ≥ 6. [6/9/12]
- A2 (3 dead, conf co-point): z₂ ∉ S₄ and |S₄| = 2: 0 + 2+2 + 3 = 7;
  z₂ ∈ S₄, |S₄| = 2: 3 + 2 + 3+3 = 11; |S₄| = 3: z₄ = z₂: three
  2-alive slots and a dead z₂: 6; z₄ ≠ z₂: 3 + 3 + 2+2 = 10;
  |S₄| = 4: 3 + 2+2+2 = 9. [7/6/9]
- A3 (3 dead, conf full) and A4 (3 full, conf dead): two constants,
  one of them everywhere-alive: cost = 2|S₄| + 3(4−|S₄|) = 12 − |S₄|
  ≥ 8. [10/9/8 each]
- A5 (3 full, conf co-point z₂): |S₄| = 2: z₂ ∈ S₄: 2 + (≥1) + 2+2 ≥ 7;
  z₂ ∉ S₄: T = p²(m+m(z₂))²(c₃v₄)⁻¹ has injective numerator and
  constant denominator on S₄, so ≤ 1 cheap: 3 + 1+3 + 2 = 9.
  |S₄| = 3: z₄ = z₂: 3 + three 3-alive ≥ 3 + 1+1+1 = 6; z₄ ≠ z₂:
  2 + 2 + 1+1 = 6. |S₄| = 4: v₄ two-valued and (m+m(z₂))² injective ⟹
  ≤ 1 cheap per v₄-pair, ≤ 2 total: 2 + 1+1+3 = 7. [7/6/7]
- A6 (3 full, conf full): |S₄| = 2: v₄ constant on S₄, so both
  S₄-slots can satisfy c₂² = c₃v₄: 1+1 + 2+2 = 6 (tight); |S₄| = 3:
  v₄ injective ⟹ ≤ 1 cheap: 1+3+3 + 2 = 9; |S₄| = 4: v₄ two-valued ⟹
  ≤ 2 cheap: 1+1+3+3 = 8. [6/9/8]

**B. a ≠ 0** (comp 3 co-point at z₃, v₃ = a(m + m(z₃))).
- B1 (conf dead): b = 1: z₄ = z₃ gives three 2-alive slots: 6; else
  3+3+2+2 = 10. b ≠ 1: |S₄| = 2: z₃ ∉ S₄: 0 + 2+2 + 3 = 7 (z₃ ∈ S₄:
  11); |S₄| = 4: 3 + 2+2+2 = 9. [6; 7/9]
- B2 (conf full): b = 1: z₄ = z₃: 3 + (three 3-alive ≥ 1+1+1) = 6;
  z₄ ≠ z₃: 2+2+1+1 = 6. b ≠ 1: |S₄| = 2: z₃ ∈ S₄: 2 + ≥1 + 2+2 ≥ 7;
  z₃ ∉ S₄: T = c₂²(v₃v₄)⁻¹ with v₃ injective, v₄ constant on S₄: ≤ 1
  cheap: 3 + 1+3 + 2 = 9. |S₄| = 4: v₃v₄ injective on each v₄-pair: ≤2
  cheap: 2 + 1+1+3 = 7. [6; 7/7]
- B3 (conf co-point z₂, b ≠ 1): z₂ = z₃ =: z: the conf and comp-3
  values are **proportional** (both co-points of the m-line at z), so
  T = (p²/a)(m+m(z))·v₄⁻¹; |S₄| = 2, z ∉ S₄: injective over constant
  on S₄: ≤ 1 cheap: 0 + 1+3 + 2 = 6 (tight); z ∈ S₄: 3 + ≥1 + 2+2 ≥ 8;
  |S₄| = 4: ≤ 1 cheap per v₄-pair: 3 + 1+1+3 = 8. z₂ ≠ z₃:
  |S₄| = 2: each of S₄ ⊇, ⊉ {z₂, z₃} cases gives ≥ 8 (two 2-alive
  slots cost 4 and either two 1-alive slots or a 3-alive pair join);
  |S₄| = 4: 2 + 2 + 1+1 = 6. [6/8; 8/6]
- B4 (conf co-point, b = 1): z₂ = z₃ = z₄ =: z: all of ¬z is 3-alive
  and z is free; cheapness reads p²(m(s)+m(z))² = a(m(s)+m(z))·v₄(s),
  i.e. (m(s)+m(z))·(k₄(s)+k₄(z))⁻¹ = a·p⁻², a level condition on the
  chord slope of the quadruple (m, k₄) = (m, m+ωθ) = H_{ω²} (§10.4):
  no three collinear ⟹ ≤ 1 cheap: 0 + 1+3+3 = 7. Other alignments:
  two of {z₂, z₃, z₄} equal: the doubled slot is ≤ 1-alive (cost ≥ 3
  if v₀-free cost 3 — e.g. z₂ = z₃ ≠ z₄: z costs 3 — or the third
  dead slot costs 2) and at most two 3-alive slots remain: ≥ 7 in each
  of the three patterns; all distinct: 2+2+2 + ≥1 = 7. [7/7/9/9/7]

Every bucket is ≥ 6. ∎

The 24-row bucket table with its exact minima is Appendix C.1; the
recheck script certifies each row and the equality of the four wt-24
block tables with the S-reindexings.

## 12. The wt-16/18 orbits: locus rules and the per-cell tables

Here the unlinked block floors are 3–5 and the linkage (shared V₀ and
γ) carries the floor to 10. We produce, per orbit and cell, the
function (V₀, γ) ↦ (min_L, min_R) far enough to certify the §10.6
requirements. The locus rules:

**R1 (zero slot).** A slot costs 0 iff v₀ = 0 and all three constrained
components vanish there.

**R2 (dead-pair rigidity).** Two zero slots {s, s′} force the conf
component ≡ 0 (a nonzero point of the conf line vanishes at ≤ 1 slot)
and force {s, s′} inside a single fibre of the comp-3 AND comp-4
directions. Given the directions' fibre tables (§10.3), this pins the
spine and the constants (hence γ) up to the listed fibre choices.
Three zero slots additionally force v₃ ≡ 0 on them, i.e. a fibre of
size ≥ 3 in the comp-3 direction — available only where comp 3 is
conf-parallel and the spine kills it (the wt-18a row a₃ = 1), with a
3+1 fibre of k₄ carrying the rest.

**R3 (δ-slot).** A v₀ = 1 slot costs 1 iff all three components are
alive and T = 1 there; the conf scale p enters T quadratically on L
(linearly on R), so matching two δ-slots (or a δ-slot and a 3-alive
cheap slot) against one p is one consistency equation in F₄, solvable
or not by inspection.

**R4 (cost-2 slot).** A v₀ = 0 slot costs 2 iff exactly two components
are alive, or all three with T = 1.

**R5 (shapes).** By parity the per-block slot-cost multisets at cost
3, 4, 5 are: cost 3: {3,0,0,0}, {1,2,0,0} (|V₀| = 1), {1,1,1,0}
(|V₀| = 3); cost 4: {4,0,0,0}, {2,2,0,0} (|V₀| = 0), {1,1,2,0},
{1,3,0,0} (|V₀| = 2), {1,1,1,1} (|V₀| = 4); cost 5: {1,2,2,0},
{1,4,0,0}, {3,2,0,0} (|V₀| = 1), {1,1,3,0}, {1,1,1,2} (|V₀| = 3).

Each locus table row below is derived by: choose the shape (R5), apply
R1–R4 to pin the configuration data, and check the F₄ consistency
equations. We work one cell per orbit in full; the remaining rows are
the same finite procedure (minutes per cell by hand), and every row is
machine-certified (Appendix D).

### 12.1 wt-16

L-frame: conf ⟨m⟩; v₃ = a₃m + ωθ + c₃; v₄ = a₄m + ωθ + c₄,
d₄L = ωγ + ω. R-frame (after Frobenius on comp 4): conf ⟨m′⟩;
v₃ = a₃m′ + θ + c₃; ṽ₄ = a₄²m′ + θ + c₄. Directions (§10.3): k₃ and k₄
are double-paired for spine value in {0, ω, ω²} and bijective at 1 — on
L the pairings are {e,y|x,xy} at 0, {e,x|y,xy} at ω, {e,xy|x,y} at ω²;
on R (θ-offset against m′) the pairings at ω and ω² are exchanged.

**Worked cell (ω², ω²), the (4,6) locus.** Cost-4 L-shapes: {2,2,0,0}
needs a dead pair: by R2, conf ≡ 0 and the dead pair lies in a common
fibre of k₃ = ω²m + ωθ and k₄ = ω²m + ωθ — equal directions with
pairing {e,xy | x,y} (pair-ratio ω² at a = ω²); both fibres are
available: dead pair {e, xy} pins c₃ = c₄ = k(e) and d₄L = k₄(e) =
ω²m(e) + ωθ(e) = ω + ω = 0, i.e. γ = ω²·(0 + ω)·ω⁻¹·… solving
ωγ + ω = 0 gives γ = 1; dead pair {x, y} pins d₄L = k₄(x) = 1, γ = ω.
The two live slots then carry v₃ = v₄ = the pair-gap value, two
components alive each: cost 2 + 2 with V₀ = 0000: **min_L = 4 at
(V₀, γ) ∈ {(0000, 1), (0000, ω)}**, argmin unique. The |V₀| = 4 all-δ
shape {1,1,1,1} also solves here: with k₃ = k₄ the δ-condition
T ≡ 1 reads p²(m-line)² = v₃v₄ = v₃², one equation per slot whose
consistency across all four slots holds exactly at γ ∈ {0, ω²}
(V₀ = 1111). The |V₀| = 2 shapes and {4,0,0,0} fail (R3's equations
are overdetermined with k₃ = k₄). The R block at each of these
(V₀, γ) has min_R = 6, so the cell contributes (4,6) achievers at the
four loci 1111@0, 0000@1, 0000@ω, 1111@ω², with |Argmin_R| = 2 each —
matching the table.

**Worked cell (ω, 1), a (5,5) locus.** Take V₀ = δ_{xy}, γ = 0 (so
d₄L = ω). Shape {1,2,2,0}: the zero slot s₀ must satisfy
k₄(s₀) = d₄L; k₄ = m + ωθ = (1, ω, ω², 0) (bijective, a₄ = 1):
s₀ = x. By R1, conf is the co-point p(m + m(x)); v₃'s direction
k₃ = ωm + ωθ = (ω², ω², 0, 0) is double-paired {e,x | y,xy}, so v₃
dies on the whole pair {e, x}: slot e has exactly conf and v₄ alive —
cost 2 ✓. Slots y, xy have all three alive; the δ-slot is xy (v₀ = 1)
and y needs T = 1 (R4). Both give one equation for p²:
at xy: p²·ω² = v₃(xy)·v₄(xy) = ω²·ω, so p² = ω; at y:
p²·(ω²)² = ω²·1, so p² = ω — **consistent**, p = ω². The
configuration exists and is unique: a (5,5) locus with singleton
argmins. The other three (V₀, γ) = (δ_s, ·) loci are its images under
the slot translations (the stabilizer of ζ has order 4 and acts by the
three nonzero slot translations, which permute the δ-positions and
shift γ accordingly).

The full table (every cell, both blocks; certified):

- **floor-10 cells** (ω,1), (ω,ω²), (ω²,1), (ω²,ω²): loci and
  achiever counts as in Appendix C.2 — per cell four (5,5) loci with
  singleton argmins and four (6,4)- or (4,6)-loci with two argmin pairs
  each: 4 + 8 = 12 achievers per cell, 48 in total.
- **all other cells**: the (4,4)-kill is the disjointness of the L4 and
  R4 loci visible in Appendix C.2's locus columns — at every cell
  either one side is empty, or the V₀-sets are disjoint (e.g. cell
  (ω,1): V₀(L4) ⊂ {0011, 1100} vs V₀(R4) ⊂ {1001, 0110}), or the V₀'s
  agree and the γ-sets are complementary (e.g. cell (0,0): L4 at
  (0000, {0,1}) ∪ (1111, {ω,ω²}), R4 at (1111, {0,1}) ∪ (0000,
  {ω,ω²})).
- **L3 = R3 = ∅ at every wt-16 cell**, fully derived: the |V₀| = 1
  shapes {1,2,0,0} and {3,0,0,0} need ≥ 2 zero slots, killing the conf
  component (R2) — the former then has no alive conf at its δ-slot,
  and the latter needs v₃ ≡ 0 on three slots, impossible since
  κ₃L = ωθ is non-constant and k₃ has no fibre of size ≥ 3. The
  |V₀| = 3 shape {1,1,1,0} (one zero slot s₀, three δ-slots) dies in
  three steps: at a₃ ≠ 1 the comp-3 direction is double-paired, so
  v₃(s₀) = 0 kills v₃ on s₀'s partner slot, contradicting that
  δ-slot; at (1, a₄) with a₄ ≠ 1 the same argument applies to comp 4;
  and at (1,1), k₃ = k₄ = m + ωθ, so the triple-δ condition says
  (m + m(s₀))·(k₃ + k₃(s₀))⁻¹ is constant on ¬s₀ — three points of
  (m, m+ωθ) = H_{ω²} collinear, contradicting §10.4. With parity,
  every (V₀, γ) has min_L + min_R ≥ 10: **m(cell) ≥ 10 for all 16
  cells, = 10 exactly at the four floor-10 cells.**

### 12.2 wt-18a

L-frame: v₃ = (1+a₃)m + c₃ (κ₃L = m **is** the labeling: comp 3 is
conf-parallel, dead/full at a₃ = 1, co-point otherwise); v₄ has
direction k₄ = (0,ω,ω²,0) + a₄m with fibre types 2+1+1 / 2+1+1 / 3+1 /
2+1+1 over a₄ = 0, 1, ω, ω²; d₄L = ωγ + ω². R-frame: v₃ = (1+a₃)m′;
ṽ₄ direction ω(1,1,1,0) + a₄²m′ (types 3+1 at a₄ = 0, else 2+1+1).
The translation stabilizer of ζ has order 3 and acts on the spine by
a₃ ↦ ω(1+a₃)+1-type affine maps fixing a₄: the cells (a₃, a₄) with
1+a₃ ≠ 0 form orbits of three per a₄-column, the row a₃ = 1 is fixed.
So six cell classes: (ã₃ ≠ 0, a₄) for a₄ ∈ F₄, and (1, 0), (1, ω)
(the cells (1, 1), (1, ω²) have m = 12 with empty low loci).

Worked class rep (0, 1), |V₀| = 3 loci: shape {1,1,1,2} with the
δ-equations of R3 solvable at exactly (V₀, γ) ∈ {(1011, 1),
(1101, ω²)} on the (5,5) side, plus the (6,4) locus (1100, ω²); the
class transports to (ω, 1) and (ω², 1) verbatim (the stabilizer fixes
γ and a₄ and permutes nothing else in the table). The isolated row
a₃ = 1 kills comp 3 entirely (dead or full): at (1, 0) the surviving
loci are (6,4) at (0000, 0) and (7,3) at (0001, 0); at (1, ω) the
mirror (3,7)/(4,6). Appendix C.3 lists all 14 floor-10 cells: 48
achievers (12 per a₄ ∈ {1, ω²} column-orbit, 6 per a₄ ∈ {0, ω}
column-orbit, 6 + 6 at the two fixed cells).

The cost-8 kill: all L4/R4/L3/R3 loci are singletons (Appendix C.3),
pairwise disjoint in (V₀, γ) at every cell; the only L3/R3 sites are
(1, ω)/(1, 0) where the partner block's minimum at that (V₀, γ) is 7.

### 12.3 wt-18b

L-frame: κ₃L = (1,ω,ω²,0) (bijective offset), k₃ = κ₃L + a₃m with
fibre types 1+1+1+1 / 2+2 / 2+2 / 2+2 over a₃ = 0, 1, ω, ω² (pair-ratio
table as in §10.3); κ₄L = (ω,ω,1,0), k₄ types 2+1+1 / 3+1 / 2+1+1 /
2+1+1; d₄L = ωγ + 1. R-frame: κ₃R = ω²m (in the m′-frame a fixed
non-affine offset), κ̃₄R = (ω²,ω,ω²,0). The translation stabilizer is
trivial, but the swap-type symmetry of the orbit (translation∘swap
fixes ζ) exchanges the blocks and pairs the cells: each locus table at
(a₃, a₄) mirrors a partner cell's with L and R exchanged (visible in
Appendix C.4: e.g. (0,1) carries (3,7) + (4,6) and (0,ω²) carries
(7,3) + (6,4) with the same V₀'s). 12 floor-10 cells, 22 achievers;
the two L3/R3 sites ((0,1) and (0,ω²), V₀ = 0111, the unique |V₀| = 3
cost-3 shape {1,1,1,0} the frame admits) have partner minima 7.

### 12.4 Summary

Per-cell locus tables: Appendix C.2–C.4. Together with §11:

> **C-table floor.** Every Smith-coset element has weight ≥ 12 on the
> wt-24 orbits and ≥ 10 on wt-16/18a/18b; per (V₀, γ) the block minima
> sum to ≥ 10 with equality exactly on the listed loci; the cost-10
> configurations are exactly the 48 + 48 + 22 = 118 achievers of
> Appendix C.5.

## 13. The ρ-link kills: no weight-10 elements

By §10.6, a weight-10 element realizes one of the 118 achievers with
its free sides in the per-slot argmin sets and **both** links
V₁R = ρ₁·V₁L, V₂L = ρ₂·V₂R (§9.4). For an achiever, V₁R and V₂L are
part of the configuration; the links demand V₁L ∈ ρ₁⁻¹(V₁R) (a coset
of ker ρ₁ = F₄Â₁ ⊕ F₄XY, 16 elements; nonempty since V₁R ∈ im ρ₁) to
meet the product of the four argmin sets Argmin₁(s) ⊆ F₄, and mirror
for V₂R. The argmin sets are read off the value table: at a slot of
cost c, Argmin₁(s) = {v₁ : the layer with values (v₀; v₁, v₂, v₃, v₄)
has weight c} — almost always a singleton (a δ-point pins all five
values; a weight-2 slot pins the values up to its one dead component).

**Worked kill (the wt-16 (5,5) family head, §12.1's worked cell).**
At cell (ω,1), V₀ = δ_{xy} = 0001, γ = 0: the achiever's L data is
V₂L = (ω²,0,ω,1), V₃L = (0,0,ω²,ω²), V₄L = (ω²,0,1,ω) with slot costs
[2,0,2,1]; the per-slot comp-1 argmin sets are the **singletons**
({1},{0},{0},{ω²}) — at the zero slot the empty layer forces v₁ = 0,
at the δ-slot the δ-point pins v₁ = ψ₁(its cell), and at the weight-2
slots the pair's one dead component is not comp 1. So link 1 holds iff
the single convolution ρ₁·(1,0,0,ω²) equals V₁R = (ω²,ω,0,1).
Computing in the X, Y basis: (1,0,0,ω²) = ω·1 + ω²X + ω²Y + ω²XY, and
(X + ωY + ω²XY)·(ω + ω²X + ω²Y + ω²XY) = ωX + ω²Y + ω²XY, with slot
values (ω, 1, 0, ω²) ≠ (ω², ω, 0, 1): **link 1 fails.** The mirror
computation kills link 2 as well. The same one-convolution check,
transported by the orbit symmetries of §12 across each family, kills
all achievers; the full table is Appendix C.5: **116 achievers fail
both links, 2 (wt-18b) fail exactly one — all 118 fail.** ∎

With §§11–12 (no cost ≤ 9 anywhere, no link-compatible cost-10) and
evenness (§9.3): **no Smith-coset element has weight < 12.** Transport
(§9.3) extends the bound from the five representatives to all 63
nonzero classes:

> **(M-im).** Every base 1-cycle in a nonzero imΔ class has weight
> ≥ 12.

## 14. Theorem D: assembly and status

**Proof of Theorem D.** Lower bound: let v be a nontrivial cover
Z-logical. If [p(v)] = 0: |v| ≥ 12 by Theorem C. Else p(v) ≠ 0 and by
(R) (§9.1) [p(v)] ∈ im Δ ∖ 0, so p(v) lies in a coset C(ζ), ζ ≠ 0,
and |v| ≥ |p(v)| ≥ 12 by (M-im). d_X = d_Z by Lemma 2.1. Upper bound:
u\* (§4.6) is a weight-6 base logical with nonzero seam flux (a finite
overlap count, §6.5/Entry 17), so [u\*] ∉ im Δ = ker τ_\*; hence
τ(u\*) = (u\*, u\*) is a weight-12 cover cycle that is not a boundary:
d(gross) = 12. **∎**

**Epistemic status.** Every reduction (Part I; §§9–10; the §11 walk;
the §12 rules; §13's lemma) is hand-proven. The finite case content is:
the M-table rule (§10.2, hand-proven with an 18-orbit table), the §11
bucket table (33 buckets, each derived in 1–3 lines), the §12 per-cell
locus tables (Appendix C.2–C.4; each row a minutes-long application of
R1–R5), and the §13 kill table (118 one-line F₄ evaluations in
families). This meets the program's §1 bar at the same grade as Part
I's §6.3 classification: analytic reductions with surveyable case
tables, machine-verified as confirmation only. This honestly restores
the headline **d(gross) = 12, fully analytic** (Entry 27's two
machine-certified residues are discharged: the wt-24 closure by the
§11 walk, the achiever-list completeness by §10.6 + §12).

---

## Appendix C. Part-II tables

### C.1 The S(a,b) bucket table (§11)

Machine-exact bucket minima (v₀-free costs; all ≥ 6):

| bucket | min | | bucket | min |
|---|---|---|---|---|
| A1 \|S₄\|=2/3/4 | 6/9/12 | | B1 b=1 | 6 |
| A2 \|S₄\|=2/3/4 | 7/6/9 | | B1 b≠1, \|S₄\|=2/4 | 7/9 |
| A3 \|S₄\|=2/3/4 | 10/9/8 | | B2 b=1 | 6 |
| A4 \|S₄\|=2/3/4 | 10/9/8 | | B2 b≠1, \|S₄\|=2/4 | 7/7 |
| A5 \|S₄\|=2/3/4 | 7/6/7 | | B3 z₂=z₃, \|S₄\|=2/4 | 6/8 |
| A6 \|S₄\|=2/3/4 | 6/9/8 | | B3 z₂≠z₃, \|S₄\|=2/4 | 8/6 |
| | | | B4 z₂=z₃=z₄ / z₂=z₃ / z₂=z₄ / z₃=z₄ / distinct | 7/7/9/9/7 |

S-table: S(a,b) = 6 for all 16 (a,b). Block tables: L(24a) = S(a₃,a₄),
L(24b) = S(a₄,a₃), R(24a) = S(a₃,a₄²), R(24b) = S(a₄²,a₃) (as 4×4
tables, after the §10.5 moves).

### C.2 wt-16 locus tables (V₀ as a bit-string over (e,x,y,xy); γ ∈ F₄)

Floor-10 cells — achiever loci:

| cell | (5,5) loci (argmins 1×1) | (4,6)/(6,4) loci (argmins 1×2 / 2×1) |
|---|---|---|
| (ω,1)   | 0001@0, 0100@1, 0010@ω, 1000@ω² | (6,4): 1001@0, 0110@1, 0110@ω, 1001@ω² |
| (ω,ω²)  | 0111@0, 1110@0, 1011@ω², 1101@ω² | (6,4): 1111@0, 0000@1, 0000@ω, 1111@ω² |
| (ω²,1)  | 1000@0, 0010@1, 0100@ω, 0001@ω² | (4,6): 1001@0, 0110@1, 0110@ω, 1001@ω² |
| (ω²,ω²) | 1011@0, 1101@0, 0111@ω², 1110@ω² | (4,6): 1111@0, 0000@1, 0000@ω, 1111@ω² |

12 achievers per cell; 48 total. Cost-4 loci at the other cells (the
(4,4) disjointness): L4 and R4 as listed by the recheck (K4 layout);
at every cell L4 ∩ R4 = ∅, L3 = R3 = ∅.

### C.3 wt-18a locus tables

Cell classes under the order-3 stabilizer (rows ã₃ = 1+a₃ ≠ 0
transport; row a₃ = 1 fixed):

| class | loci |
|---|---|
| (ã₃≠0, 0)  | (4,6): 0110@ω |
| (ã₃≠0, 1)  | (5,5): 1011@1, 1101@ω²; (6,4): 1100@ω² |
| (ã₃≠0, ω)  | (6,4): 0110@ω² |
| (ã₃≠0, ω²) | (4,6): 1100@ω; (5,5): 1011@0, 1101@ω |
| (1, 0)     | (6,4): 0000@0; (7,3): 0001@0 |
| (1, ω)     | (3,7): 0001@1; (4,6): 0000@1 |

Achiever counts: 2 per (ã₃≠0, 0)- and (ã₃≠0, ω)-cell, 4 per
(ã₃≠0, 1)- and (ã₃≠0, ω²)-cell, 6 at each fixed cell: 3·(2+4+2+4) +
6 + 6 = 48. Cells (1,1), (1,ω²): m = 12, empty loci.

### C.4 wt-18b locus tables

| cell | loci | | swap-partner | loci |
|---|---|---|---|---|
| (0,1)  | (3,7): 0111@0; (4,6): 0101@0 | | (0,ω²) | (6,4): 0101@ω; (7,3): 0111@ω |
| (1,ω)  | (4,6): 0000@1 | | (1,0)  | (6,4): 0000@ω² |
| (1,ω²) | (4,6): 1010@1; (5,5): 0010@1 | | (1,1)  | (5,5): 0010@ω²; (6,4): 1010@ω² |
| (ω,0)  | (4,6): 1001@0; (5,5): 1110@1; (6,4): 1100@1 | | (ω²,ω) | (4,6): 1100@ω²; (5,5): 1110@ω²; (6,4): 1001@ω |
| (ω,1)  | (5,5): 1011@ω | | (ω²,ω²) | (5,5): 1011@0 |
| (ω²,0) | (4,6): 0000@ω; (5,5): 0001@ω | | (ω,ω)  | (5,5): 0001@0; (6,4): 0000@0 |

(The swap symmetry of the orbit pairs each left row with its right
partner, exchanging the (cL, cR) splits.) Achiever count
2+2+1+1+2+2+3+3+1+1+2+2 = 22.

### C.5 The 118 kills

Every achiever fails at least one ρ-link; 116 fail both, the two
exceptions (wt-18b, cells (ω,ω) and (ω²,0), the (5,5) achievers) fail
exactly one. Worked family heads: §13; full table: the recheck script
(per achiever, the argmin product and the 16-element link coset are
disjoint — one F₄ evaluation per slot).

## Appendix D. Verification map (Part II; confirmation only)

| claim | script / check |
|---|---|
| frame: labelings, lines, ties, offsets, fibre types | `a3_a4ext_recheck.py` F1–F6 |
| S(a,b) ≡ 6; the four wt-24 block tables = S-reindexings | W1–W2 |
| the §11 bucket minima (33 buckets, all ≥ 6) | W3 |
| per-cell linked floors: ≥ 10 / ≥ 12; m-values | K1 |
| per-cell loci (C.2–C.4) and argmin counts | K2 |
| the 118 achievers and the link kills (116 both / 2 one) | K3 |
| achiever-structure lemma instance check | K4 |
| upstream: Entries 16–26 chain re-verified | `a3_adv27_recheck.py` (75 checks) |
| original machine sweeps (superseded as evidence, kept as cross-checks) | `a3_mim_*.py` |
