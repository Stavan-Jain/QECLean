# Literature notes: gross code distance bounds (Stage-2 hypothesis dive)

Compiled 2026-05-22. Skim-depth: abstracts + key result sections of arXiv
preprints, plus reachable PDFs. Goal: enough prior-art coverage to pick a
first-approach direction.

## Primary target reference

### Bravyi-Cross-Gambetta-Maslov-Rall-Yoder, *Nature* 2024 (arXiv:2308.07915)

The IBM Gross-code paper. From the available secondary sources
(PMC mirror, postquantum overview, GitHub repo, scirate, semantic scholar):

- **Group**: `Z_12 × Z_6`, so `n = 2·ℓ·m = 2·12·6 = 144`.
- **Polynomials** (the [[144,12,12]] entry of Extended Data Table 1):
  - `A(x, y) = x^3 + y + y^2`
  - `B(x, y) = y^3 + x + x^2`
  where `x^12 = y^6 = 1` and `xy = yx`.
- **Check matrices**: `H_X = [A | B]`, `H_Z = [B^T | A^T]` (each block of
  size `ℓm × ℓm = 72 × 72`). Total stabilizer weight `Δ = 6`.
- **Distance certification**: "Code distance was computed by the mixed
  integer programming approach." Per the PMC mirror, `d = 12` is the
  value confirmed by MIP solver runs; no closed-form analytical lower
  bound is given. The "circuit-level distance" is `d_circ ≤ 10`,
  separately bounded.

**Implication for us**: there is no analytical lower-bound proof of
`d ≥ 12` in the literature for this specific polynomial pair. Any Lean
formalization of `d ≥ 12` would be the first published analytical proof.
A loose analytical bound (`d ≥ 4` or `d ≥ 6` or `d ≥ 8`) would still be
the first analytical bound of any kind.

## Classical algebraic-bound machinery

### Camion 1971 (MRC Tech Report #1059, "Abelian Codes")

The originator. Extended the BCH bound from cyclic codes (`F_q[Z_n]`) to
abelian codes (`F_q[G]` for finite abelian `G`). Key concept:
**apparent distance** of an abelian code, defined via consecutive-zero
patterns in the Discrete Fourier Transform over `G`.

The apparent distance is a **lower bound** on the true minimum distance,
analogous to how the cyclic BCH bound is a lower bound. It's not tight
in general.

### Bernal, Bueno-Carreño, Simón ~2013-2014 (CACTC 2014, "A notion of
multivariate BCH bounds and codes")
PDF at `singacom.uva.es/~edgar/cactc2014/files/DBueno.pdf`.

- Algorithm for computing the apparent distance of multivariate abelian
  codes via **hypermatrix manipulations**.
- For 2D abelian codes (over `Z_ℓ × Z_m`), the algorithm runs in linear
  complexity in the appropriate measure.
- Defines a notion of **BCH multivariate code**: an abelian code whose
  minimum distance equals its apparent distance (the bound is tight).
- Gives constructions of abelian codes that multiply the dimension of a
  given cyclic code while preserving the BCH bound.

### Bernal-Simón et al. 2024 (arXiv:2402.03938, "Apparent Distance and
a Notion of BCH Multivariate Codes")

The modern IEEE TIT writeup of the above. **Best source for the formal
definitions and the proof that apparent distance lower-bounds true
distance.**

Headline:
- The apparent distance of an abelian code with respect to a set of
  bounds is defined via the discrete Fourier transform; the weight of
  codewords is related to that distance.
- Procedure works for multivariate cyclotomic / Reed-Solomon-style
  constructions, but the consecutive-zero analysis in `Z_ℓ × Z_m`
  doesn't yet incorporate the *quantum* CSS structure.

**Gap for us**: Camion theory is classical (`F_q[G]`-ideals as codes).
Lifting it to a quantum-CSS setting where the code is the kernel
quotient `ker H_X / im H_Z^T` is open. This is the "quantum extension"
described in the moonshot spec.

## Quantum BB code literature (post-2023)

### Lin-Pryadko 2023 (arXiv:2306.16400, "Quantum two-block group algebra codes")

The canonical 2BGA reference; subsumes BB codes as the abelian-2BGA case.

- Gives bounds for code parameters; explicit and in relation to other
  codes (lifted-product, hypergraph-product).
- States bounds without Fourier/character decomposition (per the
  abstract). Lower bounds are typically `d ≥ Ω(√n)` (sqrt scaling),
  loose for the gross-style numerically-optimized codes.

### Otjens 2025 (arXiv:2502.17052, "Existence and Characterisation of
Bivariate Bicycle Codes")

**Most relevant for us.** Algebraic characterization via the ring
structure of `F_2[Z_ℓ × Z_m] / (A, B)`.

- Distance `d = min{ ω_H(c) | c ∈ ker H_X \ im H_Z^T }` (operational
  definition; matches our `chainWeight` / `xChainOf` setup).
- **Upper bound** (Theorem 2.18): `d ≤ 2 √γ_D (√D + 4) n^(1 - 1/D)` where
  `D = Δ - 2`. For `Δ = 6`, `D = 4` gives `d ≤ O(n^{3/4})`, which is
  asymptotically bad. For the gross code `n = 144`, this gives a
  numerical upper bound around `d ≤ 130-ish` (not useful for our
  problem of *lower-bounding* `d`).
- **No closed-form lower bound**: the paper explicitly says no closed-
  form analytical formula relates `d` to the polynomial exponents.
- Approach uses polynomial-ideal theory + Gröbner bases + CRT
  decomposition. The CRT decomposition of `F_2[Z_ℓ × Z_m]` is essentially
  the algebraic side of the Fourier decomposition, so there's a bridge
  to Camion-style analysis.

### Cao et al. 2025 (arXiv:2503.04699, "Anyon Theory and Topological
Frustration of High-Efficiency Quantum LDPC Codes")

Uses **Bernstein-Khovanskii-Kushnirenko (BKK) theorem** on the Newton
polytope of the quotient `R/(A, B)` to compute the **logical dimension
`k`** of BB codes. Confirmed in our literature dive: BKK gives `k`, not
`d`.

- Connection to anyon theory via Koszul complex.
- Extending BKK to bound minimum Hamming weight (`d`) is *open*; the
  Newton polytope measures multiplicity of the quotient module, not its
  minimal-weight support.
- Lower-promise as a distance-bound approach, but useful for
  understanding the quotient-module structure.

### Cao-Sun 2025 (arXiv:2510.05211, "Self-dual bivariate bicycle codes
with transversal Clifford gates")

Self-dual BB codes; examples `[[160, 8, 16]]`, `[[120, 8, 12]]`. Uses
"twisted tori" to enhance code distance. Abstract gives no analytical
distance-bound theorem; the construction-distance pairs appear to be
verified numerically.

### Pesah et al. 2025 (arXiv:2511.13560, "Sequences of Bivariate Bicycle
Codes from Covering Graphs")

For an odd `h`-cover of a base `[[n, k, d]]` BB code:
- `k_h ≥ k`, `d_h ≤ h·d`, and (when `k_h = k`) `d_h ≥ d`.
- Proof technique: **chain-map between covering complexes**, induced
  projection/lifting maps on (co)homology. This is **directly compatible
  with our `Stabilizer/Homological/` framework**.
- Notes that the gross code is itself a cover of a smaller base BB
  code — but the paper does not give an analytical `d ≥ 12` for the
  gross code.

### Wang-Pryadko 2022 (arXiv:2203.17216, "Distance bounds for generalized
bicycle codes")

GB codes (1D cyclic case, abelian over `Z_n`). Upper bounds by mapping
to local codes in `D ≤ w − 1` dimensions. Lower existence bounds
`d ≥ Ω(√n)`. These are GB (single cyclic), not bivariate, but the
sqrt-scaling is the prototype for what we'd expect from a "naive"
algebraic argument.

## Synthesis

After this dive, the picture is:

1. **Camion's apparent distance** is the only well-established analytical
   lower-bound machinery for abelian codes. It has *not* been adapted to
   quantum CSS codes in the literature. The Otjens paper acknowledges
   no closed-form lower bound exists for BB codes (which is exactly the
   Camion-quantum-extension gap).

2. **For the gross code specifically**, a Camion-style apparent distance
   computation on `F_2[Z_12 × Z_6]` would give *some* `d ≥ d_app` lower
   bound. Heuristically (without computing) we expect `d_app` between
   `2` and `8` — possibly as low as `2` if the consecutive-zero pattern
   in the dual code is short.

3. **Lifted-product bounds** (Tillich-Zémor style; Lin-Pryadko et al.)
   give `Ω(√n)` ≈ `12-ish` for `n = 144`, but these are *asymptotic
   existence* bounds, not deterministic lower bounds for a specific
   polynomial pair. They typically require a *constituent* classical
   distance to be computed first, which for `A` and `B` over
   `Z_12 × Z_6` is itself a nontrivial computation.

4. **BKK / Newton polytope** gives `k = 12` analytically — this is a
   nice result but doesn't bound `d`. Extending to bound `d` is open.

5. **Covering-graph chain-map** (Pesah et al.) plugs into our existing
   `HomologicalCode` framework directly, but the bound it gives
   (`d_h ≥ d` for the base code's `d`) requires knowing `d` for a
   *base* code — which is precisely the same hard problem one level
   down.

**Choice for approach ordering** (most promise-to-cost first):

- **Approach A — Camion apparent-distance, classical first then CSS
  bridge** is the cleanest, has the most well-established mathematical
  infrastructure (1970s + 2010s), and would be the first formalization
  of its kind. The CSS bridge is the only novel piece.
- **Approach B — Lifted-product / Tillich-Zémor** is a fallback if A
  gives `d ≥ 2` and we want to compare. Likely *also* gives a weak
  bound for this specific code.
- **Approach C — Polynomial-ideal Gröbner basis on the quotient** is
  the highest-risk research direction (no prior art for distance
  bounding via this route), and would require building Gröbner basis
  infrastructure that doesn't exist in mathlib. Defer.

## Repo abstractions we'd build on

- `Stabilizer/Homological/Code.lean` — `HomologicalCode` struct, chains
  `C0`, `C1`, `C2`, `boundary1`, `boundary2`, `cycles`, `boundaries`,
  `H1`.
- `Stabilizer/Homological/CSS.lean` — `chainXOperator`, `chainZOperator`,
  bridges 1-chains to Pauli operators.
- `Stabilizer/Homological/Distance.lean` — `xChainOf`, `zChainOf`,
  `chainSupport`, `chainWeight`, `weight_ge_chainWeight_xChainOf`. **This
  is exactly the right abstraction layer** for a generic distance
  argument: we need to give a lower bound on `chainWeight c` for any
  `c ∈ ker ∂_1 \ im ∂_2`.
- `Stabilizer/Homological/LogicalCorrespondence.lean` — translates
  between Pauli logical operators and chain-level cycles.

## Repo abstractions we'd need to add

- `Stabilizer/GroupAlgebra/` — `F_2[G]` for finite abelian `G`:
  - `GroupAlgebra.lean` — the group algebra, multiplication, units.
  - `Fourier.lean` — DFT over `Z_ℓ × Z_m` (or generally `G`), characters,
    inversion formula.
  - `Maschke.lean` — Maschke's theorem for `gcd(|G|, char F) = 1`
    (note: for `F_2[Z_12 × Z_6]`, `char = 2` and `|G| = 72`, so the
    semisimple case fails — we need the **modular Maschke** /
    Jacobson-radical decomposition. *This is a real obstacle.*)
- `Stabilizer/Homological/AbelianCSS.lean` — abelian-symmetric CSS:
  given a `HomologicalCode` carrying an abelian group action commuting
  with the boundary maps, decompose `H_1` into character isotypic
  components.
- `Stabilizer/Codes/BB.lean` — concrete BB code construction for a given
  polynomial pair `(A, B) ∈ F_2[Z_ℓ × Z_m]^2`. The instance
  `grossCode : BBCode 12 6` then specializes to our target.
- `Stabilizer/Codes/Camion.lean` — apparent distance, consecutive-zero
  patterns, and the Camion-style lower bound theorem.

## Open question to surface for human review

The character-decomposition approach over `F_2[Z_12 × Z_6]` is
**modular** (characteristic 2 divides `72 = |G|`), so the usual
Maschke / DFT story doesn't directly apply. We'd need to work with
either:
1. The *radical* of `F_2[G]` and a corresponding non-semisimple
   decomposition, or
2. Lift to `Q[G]` or `F_q[G]` for `q = 2^k` with `gcd(q-1, 72) = 72`
   (so `q = 2^?` with `?` large enough — `q = 64` gives
   `gcd(63, 72) = 9`, not 72, so we'd need `q` with `72 | q-1`, e.g.
   `q = 73` if prime power, but we're in characteristic 2).

The right path is (1): work with `F_2[Z_12 × Z_6]` directly, use the
CRT decomposition `F_2[x] / (x^12 - 1) = ∏ F_2[x] / (irr_i)` (and
similarly in `y`), and analyze the bivariate quotient ring. This is
exactly what Otjens does — but for the dimension `k`, not the distance.
The **Camion apparent-distance recipe via this CRT decomposition is
where the open mathematical work lives.**
