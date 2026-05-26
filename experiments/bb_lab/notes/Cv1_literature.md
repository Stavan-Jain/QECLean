# C-v1 — Literature check for weight-aware Jacobson-radical filtration

Date: 2026-05-26.

This is the literature pass required by HANDOFF_C §6 before defining
`w_μ(A, O)`. The bar (HANDOFF §6a): a "novel to us" candidate must
survive a serious literature search, and prior art must be documented
even if it doesn't fully overlap.

## 1. The combination being checked

For a finite abelian group `G` with `2 | |G|`, write
`G = G_odd × G_2` (the 2-Sylow / odd-part factorization). The group
algebra factors as

  F₂[G] ≅ F₂[G_odd] ⊗ F₂[G_2] ≅ ∏_O R_O, where R_O = F_{2^|O|}[G_2]

(`O` ranges over Frobenius orbits on Ĝ_odd; this is exactly the
decomposition `algebraic_features.py` uses for `μ_O`). Each `R_O` is a
finite-dimensional **local** ring with maximal ideal `m_O` the
augmentation ideal of `F_{2^|O|}[G_2]`; its powers give the Loewy
filtration `R_O ⊃ m_O ⊃ m_O² ⊃ ⋯`.

The combination C-v1 wants to address:

> Per-orbit, per-Loewy-layer, Hamming-weight invariant of an element
> `A ∈ F₂[G]`, restricted to its annihilator inside `R_O`, in the
> presence of a non-trivial 2-Sylow.

Concretely: for each orbit `O` and depth `μ ≥ 1`, define some
F₂-subspace `V_{O,μ}(A) ⊂ F₂[G]` derived from `(A, O, μ)`, and set
`w_μ(A, O) := min{|f|_H : f ∈ V_{O,μ}(A), f ≠ 0}`.

The literature splits cleanly into two camps. C-v1 lives in the gap
between them.

## 2. Camp 1 — Radical powers as Reed-Muller-type codes

**Berman 1967** (Kibernetika 3(1), pp. 31–39) is the seed result:
binary Reed-Muller codes of length `2^m` are the radical powers of
`F₂[(Z/2)^m]` (the group algebra of the elementary abelian
2-group of order `2^m`). The radical `M = rad(F₂[(Z/2)^m])` is the
augmentation ideal; `M^μ` is the order-`(m - μ)` Reed-Muller code,
and the minimum weight of `M^μ` is `2^μ` (Delsarte–Goethals–MacWilliams).

**Charpin 1988** (Communications in Algebra 16) generalizes to
prime-field elementary abelian p-groups.

**Andriatahiny 2016 — [arXiv:1601.07633](https://arxiv.org/abs/1601.07633)**
("The Generalized Reed-Muller codes and the radical powers of a
modular algebra") gives a clean modern proof of Berman–Charpin and
extends to GRM codes over `F_q` (`q = p^r`). The setting:

> `A := F_q[X_1, …, X_m] / (X_1^q − 1, …, X_m^q − 1)`.
>
> A linear basis of `M^d` over `F_q` is the set of monomials
> `(X_1 − 1)^{i_1} ⋯ (X_m − 1)^{i_m}` with `i_1 + ⋯ + i_m ≥ d`.
> The minimum non-zero Hamming weight of `M^d` is determined via the
> Reed-Muller correspondence (the Delsarte-Goethals-MacWilliams
> formula).

**Andriatahiny–Rakotomalala 2016 —
[arXiv:1609.09531](https://arxiv.org/abs/1609.09531)**
extends Berman to `F_{p^r}[G]` where `G` is the additive group of a
Galois ring `GR(p^r, m)` of characteristic `p^r`. Theorem 3.5 gives
the Jennings basis of `F_{p^r}[F_{p^m}]` (an elementary abelian
p-group of rank m as an F_{p^r}-vector space) and identifies the
radical layers `M^t` with explicit ideals.

**Scope of Camp 1**:
- The group `G` is always an **elementary abelian p-group** in
  characteristic p (so `F_p[G]` is local — a single orbit, the
  trivial one).
- Or its scalar extension to `F_{p^r}`.
- For elementary abelian, there's no `G_odd × G_2` split — only the
  G_2-like factor, and `F_2[G] = R_{trivial orbit}` is a single local
  ring.
- The min-weight formula is for the **whole radical power**
  `M^μ ⊂ F₂[G]`, not for one orbit's component, and not constrained
  by a kernel condition.

**Does Camp 1 apply to gross?** No.
- Gross's group `Z_12 × Z_6` is NOT a 2-group (it has the odd part
  `Z_3 × Z_3`).
- The 2-Sylow `G_2 = Z_4 × Z_2` is NOT elementary abelian (it has an
  order-4 element).
- `F₂[gross]` has 5 Frobenius orbits, hence 5 local-ring components
  `R_O`, only one of which (the trivial-character orbit) has
  `R_O = F₂[G_2]`. The other four are `F_{2²}[G_2]` (the four
  size-2 orbits).
- Berman–Charpin–Andriatahiny do not address per-orbit refinements
  or the `F_{2^r}[G_2]` setting for non-elementary G_2.

**Conclusion**: the *idea* of "min weight of a radical-filtration
layer" is in Camp 1, but the specific quantity C-v1 needs
(per-orbit, kernel-restricted, non-elementary G_2) is not.

## 3. Camp 2 — Distance bounds in the semisimple regime

Multivariate cyclic / abelian codes have a Fourier-style decomposition
when `gcd(|G|, char F) = 1` (the semisimple regime). Distance bounds
exploit this decomposition orbit-by-orbit. Triaged in HANDOFF.md §6j
and `notes/T2R3.0_literature_check.md`:

- **Camion 1971**, **Sabin–Lomonaco 1992**, **Saints–Heegard 1995**
  (TIT 41(6)) define the multivariate **apparent distance** of an
  abelian code from its defining set (the set of vanishing
  characters).
- **Bernal–Bueno-Carreño–Simón 2016**
  ([arXiv:2402.03938](https://arxiv.org/abs/2402.03938))
  ("Apparent Distance and a Notion of BCH Multivariate Codes")
  introduces the **strong apparent distance** as a refinement
  reducing complexity from exponential to linear in the bivariate
  case.
- **Bernal–Guerreiro–Simón 2017**
  ([arXiv:1704.03761](https://arxiv.org/abs/1704.03761))
  ("From ds-bounds for cyclic codes to true distance for abelian
  codes") extends defining-set bounds to multivariate codes via the
  notion of **B-apparent distance** and gives conditions for
  apparent = true distance.
- Hartmann–Tzeng 1972, Roos 1983, van Lint–Wilson are the
  univariate-cyclic precursors.

**Scope of Camp 2**:
- All papers in this line assume `F[G]` is semisimple — i.e.
  `gcd(|G|, char F) = 1`. The apparent distance machinery is built
  on the Fourier transform / Wedderburn decomposition into a product
  of fields, which exists only in the semisimple case.

**Does Camp 2 apply to gross?** No — for the reason quoted from
Jitman–Ling 2013 (TIT 59(5), 3046–3058,
[Semantic Scholar](https://www.semanticscholar.org/paper/Abelian-Codes-in-Principal-Ideal-Group-Algebras-Jitman-Ling/aa17c6e148f62732aaa1e388441cce5acd77d838)):

> "An upper bound for the minimum distance of abelian codes in a
> non-semisimple PIGA is given in terms of the minimum distance of
> abelian codes in semisimple group algebras."

Distance bounds in non-semisimple PIGAs **transfer through the
semisimple quotient** and are **never sharper** than what the
semisimple quotient yields. This is the exact reason HANDOFF.md §6j
declared the entire character-theoretic family blind to gross.

**Conclusion**: Camp 2 has rich theory for orbit-restricted weight
invariants — `per_orbit_dual_distance` in `weight_invariants.py` is a
small one — but the entire camp lives over the semisimple quotient.
Camp 2 cannot see the Jacobson radical of `F₂[G]` by construction.

## 4. The gap

C-v1 lives in the cross-section that neither camp covers:

| | Camp 1 | Camp 2 | C-v1 target |
|---|---|---|---|
| **Group structure** | elem. abelian p-group | abelian, semisimple `F[G]` | abelian, **non-semisimple** `F₂[G]` with `2 \| \|G\|` |
| **Decomposition** | single local ring | product of fields | product of local rings `R_O = F_{2^\|O\|}[G_2]` |
| **What is min-wted** | full radical power `M^μ` | orbit-restricted kernel `(ker M_A)_O` (semisimple) | per-orbit, per-Loewy-layer, **plus** kernel-restriction |
| **Refines** | dim of radical power | character-defining-set bounds | both, simultaneously |

The literature gives:
- min-weight of `M^μ(F₂[G_2])` for `G_2` elem. abelian via Camp 1
- min-weight of `(ker M_A)_O` (semisimple per-orbit) via Camp 2

C-v1 needs:
- min-weight of `(R_O ∩ m_O^{μ-1} ∩ ker(M_A))` for **non-elem-abelian**
  `G_2` and **non-trivial orbit O**

No search hit names this object. The closest combinations checked
(May 2026):

- `"Loewy series" OR "Loewy filtration" "Hamming weight" modular
  group algebra code` — finds Andriatahiny / Berman / Charpin only.
- `"modular representation" "minimum distance" "abelian code"
  non-semisimple group algebra` — finds Jitman–Ling (semisimple
  quotient barrier).
- `"strong apparent distance" abelian code Bernal Simon
  Bueno-Carreno multivariate` — finds BBCS 2016, B-G-S 2017 (both
  semisimple-only).
- `"Brauer character" weight enumerator modular code minimum
  distance` — no hits.
- `"radical filtration" "minimum weight" code modular group ring` —
  finds Andriatahiny / GRM-as-radical-power only.

## 5. Related but distinct: Reed-Muller codes inside R_O

The cleanest "near miss" is that `F_2[G_2]` for a 2-group `G_2`
admits a radical filtration whose layers, **as additive subgroups of
F_2[G_2]**, have well-studied minimum weights via Berman–Charpin.
For gross's `G_2 = Z_4 × Z_2`, however, `G_2` is **not elementary
abelian**, so the standard Reed-Muller correspondence doesn't apply
directly. The Jennings basis (Theorem 3.5 of arXiv:1609.09531) covers
elementary abelian; for non-elementary G_2, one needs the Jennings
basis of `F_2[Z_4 × Z_2] = F_2[y]/(y^4) ⊗ F_2[z]/(z^2)`, which is
the tensor of two univariate radical filtrations.

This is a computable object, but the published Berman–Charpin–
Andriatahiny machinery does not give a closed-form min-weight
formula for non-elementary 2-Sylow. Hence C-v1's computation falls
back to direct subspace enumeration via Gray-code traversal
(`features.min_weight_in_kernel`).

## 6. Verdict — proceeding with C-v1 is justified

- The proposed `w_μ(A, O)` is a weight invariant (`min |·|_H` over
  an F₂-subspace), so it dodges the §6h "dimension on the RHS"
  footgun by construction.
- No published quantity matches the per-orbit × per-Loewy-layer ×
  kernel-restricted combination, in the non-elementary 2-Sylow
  regime.
- The semisimple-limit recovery (W4) reduces to
  `per_orbit_dual_distance(A, O)` for `μ = 1`, which IS a published
  weight invariant.
- The construction proceeds via building blocks already in
  `algebraic_features.py` (orbit projection `_project_poly_to_R_O`)
  and `weight_invariants.py` (per-orbit kernel computation), so the
  computational substrate is largely in place.

Documenting prior art means citing Berman 1967, Charpin 1988,
Andriatahiny 2016, Jitman–Ling 2013, and the BBCS/B-G-S line as
"adjacent prior work that does not address this specific combination."

## 7. Open question (not for C-v1)

Whether `w_μ(A, O)` can be assembled into a *distance bound* on
`d_X(BB(G, A, B))` is the C-v2 question. Per Jitman–Ling 2013, any
classical character-theoretic argument is structurally blind to the
2-radical, so a hypothetical bound `d ≥ F(w_μ values)` would
necessarily use a non-character-theoretic mechanism. C-v1 simply
**defines the object**; whether downstream bounds can be derived is
explicitly out of scope per HANDOFF_C §2.

## References (canonical form)

1. S. D. Berman, "On the theory of group codes", Kibernetika 3(1)
   (1967), 31–39.
2. P. Charpin, "Une généralisation de la construction de Berman des
   codes de Reed et Muller p-aires", Communications in Algebra 16
   (1988), 2231–2246.
3. H. Andriatahiny, "The Generalized Reed-Muller codes and the
   radical powers of a modular algebra",
   [arXiv:1601.07633](https://arxiv.org/abs/1601.07633) (2016).
4. H. Andriatahiny & V. H. Rakotomalala, "The Generalized
   Reed-Muller codes in a modular group algebra",
   [arXiv:1609.09531](https://arxiv.org/abs/1609.09531) (2016).
5. S. Jitman, S. Ling, H. Liu, X. Xie, "Abelian Codes in Principal
   Ideal Group Algebras", IEEE TIT 59(5) (2013), 3046–3058.
6. J. J. Bernal, D. H. Bueno-Carreño, J. J. Simón, "Apparent
   Distance and a Notion of BCH Multivariate Codes", IEEE TIT 62(2)
   (2016), 655–668; updated preprint
   [arXiv:2402.03938](https://arxiv.org/abs/2402.03938).
7. J. J. Bernal, M. Guerreiro, J. J. Simón, "From ds-bounds for
   cyclic codes to true distance for abelian codes",
   [arXiv:1704.03761](https://arxiv.org/abs/1704.03761) (2017).
8. J. P. Camion, "Abelian codes", U. Wisconsin MRC Technical Report
   1059 (1971).
9. C. R. Sabin & S. J. Lomonaco, "Metacyclic codes and metacyclic
   structures on hyperbolic groups", IEEE Workshop on Information
   Theory (1992).
10. K. Saints & C. Heegard, "Algebraic-geometric codes and
    multidimensional cyclic codes: A unified theory and algorithms
    for decoding using Gröbner bases", IEEE TIT 41(6) (1995),
    1733–1751.
11. C. R. R. Hartmann & K. K. Tzeng, "Generalizations of the BCH
    bound", Information and Control 20(5) (1972), 489–498.
12. C. Roos, "A new lower bound for the minimum distance of a cyclic
    code", IEEE TIT 29(3) (1983), 330–332.
