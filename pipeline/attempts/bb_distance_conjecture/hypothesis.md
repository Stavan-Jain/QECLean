# Hypothesis: Jacobson-radical distance bound for BB codes

**Conjecture.** For a bivariate-bicycle (BB) code over a finite abelian
group `G = Z_ℓ × Z_m` with polynomials `A, B ∈ F_2[G]`,

```
d_X(BB(G, A, B)) ≥ Σ_{O ∈ V_A ∩ V_B} |O| · min(μ_O(A), μ_O(B))
```

where:

- `V_A`, `V_B` ⊂ orbits-on-Ĝ_odd = the sets of Frobenius orbits on the
  character group of `G_odd = G / 2-Sylow(G)` on which `A` (resp. `B`)
  vanishes.
- `μ_O(A)` is the **Jacobson-radical filtration depth** of `A` in the
  local component `R_O` of `F_2[G]`. Operationally,

  ```
  μ_O(A) := dim_{F_{2^|O|}} ker( mult_{a_O} : R_O → R_O )
  ```

  where `a_O ∈ R_O` is the projection of `A` and `R_O = F_{2^|O|}[G_2]`
  is the local ring at orbit `O` (residue field `F_{2^|O|}`, radical the
  augmentation ideal of `F_{2^|O|}[G_2]`).

- Convention:
  - `μ_O(A) = 0` if `A` does **not** vanish on `O` (i.e., `a_O` is a
    unit in `R_O`).
  - `μ_O(A) ≥ 1` if `A` vanishes on `O`. For semisimple components
    (where `G_2` is trivial, e.g., when `|G|` is odd), `μ ∈ {0, 1}`.
    For non-semisimple components, `μ` ranges over `{0, 1, ..., |G_2|}`.

- The compatibility identity (consequence of the operational definition)
  is

  ```
  dim_{F_2} ker M_A  =  Σ_O |O| · μ_O(A)
  ```

  summed over all Frobenius orbits on `Ĝ_odd`.

## Motivation

Panteleev–Kalachev (arXiv:2012.04068 §III.E) explicitly flag the
modular case `gcd(|G|, char F) > 1` — which includes the gross code's
`|G| = 72, char F = 2` — as needing **Jacobson-radical refinement** to
the semisimple Wedderburn decomposition. T2.2 of the bb_lab program
([`experiments/bb_lab/notes/T2.2_algebraic_features.md`](../../../experiments/bb_lab/notes/T2.2_algebraic_features.md))
made the empirical observation that gross's `A = x³+y+y²` has

```
dim ker M_A = 12 = 3 vanishing G_odd-orbits × |O|=2 × multiplicity=2
```

with the **multiplicity factor 2** identified as the nilpotency index
of `A` in the 2-Sylow-radical of the local ring. T2.3 confirmed that no
surveyed paper (Lin–Pryadko 2023, Kovalev–Pryadko 2013, Bravyi 2024,
Panteleev–Kalachev 2021, Wang–Pryadko 2022, Raveendran–Declercq–Vasić
2025, Otjens 2025) derives such a bound; the conjecture is therefore
plausibly novel.

The conjecture asserts that this orbit-by-orbit multiplicity counting
gives a valid analytic *lower* bound on the BB code's X-distance.

## Predictions

- Tight on gross `[[144, 12, 12]]`: 2 jointly vanishing orbits each of
  G_odd-size 2 with μ_A = μ_B = 2, giving `2·min(2,2) + 2·min(2,2) = 8`.
  (Note: The conjecture's promoting context [the Tier-3 spec] claimed
  the bound on gross is 12 by counting 3 joint vanishing orbits. This
  is inaccurate — only 2 orbits jointly vanish [verified empirically
  and analytically]; the bound on gross is **8**, leaving a gap of 4
  to actual d=12.)
- Holds rigorously (no violations) across all corpus instances.
- Computable from `(G, A, B)` in polynomial time via the kernel-dimension
  evaluation.
