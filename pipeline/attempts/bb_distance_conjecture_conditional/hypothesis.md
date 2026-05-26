# Conditional Jacobson-radical conjecture for BB codes

## Statement

For a bivariate-bicycle (BB) quantum LDPC code `BB(G, A, B)` over a
finite abelian group `G = Z_ℓ × Z_m` and polynomials `A, B ∈ F_2[G]`
with each `⟨supp(A)⟩ = G` and `⟨supp(B)⟩ = G` (the **non-degeneracy**
condition),

```
d_X(BB(G, A, B))  ≥  Σ_{O ∈ V_A ∩ V_B}  |O| · min(μ_O(A), μ_O(B))
```

where:

* `V_A, V_B` are the sets of Frobenius orbits on `Ĝ_odd` (the
  character group of `G_odd = G / 2-Sylow`) on which `A, B`
  respectively vanish.
* `μ_O(A)` is the Jacobson-radical filtration depth of `A`'s
  projection to the local ring `R_O = F_{2^|O|}[G_2]`, defined as
  `dim_{F_{2^|O|}} ker(mult_{a_O} : R_O → R_O)`.

The RHS is identical to the unconditional conjecture from Tier-3
round 1 (`bb_distance_conjecture`). The novelty here is the
**hypothesis restriction** to non-degenerate codes.

## Motivation

Tier-3 round 1 falsified the unconditional conjecture: 10.5% of
corpus rows violate, and `bb_72_12_6` violates with bound=8 > d=6.

A quick query suggested that violations are concentrated on
**degenerate** codes — those where `⟨supp(A)⟩ < G` or `⟨supp(B)⟩ < G`.
This makes intuitive sense: when `A`'s support generates only a
proper subgroup `H < G`, the BB-block effectively decomposes into
`|G : H|` copies of a smaller BB code on `H`. The orbit-wise μ sum
over-counts because it doesn't see the decomposition.

If the conjecture survives on the non-degenerate subset, it would
be a "clean" structural statement: a quasi-tight algebraic distance
bound on a well-defined class of BB codes.

## Non-degeneracy: the definition we test

We use the spec's **strict per-polynomial** definition:

> `(A, B)` is **non-degenerate** iff each individual support set
> generates `G` as an additive subgroup:
>
>   `⟨supp(A)⟩ = G  AND  ⟨supp(B)⟩ = G`.

This is **stricter** than the joint condition `⟨supp(A) ∪ supp(B)⟩ = G`
that Lin–Pryadko 2306.16400 (and related 2BGA references) loosely
implies. The strict definition is more conservative — it excludes
codes where either polynomial alone fails to cover G.

The classifier implementation is in
`experiments/bb_lab/src/bb_lab/degeneracy.py`:

* `supp_generates_G(poly, G)`: BFS the additive-subgroup closure
  of `supp(poly)`; compare to `|G|`.
* `support_subgroup_index(poly, G)`: returns `[G : ⟨supp(poly)⟩]`.
  Equals 1 iff non-degenerate.
* `is_non_degenerate(A, B, G)`: both individually non-degenerate.

## What "survives" means here

The conjecture **survives** the non-degenerate condition iff:

(a) the non-degenerate corpus subset has no violations of the real
    Jacobson bound (not the `k/2` proxy used in the round-1
    pre-query), AND
(b) the Bravyi-table instances either pass or are in scope and
    satisfy the bound.

Failure of either (a) or (b) — or a heterogeneous residual without a
clean tightening — qualifies the conditional version as a partial or
falsified result, per the spec's verdict taxonomy.

## A priori concerns

1. **§6h footgun**: the bound's RHS is fundamentally a
   *dimension count* (`Σ|O|·μ_O(A) = dim_{F_2} ker M_A` exactly),
   and dimension counts give upper bounds on coset sizes, not
   lower bounds on weight. The whole class of dimension-RHS
   conjectures has a theoretical reason to fail eventually. The
   conditional version doesn't escape this — it just hopes the
   structural restriction picks up the *cases where dimension
   happens to lower-bound weight*. Whether such cases are
   measure-zero or measure-positive in the BB-code space is an
   empirical question.

2. **Bravyi exclusion risk**: the Bravyi target codes
   (`x^3 + y + y^2` family) have x-axis support `{(3, 0)}` of
   subgroup order `ℓ / gcd(3, ℓ)`. For `ℓ ∈ {6, 9, 12, 15}` (the
   Bravyi groups), `gcd(3, ℓ) = 3`, so the subgroup is index 3 and
   the polynomial fails strict non-degeneracy. **This is a concern
   the round-2 spec did not flag.** The empirical Bravyi-table
   check (T3R2.4) confirms all 5 Bravyi instances are degenerate.

3. **Conjecture-mechanism uniformity**: round 1's violators
   spanned `d_exact ∈ {2, 4, 6}` and slack `∈ {-22, ..., -1}`.
   If round 2's residual violators are concentrated in one
   structural class (e.g., all `d = 2` cases with `B = unit · A`),
   that's a clean tightening candidate. If they're spread across
   the parameter space heterogeneously, the conditional bound is
   "almost-but-not-clean."
