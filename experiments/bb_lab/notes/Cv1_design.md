# C-v1 design — `w_μ(A, O)`

Date: 2026-05-26.

Companion to [`Cv1_literature.md`](Cv1_literature.md). This note
records the chosen definition of `w_μ(A, O)`, the properties it
satisfies, and the implementation plan.

## 1. Setup

`G` is a finite abelian group with `2 | |G|`. Write `G = G_odd × G_2`
with `G_2` the 2-Sylow. The group algebra factors as

  F₂[G]  ≅  ⊕_O R_O,    R_O = F_{2^|O|}[G_2]

over Frobenius orbits `O` on `Ĝ_odd ≅ G_odd`. Each `R_O` is a finite
local ring with maximal ideal `m_O = F_{2^|O|} · aug(F₂[G_2])`. The
Loewy filtration is

  R_O ⊃ m_O ⊃ m_O² ⊃ ⋯ ⊃ m_O^L = 0

where `L = depth(O)` is the nilpotency index. For `G_2` abelian, if
`G_2 = ∏_i Z_{2^{a_i}}` then `L = Σ_i (2^{a_i} − 1) + 1`. For gross's
`G_2 = Z_4 × Z_2`, `L = 5`.

For a polynomial `A ∈ F₂[G]`, write `a_O ∈ R_O` for its image under
the projection F₂[G] → R_O. The Jacobson depth invariant from
`algebraic_features.py:jacobson_radical_depth` is

  `μ_O(A) := dim_{F_{2^|O|}} ker(mult_{a_O} : R_O → R_O)`

— a **dimension** invariant, falsified for distance bounds in
Round 1 (HANDOFF §6h). C-v1 instead defines a **weight** refinement.

## 2. Chosen definition

For each Frobenius orbit `O` on `Ĝ_odd` and each `μ ∈ {1, …, L}`:

> **`V_{O, μ}(A) := { f ∈ R_O ⊂ F₂[G] : f · A = 0 in F₂[G], and f ∈ m_O^{μ−1} }`**
>
> **`w_μ(A, O) := min { |f|_H : f ∈ V_{O, μ}(A), f ≠ 0 }`**
>
> (with the convention `min ∅ = ∞`).

`|f|_H` is the Hamming weight of `f` viewed as an element of
`F₂[G]` in the standard `G`-basis. Two subtleties:

- **`f ∈ R_O ⊂ F₂[G]`**: `R_O` is realized as a sub-F₂-vector-space
  of `F₂[G]` via the primitive central idempotent `e_O ∈ F₂[G_odd]`,
  i.e. `R_O = e_O · F₂[G]`. Equivalently (and more practically),
  `f ∈ R_O` iff for every other orbit `O'`, `f`'s `O'`-Fourier-image
  is zero **on every `G_2`-fiber**. This is stronger than the
  G_2-fiber-summed condition used by
  `weight_invariants._char_constraint_rows_g_odd`; see §4 below.

- **`f · A = 0`**: equivalent to `f · a_O = 0 in R_O` (since `f ∈ R_O`
  and `R_O · R_{O'} = 0` for `O' ≠ O`). So this is the kernel of
  multiplication-by-`a_O` inside `R_O`.

Convention notes:
- `μ = 1` corresponds to `f ∈ m_O^0 = R_O` (no filtration constraint).
  This is the base level; it recovers the per-orbit dual distance in
  the semisimple limit (W4 below).
- `μ ≥ 2` tightens by requiring `f ∈ m_O^{μ−1}` (deeper in the
  radical).
- `w_μ(A, O) = ∞` when `V_{O, μ}(A) = {0}` (e.g., `μ` larger than
  the deepest possible witness, or non-vanishing orbit with `a_O` a
  unit).

## 3. Properties

**(W1) Invariance.** The BB-code equivalence group, restricted to
G-translation × Aut(G) × block-swap (the subgroup the corpus
de-dups under):

- *G-translation* `f ↦ g · f`: preserves `R_O` (ideal), preserves
  `m_O^{μ-1}` (`g` acts via a unit in `R_O`), preserves the
  annihilation `(g·f) · a_O = g · (f · a_O) = 0`, preserves Hamming
  weight (basis permutation). ✓
- *`Aut(G)`* `f ↦ σ̃(f)`: permutes orbits `O ↦ σ̃(O)`, sends
  `R_O ↦ R_{σ̃(O)}`, `m_O ↦ m_{σ̃(O)}`, preserves
  Hamming weight. Hence `w_μ(σ̃(A), σ̃(O)) = w_μ(A, O)`. ✓
- *Block-swap*: `w_μ` is defined per-polynomial, no interaction
  with the partner polynomial.

Per HANDOFF_C §7, we **drop F₂[G]-unit invariance** because Hamming
weight is not preserved by unit multiplication
(e.g. `(1+x) · 1` has weight 2 vs. `1` weight 1). This restriction
is acceptable: the corpus is canonicalized under the smaller group.

**(W2) Weight-shaped.** `w_μ(A, O) = min |·|_H` over an F₂-subspace
of F₂[G] by construction. ✓

**(W3) Computable.** `V_{O, μ}(A)` is the F₂-kernel of a stacked
constraint matrix on `F₂[G] ≅ F₂^{|G|}`. The three constraint
blocks:

1. *Kernel*: `M_A · v = 0` (the convolution matrix from
   `checks.circulant(A)`).
2. *Per-orbit isotypic*: for each `O' ≠ O`, for each `g_2 ∈ G_2`,
   the fiber `v_{(·, g_2)}` is annihilated by every character in `O'`
   (= `|O'|` F₂-rows per `g_2`).
3. *Loewy depth*: for each `(y, z)`-monomial of total degree
   `< μ − 1` in `F_{2^|O|}[G_2]`, the corresponding coefficient of
   `v`'s `R_O`-projection vanishes (= `|O|` F₂-rows per missing
   monomial; see §4 for the change-of-basis recipe).

The F₂-nullspace of the stacked matrix gives a basis of
`V_{O, μ}(A)`. Min Hamming weight is then computed by Gray-code
traversal of that basis (`features.min_weight_in_kernel` provides
the routine).

For gross (|G| = 72, |O| = 1 or 2, |G_2| = 8, μ_O ≤ 2), the
expected basis dimension is small (≤ |O| · μ_O(A) = 4 per
vanishing orbit), so brute-force enumeration is cheap. The
sub-routine handles dimensions ≤ 22 in seconds.

**(W4) Semisimple-limit recovery.** When `G_2` is trivial,
`R_O = F_{2^|O|}` and `m_O = 0`:

- `μ = 1`: `m_O^0 = R_O`. `V_{O, 1}(A) = ker(mult_{a_O} : F_{2^|O|} → F_{2^|O|})`.
  - If `a_O = 0` (A vanishes on O): `V_{O, 1}(A) = R_O`. Then
    `w_1(A, O) = min |·|_H` over `R_O \ {0}` = **per-orbit dual
    distance `d_O^⊥(A)`** as defined in
    `weight_invariants.per_orbit_dual_distance` for the semisimple
    case.
  - If `a_O ≠ 0`: `V_{O, 1}(A) = {0}`, `w_1(A, O) = ∞`. ✓
- `μ ≥ 2`: `m_O^{μ-1} = 0`. `V_{O, μ}(A) = {0}`, `w_μ(A, O) = ∞`. ✓

So for semisimple G, the entire `w_μ` invariant collapses to
`{1: d_O^⊥(A), 2: ∞, 3: ∞, ...}` — the classical per-orbit dual
distance plus a trivial extension. ✓

**Note for non-semisimple G**: `w_1(A, O)` is **not** in general
equal to `per_orbit_dual_distance(A, O)` from
`weight_invariants.py`. The existing function uses the *fiber-summed*
character constraint (which collapses `G_2`-fibers); the C-v1
invariant uses the *proper* per-orbit constraint (one constraint per
`(O', g_2)` pair). For semisimple G the two coincide. For
non-semisimple G the proper constraint is more restrictive (so
`V_{O, 1}(A)` is smaller than the existing function's subspace,
hence `w_1(A, O) ≥ per_orbit_dual_distance`).

## 4. Implementation recipe

### 4.1 R_O membership constraints

For each `O' ≠ O`, for each `g_2 ∈ G_2`, build `|O'|` F₂-rows
enforcing "fiber `v_{(·, g_2)}` is annihilated by characters in
`O'`":

```
constraint[i, (h, g_2')] = (i-th F₂-coord of χ(h)) if g_2' == g_2 else 0
```

where `χ` is a representative character of `O'`, viewed as a map
`G_odd → F_{2^|O'|}`. There are `|O'|` such rows (one per F₂-coord
of `F_{2^|O'|}`), per `g_2`. Total rows for `O'`: `|O'| · |G_2|`.

The character evaluation logic is identical to
`_char_constraint_rows_g_odd`; the difference is restricting each
constraint to one `g_2`-fiber.

For gross with `|O'|`-sum over `O' ≠ O` = `1 + 2·3 = 7`,
`|G_2| = 8`: 56 F₂-rows per orbit `O`.

### 4.2 Loewy-depth constraints

For each monomial `y^i z^j` with `i + j < μ − 1` (over the
`(y_axis - 1)` generators of `G_2`'s 2-Sylow basis), build `|O|`
F₂-rows that read off the F_{2^|O|}-coefficient of `y^i z^j` in
`v`'s R_O-projection:

```
(y^i z^j)-coeff = Σ_{a ≥ i, b ≥ j} (C(a, i) · C(b, j) mod 2) ·
                  (R_O-proj of v_{(·, b_y^a b_z^b)})
```

For `v ∈ R_O` already (constraint 4.1 satisfied), the R_O-projection
of `v_{(·, g_2)}` is `ε_O(v_{(·, g_2)})` where `ε_O : F₂[G_odd] →
F_{2^|O|}` is the orbit-O character map. Each such F_{2^|O|}-output
contributes `|O|` F₂-constraints.

Each (i, j) below threshold gives `|O|` F₂-rows. Total: `|O|` × #
monomials with `i + j < μ − 1`.

For gross's G_2 = Z_4 × Z_2 (Loewy length 5), monomial counts by
threshold are:

| μ-1 | monomials w/ i+j < μ-1 | count | × \|O\| | rows |
|:--:|:--|:--:|:--:|:--:|
| 0  | (none)                       | 0 | 0 | 0  |
| 1  | y⁰z⁰                         | 1 | 2 | 2  |
| 2  | y⁰z⁰, y¹z⁰, y⁰z¹             | 3 | 2 | 6  |
| 3  | + y²z⁰, y¹z¹                 | 5 | 2 | 10 |
| 4  | + y³z⁰, y²z¹                 | 7 | 2 | 14 |

### 4.3 Generic case (G_2 = ∏ Z_{2^{a_i}})

The recipe above extends mechanically: replace `(y, z)` with
generators `y_1, …, y_k` (one per 2-Sylow axis), with `y_i = [b_i] - 1`
where `b_i` is the axis generator. Each `y_i` has `y_i^{2^{a_i}} = 0`.
The monomial basis of `F₂[G_2]` is `∏_i y_i^{e_i}` with
`0 ≤ e_i < 2^{a_i}`. The Loewy filtration layer `m_O^μ` is spanned by
monomials with `Σ e_i ≥ μ`.

### 4.4 Combining

`V_{O, μ}(A) = nullspace_F₂(stack[M_A, R_O-constraints,
Loewy-constraints])`. Implementation uses
`bb_lab.linalg.nullspace_f2`.

`w_μ(A, O) = min nonzero |·|_H` over basis, via Gray-code (re-implements
the inner loop of `weight_invariants.per_orbit_dual_distance` to
keep the C-v1 module self-contained per HANDOFF_C §6 ("don't modify
existing modules")).

### 4.5 Verification anchors

- **`G = Z_4`** (single orbit, Loewy length 4): exhaustive
  check against hand computation. `w_μ(A, O₀)` for
  `A = (1+x)^k` follows the chain-ring filtration.
- **Semisimple-limit**: any `G` with `|G|` odd. Confirm
  `w_1(A, O) == per_orbit_dual_distance(A, O)` for every vanishing
  orbit (read from the existing function), and `w_μ(A, O) == ∞`
  for `μ ≥ 2`.
- **Gross**: compute the `(A, B, O, μ)` table for the 3
  vanishing orbits of `A = x³+y+y²` and `B = y³+x+x²` and
  `μ ∈ {1, 2, 3, 4, 5}`. Report all values; identify any orbit/μ
  with `w_μ ≥ 6` (the HANDOFF_C §4.6 "potentially useful" threshold).

## 5. Out of scope (for C-v1)

- Whether `w_μ` produces a distance bound (C-v2).
- Whether the proper per-orbit constraint changes existing
  `per_orbit_dual_distance` values on non-semisimple G in the
  corpus. (Possible follow-up: a corpus sweep documenting where the
  two diverge.)
- Optimizing computation beyond Gray-code enumeration. The expected
  basis dim is small for the corpus and gross; smarter min-weight
  algorithms are future work if (W3) becomes a bottleneck.
