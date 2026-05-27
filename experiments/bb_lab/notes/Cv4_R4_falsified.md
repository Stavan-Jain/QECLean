# C-v4 — R1+R4 conjecture FALSIFIED (clean in-hypothesis counterexample)

Date: 2026-05-27. Follow-up to [`T3_CV3_R4_crossorbit.md`](T3_CV3_R4_crossorbit.md)
and [`pipeline/attempts/bb_distance_conjecture_radical_weight_narrow_tier3/result.md`](../../../pipeline/attempts/bb_distance_conjecture_radical_weight_narrow_tier3/result.md).

## Verdict

The R1 + R4 conjecture (loose-but-correct candidate that survived Tier 3
round on Bravyi-style codes) is **falsified** by a clean in-hypothesis
counterexample on a non-Bravyi-style group structure.

> **Counterexample**: `G = Z_3 × Z_15`, `A = 1 + x + x²`, `B = 1 + y + y² + y³ + y⁴`.
>
> - `|A| = 3, |B| = 5` both odd (R1 ✓)
> - `G_odd = Z_3² × Z_5`, each prime-part elementary abelian (loose elem-ab ✓)
> - `c = [G_a : G_a ∩ G_b] = 3` (✓)
> - `n = 90, k = 16`
> - **R4 bound = 4, d_X = 2 → CONJECTURE FALSIFIED, gap +2**

## Reproduction

```bash
cd experiments/bb_lab
uv run python scripts/adv_attack3_z3xz7.py
uv run python scripts/adv_attack3_verify.py     # detailed verification
uv run python scripts/adv_attack3_recheck.py    # comprehensive recheck
```

## Verification (multi-path)

Every key quantity confirmed by ≥2 independent methods:

| Quantity | Methods agreeing |
|---|---|
| `H_X · H_Z^T = 0` mod 2 | manual circulants + lab `bb_check_matrices` |
| `n = 90, k = 16` | manual rank + lab `code_params` |
| `d_X ≥ 2` | brute-force of all 90 weight-1 vectors (zero logicals found) |
| `d_X = 2` | SAT cap=2 + **45 explicit weight-2 X-logical witnesses** |
| 2 joint-vanishing orbits | lab + manual Frobenius analysis on Z_3 × Z_3 × Z_5 characters |
| R4 raw = 12 | Gray-code + random sampling + **exhaustive enumeration of all 255 nonzero F₂-combinations** of the 8-dim basis |
| Lin–Pryadko is satisfied | explicit `(1 + y + y⁵ + y⁶ + y¹⁰ + y¹¹) ∈ ker(M_B)` of weight 6 → `⌈6/3⌉ = 2 = d_X` |

## Mechanism — the proof gap, realized

The Lin–Pryadko (Statement 12, [arXiv:2306.16400](https://arxiv.org/abs/2306.16400)) bound uses
`min weight in ker(M_A)` (which equals `d_A^⊥`). R1+R4 strengthens this to
`min weight in W(A, B) = (⊕_{O ∈ JointVan(A,B)} R_O) ∩ ker(M_A)`. The
strengthening assumes the minimum-weight kernel element of `M_A` can be
chosen with support entirely on joint-vanishing orbits. **This assumption
is false in general.**

Concretely on the counterexample:

- `(1 + x) ∈ ker(M_A)` of weight 2: `A · (1 + x) = (1+x+x²)(1+x) = 1 + x³ = 0`
  in `F_2[Z_3 × Z_15]`. So `d_A^⊥ = 2`.
- But `(1 + x)`'s Fourier support is on orbits with `χ_1` (first-`Z_3` character)
  nontrivial — including the `B`-unit orbits, NOT just the joint-vanishing ones.
  Hence `(1 + x) ∉ W(A, B)`, and R4 doesn't see it.
- The minimum-weight element of `W(A, B)` has weight 12 (verified exhaustively).
  R4 reports `ρ_A = 12`, giving bound `⌈12/3⌉ = 4`.
- The weight-2 element `(1 + x)`, combined with the weight-6 element of
  `ker(M_B)` above, produces a weight-2 X-logical `(0, β)` with
  `β = δ_{(0,0)} + δ_{(1,0)}`, as verified by all 45 explicit witnesses.

So R4's joint-vanishing restriction is structurally invalid.

## Scope of the failure

[`scripts/adv_attack3_scope.py`](../scripts/adv_attack3_scope.py) probed
the structural scope:

| `G` | `G_odd` | semisimple? | Verdict |
|---|---|:---:|---|
| `Z_3 × Z_15` | `Z_3² × Z_5` (multi-prime) | yes | **FALSIFIES** R4=4 > d=2 |
| `Z_6 × Z_15` | `Z_3² × Z_5` (multi-prime) | no (`G_2 = Z_2`) | **FALSIFIES** R4=4 > d=2 |
| `Z_3 × Z_30` | `Z_3² × Z_5` (multi-prime) | no (`G_2 = Z_2`) | **FALSIFIES** R4=4 > d=2 |
| `Z_3 × Z_3` | `Z_3²` (single-prime) | yes | tight (R4 = d = 2) |
| `Z_15 × Z_15` | `Z_3² × Z_5²` (multi-prime, rank≥2 each) | yes | loose-correct (R4 < d) |
| `Z_12 × Z_12` (Bravyi domain) | `Z_3²` (single-prime) | no | satisfies (prior testing) |

The failure mode requires:

1. **Multi-prime `G_odd`** with at least one prime appearing at rank 1.
2. Polynomial choices where `A` vanishes on one prime's nontrivial-character
   orbits and `B` vanishes on the other prime's nontrivial-character orbits
   — making `JointVan(A, B)` a tiny fraction of `ker(M_A)` and `ker(M_B)`.

This regime includes BB code `[[90, 8, 10]]` (Bravyi) by group structure
(`G_odd = Z_3² × Z_5`), though bb_90's specific polynomial choices avoid
the failure mode and the code satisfies the conjecture.

The other three Bravyi codes (`[[72,12,6]]`, gross `[[144,12,12]]`,
`[[288,12,18]]`) all have single-prime `G_odd = Z_3²` and are NOT affected
by this falsifier.

## Implications

1. **R1+R4 as stated is dead.** The clean in-hypothesis counterexample
   removes it from the Lean formalization track. Recommendation in
   [`pipeline/attempts/bb_distance_conjecture_radical_weight_narrow_tier3/result.md`](../../../pipeline/attempts/bb_distance_conjecture_radical_weight_narrow_tier3/result.md)
   to pursue `HANDOFF_C4_R4.md` is withdrawn.

2. **Lin–Pryadko Statement 12 remains the only correct formalization target**
   in this space — the original (un-strengthened) bound `d_X ≥ ⌈d_A^⊥ / c⌉`,
   which is satisfied (and tight at 2) on the counterexample.

3. **Possible salvage: add single-prime `G_odd` hypothesis.** The scope
   probe shows the falsifier requires multi-prime `G_odd`. Restricting
   the conjecture domain to `G_odd = (Z_p)^k for some single prime p`
   excludes the falsifier and bb_90, retaining the other 3 Bravyi codes.
   Whether the R1+R4 bound provably holds on the single-prime subset is
   open — the proof would still need to handle the joint-vanishing
   restriction, and there is no proof-theoretic reason the single-prime
   case avoids the proof gap demonstrated by the `(1+x)` mechanism.

4. **The C-program (Cv1 → Cv2 → Cv3 → R1+R4) has now run its course**
   with no surviving tight or loose-correct bound applicable to the
   engineering target. The empirically-clean "0 violations on c ≥ 3"
   finding from the corpus sweep ([`Cv3_restricted_sweep.md`](Cv3_restricted_sweep.md))
   is now understood as a side effect of the corpus being dominated by
   single-prime `G_odd`. The conjecture was overfit to that regime.

## Side note: Lin–Pryadko's d_A^⊥ vs R4's ρ_A on this instance

- `d_A^⊥ = 2` (achieved by `1 + x`)
- `d_B^⊥ ≤ 6` (achieved by `1 + y + y⁵ + y⁶ + y¹⁰ + y¹¹`)
- `ρ_A = ρ_B = 12` (cross-orbit min over joint-vanishing direct sum)

So R4 strengthens `d_A^⊥` from 2 to 12 — a factor of 6 — and over-shoots
`d_X` by a factor of 2 after dividing by `c = 3`. This is the cleanest
numerical demonstration to date that the joint-vanishing restriction is
NOT a sound strengthening of Lin–Pryadko.
