# Result — Tier 3 FALSIFIES C-v3 (tight form); R1 + R4 survives (loose form)

**Verdict: FALSIFIED-AS-TIGHT, SURVIVES-AS-LOOSE** per HANDOFF_TIER3_CV3 §6
stop conditions, with refined nuance from two parallel refinement
attempts.

The C-v3 narrowed radical-weight distance conjecture fails adversarial
out-of-corpus testing in its original (tight) form:

1. **Weight-4 BB codes (T3-A)**: 78 violators / 500 in-scope rows on
   Z_6 × Z_6 (15.6% violation rate). All even-weight A.
2. **Larger G_2 structure (T3-C)**: same A polynomial that's tight on
   gross (Z_12 × Z_6) is a clean violator on Z_12 × Z_12 (bound = 18,
   d = 12).

**Two refinement attempts** were tested in parallel:

- **R1 (odd-weight)** [committed in 283ddd4]: saves all 78 T3-A
  violators by adding `weight(A), weight(B) both odd` to the
  hypothesis. Necessary but not sufficient.

- **R4 (cross-orbit min weight)** [committed in 283ddd4]: replaces
  per-orbit `min_O w_1` with the min Hamming weight over the joint-
  vanishing direct sum `⊕_O R_O ∩ ker(M_A)`. **Saves the T3-C C1
  violator** (R4 bound = 12 = d). But R4 is **loose on Bravyi**:
  - gross: R4 bound = 8 (vs d = 12, gap 4)
  - bb_288: R4 bound = 12 (vs d = 18, gap 6)
  - bb_72: R4 bound = 4 (vs d = 6, gap 2)

- **H_UNIT² (unit-factor order ≤ 2)** [this artifact]: a candidate
  TIGHT refinement requiring A's per-axis Loewy decomposition to
  have unit factor of order ≤ 2. **Refuted by case (4, 5) on
  Z_12 × Z_12**: y-axis Loewy poly is bare `y'` (no unit factor,
  trivially H_UNIT² ✓), predicted tight, but actual d = 12 < bound
  = 18 → violation.

## Synthesis

| Refinement combination | Coverage | Tightness | Status |
|---|---|---|---|
| C-v3 (original) | broad | tight on corpus | **FALSIFIED** (T3-A, T3-C) |
| C-v3 + R1 | narrower | tight on corpus + T3-B/D/E | **FALSIFIED** (T3-C) |
| C-v3 + R1 + R4 | narrowed | **correct but loose** | **SURVIVES** (loose-but-correct) |
| C-v3 + R1 + H_UNIT² | narrowed | tight target | **FALSIFIED** (case 4,5) |

The conclusion: **no clean structural refinement gives a tight
bound** that matches d on the Bravyi codes. Either:
- Accept a LOOSE bound (R1 + R4): empirically correct, formally
  derivable, but doesn't match d on the engineering targets.
- Pursue a TIGHTER refinement: would require a new invariant
  beyond C-v1 (e.g., not R_O-unit-invariant), which is a
  research-level pivot.

## Implication for C-v4 (Lean)

**C-v4 is RECOMMENDED, but for the R1 + R4 LOOSE bound**, not the
original tight C-v3 bound:

- The R1 + R4 bound is correct on all tested cases (gross, bb_72,
  bb_90, bb_108 excluded, gross, bb_288; all T3-A weight-4
  violators excluded; T3-C C1 fixed).
- It would prove `d_X ≥ ⌈(1/c) · cross_orbit_min_weight(A, B, G)⌉`
  under the elem-ab G_odd + c≥3 + odd-weight hypothesis.
- The proof would adapt Lin-Pryadko Statement 12's technique with
  the cross-orbit kernel as the numerator (mathematically a more
  natural choice than per-orbit anyway).

The Lean proof would NOT claim tightness on gross. It would say:
"d_X ≥ (some bound) = 8 on gross", which is weaker than the
empirical d = 12 but provable.

## Why C-v1's per-orbit framework is structurally limited

The diagnosis from the H_UNIT² failure:

C-v1's `w_1` is invariant under R_O-unit multiplication. This means
it collapses polynomials whose `a_O` projections are R_O-unit-
equivalent. But BB-code distance distinguishes such polynomials
(case (4, 5) vs case (1, 11) on Z_12 × Z_12: same y-axis Loewy
structure but different d).

R4 sidesteps this by using the cross-orbit kernel directly (NOT
per-orbit), which can see fine-grained polynomial structure
through cross-orbit cancellation. R4 is mathematically natural
but doesn't predict tightness — it just gives a smaller (possibly
loose) bound.

## Per-battery summary

| battery | in-scope tested | violations | status |
|---|:---:|:---:|---|
| T3-A weight-4 (Z_6×Z_6) | 500 | **78** | falsified, R1 saves all |
| T3-B other primes | 1 | 0 | inconclusive (k=0 dominant) |
| T3-C larger G_2 | 1 | **1** | **falsified**, R4 saves |
| T3-D adversarial | 2 | 0 | clean (small sample) |
| T3-E gross-family | 3 | 0 | clean |
| H_UNIT² targeted | ≥4 | 1 unexpected | **tight refinement falsified** |
| R4 cross-orbit | 4 critical | 0 | correct but loose on Bravyi |

## Recommended next steps

1. **Write `HANDOFF_C4_R4.md`** for the **R1 + R4 loose bound** in
   Lean. The proof should follow Lin-Pryadko's Statement 12
   technique substituting cross-orbit min for d_A^⊥.

2. **Stop pursuing tight C-v3-style bounds via C-v1 invariant**.
   The H_UNIT² failure suggests no clean per-axis algebraic
   condition will work. A tight bound would require a new
   invariant beyond C-v1's R_O-unit-invariant `w_1`.

3. **Document `w_1` as a contribution** (a novel weight invariant
   refining per-orbit dual distance via the Jacobson radical
   filtration), separate from any distance-bound claim.

4. **Add §6m to HANDOFF.md**: "Local-algebraic refinements of
   Lin–Pryadko via C-v1 invariants overshoot d on larger G_2 even
   under elem-ab + c≥3 + odd-weight hypothesis (T3-C C1 case).
   Cross-orbit min weight (R4) is the algebraically natural fix
   but is loose on Bravyi codes."

## Reproducibility

All scripts in `experiments/bb_lab/scripts/`. All notes in
`experiments/bb_lab/notes/T3_CV3_*.md`. Pipeline artifacts in this
directory.

```
cd experiments/bb_lab
uv sync --extra dev
uv run pytest -m 'not slow' -q
```

The Tier 3 falsifier (T3-C C1):

```
uv run python -c "
from bb_lab.group import ZmZn
from bb_lab.poly import Poly
from bb_lab.radical_weight import bb_radical_bound, joint_support_subgroup_index
from bb_lab.degeneracy import is_g_odd_elementary_abelian
G = ZmZn(12, 12)
A = Poly.from_string('x^3 + y + y^2', G)
B = Poly.from_string('y^3 + x + x^2', G)
print(f'elem_ab={is_g_odd_elementary_abelian(G)}')
print(f'c={joint_support_subgroup_index(A, B, G)}')
print(f'bound={bb_radical_bound(A, B, G)}')
print(f'(d=12 per SAT; bound > d)')
"
```

The H_UNIT² refutation ((4, 5) on Z_12 × Z_12):

```
uv run python scripts/tier3_cv3_unit_squared_targeted.py --workers 6 --cap 13
```

## Final note

This is a Tier-3 round delivering a **rich, nuanced verdict**:

- The original C-v3 bound is **falsified** as tight.
- A LOOSE refinement (R1 + R4) **survives** and is Lean-tractable.
- A TIGHT refinement (R1 + H_UNIT²) is **falsified** — confirming
  the C-v1 framework's structural limitation.

Two months of C-series work yield: a novel weight invariant `w_1`
(C-v1, contribution), a calibrated understanding of where local-
algebraic refinements break (this verdict), and a clean roadmap
for either accepting the loose bound (C-v4 with R4) or pursuing
fresh theory.

The 4-tier pipeline architecture (HANDOFF.md §2) caught both
the original failure (via T3) and the false-tight-refinement
(H_UNIT²) BEFORE Lean — saving weeks of misdirected formalization.

---

## POSTSCRIPT (2026-05-27): R1 + R4 itself FALSIFIED

The "loose-but-correct" R1 + R4 conjecture that this document recommended
for Lean formalization (§"Recommended next steps" item 1) has now been
falsified by a clean in-hypothesis counterexample:

> `G = Z_3 × Z_15`, `A = 1 + x + x²`, `B = 1 + y + y² + y³ + y⁴`.
> All R1 + R4 hypotheses hold (odd weights, loose elem-ab `G_odd`, `c = 3`).
> R4 bound = 4 but `d_X = 2`. **Conjecture falsified, gap +2**.

The mechanism is the proof gap predicted by abstract critique but never
explicitly demonstrated: `(1 + x) ∈ ker(M_A)` of weight 2 lives on
A-only-vanishing orbits (not joint-vanishing), so R4's restriction to
`W(A, B)` doesn't see it. Lin–Pryadko Statement 12 (using full `d_A^⊥`)
remains correct and is tight at 2 on this instance.

Verification: 45 explicit weight-2 X-logical witnesses found by
brute-force enumeration; R4 raw value 12 verified by exhaustive
enumeration of all 255 nonzero F₂-combinations in the 8-dim basis;
CSS commutation, `(n, k)`, and Frobenius orbit analysis all confirmed
by independent paths. See [`notes/Cv4_R4_falsified.md`](../../../experiments/bb_lab/notes/Cv4_R4_falsified.md)
and scripts `experiments/bb_lab/scripts/adv_attack3_{z3xz7, verify, recheck, scope}.py`.

**Updated recommendations:**

1. ~~Write `HANDOFF_C4_R4.md`~~ — **WITHDRAWN.** R1 + R4 has no provable
   form in its currently-stated hypothesis domain.
2. **Lin–Pryadko Statement 12 remains the only correct Lean target**
   for analytic distance bounds on BB codes in the C-program's lineage.
3. The empirical "0 violations on c ≥ 3" finding from the corpus sweep
   is now understood as an artifact of the corpus being dominated by
   single-prime `G_odd`. The failure regime is multi-prime `G_odd` with
   rank-1 on at least one prime — which includes `[[90, 8, 10]]`'s
   group structure (`Z_3² × Z_5`), though its specific polynomials
   happen to avoid the failure.
4. **The C-program (Cv1 → Cv2 → Cv3 → R1+R4) is closed** with no
   surviving bound on the Bravyi engineering target. The `w_1` weight
   invariant (Cv1) stands as a standalone contribution; the
   distance-bound thread is exhausted.
