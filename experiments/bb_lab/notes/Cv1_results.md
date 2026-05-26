# C-v1 — results

Date: 2026-05-26.

Summary of the C-v1 deliverable: definition of `w_μ(A, O)`, the
weight-aware Jacobson-radical filtration invariant for `F_2[G]`
(non-semisimple). See [`Cv1_design.md`](Cv1_design.md) for the
mathematical setup and [`Cv1_literature.md`](Cv1_literature.md) for
prior-art positioning.

## 1. Definition (recap)

For `G = G_odd × G_2` abelian, `F_2[G] = ⊕_O R_O` with
`R_O = F_{2^|O|}[G_2]` (Frobenius orbits on `Ĝ_odd`), each `R_O` a
local ring with maximal ideal `m_O = aug(F_{2^|O|}[G_2])`. For
`A ∈ F_2[G]` and `μ ∈ {1, …, L}` where `L = loewy_length(G)`:

```
V_{O, μ}(A) := { f ∈ R_O ⊂ F_2[G] : f · A = 0, f ∈ m_O^{μ−1} }
w_μ(A, O)   := min { |f|_H : f ∈ V_{O, μ}(A) \ {0} }     (∞ if {0})
```

## 2. Property check against (W1)–(W4)

| Property | Status |
|---|---|
| (W1) Invariance under G-translation × Aut(G) × block-swap | ✓ (proven structurally; tested for translation) |
| (W1) Invariance under F_2[G]-units | ✗ (per HANDOFF_C §7 — Hamming weight not preserved by units; restricted equivalence accepted) |
| (W2) `min \|·\|_H` over an F_2-subspace | ✓ by construction |
| (W3) Computable in the corpus regime | ✓ (~0.1s per orbit for gross; basis dim ≤ 4 in tests) |
| (W4) Semisimple-limit recovery → `per_orbit_dual_distance` | ✓ (tested on Z_3 × Z_3, Z_3 × Z_5) |

Per HANDOFF_C §4 stop conditions: this is outcome **(b)** — a clean
definition satisfying (W1)–(W4) with the documented restriction
that F_2[G]-unit invariance is dropped (because Hamming weight is
not preserved by unit multiplication).

## 3. Gross numerical table

`G = Z_12 × Z_6 = G_odd × G_2 = (Z_3 × Z_3) × (Z_4 × Z_2)`.
Loewy length `L = 5`. Five Frobenius orbits on `Ĝ_odd = Z_3 × Z_3`,
of sizes `1, 2, 2, 2, 2`.

### 3.1 `A = x³ + y + y²` (grossA)

| Orbit (rep) | size | μ_O | w_1 | w_2 | w_3 | w_4 | w_5 |
|:---|:---:|:---:|:---:|:---:|:---:|:---:|:---:|
| (0, 0) | 1 | 0 | ∞ | ∞ | ∞ | ∞ | ∞ |
| (0, 1)  ↔ (0, 2) | 2 | 2 | **36** | 36 | 36 | 36 | **48** |
| (1, 0)  ↔ (2, 0) | 2 | 0 | ∞ | ∞ | ∞ | ∞ | ∞ |
| (1, 1)  ↔ (2, 2) | 2 | 2 | **36** | 36 | 36 | 36 | **48** |
| (1, 2)  ↔ (2, 1) | 2 | 2 | **36** | 36 | 36 | 36 | **48** |

### 3.2 `B = y³ + x + x²` (grossB)

Same structure by the `x ↔ y` symmetry of gross:

| Orbit (rep) | size | μ_O | w_1 | w_2 | w_3 | w_4 | w_5 |
|:---|:---:|:---:|:---:|:---:|:---:|:---:|:---:|
| (0, 0) | 1 | 0 | ∞ | ∞ | ∞ | ∞ | ∞ |
| (0, 1)  ↔ (0, 2) | 2 | 0 | ∞ | ∞ | ∞ | ∞ | ∞ |
| (1, 0)  ↔ (2, 0) | 2 | 2 | **36** | 36 | 36 | 36 | **48** |
| (1, 1)  ↔ (2, 2) | 2 | 2 | **36** | 36 | 36 | 36 | **48** |
| (1, 2)  ↔ (2, 1) | 2 | 2 | **36** | 36 | 36 | 36 | **48** |

### 3.3 Observations

- **All vanishing orbits give identical w_μ profiles** for both A and B.
  This is consistent with the Aut(G)-orbit structure on gross — the
  three vanishing orbits for A are permuted by the `(x_axis_odd ↔
  y_axis_odd)` symmetry and analogous automorphisms.
- **The `w_μ` value plateaus** at 36 for `μ ∈ {1, …, 4}`, then jumps
  to 48 at `μ = 5`. The plateau means the radical-depth filtration
  doesn't tighten the min-weight witness until the very last layer.
- **The jump 36 → 48 at μ = 5** corresponds to forcing `f ∈ m_O^4`,
  which (for `G_2 = Z_4 × Z_2`) is the 1-dimensional `F_{2^|O|}`-span
  of `y³z`. Any non-zero element is `c · e_O · y³z` for `c ∈ F_4^*`,
  with support `|supp(e_O)| · |supp(y³z)| = 6 · 8 = 48`. So `w_5`
  is structurally determined.
- **HANDOFF_C §4.6 threshold check**: "at least one (orbit, μ)
  entry should give a value ≥ 6 to be even potentially useful for
  downstream C-v2/v3/v4 work". The table has values ≥ 36 across the
  board for vanishing orbits — well above the threshold. The
  "useful" question for C-v2 is whether these values can be combined
  into a distance bound, which is **out of scope** for C-v1.

## 4. Divergence from `per_orbit_dual_distance` on non-semisimple G

A noteworthy structural finding (validated by `test_w_mu_diverges_
from_per_orbit_dual_on_non_semisimple_gross`):

| Quantity | Gross vanishing orbit |
|---|---|
| `per_orbit_dual_distance(grossA, O)` (existing) | 12 |
| `w_1(grossA, O)` (C-v1) | 36 |

The existing `per_orbit_dual_distance` uses the G_2-fiber-summed
character constraint (`_char_constraint_rows_g_odd` projects to
G_odd by summing fibers). C-v1's `w_1` uses the proper per-fiber
per-orbit constraint, which is strictly more restrictive on
non-semisimple G. Result: `w_1 ≥ per_orbit_dual_distance`, with
strict inequality on gross.

The semisimple-limit recovery (Z_3 × Z_5, Z_3 × Z_3 in tests) shows
the two coincide when `G_2 = trivial`. The divergence in the
non-semisimple case is a feature, not a bug: C-v1 sees the proper
R_O structure that fiber-summing washes out.

**Follow-up question (NOT for C-v1)**: should
`weight_invariants.per_orbit_dual_distance` be updated to use the
proper per-fiber constraint? This would change the function's
return values on non-semisimple G and may have downstream effects
on existing tier-2/3 conjecture tests. Documenting as a separate
issue, not pursuing in this session.

## 5. Implementation summary

- New module:
  [`src/bb_lab/radical_weight.py`](../src/bb_lab/radical_weight.py)
  — public API `w_mu`, `w_mu_table`, `loewy_length`,
  `jacobson_filtration_dims`; private helpers
  `r_o_constraint_rows`, `loewy_depth_constraint_rows`.
- New tests:
  [`tests/test_radical_weight.py`](../tests/test_radical_weight.py)
  — 26 tests covering Loewy structure, Z_4 chain ring, semisimple
  recovery, invariance, gross table, monotonicity, API edge cases.
- Reproducibility script:
  [`scripts/cv1_gross_table.py`](../scripts/cv1_gross_table.py)
  — prints the §3 table.
- Notes:
  [`notes/Cv1_literature.md`](Cv1_literature.md),
  [`notes/Cv1_design.md`](Cv1_design.md), this file.

No existing module modified (per HANDOFF_C §6 hard constraint).

## 6. Out-of-scope items (for future handoffs)

- **C-v2**: Propose a distance bound `d_X ≥ F(w_μ values)`. The
  gross w_μ values (36, 48) are higher than the actual `d = 12`,
  so any C-v2 bound must depend on combining values *across*
  orbits/levels — likely with some quotient or floor. Not pursued
  here.
- **Corpus-wide w_μ sweep**: Run `w_mu_table` over the 460-row
  corpus, report distribution of profiles by `(group, μ_O pattern,
  …)`. ~1 hour of compute. Useful Tier 2 input.
- **Update `per_orbit_dual_distance`?** The divergence in §4
  raises the question of whether the existing function should use
  the proper per-fiber constraint. Decided to defer — changes a
  public API and may break Tier 2/3 conjecture tests.
- **Non-prime-axis G_2**: gross has `G_2 = Z_4 × Z_2`. The C-v1
  implementation handles arbitrary abelian `G_2 = ∏_axis Z_{2^{a_axis}}`
  (the only structure where the (y_axis) generators provide a
  Loewy-graded basis). Mixed 2-Sylow with `Z_{2 ⋅ q}` for `q` odd
  would need a different treatment, but such G aren't in the BB
  setting.
- **Lean formalization (C-v3)**: definition is in Python; Lean
  port is its own multi-week task.
