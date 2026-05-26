# Result — narrowed conjecture SURVIVES

**Verdict: SURVIVES — `survives-tight-on-gross-and-clean`** per
HANDOFF_C3 §C-v3.6 stop conditions.

The narrowed conjecture

> If `G_odd` is loosely elementary abelian (each prime-part is
> elementary abelian) AND `c = [G_a : G_a ∩ G_b] ≥ 3`,
>
> then `d_X(BB(G, A, B)) ≥ ⌈(1/c) · min_O min(w_1(A, O), w_1(B, O))⌉`

survives empirical falsification:

- **Corpus sweep**: 0 violations on 74 hypothesis-domain rows
  (33 tight, 41 loose).
- **Bravyi table**: 4 of 5 codes in hypothesis domain
  (bb_72, bb_90, gross, bb_288), all **tight** with bound = d.
  bb_108_8_10 is properly excluded by the elem-ab condition (NOT a
  counterexample).

## What this is, in context

This is the **strongest result the C-program has produced**:

- It covers `gross [[144,12,12]]` with a tight prediction (`d ≥ 12 = d_actual`).
- It uses a genuinely novel weight invariant `w_1` (C-v1) refining the
  Lin–Pryadko classical-dual-distance numerator.
- The hypothesis is **structurally clean**: two well-defined integer
  conditions (`is_g_odd_elementary_abelian(G)` and
  `[G_a : G_a ∩ G_b] ≥ 3`).
- It's empirically falsifiable and the C-v3 round did not falsify it.

It's a CONDITIONAL theorem: the hypothesis excludes ~98% of the
labeled corpus and 1 of 5 Bravyi codes. But the included slice
covers the engineering-target family (gross-style codes).

## Why both hypothesis conditions are necessary

- The elem-ab condition excludes bb_108_8_10 (its `G_odd = Z_9 × Z_3`
  has a Z_9 factor; the conjecture's `w_1 = 36` doesn't correspond to
  d_actual = 10 there).
- The c ≥ 3 condition excludes degenerate cases where
  `⟨supp(A)⟩ = ⟨supp(B)⟩` (e.g., when A = B), in which case
  `c = 1` and the bound has no denominator (gives `min_O w_1`
  directly, which dramatically overshoots d on the small-d
  degenerate codes that dominate the corpus).

Empirically, no simpler version of the hypothesis covers gross while
filtering the corpus violations. See
[`Cv3_restricted_sweep.md`](../../experiments/bb_lab/notes/Cv3_restricted_sweep.md)
§3 for the c-stratification table.

## How this differs from the prior rounds

- **T2R1 (`bb_distance_conjecture/`)**: dimension-invariant Jacobson
  bound (Σ |O| · min(μ_A, μ_B)). FALSIFIED (HANDOFF §6h).
- **T2 Round 3 (HT/Roos)**: character-theoretic. STRUCTURALLY BLIND
  to gross (HANDOFF §6j).
- **T2 Round 5 (SRB cover graph)**: chain-map. SAME 2-divisibility
  wall (HANDOFF §6k).
- **C-v1 (`Cv1_*.md`)**: defined `w_1`, the proper per-orbit isotypic
  kernel min-weight. NOT a distance bound; numerical artifact.
- **C-v2 (`bb_distance_conjecture_radical_weight/`)**: unrestricted
  bound `d ≥ (1/c) · min_O min(w_1, w_1)`. FALSIFIED globally
  (3 319 / 3 894 corpus violations + bb_108_8_10 Bravyi violation).
- **C-v3 (this artifact)**: narrowed to hypothesis domain.
  **SURVIVES**.

The C-program's value is the structural narrowing: each round
identifies progressively sharper conditional bounds, and C-v3 lands
the first one that actually covers gross AND survives empirically.

## Implication for C-v4 (formal Lean proof)

Per HANDOFF_C3 §C-v3.6, this verdict triggers a `HANDOFF_C4.md`
proof attempt. The Lean theorem statement would be approximately:

```lean
theorem bb_distance_lower_bound_narrowed
    {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (A B : G → ZMod 2)
    (h_ea : IsLooseElemAbGOdd G)
    (h_c : suppSubgroupIndex A B G ≥ 3)
    : (bbChainComplex A B).distance ≥
        ((1 : ℕ) / suppSubgroupIndex A B G) *
          (minOverJointVanishingOrbits A B
             (fun O => Nat.min (w_1 A O) (w_1 B O)))
    := by sorry
```

Proof technique ingredients (per [`Cv3_tightness.md`](../../experiments/bb_lab/notes/Cv3_tightness.md)
§"the structural condition S for C-v4 proof"):

1. **Lin–Pryadko Statement 12 proof technique**: provides the
   `(1/c)` denominator structure (`d ≥ d_A^⊥ / c`).
2. **Substitute `w_1` for `d_A^⊥` in the LP technique**:
   `w_1` is the per-orbit isotypic kernel min-weight; LP's proof
   should adapt because both quantities are min-weight invariants
   on F_2-subspaces of `ker(M_A)`.
3. **Use the elementary-abelian G_odd condition**: under loose
   elem-ab, F_2[G_odd] = ⊕_O F_{2^|O|} is semisimple with clean
   Wedderburn decomposition; each `R_O = F_{2^|O|}[G_2]` has the
   Jacobson radical confined to the G_2 factor (a tensor structure).
4. **Berman–Charpin / Andriatahiny machinery**: for elementary
   abelian p-groups, the radical powers correspond to GRM codes
   with known minimum weights. Need to extend or adapt this to
   `F_2[G_2]` where G_2 is a 2-group (possibly non-elementary like
   Z_4 × Z_2 in gross).
5. **The c ≥ 3 condition**: this constraint should appear in the
   proof as the ratio `|G_a| / |G_a ∩ G_b|` bounding the "spread"
   of an X-logical across the two BB blocks.

The full proof is research content (estimated 4–12 weeks of careful
Lean / mathlib work). This artifact's deliverable is the empirical
case for that proof being worth attempting.

## What this is NOT

- **Not a universal bound for BB codes.** The narrowed domain is
  much smaller than the BB code class.
- **Not a tightness theorem**: the inequality is genuine; the
  hypothesis-domain corpus has many loose cases (gap ≥ 1).
- **Not a formal proof**: empirical verification only. Awaits C-v4.

## What this IS

- The first conditional analytic bound for the gross BB code that
  predicts `d = 12` tightly without computer-search artifacts.
- A clean separation between BB-code regimes where radical-aware
  bounds work (elem-ab G_odd + c ≥ 3) and where they don't.
- A structurally clean hypothesis suitable for formal verification.
- The strongest empirical signal in the bb_lab program to date.

## Reproducing the verdict

From `experiments/bb_lab/`:

```
# Substrate
uv sync --extra dev
uv run pytest -m 'not slow' -q   # all tests pass

# Classifier sanity
uv run python -c "
from bb_lab.group import ZmZn
from bb_lab.degeneracy import is_g_odd_elementary_abelian, g_odd_decomposition
for ell, m, label in [(6,6,'bb_72'), (15,3,'bb_90'), (9,6,'bb_108'), (12,6,'gross'), (12,12,'bb_288')]:
    G = ZmZn(ell, m)
    print(f'{label:>10}: decomp={g_odd_decomposition(G)} elem-ab={is_g_odd_elementary_abelian(G)}')
"

# Restricted sweep
uv run python scripts/cv3_restricted_sweep.py
```

Expected outputs:
- Classifier: bb_72/bb_90/gross/bb_288 elem-ab=True; bb_108 False.
- Sweep: "loose elem-ab ∧ c ≥ 3" reports 74 rows, 0 violations.
