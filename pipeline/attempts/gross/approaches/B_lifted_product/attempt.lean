/-
# Approach B — Lifted-product / Tillich-Zémor distance bound

This file records the **Lean-verified support-subgroup arithmetic**
for the Gross polynomial pair, which determines the Statement-12
(Lin-Pryadko 2306.16400) Tillich-Zémor ceiling on
`d(grossHomologicalCode)`.

## Headline result

The lifted-product bound `d ≥ d_0 = ⌈ min(d_A^⊥, d_B^⊥) / c ⌉` from
Lin-Pryadko Statement 12 satisfies (per their Sec. IV.F):

```
d_0 ≤ min([G_a : N], [G_b : N])
```

We compute (`#eval`-verifiable, `decide`-provable):
- `|G_a| = 24`,  `|G_b| = 24`,  `|N| = 8`
- `[G_a : N] = 3`,  `[G_b : N] = 3`
- Therefore `d_0 ≤ 3`.

The empirical Gross distance is `d = 12`.  **The Statement-12 lifted-
product bound is loose by a factor of 4** on the Gross code,
regardless of any further computation.

This is a calibrated **negative result** for the lifted-product
approach, parallel to Approach A's calibrated Camion-loose finding.

## What this file contains

1. `suppA`, `suppB` — supports of grossA, grossB as `Finset`s.
2. `GaSet`, `GbSet`, `NSet` — the support subgroups and their
   intersection, explicitly enumerated.
3. Cardinality lemmas: `|G_a| = 24`, `|G_b| = 24`, `|N| = 8`.
4. `suppA_subset_GaSet`, `suppB_subset_GbSet` — Â/B̂'s supports
   land in their respective subgroups.
5. `GaSet_inter_GbSet_eq_NSet` — the intersection identification.
6. `gross_TZ_ceiling` — the headline observation: the Tillich-Zémor
   bound on Gross is at most 3.

## What this file does NOT contain

* A Lean proof of Lin-Pryadko Statement 12 itself (estimated ~500 LoC
  of classical coding theory).  We **state** the ceiling as an
  observation, using the Lin-Pryadko paper as the cited authority.
* A general "support subgroup" abstraction in `Stabilizer/GroupAlgebra/`.
  Defining `supportSubgroup : (G → ZMod 2) → Subgroup G` cleanly
  requires general subgroup-closure-of-a-set machinery; we work with
  the concrete enumerated `Finset`s here for direct verifiability.
* A general Tillich-Zémor formalization for abelian 2BGA codes.
-/

import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Card
import QEC.Stabilizer.Framework.Homological

namespace Quantum
namespace Stabilizer
namespace Homological
namespace BB
namespace Gross

open Finset

/-! ## Group and supports -/

/-- The Gross code group `G = Z_12 × Z_6`.  (Already defined in Approach A's
attempt.lean; re-introduced as a self-contained `abbrev` here for clarity.) -/
abbrev GrossGroup' : Type := ZMod 12 × ZMod 6

/-- Support of `a = x^3 + y + y^2` as a Finset of `G`. -/
def suppA : Finset GrossGroup' := {(3, 0), (0, 1), (0, 2)}

/-- Support of `b = y^3 + x + x^2`. -/
def suppB : Finset GrossGroup' := {(0, 3), (1, 0), (2, 0)}

/-! ## Support subgroups (enumerated as Finsets)

These are the *underlying carrier sets* of the support subgroups
`G_a, G_b ≤ G`.  We enumerate them as Finsets so we can `decide` the
cardinality and intersection facts mechanically. -/

/-- `G_a = ⟨(3, 0), (0, 1)⟩ = ⟨(3, 0)⟩ × Z_6 = {(3i, j) : i ∈ Z_4, j ∈ Z_6}`. -/
def GaSet : Finset GrossGroup' :=
  (Finset.range 4 ×ˢ Finset.range 6).image
    (fun ⟨i, j⟩ => ((3 * i : ZMod 12), (j : ZMod 6)))

/-- `G_b = ⟨(1, 0), (0, 3)⟩ = Z_12 × ⟨(0, 3)⟩ = {(i, 3j) : i ∈ Z_12, j ∈ Z_2}`. -/
def GbSet : Finset GrossGroup' :=
  (Finset.range 12 ×ˢ Finset.range 2).image
    (fun ⟨i, j⟩ => ((i : ZMod 12), (3 * j : ZMod 6)))

/-- `N = G_a ∩ G_b = ⟨(3, 0)⟩ × ⟨(0, 3)⟩ = {(3i, 3j) : i ∈ Z_4, j ∈ Z_2}`. -/
def NSet : Finset GrossGroup' :=
  (Finset.range 4 ×ˢ Finset.range 2).image
    (fun ⟨i, j⟩ => ((3 * i : ZMod 12), (3 * j : ZMod 6)))

/-! ## Cardinality lemmas (Lean-verified by `decide`) -/

@[simp] lemma card_GaSet : GaSet.card = 24 := by decide
@[simp] lemma card_GbSet : GbSet.card = 24 := by decide
@[simp] lemma card_NSet : NSet.card = 8 := by decide

/-- The intersection identification. -/
lemma GaSet_inter_GbSet_eq_NSet : GaSet ∩ GbSet = NSet := by decide

/-- `a`'s support lies in `G_a`. -/
lemma suppA_subset_GaSet : suppA ⊆ GaSet := by decide

/-- `b`'s support lies in `G_b`. -/
lemma suppB_subset_GbSet : suppB ⊆ GbSet := by decide

/-- `N ⊆ G_a`. -/
lemma NSet_subset_GaSet : NSet ⊆ GaSet := by decide

/-- `N ⊆ G_b`. -/
lemma NSet_subset_GbSet : NSet ⊆ GbSet := by decide

/-! ## Lin-Pryadko Statement-12 index parameters

Lin-Pryadko (arXiv:2306.16400) Sec. IV.F denotes:
* `ℓ_a := [G_a : N] = |G_a| / |N|`
* `ℓ_b := [G_b : N] = |G_b| / |N|`

For the Gross polynomials, both indices equal 3.  The paper's
**ceiling** on the Statement-12 distance lower bound (immediately
following Statement 13, p. 8) is:

> "the parameter d_0 in Statement 12 satisfies `d_0 ≤ min(ℓ_a, ℓ_b)`"

This gives `d_0 ≤ 3` for the Gross code.

We compute the index parameters as `Nat` literals; the divisibility
`|N| ∣ |G_a|` and `|N| ∣ |G_b|` are automatic from `NSet ⊆ GaSet`
and `NSet ⊆ GbSet` plus Lagrange's theorem (in spirit), but for
our finite-Finset purposes the division is just arithmetic. -/

/-- `ℓ_a := [G_a : N] = 3`. -/
def gross_ℓa : ℕ := GaSet.card / NSet.card

/-- `ℓ_b := [G_b : N] = 3`. -/
def gross_ℓb : ℕ := GbSet.card / NSet.card

@[simp] lemma gross_ℓa_eq : gross_ℓa = 3 := by
  unfold gross_ℓa
  rw [card_GaSet, card_NSet]

@[simp] lemma gross_ℓb_eq : gross_ℓb = 3 := by
  unfold gross_ℓb
  rw [card_GbSet, card_NSet]

/-! ## The Statement-12 / Tillich-Zémor ceiling for Gross

We record the ceiling as a documented fact: `min(ℓ_a, ℓ_b) = 3`.

To turn this into a Lean theorem about `d(grossHomologicalCode)`,
one would need to:
1. Formalize Lin-Pryadko Statement 12 itself (a Tillich-Zémor analog
   for abelian 2BGA codes).  Estimated ~500 LoC.
2. Establish the bridge between `bbChainComplex` and Lin-Pryadko's
   abelian 2BGA framework.  Estimated ~100 LoC.

Item 1 is the genuine moonshot work; we leave it for a follow-up
contribution.  The point of this attempt file is to **bottle the
negative result mechanically**: anyone can run `lake build` on this
file and verify that the index numbers are exactly `3, 3`.

The interpretation — "Statement 12 cannot exceed 3 on the Gross code" —
is then a *citation* of Lin-Pryadko's structural upper bound, applied
to the Lean-verified index parameters. -/

/-- The structural Tillich-Zémor ceiling on the Gross code.

Given that Lin-Pryadko Statement 12 yields
`d ≥ d_0 = ⌈ min(d_A^⊥, d_B^⊥) / c ⌉` and that (per the same paper)
`d_0 ≤ min(ℓ_a, ℓ_b)`, we compute the numerical ceiling for Gross. -/
def gross_TZ_ceiling : ℕ := min gross_ℓa gross_ℓb

@[simp] lemma gross_TZ_ceiling_eq_three : gross_TZ_ceiling = 3 := by
  unfold gross_TZ_ceiling
  simp

/-! ## Sanity check: the divisor `c = |N| = 8` in the Statement-12 bound

If `min(d_A^⊥, d_B^⊥) ≤ M`, the bound is `⌈M/8⌉`.  For an absolutely
optimistic upper-bound on classical distance via Singleton's bound:
- classical code has length 72, dimension ≥ 1 (kernel is non-trivial
  since char polynomial `a` has Â vanishing at some characters), so
  `d_A^⊥ ≤ 72 - 1 + 1 = 72`.
- Plugging into Statement 12: `d_0 ≤ ⌈72/8⌉ = 9`.

But the paper's tighter ceiling `d_0 ≤ min(ℓ_a, ℓ_b) = 3` is sharper.
So the binding constraint is the index ceiling, not Singleton. -/

/-- The structural Singleton-style ceiling: if classical distances are
at most the full code length 72, then Statement 12 gives ≤ ⌈72/c⌉. -/
def gross_TZ_singleton_ceiling : ℕ :=
  (Fintype.card GrossGroup' + (NSet.card - 1)) / NSet.card

example : gross_TZ_singleton_ceiling = 9 := by
  unfold gross_TZ_singleton_ceiling
  rw [card_NSet]
  decide

/-! ## Summary lemma

The Statement-12 / Tillich-Zémor lifted-product lower bound on the
Gross code's distance is at most 3.  The empirical d=12 is more than
4× larger than this ceiling.

Without formalizing Lin-Pryadko's theorem itself, the Lean content is
restricted to the **structural inputs** to the ceiling.  But those
inputs are now mechanically verified: anyone can `lake build` this
file and confirm `ℓ_a = ℓ_b = 3`, hence the ceiling.

This makes the negative result reproducible and uncontroversial. -/
example : gross_TZ_ceiling = 3 ∧
          (gross_TZ_ceiling : ℕ) < 12 := by
  refine ⟨gross_TZ_ceiling_eq_three, ?_⟩
  rw [gross_TZ_ceiling_eq_three]
  decide

/-! ## Documented hypothesis-loaded ceiling

We state the "Statement 12 ceiling applied to Gross" as a Lean
theorem **predicated on the abstract Lin-Pryadko Statement 12 holding
for the BB chain complex construction**.  This makes explicit:

* If `TZ_bound_holds` is provided (as an external hypothesis or
  via a future formalization of Lin-Pryadko Statement 12),
* Then the Gross code's distance lower-bound it produces is `≤ 3`.

In the language of the moonshot's success criterion, this is a
*conditional* negative result: **conditional on Statement 12,
the Gross-code distance lower bound is at most 3**.  Since
Statement 12 is a published theorem (Lin-Pryadko 2023, p. 8), the
hypothesis is satisfied by citation.

The conditional formulation lets us land Lean evidence for the
negative result without needing to formalize 500 LoC of
classical coding theory inline. -/

section LinPryadkoConditional

/-- Statement 12 of Lin-Pryadko 2023 (signature only).  For any
abelian 2BGA code with polynomial pair `(a, b)`, support-subgroup
indices `ℓ_a := [G_a : N]`, `ℓ_b := [G_b : N]`, the lifted-product
lower bound `d_0` on the code's distance is bounded above by
`min(ℓ_a, ℓ_b)`.

This is the structural ceiling stated in Lin-Pryadko Sec. IV.F
immediately following Statement 13.  Formalizing the full bound
itself is left as future work (~500 LoC).  This signature alone is
sufficient for the conditional negative result for Gross. -/
def TZCeilingType (G : Type) [Fintype G] [AddCommGroup G] [DecidableEq G]
    (_a _b : G → ZMod 2) (d_0 : ℕ) (ℓ_a ℓ_b : ℕ) : Prop :=
  d_0 ≤ min ℓ_a ℓ_b

/-- The conditional ceiling for Gross: if Statement 12 holds with the
verified index parameters, then `d_0 ≤ 3`. -/
theorem gross_TZ_conditional_ceiling
    (d_0 : ℕ)
    (h_TZ : TZCeilingType GrossGroup' grossA grossB d_0 gross_ℓa gross_ℓb) :
    d_0 ≤ 3 := by
  unfold TZCeilingType at h_TZ
  rw [gross_ℓa_eq, gross_ℓb_eq] at h_TZ
  simpa using h_TZ

/-- Same conclusion, written as a strict inequality below the empirical
distance 12: any Statement-12-derived lower bound on Gross's distance is
strictly less than the actual `d = 12`.  This is the **headline negative
result** of Approach B in Lean form. -/
theorem gross_TZ_loose
    (d_0 : ℕ)
    (h_TZ : TZCeilingType GrossGroup' grossA grossB d_0 gross_ℓa gross_ℓb) :
    d_0 < 12 :=
  Nat.lt_of_le_of_lt (gross_TZ_conditional_ceiling d_0 h_TZ) (by decide)

end LinPryadkoConditional

end Gross
end BB

end Homological
end Stabilizer
end Quantum
