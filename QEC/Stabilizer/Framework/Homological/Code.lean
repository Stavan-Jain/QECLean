import Mathlib.Tactic

/-!
# Length-3 chain complexes over `ZMod 2`

A `HomologicalCode` is a chain complex `C₂ →∂₂ C₁ →∂₁ C₀` over `𝔽₂` on finite
cell types, with `∂₁ ∘ ∂₂ = 0`, together with a numbering of the 1-cells by
`Fin numQubits`. It is the data of a CSS code with one qubit per 1-cell, one
X-check per 2-cell and one Z-check per 0-cell, encoding `dim H₁` logical
qubits.

This file provides the chain-level API:

* `HomologicalCode`, with `cycles`, `boundaries`, the homology `H1` and
  `boundaries_le_cycles`;
* the dimension counts `rank_nullity_boundary1`, `rank_nullity_boundary2` and
  `finrank_H1_eq_cycles_sub_boundaries`;
* the transposes `cutMap` of `∂₁` and `dualBoundary` of `∂₂`, with the pairing
  identities `boundary1_cutMap_transpose` and
  `boundary2_dualBoundary_transpose`;
* the dual complex: `dualCycles`, `dualBoundaries`,
  `dualBoundaries_le_dualCycles`, and the pairing certificate
  `not_mem_boundaries_of_dual_witness` for a chain not being a boundary.

The notation `dim₂ V` (scope `Homology`) abbreviates
`Module.finrank (ZMod 2) V`.
-/

/-- `dim₂ V` is `Module.finrank (ZMod 2) V`, the `𝔽₂`-dimension of a chain
space, cycle space, or homology group. It elaborates to exactly
`Module.finrank (ZMod 2) V`, and is printed back while the scope is open.
Scoped: enable with `open scoped Homology`. -/
scoped[Homology] notation "dim₂" => Module.finrank (ZMod 2)

namespace Quantum
namespace Stabilizer
namespace Homological

open scoped BigOperators
open scoped Homology

open Lean Elab Command in
/-- Display test: elaborate `stx` and check that its pretty-printed text is
`expected` (`exact := false`: contains `expected`). Run through `run_cmd` so no
`#`-command is needed. -/
private def checkDisplay (stx : Syntax) (expected : String) (exact : Bool := true) :
    CommandElabM Unit :=
  liftTermElabM do
    let e ← Term.elabTerm stx none
    Term.synthesizeSyntheticMVarsNoPostponing
    let s := toString (← Meta.ppExpr (← instantiateMVars e))
    unless (if exact then s == expected else (s.splitOn expected).length > 1) do
      throwError "display test failed:{indentD s}\nexpected{indentD expected}"

run_cmd do
  checkDisplay (← `(Module.finrank (ZMod 2) (Fin 3 → ZMod 2))) "dim₂ (Fin 3 → ZMod 2)"

/-! ## Coordinate lemmas over `ZMod 2` -/

/-- Every element of `ZMod 2` is `0` or `1`. -/
lemma zmod2_eq_zero_or_eq_one (a : ZMod 2) : a = 0 ∨ a = 1 := by
  revert a
  decide

/-- An element of `ZMod 2` is nonzero iff it is `1`. -/
lemma zmod2_ne_zero_iff {a : ZMod 2} : a ≠ 0 ↔ a = 1 := by
  revert a
  decide

/-- A linear map between `𝔽₂`-coordinate spaces, expanded in the standard basis
of its domain: `(T c) b = ∑ a, c a * (T δ_a) b` with `δ_a := Pi.single a 1`. -/
lemma linearMap_apply_eq_sum_single {A B : Type*} [Fintype A] [DecidableEq A]
    (T : (A → ZMod 2) →ₗ[ZMod 2] (B → ZMod 2)) (c : A → ZMod 2) (b : B) :
    T c b = ∑ a, c a * T (Pi.single a 1) b := by
  have hc : c = ∑ a, c a • (Pi.single a (1 : ZMod 2)) := by
    ext a
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hc]
  simp [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

/-- Transposition in coordinates: pairing `T c` with `s` is pairing `c` with
the transpose of `T` applied to `s`, where the standard pairing is
`⟨a, b⟩ = ∑ x, a x * b x`. -/
lemma sum_apply_mul_eq_sum_mul_sum_single {A B : Type*} [Fintype A] [DecidableEq A]
    [Fintype B] (T : (A → ZMod 2) →ₗ[ZMod 2] (B → ZMod 2)) (c : A → ZMod 2)
    (s : B → ZMod 2) :
    ∑ b, T c b * s b = ∑ a, c a * ∑ b, s b * T (Pi.single a 1) b := by
  simp_rw [linearMap_apply_eq_sum_single T c, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

/-! ## The chain complex -/

/-- A length-3 chain complex `C₂ →∂₂ C₁ →∂₁ C₀` over `ZMod 2` with finite,
decidable cell types, chains being `ZMod 2`-valued functions on the cells,
together with a numbering of the 1-cells by `Fin numQubits`. -/
structure HomologicalCode where
  /-- Type of 0-cells (e.g. vertices). -/
  C0 : Type
  /-- Type of 1-cells (e.g. edges); these are the physical qubits. -/
  C1 : Type
  /-- Type of 2-cells (e.g. faces). -/
  C2 : Type
  /-- Decidable equality on 0-cells. -/
  decEq0 : DecidableEq C0
  /-- Decidable equality on 1-cells. -/
  decEq1 : DecidableEq C1
  /-- Decidable equality on 2-cells. -/
  decEq2 : DecidableEq C2
  /-- Finitely many 0-cells. -/
  fin0 : Fintype C0
  /-- Finitely many 1-cells. -/
  fin1 : Fintype C1
  /-- Finitely many 2-cells. -/
  fin2 : Fintype C2
  /-- Boundary map `∂₁` from 1-chains to 0-chains. -/
  boundary1 : (C1 → ZMod 2) →ₗ[ZMod 2] (C0 → ZMod 2)
  /-- Boundary map `∂₂` from 2-chains to 1-chains. -/
  boundary2 : (C2 → ZMod 2) →ₗ[ZMod 2] (C1 → ZMod 2)
  /-- Chain-complex law: `∂₁ ∘ ∂₂ = 0`. -/
  boundary_comp : boundary1.comp boundary2 = 0
  /-- The number of physical qubits. It is a field, tied to the 1-cells by
  `numQubits_eq`, so that each instance can use its own expression for it
  (e.g. `2 * L * L` for the toric code) and the type
  `NQubitPauliGroupElement numQubits` is the one that instance works with. -/
  numQubits : ℕ
  /-- The number of qubits is the number of 1-cells. -/
  numQubits_eq : @Fintype.card C1 fin1 = numQubits
  /-- The numbering of the 1-cells by qubit indices, chosen by each instance. -/
  edgeEquiv : C1 ≃ Fin numQubits

namespace HomologicalCode

attribute [instance] decEq0 decEq1 decEq2 fin0 fin1 fin2

variable (X : HomologicalCode)

/-- Pointwise form of the chain-complex law. -/
theorem boundary_comp_apply (f : X.C2 → ZMod 2) :
    X.boundary1 (X.boundary2 f) = 0 :=
  LinearMap.congr_fun X.boundary_comp f

/-- 1-cycles: `Z₁ = ker ∂₁`. -/
def cycles : Submodule (ZMod 2) (X.C1 → ZMod 2) :=
  LinearMap.ker X.boundary1

/-- 1-boundaries: `B₁ = im ∂₂`. -/
def boundaries : Submodule (ZMod 2) (X.C1 → ZMod 2) :=
  LinearMap.range X.boundary2

/-- Boundaries are cycles (`im ∂₂ ≤ ker ∂₁`). -/
theorem boundaries_le_cycles : X.boundaries ≤ X.cycles := by
  rintro _ ⟨f, rfl⟩
  exact X.boundary_comp_apply f

/-- Cycle membership unfolds to `∂₁ c = 0`. -/
@[simp] theorem mem_cycles_iff (c : X.C1 → ZMod 2) :
    c ∈ X.cycles ↔ X.boundary1 c = 0 :=
  LinearMap.mem_ker

/-- Boundary membership unfolds to existence of a 2-chain witness. -/
theorem mem_boundaries_iff (c : X.C1 → ZMod 2) :
    c ∈ X.boundaries ↔ ∃ f : X.C2 → ZMod 2, X.boundary2 f = c :=
  Iff.rfl

/-- `B₁` viewed as a submodule of `Z₁`. -/
abbrev boundarySubmoduleInCycles : Submodule (ZMod 2) X.cycles :=
  Submodule.comap X.cycles.subtype X.boundaries

/-- First homology `H₁ = Z₁ / B₁`. -/
abbrev H1 : Type :=
  X.cycles ⧸ X.boundarySubmoduleInCycles

/-! ## Dimension counts -/

/-- The `C₀` chain space has `Fintype.card C₀` dimensions. -/
theorem finrank_C0 :
    dim₂ (X.C0 → ZMod 2) = Fintype.card X.C0 :=
  Module.finrank_fintype_fun_eq_card (R := ZMod 2) (η := X.C0)

/-- The `C₁` chain space has `Fintype.card C₁` dimensions. -/
theorem finrank_C1 :
    dim₂ (X.C1 → ZMod 2) = Fintype.card X.C1 :=
  Module.finrank_fintype_fun_eq_card (R := ZMod 2) (η := X.C1)

/-- The `C₂` chain space has `Fintype.card C₂` dimensions. -/
theorem finrank_C2 :
    dim₂ (X.C2 → ZMod 2) = Fintype.card X.C2 :=
  Module.finrank_fintype_fun_eq_card (R := ZMod 2) (η := X.C2)

/-- Rank-nullity for `∂₁`: `dim C₁ = dim Z₁ + rank ∂₁`. -/
theorem rank_nullity_boundary1 :
    dim₂ (X.C1 → ZMod 2) = dim₂ X.cycles + dim₂ (LinearMap.range X.boundary1) := by
  simpa [cycles, add_comm] using
    (LinearMap.finrank_range_add_finrank_ker X.boundary1).symm

/-- Rank-nullity for `∂₂`: `dim C₂ = dim (ker ∂₂) + dim B₁`. -/
theorem rank_nullity_boundary2 :
    dim₂ (X.C2 → ZMod 2) = dim₂ (LinearMap.ker X.boundary2) + dim₂ X.boundaries := by
  simpa [boundaries, add_comm] using
    (LinearMap.finrank_range_add_finrank_ker X.boundary2).symm

/-- The dimension of homology: `dim H₁ = dim Z₁ - dim B₁`. -/
theorem finrank_H1_eq_cycles_sub_boundaries :
    dim₂ X.H1 = dim₂ X.cycles - dim₂ X.boundaries := by
  rw [← (Submodule.comapSubtypeEquivOfLe X.boundaries_le_cycles).finrank_eq]
  exact Nat.eq_sub_of_add_eq (Submodule.finrank_quotient_add_finrank _)

/-! ## The transposes of the boundary maps -/

/-- The `𝔽₂`-transpose of `∂₁`, written as a finite sum:
`(cutMap s) e = ∑ v, s v * (∂₁ δ_e) v` with `δ_e := Pi.single e 1`. The cut of
a single vertex is the Z-check at that vertex. -/
noncomputable def cutMap : (X.C0 → ZMod 2) →ₗ[ZMod 2] (X.C1 → ZMod 2) where
  toFun s := fun e => ∑ v : X.C0, s v * X.boundary1 (Pi.single e 1) v
  map_add' s t := by
    ext e
    simp [add_mul, Finset.sum_add_distrib]
  map_smul' a s := by
    ext e
    simp [Finset.mul_sum, mul_assoc]

@[simp] theorem cutMap_apply (s : X.C0 → ZMod 2) (e : X.C1) :
    X.cutMap s e = ∑ v : X.C0, s v * X.boundary1 (Pi.single e 1) v := rfl

/-- Pointwise expansion of `∂₁` in the standard basis of `C₁`:
`(∂₁ c) v = ∑ e, c e * (∂₁ δ_e) v` with `δ_e := Pi.single e 1`. -/
theorem boundary1_apply_eq_sum (c : X.C1 → ZMod 2) (v : X.C0) :
    X.boundary1 c v = ∑ e : X.C1, c e * X.boundary1 (Pi.single e 1) v :=
  linearMap_apply_eq_sum_single X.boundary1 c v

/-- `cutMap` is the transpose of `∂₁`: `⟨∂₁ c, s⟩ = ⟨c, cutMap s⟩` for the
standard pairing `⟨a, b⟩ = ∑ x, a x * b x`. -/
theorem boundary1_cutMap_transpose (c : X.C1 → ZMod 2) (s : X.C0 → ZMod 2) :
    ∑ v : X.C0, X.boundary1 c v * s v =
      ∑ e : X.C1, c e * X.cutMap s e :=
  sum_apply_mul_eq_sum_mul_sum_single X.boundary1 c s

/-- The `𝔽₂`-transpose of `∂₂`, written as a finite sum:
`(dualBoundary c) f = ∑ e, c e * (∂₂ δ_f) e` with `δ_f := Pi.single f 1`. -/
noncomputable def dualBoundary :
    (X.C1 → ZMod 2) →ₗ[ZMod 2] (X.C2 → ZMod 2) where
  toFun c := fun f => ∑ e : X.C1, c e * X.boundary2 (Pi.single f 1) e
  map_add' c d := by
    ext f
    simp [add_mul, Finset.sum_add_distrib]
  map_smul' a c := by
    ext f
    simp [Finset.mul_sum, mul_assoc]

@[simp] theorem dualBoundary_apply (c : X.C1 → ZMod 2) (f : X.C2) :
    X.dualBoundary c f = ∑ e : X.C1, c e * X.boundary2 (Pi.single f 1) e := rfl

/-- `dualBoundary` is the transpose of `∂₂`:
`⟨∂₂ f, c⟩ = ⟨f, dualBoundary c⟩`. -/
theorem boundary2_dualBoundary_transpose
    (f : X.C2 → ZMod 2) (c : X.C1 → ZMod 2) :
    ∑ e : X.C1, X.boundary2 f e * c e =
      ∑ p : X.C2, f p * X.dualBoundary c p :=
  sum_apply_mul_eq_sum_mul_sum_single X.boundary2 f c

/-! ## The dual complex -/

/-- Dual cycles: the kernel of `dualBoundary`. -/
noncomputable def dualCycles : Submodule (ZMod 2) (X.C1 → ZMod 2) :=
  LinearMap.ker X.dualBoundary

/-- Dual boundaries: the range of `cutMap`. -/
noncomputable def dualBoundaries : Submodule (ZMod 2) (X.C1 → ZMod 2) :=
  LinearMap.range X.cutMap

/-- The dual chain-complex law `dualBoundary ∘ cutMap = 0`, the transpose of
`∂₁ ∘ ∂₂ = 0`. -/
theorem dualBoundary_cutMap (s : X.C0 → ZMod 2) : X.dualBoundary (X.cutMap s) = 0 := by
  funext f
  rw [dualBoundary_apply, Finset.sum_congr rfl fun e _ => mul_comm _ _,
    ← X.boundary1_cutMap_transpose, X.boundary_comp_apply]
  simp

/-- Dual boundaries are dual cycles. -/
theorem dualBoundaries_le_dualCycles : X.dualBoundaries ≤ X.dualCycles := by
  rintro _ ⟨s, rfl⟩
  exact X.dualBoundary_cutMap s

variable {X}

/-- Dual-pairing certificate for a chain not being a boundary: if `w` is a dual
cycle and pairs to `1` with `c`, then `c` is not a boundary, since boundaries
pair to `0` with dual cycles by `boundary2_dualBoundary_transpose`. -/
theorem not_mem_boundaries_of_dual_witness
    {w c : X.C1 → ZMod 2}
    (hw : X.dualBoundary w = 0) (hpair : ∑ e : X.C1, w e * c e = 1) :
    c ∉ X.boundaries := by
  rintro ⟨f, rfl⟩
  rw [Finset.sum_congr rfl fun e _ => mul_comm _ _, X.boundary2_dualBoundary_transpose f w,
    hw] at hpair
  simp at hpair

end HomologicalCode

end Homological
end Stabilizer
end Quantum
