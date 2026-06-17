/-
# The weight-12 nontrivial cycle of the gross code

Headline (`gross_exists_weight12_nontrivial_cycle`): the gross complex has a
1-cycle of weight 12 that is not a boundary, namely the pullback `τ(u*)` of
the weight-6 base cycle `u*` whose right block is

  `z* = 1 + y + y² + y⁵ + x³ + x³y⁴`  (satisfying `A ⋆ z* = 0` over `Z₆ × Z₆`).

Non-boundaryness is certified by an explicit dual witness `w` with
`dualBoundary w = 0` and `⟨w, τ(u*)⟩ = 1`, fed to
`not_mem_boundaries_of_dual_witness`.  The witness support was found by `𝔽₂`
row reduction offline; its provenance is irrelevant since both defining
properties are re-checked here by `native_decide` (via the transpose formula
`bb_dualBoundary_eq`).

## Convention bridge (lab notes → repo)

Repo convention: `∂₂ f = (A⋆f | B⋆f)`, `∂₁ c = B⋆c_L + A⋆c_R`; cycle
condition `B⋆v_L = A⋆v_R`.  **Repo-left = lab-right** — hence `u*` carries
`z*` in the *right* block (so `∂₁ u* = B⋆0 + A⋆z* = 0`).
-/

import QEC.Stabilizer.Codes.BivariateBicycle.DeckHomotopy

namespace Quantum
namespace Stabilizer
namespace Homological
namespace BB

-- kernel decide needs more recursion headroom here.
set_option maxRecDepth 40000

open scoped BigOperators

/-! ## The base cycle `u*` -/

/-- `z* = 1 + y + y² + y⁵ + x³ + x³y⁴` over the base group `Z₆ × Z₆`. -/
def zStar : BaseGroup → ZMod 2 := fun g =>
  if g = (0, 0) ∨ g = (0, 1) ∨ g = (0, 2) ∨ g = (0, 5) ∨
     g = (3, 0) ∨ g = (3, 4) then 1 else 0

theorem conv_baseA_zStar : conv baseA zStar = 0 := by
  decide

/-- The base 1-chain `u*`: `z*` in the right block, zero in the left. -/
def uStar : BaseGroup × Fin 2 → ZMod 2 := fun p =>
  if p.2 = 1 then zStar p.1 else 0

theorem uStar_mem_cycles : uStar ∈ bb72Complex.cycles := by
  have h : bbBoundary1Fn baseA baseB uStar = 0 := by decide
  exact h

theorem chainWeight_uStar : bb72Complex.chainWeight uStar = 6 := by
  rw [bb72Complex_chainWeight_eq]
  decide

/-! ## The pulled-back gross cycle `τ(u*)` -/

/-- Computable form of the pullback `τ(u*)`. -/
def tauUStarFn : GrossGroup × Fin 2 → ZMod 2 :=
  uStar ∘ Prod.map ⇑coverPi id

lemma coverPull1_uStar_eq : coverPull1 uStar = tauUStarFn := rfl

theorem tauUStar_mem_cycles : coverPull1 uStar ∈ grossComplex.cycles :=
  coverPull1_mem_cycles uStar_mem_cycles

theorem chainWeight_tauUStar : grossComplex.chainWeight (coverPull1 uStar) = 12 := by
  rw [chainWeight_coverPull1, chainWeight_uStar]

/-! ## The dual witness -/

/-- An explicit dual cycle pairing oddly with `τ(u*)`.  Left-block support
`x y⁰ + x y³ + x⁴(1 + y + y² + y³ + y⁴ + y⁵)`, right-block support
`1 + y³ + x + x y³`. -/
def fluxWitness : GrossGroup × Fin 2 → ZMod 2 := fun p =>
  if p.2 = 0 then
    (if p.1 = (1, 0) ∨ p.1 = (1, 3) ∨ p.1 = (4, 0) ∨ p.1 = (4, 1) ∨
        p.1 = (4, 2) ∨ p.1 = (4, 3) ∨ p.1 = (4, 4) ∨ p.1 = (4, 5)
     then 1 else 0)
  else
    (if p.1 = (0, 0) ∨ p.1 = (0, 3) ∨ p.1 = (1, 0) ∨ p.1 = (1, 3)
     then 1 else 0)

/-- Raw (computable) form of `dualBoundary fluxWitness = 0`, via the
transpose formula `bb_dualBoundary_eq`. -/
theorem fluxWitness_dual_raw :
    (fun f => conv (reflect grossA) (leftHalf fluxWitness) f
      + conv (reflect grossB) (rightHalf fluxWitness) f)
      = (0 : GrossGroup → ZMod 2) := by
  decide

theorem fluxWitness_dualBoundary :
    grossComplex.dualBoundary fluxWitness = 0 := by
  change (bbChainComplex grossA grossB).dualBoundary fluxWitness = 0
  rw [bb_dualBoundary_eq]
  exact fluxWitness_dual_raw

theorem fluxWitness_pairing :
    ∑ e : GrossGroup × Fin 2, fluxWitness e * tauUStarFn e = 1 := by
  decide

/-! ## Non-boundaryness and the headline -/

theorem tauUStar_not_mem_boundaries :
    coverPull1 uStar ∉ grossComplex.boundaries := by
  refine HomologicalCode.not_mem_boundaries_of_dual_witness
    fluxWitness_dualBoundary ?_
  change ∑ e : GrossGroup × Fin 2, fluxWitness e * coverPull1 uStar e = 1
  rw [coverPull1_uStar_eq]
  exact fluxWitness_pairing

/-- **The gross code has a weight-12 nontrivial logical chain**: an explicit
1-cycle that is not a boundary and has chain weight exactly 12. -/
theorem gross_exists_weight12_nontrivial_cycle :
    ∃ v ∈ grossComplex.cycles,
      v ∉ grossComplex.boundaries ∧ grossComplex.chainWeight v = 12 :=
  ⟨coverPull1 uStar, tauUStar_mem_cycles,
    tauUStar_not_mem_boundaries, chainWeight_tauUStar⟩

end BB
end Homological
end Stabilizer
end Quantum
