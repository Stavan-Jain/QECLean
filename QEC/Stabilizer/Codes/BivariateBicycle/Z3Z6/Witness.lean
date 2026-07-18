/-
# The weight-8 nontrivial cycle of the [[72,4,8]] cover

Headline (`pair72_exists_weight8_nontrivial_cycle`): the cover complex has
a 1-cycle of weight 8 that is not a boundary — the pullback `τ(u*)` of the
weight-4 base cycle

  `u* = (1 | 0,0)  +  (y + y³ + x² | block 1)`

(left block `{(0,0)}`, right block `{(0,1),(0,3),(2,0)}`; found by SAT and
re-certified here by kernel computation).  Non-boundaryness is certified by
an explicit dual witness `w` (left-block weight 12) with
`dualBoundary w = 0` and `⟨w, τ(u*)⟩ = 1`, fed to
`not_mem_boundaries_of_dual_witness`.  Provenance:
`qec-lab:experiments/bb_lab/scripts/gen_pair72_z6z6_data.py` §4.
-/

import QEC.Stabilizer.Codes.BivariateBicycle.Z3Z6.Defs

namespace Quantum
namespace Stabilizer
namespace Homological
namespace BB
namespace Z3Z6

open scoped BigOperators

/-! ## The base cycle `u*` -/

/-- The weight-4 base 1-chain `u*`: left block `1`, right block
`y + y³ + x²`. -/
def uStar36 : G36 × Fin 2 → ZMod 2 := fun p =>
  if p.2 = 0 then (if p.1 = (0, 0) then 1 else 0)
  else (if p.1 = (0, 1) ∨ p.1 = (0, 3) ∨ p.1 = (2, 0) then 1 else 0)

theorem uStar36_mem_cycles : uStar36 ∈ pair36Complex.cycles := by
  have h : bbBoundary1Fn a36 b36 uStar36 = 0 := by native_decide
  exact h

theorem chainWeight_uStar36 : pair36Complex.chainWeight uStar36 = 4 := by
  rw [show pair36Complex.chainWeight uStar36
      = (Finset.univ.filter fun p : G36 × Fin 2 => uStar36 p ≠ 0).card from rfl]
  native_decide

/-! ## The pulled-back cover cycle `τ(u*)` -/

/-- Computable form of the pullback `τ(u*)`. -/
def tauUStar36Fn : G72 × Fin 2 → ZMod 2 :=
  uStar36 ∘ Prod.map ⇑coverData.proj id

lemma pull1_uStar36_eq : coverData.pull1 uStar36 = tauUStar36Fn := rfl

theorem tauUStar36_mem_cycles :
    coverData.pull1 uStar36 ∈ coverData.coverComplex.cycles :=
  coverData.pull1_mem_cycles uStar36_mem_cycles

theorem chainWeight_tauUStar36 :
    coverData.coverComplex.chainWeight (coverData.pull1 uStar36) = 8 := by
  rw [coverData.chainWeight_pull1]
  have h : coverData.baseComplex.chainWeight uStar36 = 4 := chainWeight_uStar36
  rw [h]

/-! ## The dual witness -/

/-- An explicit dual cycle pairing oddly with `τ(u*)`: left-block support
`(x + x³ + x⁵)(y + y²) ∪ {(1,4),(1,5),(3,0),(3,3),(5,0),(5,3)}`-shaped
weight-12 set, right block empty. -/
def fluxWitness72 : G72 × Fin 2 → ZMod 2 := fun p =>
  if p.2 = 0 then
    (if p.1 = (1, 1) ∨ p.1 = (1, 2) ∨ p.1 = (1, 4) ∨ p.1 = (1, 5) ∨
        p.1 = (3, 0) ∨ p.1 = (3, 2) ∨ p.1 = (3, 3) ∨ p.1 = (3, 5) ∨
        p.1 = (5, 0) ∨ p.1 = (5, 1) ∨ p.1 = (5, 3) ∨ p.1 = (5, 4)
     then 1 else 0)
  else 0

/-- Raw (computable) form of `dualBoundary fluxWitness72 = 0`, via the
transpose formula `bb_dualBoundary_eq`. -/
theorem fluxWitness72_dual_raw :
    (fun f => conv (reflect a72) (leftHalf fluxWitness72) f
      + conv (reflect b72) (rightHalf fluxWitness72) f)
      = (0 : G72 → ZMod 2) := by
  native_decide

theorem fluxWitness72_dualBoundary :
    pair72Complex.dualBoundary fluxWitness72 = 0 := by
  change (bbChainComplex a72 b72).dualBoundary fluxWitness72 = 0
  rw [bb_dualBoundary_eq]
  exact fluxWitness72_dual_raw

theorem fluxWitness72_pairing :
    ∑ e : G72 × Fin 2, fluxWitness72 e * tauUStar36Fn e = 1 := by
  native_decide

/-! ## Non-boundaryness and the headline -/

theorem tauUStar36_not_mem_boundaries :
    coverData.pull1 uStar36 ∉ coverData.coverComplex.boundaries := by
  have h : coverData.pull1 uStar36 ∉ pair72Complex.boundaries := by
    refine HomologicalCode.not_mem_boundaries_of_dual_witness
      fluxWitness72_dualBoundary ?_
    change ∑ e : G72 × Fin 2, fluxWitness72 e * coverData.pull1 uStar36 e = 1
    rw [pull1_uStar36_eq]
    exact fluxWitness72_pairing
  exact h

/-- **The `[[72,4,8]]` cover has a weight-8 nontrivial logical chain.** -/
theorem pair72_exists_weight8_nontrivial_cycle :
    ∃ v ∈ coverData.coverComplex.cycles,
      v ∉ coverData.coverComplex.boundaries ∧
      coverData.coverComplex.chainWeight v = 8 :=
  ⟨coverData.pull1 uStar36, tauUStar36_mem_cycles,
    tauUStar36_not_mem_boundaries, chainWeight_tauUStar36⟩

end Z3Z6
end BB
end Homological
end Stabilizer
end Quantum
