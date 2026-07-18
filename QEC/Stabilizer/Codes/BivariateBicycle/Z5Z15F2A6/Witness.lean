/-
# The weight-16 nontrivial cycle of the [[300,8,16]] cover

Headline (`cover300_exists_weight16_nontrivial_cycle`): the cover complex
has a 1-cycle of weight 16 that is not a boundary — the pullback `τ(u*)`
of the weight-8 base cycle

  `u* = (x²y + x²y⁵ + x²y⁹ + x³y⁷ | block 0) + (x³y⁴ + x³y⁵ + x³y⁶ + x⁴y⁴ | block 1)`.

`u*` is the descent of the A17 cover ladder's weight-16 SAT witness
(`data/a17/cover_witness.jsonl`, re-verified deck-invariant, translated
to repo convention by the global reflection) and is re-certified here by
kernel computation.  Non-boundaryness is certified by an explicit dual
witness `w` (weight 18) with `dualBoundary w = 0` and `⟨w, τ(u*)⟩ = 1`,
fed to `not_mem_boundaries_of_dual_witness`.  As a corollary `u*` itself
is a nontrivial base logical, so the SAT-side base facts split as:
`d(base) ≤ 8` kernel-checked here, `d(base) ≥ 8` certificate-checked
(CaDiCaL `UNSAT@7`, corpus `d_exact`).  Provenance:
`qec-lab:experiments/bb_lab/scripts/gen_f2a6_z5z30_data.py` §§3–4.
-/

import QEC.Stabilizer.Codes.BivariateBicycle.Z5Z15F2A6.Defs

namespace Quantum
namespace Stabilizer
namespace Homological
namespace BB
namespace Z5Z15F2A6

open scoped BigOperators

/-! ## The base cycle `u*` -/

/-- The weight-8 base 1-chain `u*`: left block `x²y + x²y⁵ + x²y⁹ + x³y⁷`,
right block `x³y⁴ + x³y⁵ + x³y⁶ + x⁴y⁴`. -/
def uStar150 : G150 × Fin 2 → ZMod 2 := fun p =>
  if p.2 = 0 then
    (if p.1 = (2, 1) ∨ p.1 = (2, 5) ∨ p.1 = (2, 9) ∨ p.1 = (3, 7)
     then 1 else 0)
  else
    (if p.1 = (3, 4) ∨ p.1 = (3, 5) ∨ p.1 = (3, 6) ∨ p.1 = (4, 4)
     then 1 else 0)

theorem uStar150_mem_cycles : uStar150 ∈ base150Complex.cycles := by
  have h : bbBoundary1Fn a150 b150 uStar150 = 0 := by native_decide
  exact h

theorem chainWeight_uStar150 : base150Complex.chainWeight uStar150 = 8 := by
  rw [show base150Complex.chainWeight uStar150
      = (Finset.univ.filter fun p : G150 × Fin 2 => uStar150 p ≠ 0).card
      from rfl]
  native_decide

/-! ## The pulled-back cover cycle `τ(u*)` -/

/-- Computable form of the pullback `τ(u*)`. -/
def tauUStar150Fn : G300 × Fin 2 → ZMod 2 :=
  uStar150 ∘ Prod.map ⇑coverData.proj id

lemma pull1_uStar150_eq : coverData.pull1 uStar150 = tauUStar150Fn := rfl

theorem tauUStar150_mem_cycles :
    coverData.pull1 uStar150 ∈ coverData.coverComplex.cycles :=
  coverData.pull1_mem_cycles uStar150_mem_cycles

theorem chainWeight_tauUStar150 :
    coverData.coverComplex.chainWeight (coverData.pull1 uStar150) = 16 := by
  rw [coverData.chainWeight_pull1]
  have h : coverData.baseComplex.chainWeight uStar150 = 8 :=
    chainWeight_uStar150
  rw [h]

/-! ## The dual witness -/

/-- An explicit dual cycle pairing oddly with `τ(u*)`: left block 16 cells,
right block `1 + x` (weight 18 total). -/
def fluxWitness300 : G300 × Fin 2 → ZMod 2 := fun p =>
  if p.2 = 0 then
    (if p.1 = (0, 21) ∨ p.1 = (1, 21) ∨ p.1 = (1, 24) ∨ p.1 = (2, 20) ∨
        p.1 = (2, 21) ∨ p.1 = (2, 23) ∨ p.1 = (2, 24) ∨ p.1 = (3, 19) ∨
        p.1 = (3, 21) ∨ p.1 = (3, 22) ∨ p.1 = (3, 24) ∨ p.1 = (4, 19) ∨
        p.1 = (4, 20) ∨ p.1 = (4, 22) ∨ p.1 = (4, 23) ∨ p.1 = (4, 24)
     then 1 else 0)
  else (if p.1 = (0, 0) ∨ p.1 = (1, 0) then 1 else 0)

/-- Raw (computable) form of `dualBoundary fluxWitness300 = 0`, via the
transpose formula `bb_dualBoundary_eq`. -/
theorem fluxWitness300_dual_raw :
    (fun f => conv (reflect a300) (leftHalf fluxWitness300) f
      + conv (reflect b300) (rightHalf fluxWitness300) f)
      = (0 : G300 → ZMod 2) := by
  native_decide

theorem fluxWitness300_dualBoundary :
    cover300Complex.dualBoundary fluxWitness300 = 0 := by
  change (bbChainComplex a300 b300).dualBoundary fluxWitness300 = 0
  rw [bb_dualBoundary_eq]
  exact fluxWitness300_dual_raw

theorem fluxWitness300_pairing :
    ∑ e : G300 × Fin 2, fluxWitness300 e * tauUStar150Fn e = 1 := by
  native_decide

/-! ## Non-boundaryness and the headlines -/

theorem tauUStar150_not_mem_boundaries :
    coverData.pull1 uStar150 ∉ coverData.coverComplex.boundaries := by
  have h : coverData.pull1 uStar150 ∉ cover300Complex.boundaries := by
    refine HomologicalCode.not_mem_boundaries_of_dual_witness
      fluxWitness300_dualBoundary ?_
    change ∑ e : G300 × Fin 2,
      fluxWitness300 e * coverData.pull1 uStar150 e = 1
    rw [pull1_uStar150_eq]
    exact fluxWitness300_pairing
  exact h

/-- `u*` is itself nontrivial in the base (pullbacks of boundaries are
boundaries). -/
theorem uStar150_not_mem_boundaries :
    uStar150 ∉ coverData.baseComplex.boundaries := fun h =>
  tauUStar150_not_mem_boundaries (coverData.pull1_mem_boundaries h)

/-- **The `[[300,8,16]]` cover has a weight-16 nontrivial logical chain**
(the kernel-checked half of `d(cover) = 16`). -/
theorem cover300_exists_weight16_nontrivial_cycle :
    ∃ v ∈ coverData.coverComplex.cycles,
      v ∉ coverData.coverComplex.boundaries ∧
      coverData.coverComplex.chainWeight v = 16 :=
  ⟨coverData.pull1 uStar150, tauUStar150_mem_cycles,
    tauUStar150_not_mem_boundaries, chainWeight_tauUStar150⟩

/-- **The `[[150,8,8]]` base has a weight-8 nontrivial logical chain**
(the kernel-checked half of `d(base) = 8`). -/
theorem base150_exists_weight8_nontrivial_cycle :
    ∃ u ∈ coverData.baseComplex.cycles,
      u ∉ coverData.baseComplex.boundaries ∧
      coverData.baseComplex.chainWeight u = 8 :=
  ⟨uStar150, uStar150_mem_cycles, uStar150_not_mem_boundaries,
    chainWeight_uStar150⟩

end Z5Z15F2A6
end BB
end Homological
end Stabilizer
end Quantum
