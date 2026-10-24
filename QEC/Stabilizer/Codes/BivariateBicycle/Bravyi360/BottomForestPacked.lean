import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.BottomForestCheck

noncomputable section
namespace Quantum.Stabilizer.Homological.BB.Bravyi360.BottomForest
open F2Mask FiberData PackedDigits

/-- Literal packed tables cache the intermediate list packings of one forest chunk. -/
structure PackedGroup where
  eRep : Nat
  eInput : Nat
  eOutput : Nat
  rRep : Nat
  rInput : Nat
  rOutput : Nat
  jRep : Nat
  jFirst : Nat
  jSecond : Nat
  jOutput : Nat

/-- Check each literal packing once before checking its parallel full-matrix equation. -/
noncomputable def packedGroupCheck (rs : List Fiber) (p : PackedGroup) : Bool :=
  rs.all fiberCheck &&
  Nat.beq (packList 256 ((ePairs rs).map fun _ => 1)) p.eRep &&
  Nat.beq (packList 256 ((ePairs rs).map Prod.fst)) p.eInput &&
  Nat.beq (packList 256 ((ePairs rs).map Prod.snd)) p.eOutput &&
  Nat.beq (batchRecon p.eRep p.eInput bottomEColumns) p.eOutput &&
  Nat.beq (packList 256 ((rPairs rs).map fun _ => 1)) p.rRep &&
  Nat.beq (packList 256 ((rPairs rs).map Prod.fst)) p.rInput &&
  Nat.beq (packList 256 ((rPairs rs).map Prod.snd)) p.rOutput &&
  Nat.beq (batchRecon p.rRep p.rInput bottomRColumns) p.rOutput &&
  Nat.beq (packList 256 ((joinTriples rs).map fun _ => 1)) p.jRep &&
  Nat.beq (packList 256 ((joinTriples rs).map Prod.fst)) p.jFirst &&
  Nat.beq (packList 256 ((joinTriples rs).map fun t => Nat.xor t.1 t.2.1)) p.jSecond &&
  Nat.beq (packList 256 ((joinTriples rs).map fun t => t.2.2)) p.jOutput &&
  Nat.beq (Nat.xor (batchRecon p.jRep p.jFirst bottomLeft)
    (batchRecon p.jRep p.jSecond bottomRight)) p.jOutput

/-- Cached literal packings preserve the original forest checker's exact meaning. -/
theorem packedGroupCheck_sound (rs : List Fiber) (p : PackedGroup)
    (h : packedGroupCheck rs p = true) : groupCheck rs = true := by
  simp only [packedGroupCheck,Bool.and_eq_true,Nat.beq_eq,and_assoc] at h
  rcases h with ⟨hs,heR,heI,heO,he,hrR,hrI,hrO,hr,hjR,hjF,hjS,hjO,hj⟩
  simp only [groupCheck,Bool.and_eq_true,and_assoc]
  refine ⟨hs,?_,?_,?_⟩
  · unfold mapCheck
    rw [heR,heI,heO]
    exact Nat.beq_eq.mpr he
  · unfold mapCheck
    rw [hrR,hrI,hrO]
    exact Nat.beq_eq.mpr hr
  · unfold joinsCheck
    rw [hjR,hjF,hjS,hjO]
    exact Nat.beq_eq.mpr hj

#print axioms packedGroupCheck_sound
end Quantum.Stabilizer.Homological.BB.Bravyi360.BottomForest
