import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.Defs
import QEC.Stabilizer.Framework.Homological.Certificate.MaskLinear

noncomputable section

namespace Quantum.Stabilizer.Homological.BB.Bravyi360
open F2Mask HomologicalCode

/-- The first polynomial is the sum of its three point masses. -/
theorem middleA_eq_singles : middleA = Pi.single (9,0) 1 + Pi.single (0,1) 1 + Pi.single (0,2) 1 := by
  decide +kernel

/-- The second polynomial is the sum of its three point masses. -/
theorem middleB_eq_singles : middleB = Pi.single (0,0) 1 + Pi.single (25,0) 1 + Pi.single (26,0) 1 := by
  decide +kernel

/-- Point-mass face boundaries in a sparse coefficient form. -/
noncomputable def middleFaceRow (g : MiddleGroup) : MiddleGroup × Fin 2 → ZMod 2 :=
  fun q => if q.2 = 0 then middleA (q.1 - g) else middleB (q.1 - g)

/-- Point-mass vertex cuts in a sparse coefficient form. -/
noncomputable def middleVertexRow (g : MiddleGroup) : MiddleGroup × Fin 2 → ZMod 2 :=
  fun q => if q.2 = 0 then middleB (g - q.1) else middleA (g - q.1)

/-- The sparse face row is the original boundary of a point mass. -/
theorem middleBoundary2_single_eq_faceRow (g : MiddleGroup) :
    middleComplex.boundary2 (Pi.single g 1) = middleFaceRow g := by
  ext ⟨h,j⟩
  exact bbBoundary2Fn_single middleA middleB g h j

/-- The sparse vertex row is the original cut of a point mass. -/
theorem middleCutMap_single_eq_vertexRow (g : MiddleGroup) :
    middleComplex.cutMap (Pi.single g 1) = middleVertexRow g := by
  change (bbChainComplex middleA middleB).cutMap (Pi.single g 1) = middleVertexRow g
  rw [bb_cutMap_eq]
  ext ⟨h,j⟩
  by_cases hj : j = 0
  · change (if j = 0 then _ else _) = (if j = 0 then _ else _)
    rw [if_pos hj, if_pos hj, conv_comm (reflect middleB)]
    simpa only [reflect_apply, neg_sub] using conv_single_left_apply g (reflect middleB) h
  · change (if j = 0 then _ else _) = (if j = 0 then _ else _)
    rw [if_neg hj, if_neg hj, conv_comm (reflect middleA)]
    simpa only [reflect_apply, neg_sub] using conv_single_left_apply g (reflect middleA) h

/-- The six physical qubits incident on a face check. -/
noncomputable def middleFacePoints (g : MiddleGroup) : List (MiddleGroup × Fin 2) :=
  [(g+(9,0),0),(g+(0,1),0),(g+(0,2),0),(g+(0,0),1),(g+(25,0),1),(g+(26,0),1)]

/-- The six physical qubits incident on a vertex check. -/
noncomputable def middleVertexPoints (g : MiddleGroup) : List (MiddleGroup × Fin 2) :=
  [(g-(0,0),0),(g-(25,0),0),(g-(26,0),0),(g-(9,0),1),(g-(0,1),1),(g-(0,2),1)]

/-- middleA face row is the sum of its six incident point masses. -/
theorem middleFaceRow_eq_sum (g : MiddleGroup) : middleFaceRow g =
    ((middleFacePoints g).map (fun q => Pi.single q (1 : ZMod 2))).sum := by
  ext ⟨h,j⟩
  fin_cases j <;>
    simp [middleFaceRow, middleFacePoints, middleA_eq_singles, middleB_eq_singles, Pi.single_apply,
      Prod.ext_iff, sub_eq_iff_eq_add, add_comm] <;> abel

/-- middleA vertex row is the sum of its six incident point masses. -/
theorem middleVertexRow_eq_sum (g : MiddleGroup) : middleVertexRow g =
    ((middleVertexPoints g).map (fun q => Pi.single q (1 : ZMod 2))).sum := by
  have hs (h a : MiddleGroup) : g - h = a ↔ h = g - a := by
    constructor
    · intro he
      rw [← he]
      abel
    · intro he
      rw [he]
      abel
  ext ⟨h,j⟩
  fin_cases j <;>
    simp [middleVertexRow, middleVertexPoints, middleA_eq_singles, middleB_eq_singles, Pi.single_apply,
      Prod.ext_iff, hs] <;> abel

/-- Packed mask of a sparse face check. -/
noncomputable def middleFaceMask (g : MiddleGroup) : Nat := xorList ((middleFacePoints g).map (fun q => 2 ^ (middleQubitEnum q).val))

/-- Packed mask of a sparse vertex check. -/
noncomputable def middleVertexMask (g : MiddleGroup) : Nat := xorList ((middleVertexPoints g).map (fun q => 2 ^ (middleQubitEnum q).val))

/-- The six-bit face formula is the actual mask of the original face boundary. -/
theorem middleMaskOf_faceRow (g : MiddleGroup) : maskOf middleQubitEnum (middleFaceRow g) = middleFaceMask g := by
  rw [middleFaceRow_eq_sum, maskOf_sum, List.map_map]
  congr 1
  apply List.map_congr_left
  intro q hq
  exact maskOf_single middleQubitEnum q

/-- The six-bit vertex formula is the actual mask of the original vertex cut. -/
theorem middleMaskOf_vertexRow (g : MiddleGroup) : maskOf middleQubitEnum (middleVertexRow g) = middleVertexMask g := by
  rw [middleVertexRow_eq_sum, maskOf_sum, List.map_map]
  congr 1
  apply List.map_congr_left
  intro q hq
  exact maskOf_single middleQubitEnum q

/-- The three syndrome positions incident on a physical qubit. -/
noncomputable def middleSyndromePoints (q : MiddleGroup × Fin 2) : List MiddleGroup :=
  if q.2 = 0 then [q.1+(0,0),q.1+(25,0),q.1+(26,0)]
  else [q.1+(9,0),q.1+(0,1),q.1+(0,2)]

/-- middleA point-mass qubit syndrome is the sum of its three incident point masses. -/
theorem middle_boundary1_single_eq_sum (q : MiddleGroup × Fin 2) :
    middleComplex.boundary1 (Pi.single q 1) =
      ((middleSyndromePoints q).map (fun g => Pi.single g (1 : ZMod 2))).sum := by
  obtain ⟨g,j⟩ := q
  ext h
  fin_cases j
  · change bbBoundary1Fn middleA middleB (Pi.single (g,0) 1) h = _
    rw [bbBoundary1Fn_single_left]
    simp [middleSyndromePoints, middleB_eq_singles, Pi.single_apply, Prod.ext_iff,
      sub_eq_iff_eq_add, add_comm] <;> abel
  · change bbBoundary1Fn middleA middleB (Pi.single (g,1) 1) h = _
    rw [bbBoundary1Fn_single_right]
    simp [middleSyndromePoints, middleA_eq_singles, Pi.single_apply, Prod.ext_iff,
      sub_eq_iff_eq_add, add_comm] <;> abel

/-- Packed mask of the three-check syndrome of a physical qubit. -/
noncomputable def middleSyndromeMask (q : MiddleGroup × Fin 2) : Nat :=
  xorList ((middleSyndromePoints q).map (fun g => 2 ^ (middleFaceEnum g).val))

/-- The three-bit formula is the actual packed point-mass syndrome. -/
theorem maskOf_middle_boundary1_single (q : MiddleGroup × Fin 2) :
    maskOf middleFaceEnum (middleComplex.boundary1 (Pi.single q 1)) = middleSyndromeMask q := by
  rw [middle_boundary1_single_eq_sum, maskOf_sum, List.map_map]
  congr 1
  apply List.map_congr_left
  intro g hg
  exact maskOf_single middleFaceEnum g

end Quantum.Stabilizer.Homological.BB.Bravyi360
