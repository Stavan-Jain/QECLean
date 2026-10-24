import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.Defs
import QEC.Stabilizer.Framework.Homological.Certificate.MaskLinear

noncomputable section

namespace Quantum.Stabilizer.Homological.BB.Bravyi360
open F2Mask HomologicalCode

/-- The first polynomial is the sum of its three point masses. -/
theorem baseA_eq_singles : baseA = Pi.single (9,0) 1 + Pi.single (0,1) 1 + Pi.single (0,2) 1 := by
  decide +kernel

/-- The second polynomial is the sum of its three point masses. -/
theorem baseB_eq_singles : baseB = Pi.single (0,0) 1 + Pi.single (10,0) 1 + Pi.single (11,0) 1 := by
  decide +kernel

/-- Point-mass face boundaries in a sparse coefficient form. -/
noncomputable def baseFaceRow (g : BaseGroup) : BaseGroup × Fin 2 → ZMod 2 :=
  fun q => if q.2 = 0 then baseA (q.1 - g) else baseB (q.1 - g)

/-- Point-mass vertex cuts in a sparse coefficient form. -/
noncomputable def baseVertexRow (g : BaseGroup) : BaseGroup × Fin 2 → ZMod 2 :=
  fun q => if q.2 = 0 then baseB (g - q.1) else baseA (g - q.1)

/-- The sparse face row is the original boundary of a point mass. -/
theorem baseBoundary2_single_eq_faceRow (g : BaseGroup) :
    baseComplex.boundary2 (Pi.single g 1) = baseFaceRow g := by
  ext ⟨h,j⟩
  exact bbBoundary2Fn_single baseA baseB g h j

/-- The sparse vertex row is the original cut of a point mass. -/
theorem baseCutMap_single_eq_vertexRow (g : BaseGroup) :
    baseComplex.cutMap (Pi.single g 1) = baseVertexRow g := by
  change (bbChainComplex baseA baseB).cutMap (Pi.single g 1) = baseVertexRow g
  rw [bb_cutMap_eq]
  ext ⟨h,j⟩
  by_cases hj : j = 0
  · change (if j = 0 then _ else _) = (if j = 0 then _ else _)
    rw [if_pos hj, if_pos hj, conv_comm (reflect baseB)]
    simpa only [reflect_apply, neg_sub] using conv_single_left_apply g (reflect baseB) h
  · change (if j = 0 then _ else _) = (if j = 0 then _ else _)
    rw [if_neg hj, if_neg hj, conv_comm (reflect baseA)]
    simpa only [reflect_apply, neg_sub] using conv_single_left_apply g (reflect baseA) h

/-- The six physical qubits incident on a face check. -/
noncomputable def baseFacePoints (g : BaseGroup) : List (BaseGroup × Fin 2) :=
  [(g+(9,0),0),(g+(0,1),0),(g+(0,2),0),(g+(0,0),1),(g+(10,0),1),(g+(11,0),1)]

/-- The six physical qubits incident on a vertex check. -/
noncomputable def baseVertexPoints (g : BaseGroup) : List (BaseGroup × Fin 2) :=
  [(g-(0,0),0),(g-(10,0),0),(g-(11,0),0),(g-(9,0),1),(g-(0,1),1),(g-(0,2),1)]

/-- baseA face row is the sum of its six incident point masses. -/
theorem baseFaceRow_eq_sum (g : BaseGroup) : baseFaceRow g =
    ((baseFacePoints g).map (fun q => Pi.single q (1 : ZMod 2))).sum := by
  ext ⟨h,j⟩
  fin_cases j <;>
    simp [baseFaceRow, baseFacePoints, baseA_eq_singles, baseB_eq_singles, Pi.single_apply,
      Prod.ext_iff, sub_eq_iff_eq_add, add_comm] <;> abel

/-- baseA vertex row is the sum of its six incident point masses. -/
theorem baseVertexRow_eq_sum (g : BaseGroup) : baseVertexRow g =
    ((baseVertexPoints g).map (fun q => Pi.single q (1 : ZMod 2))).sum := by
  have hs (h a : BaseGroup) : g - h = a ↔ h = g - a := by
    constructor
    · intro he
      rw [← he]
      abel
    · intro he
      rw [he]
      abel
  ext ⟨h,j⟩
  fin_cases j <;>
    simp [baseVertexRow, baseVertexPoints, baseA_eq_singles, baseB_eq_singles, Pi.single_apply,
      Prod.ext_iff, hs] <;> abel

/-- Packed mask of a sparse face check. -/
noncomputable def baseFaceMask (g : BaseGroup) : Nat := xorList ((baseFacePoints g).map (fun q => 2 ^ (baseQubitEnum q).val))

/-- Packed mask of a sparse vertex check. -/
noncomputable def baseVertexMask (g : BaseGroup) : Nat := xorList ((baseVertexPoints g).map (fun q => 2 ^ (baseQubitEnum q).val))

/-- The six-bit face formula is the actual mask of the original face boundary. -/
theorem baseMaskOf_faceRow (g : BaseGroup) : maskOf baseQubitEnum (baseFaceRow g) = baseFaceMask g := by
  rw [baseFaceRow_eq_sum, maskOf_sum, List.map_map]
  congr 1
  apply List.map_congr_left
  intro q hq
  exact maskOf_single baseQubitEnum q

/-- The six-bit vertex formula is the actual mask of the original vertex cut. -/
theorem baseMaskOf_vertexRow (g : BaseGroup) : maskOf baseQubitEnum (baseVertexRow g) = baseVertexMask g := by
  rw [baseVertexRow_eq_sum, maskOf_sum, List.map_map]
  congr 1
  apply List.map_congr_left
  intro q hq
  exact maskOf_single baseQubitEnum q

/-- The three syndrome positions incident on a physical qubit. -/
noncomputable def baseSyndromePoints (q : BaseGroup × Fin 2) : List BaseGroup :=
  if q.2 = 0 then [q.1+(0,0),q.1+(10,0),q.1+(11,0)]
  else [q.1+(9,0),q.1+(0,1),q.1+(0,2)]

/-- baseA point-mass qubit syndrome is the sum of its three incident point masses. -/
theorem base_boundary1_single_eq_sum (q : BaseGroup × Fin 2) :
    baseComplex.boundary1 (Pi.single q 1) =
      ((baseSyndromePoints q).map (fun g => Pi.single g (1 : ZMod 2))).sum := by
  obtain ⟨g,j⟩ := q
  ext h
  fin_cases j
  · change bbBoundary1Fn baseA baseB (Pi.single (g,0) 1) h = _
    rw [bbBoundary1Fn_single_left]
    simp [baseSyndromePoints, baseB_eq_singles, Pi.single_apply, Prod.ext_iff,
      sub_eq_iff_eq_add, add_comm] <;> abel
  · change bbBoundary1Fn baseA baseB (Pi.single (g,1) 1) h = _
    rw [bbBoundary1Fn_single_right]
    simp [baseSyndromePoints, baseA_eq_singles, Pi.single_apply, Prod.ext_iff,
      sub_eq_iff_eq_add, add_comm] <;> abel

/-- Packed mask of the three-check syndrome of a physical qubit. -/
noncomputable def baseSyndromeMask (q : BaseGroup × Fin 2) : Nat :=
  xorList ((baseSyndromePoints q).map (fun g => 2 ^ (baseFaceEnum g).val))

/-- The three-bit formula is the actual packed point-mass syndrome. -/
theorem maskOf_base_boundary1_single (q : BaseGroup × Fin 2) :
    maskOf baseFaceEnum (baseComplex.boundary1 (Pi.single q 1)) = baseSyndromeMask q := by
  rw [base_boundary1_single_eq_sum, maskOf_sum, List.map_map]
  congr 1
  apply List.map_congr_left
  intro g hg
  exact maskOf_single baseFaceEnum g

end Quantum.Stabilizer.Homological.BB.Bravyi360
