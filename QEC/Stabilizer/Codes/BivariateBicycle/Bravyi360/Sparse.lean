import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.Defs
import QEC.Stabilizer.Framework.Homological.Certificate.MaskLinear

noncomputable section

namespace Quantum.Stabilizer.Homological.BB.Bravyi360
open F2Mask HomologicalCode

/-- The first polynomial is the sum of its three point masses. -/
theorem A_eq_singles : A = Pi.single (9,0) 1 + Pi.single (0,1) 1 + Pi.single (0,2) 1 := by
  decide +kernel

/-- The second polynomial is the sum of its three point masses. -/
theorem B_eq_singles : B = Pi.single (0,3) 1 + Pi.single (25,0) 1 + Pi.single (26,0) 1 := by
  decide +kernel

/-- Point-mass face boundaries in a sparse coefficient form. -/
noncomputable def faceRow (g : Group) : Group × Fin 2 → ZMod 2 :=
  fun q => if q.2 = 0 then A (q.1 - g) else B (q.1 - g)

/-- Point-mass vertex cuts in a sparse coefficient form. -/
noncomputable def vertexRow (g : Group) : Group × Fin 2 → ZMod 2 :=
  fun q => if q.2 = 0 then B (g - q.1) else A (g - q.1)

/-- The sparse face row is the original boundary of a point mass. -/
theorem boundary2_single_eq_faceRow (g : Group) :
    complex.boundary2 (Pi.single g 1) = faceRow g := by
  ext ⟨h,j⟩
  exact bbBoundary2Fn_single A B g h j

/-- The sparse vertex row is the original cut of a point mass. -/
theorem cutMap_single_eq_vertexRow (g : Group) :
    complex.cutMap (Pi.single g 1) = vertexRow g := by
  change (bbChainComplex A B).cutMap (Pi.single g 1) = vertexRow g
  rw [bb_cutMap_eq]
  ext ⟨h,j⟩
  by_cases hj : j = 0
  · change (if j = 0 then _ else _) = (if j = 0 then _ else _)
    rw [if_pos hj, if_pos hj, conv_comm (reflect B)]
    simpa only [reflect_apply, neg_sub] using conv_single_left_apply g (reflect B) h
  · change (if j = 0 then _ else _) = (if j = 0 then _ else _)
    rw [if_neg hj, if_neg hj, conv_comm (reflect A)]
    simpa only [reflect_apply, neg_sub] using conv_single_left_apply g (reflect A) h

/-- The six physical qubits incident on a face check. -/
noncomputable def facePoints (g : Group) : List (Group × Fin 2) :=
  [(g+(9,0),0),(g+(0,1),0),(g+(0,2),0),(g+(0,3),1),(g+(25,0),1),(g+(26,0),1)]

/-- The six physical qubits incident on a vertex check. -/
noncomputable def vertexPoints (g : Group) : List (Group × Fin 2) :=
  [(g-(0,3),0),(g-(25,0),0),(g-(26,0),0),(g-(9,0),1),(g-(0,1),1),(g-(0,2),1)]

/-- A face row is the sum of its six incident point masses. -/
theorem faceRow_eq_sum (g : Group) : faceRow g =
    ((facePoints g).map (fun q => Pi.single q (1 : ZMod 2))).sum := by
  ext ⟨h,j⟩
  fin_cases j <;>
    simp [faceRow, facePoints, A_eq_singles, B_eq_singles, Pi.single_apply,
      Prod.ext_iff, sub_eq_iff_eq_add, add_comm] <;> abel

/-- A vertex row is the sum of its six incident point masses. -/
theorem vertexRow_eq_sum (g : Group) : vertexRow g =
    ((vertexPoints g).map (fun q => Pi.single q (1 : ZMod 2))).sum := by
  have hs (h a : Group) : g - h = a ↔ h = g - a := by
    constructor
    · intro he
      rw [← he]
      abel
    · intro he
      rw [he]
      abel
  ext ⟨h,j⟩
  fin_cases j <;>
    simp [vertexRow, vertexPoints, A_eq_singles, B_eq_singles, Pi.single_apply,
      Prod.ext_iff, hs] <;> abel

/-- Packed mask of a sparse face check. -/
noncomputable def faceMask (g : Group) : Nat := xorList ((facePoints g).map (fun q => 2 ^ (qubitEnum q).val))

/-- Packed mask of a sparse vertex check. -/
noncomputable def vertexMask (g : Group) : Nat := xorList ((vertexPoints g).map (fun q => 2 ^ (qubitEnum q).val))

/-- The six-bit face formula is the actual mask of the original face boundary. -/
theorem maskOf_faceRow (g : Group) : maskOf qubitEnum (faceRow g) = faceMask g := by
  rw [faceRow_eq_sum, maskOf_sum, List.map_map]
  congr 1
  apply List.map_congr_left
  intro q hq
  exact maskOf_single qubitEnum q

/-- The six-bit vertex formula is the actual mask of the original vertex cut. -/
theorem maskOf_vertexRow (g : Group) : maskOf qubitEnum (vertexRow g) = vertexMask g := by
  rw [vertexRow_eq_sum, maskOf_sum, List.map_map]
  congr 1
  apply List.map_congr_left
  intro q hq
  exact maskOf_single qubitEnum q

/-- The three syndrome positions incident on a physical qubit. -/
noncomputable def syndromePoints (q : Group × Fin 2) : List Group :=
  if q.2 = 0 then [q.1+(0,3),q.1+(25,0),q.1+(26,0)]
  else [q.1+(9,0),q.1+(0,1),q.1+(0,2)]

/-- A point-mass qubit syndrome is the sum of its three incident point masses. -/
theorem boundary1_single_eq_sum (q : Group × Fin 2) :
    complex.boundary1 (Pi.single q 1) =
      ((syndromePoints q).map (fun g => Pi.single g (1 : ZMod 2))).sum := by
  obtain ⟨g,j⟩ := q
  ext h
  fin_cases j
  · change bbBoundary1Fn A B (Pi.single (g,0) 1) h = _
    rw [bbBoundary1Fn_single_left]
    simp [syndromePoints, B_eq_singles, Pi.single_apply, Prod.ext_iff,
      sub_eq_iff_eq_add, add_comm] <;> abel
  · change bbBoundary1Fn A B (Pi.single (g,1) 1) h = _
    rw [bbBoundary1Fn_single_right]
    simp [syndromePoints, A_eq_singles, Pi.single_apply, Prod.ext_iff,
      sub_eq_iff_eq_add, add_comm] <;> abel

/-- Packed mask of the three-check syndrome of a physical qubit. -/
noncomputable def syndromeMask (q : Group × Fin 2) : Nat :=
  xorList ((syndromePoints q).map (fun g => 2 ^ (faceEnum g).val))

/-- The three-bit formula is the actual packed point-mass syndrome. -/
theorem maskOf_boundary1_single (q : Group × Fin 2) :
    maskOf faceEnum (complex.boundary1 (Pi.single q 1)) = syndromeMask q := by
  rw [boundary1_single_eq_sum, maskOf_sum, List.map_map]
  congr 1
  apply List.map_congr_left
  intro g hg
  exact maskOf_single faceEnum g

end Quantum.Stabilizer.Homological.BB.Bravyi360
