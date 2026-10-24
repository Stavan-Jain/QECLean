import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.DualData
import QEC.Stabilizer.Framework.Homological.Certificate.SearchInitial

noncomputable section

namespace Quantum.Stabilizer.Homological.F2Mask

/-- A compressed matrix dual yields an equation on the outside-support mask. -/
theorem compressed_dual_constraint (bits k : Nat)
    (E R TE TR C L : List (Nat × Nat))
    (hE : ∀ l v, parityFold k (reconX TE l &&& v) = parityFold k (l &&& reconX E v))
    (hR : ∀ l v, parityFold k (reconX TR l &&& v) = parityFold k (l &&& reconX R v))
    (hCE : ∀ c, reconX TE (reconX L c) = reconX C c &&& (2^bits-1))
    (hCR : ∀ c, reconX TR (reconX L c) = reconX C c >>> bits)
    (coeff beta word : Nat) (hw : word < 2^bits)
    (hann : reconX C coeff &&& beta = 0)
    (he : reconX E word = reconX R beta) :
    parityFold k (reconX C coeff &&& outsideMask word beta) =
      parityFold k ((reconX C coeff >>> bits) &&& beta) := by
  rw [and_outsideMask_eq hann]
  have hlow : reconX C coeff &&& word = reconX TE (reconX L coeff) &&& word := by
    rw [hCE]
    conv_rhs => rw [Nat.and_assoc,Nat.and_comm (2^bits-1) word,Nat.and_two_pow_sub_one_of_lt_two_pow hw]
  rw [hlow,hE,he,← hR,hCR]

end Quantum.Stabilizer.Homological.F2Mask

namespace Quantum.Stabilizer.Homological.BB.Bravyi360
open F2Mask FiberData

/-- Every compressed bottom dual constrains the actual outside support. -/
theorem bottomDual_constraint (coeff beta word : Nat) (hw : word < 2^90)
    (hann : reconX bottomDualColumns coeff &&& beta = 0)
    (he : reconX bottomEColumns word = reconX bottomRColumns beta) :
    parityFold 7 (reconX bottomDualColumns coeff &&& outsideMask word beta) =
      parityFold 7 ((reconX bottomDualColumns coeff >>> 90) &&& beta) :=
  compressed_dual_constraint 90 7 _ _ _ _ _ _ bottomETranspose_parityFold7
    bottomRTranspose_parityFold7 bottomDual_E bottomDual_R coeff beta word hw hann he

/-- Every compressed top dual constrains the actual outside support. -/
theorem topDual_constraint (coeff beta word : Nat) (hw : word < 2^180)
    (hann : reconX topDualColumns coeff &&& beta = 0)
    (he : reconX topEColumns word = reconX topRColumns beta) :
    parityFold 8 (reconX topDualColumns coeff &&& outsideMask word beta) =
      parityFold 8 ((reconX topDualColumns coeff >>> 180) &&& beta) :=
  compressed_dual_constraint 180 8 _ _ _ _ _ _ topETranspose_parityFold
    topRTranspose_parityFold topDual_E topDual_R coeff beta word hw hann he

#print axioms bottomDual_constraint
#print axioms topDual_constraint
end Quantum.Stabilizer.Homological.BB.Bravyi360
