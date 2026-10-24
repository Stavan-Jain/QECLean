import QEC.Stabilizer.Framework.Homological.Certificate.MaskLinear
import QEC.Stabilizer.Framework.Homological.Certificate.ParityFold
import Mathlib.LinearAlgebra.Matrix.ToLin

open scoped BigOperators
namespace Quantum.Stabilizer.Homological.F2Mask

/-- A finite binary linear map is the sum of its point-mass columns. -/
theorem linear_eq_sum_columns {n m : Nat}
    (E : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin m → ZMod 2)) (v : Fin n → ZMod 2) :
    E v = ∑ i, v i • E (Pi.single i 1) := by
  have h := congrArg E (pi_eq_sum_univ' v)
  simpa only [map_sum, map_smul] using h

/-- Checking transposition on point-mass entries proves the full adjoint identity. -/
theorem adjoint_of_single {n m : Nat}
    (E : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin m → ZMod 2))
    (T : (Fin m → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2))
    (h : ∀ i j, T (Pi.single j 1) i = E (Pi.single i 1) j)
    (lam : Fin m → ZMod 2) (v : Fin n → ZMod 2) :
    dotProduct (T lam) v = dotProduct lam (E v) := by
  rw [linear_eq_sum_columns T lam, linear_eq_sum_columns E v]
  simp only [dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro i hi
  rw [h]
  ring

/-- The existing packed dual is the usual finite binary dot product. -/
theorem dualOfMask_eq_dot (n lam : Nat) (v : Fin n → ZMod 2) :
    dualOfMask n lam v = dotProduct (chainOfMask (Equiv.refl (Fin n)) lam) v := rfl

/-- An adjoint certificate turns a packed matrix evaluation into an intersection parity. -/
theorem dualOfMask_apply_of_adjoint {n m : Nat}
    (E : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin m → ZMod 2))
    (T : (Fin m → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2))
    (h : ∀ i j, T (Pi.single j 1) i = E (Pi.single i 1) j)
    (lam v out : Nat)
    (hout : T (chainOfMask (Equiv.refl (Fin m)) lam) = chainOfMask (Equiv.refl (Fin n)) out) :
    dualOfMask m lam (E (chainOfMask (Equiv.refl (Fin n)) v)) =
      (bitCount n (out &&& v) : ZMod 2) := by
  rw [dualOfMask_eq_dot, ← adjoint_of_single E T h, hout]
  exact (dualOfMask_chainOfMask n out v)

#print axioms dualOfMask_apply_of_adjoint
end Quantum.Stabilizer.Homological.F2Mask

namespace Quantum.Stabilizer.Homological.F2Mask

/-- One pair of certified adjoint evaluations excludes every solution supported on a shadow. -/
theorem no_flat_solution_of_adjoints {n m : Nat}
    (E R : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin m → ZMod 2))
    (TE TR : (Fin m → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2))
    (hE : ∀ i j, TE (Pi.single j 1) i = E (Pi.single i 1) j)
    (hR : ∀ i j, TR (Pi.single j 1) i = R (Pi.single i 1) j)
    (lam beta zE zR : Nat)
    (heval : TE (chainOfMask (Equiv.refl (Fin m)) lam) =
      chainOfMask (Equiv.refl (Fin n)) zE)
    (hreval : TR (chainOfMask (Equiv.refl (Fin m)) lam) =
      chainOfMask (Equiv.refl (Fin n)) zR)
    (hon : zE &&& beta = 0)
    (hodd : bitCount n (zR &&& beta) % 2 = 1)
    (s : Nat) (hs : s &&& beta = s) :
    E (chainOfMask (Equiv.refl (Fin n)) s) ≠
      R (chainOfMask (Equiv.refl (Fin n)) beta) := by
  intro heq
  have hzero : zE &&& s = 0 := by
    calc zE &&& s = zE &&& (s &&& beta) := by rw [hs]
         _ = (zE &&& beta) &&& s := by ac_rfl
         _ = 0 := by rw [hon, Nat.zero_and]
  have hx := dualOfMask_apply_of_adjoint E TE hE lam s zE heval
  have hy := dualOfMask_apply_of_adjoint R TR hR lam beta zR hreval
  have ho : (bitCount n (zR &&& beta) : ZMod 2) = 1 := by
    rw [← ZMod.natCast_mod, hodd]
    rfl
  rw [heq, hy, ho, hzero] at hx
  simpa [bitCount_eq_card] using hx

#print axioms no_flat_solution_of_adjoints
end Quantum.Stabilizer.Homological.F2Mask
