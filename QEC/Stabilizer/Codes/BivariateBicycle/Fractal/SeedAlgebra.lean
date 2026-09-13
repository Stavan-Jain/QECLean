import QEC.Stabilizer.Codes.BivariateBicycle.Fractal.Polynomial
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Algebra.CharP.Algebra

/-!
# The finite recurrence algebra

The quotient by `1+X+X^(2^s)` has a power basis of size `2^s`.
Its coordinate root satisfies the cyclic period relation. This algebra is
allowed to have zero divisors; no irreducibility assumption is made.
-/

namespace Quantum.Stabilizer.Homological.BB.Fractal

open Polynomial

/-- The low terms have degree below the leading recurrence term. -/
private lemma lowTerms_natDegree_lt {s : ℕ} (hs : 0 < s) :
    (1 + (X : (ZMod 2)[X])).natDegree < width s := by
  have h := two_le_width hs
  calc
    (1 + (X : (ZMod 2)[X])).natDegree ≤
        max (1 : (ZMod 2)[X]).natDegree (X : (ZMod 2)[X]).natDegree := natDegree_add_le _ _
    _ < width s := by simpa using h

/-- The trinomial is monic at every positive index. -/
theorem checkPolynomial_monic {s : ℕ} (hs : 0 < s) : (checkPolynomial s).Monic := by
  have h : (1 + (X : (ZMod 2)[X])).natDegree <
      ((X : (ZMod 2)[X]) ^ width s).natDegree := by
    simpa only [natDegree_X_pow] using lowTerms_natDegree_lt hs
  simpa only [checkPolynomial, add_comm] using
    (monic_X_pow (width s)).add_of_left (degree_lt_degree h)

/-- The degree is exactly the recurrence length. -/
theorem checkPolynomial_natDegree {s : ℕ} (hs : 0 < s) :
    (checkPolynomial s).natDegree = width s := by
  unfold checkPolynomial
  rw [natDegree_add_eq_right_of_natDegree_lt, natDegree_X_pow]
  simpa only [natDegree_X_pow] using lowTerms_natDegree_lt hs

/-- The seed recurrence algebra, indexed from zero as in the BB family. -/
abbrev SeedAlgebra (s : ℕ) := AdjoinRoot (checkPolynomial (s + 1))

/-- The cyclic coordinate in the recurrence algebra. -/
noncomputable def seedRoot (s : ℕ) : SeedAlgebra s :=
  AdjoinRoot.root (checkPolynomial (s + 1))

/-- A power basis of the seed algebra with the explicit recurrence-length index. -/
noncomputable def seedBasis (s : ℕ) :
    Module.Basis (Fin (width (s + 1))) (ZMod 2) (SeedAlgebra s) :=
  (AdjoinRoot.powerBasis' (checkPolynomial_monic (Nat.succ_pos s))).basis.reindex
    (finCongr (checkPolynomial_natDegree (Nat.succ_pos s)))

/-- The finite seed algebra has exactly the expected dimension. -/
theorem finrank_seedAlgebra (s : ℕ) :
    Module.finrank (ZMod 2) (SeedAlgebra s) = width (s + 1) := by
  simpa only [Fintype.card_fin] using Module.finrank_eq_card_basis (seedBasis s)

/-- The seed algebra is nontrivial, since its power basis is nonempty. -/
instance seedAlgebraNontrivial (s : ℕ) : Nontrivial (SeedAlgebra s) := by
  have h := finrank_seedAlgebra s
  exact Module.nontrivial_of_finrank_pos (by rw [h]; exact width_pos _)

/-- The seed algebra has characteristic two. -/
instance seedAlgebraCharP (s : ℕ) : CharP (SeedAlgebra s) 2 :=
  charP_of_injective_algebraMap (algebraMap (ZMod 2) (SeedAlgebra s)).injective 2

/-- The power basis has the expected coordinate powers. -/
@[simp] theorem seedBasis_apply (s : ℕ) (i : Fin (width (s + 1))) :
    seedBasis s i = seedRoot s ^ (i : ℕ) := by
  simp only [seedBasis, Module.Basis.reindex_apply, PowerBasis.basis_eq_pow,
    AdjoinRoot.powerBasis'_gen, finCongr_symm, finCongr_apply, Fin.val_cast, seedRoot]

/-- The coordinate root satisfies the characteristic-two recurrence. -/
theorem seedRoot_width (s : ℕ) :
    seedRoot s ^ width (s + 1) = 1 + seedRoot s := by
  have h := AdjoinRoot.mk_self (f := checkPolynomial (s + 1))
  simp only [checkPolynomial] at h
  change 1 + seedRoot s + seedRoot s ^ width (s + 1) = 0 at h
  exact eq_neg_of_add_eq_zero_right h |>.trans (CharTwo.neg_eq _)

/-- The coordinate root has the advertised cyclic period, even though the
recurrence algebra need not be a field. -/
theorem seedRoot_period (s : ℕ) : seedRoot s ^ period (s + 1) = 1 := by
  have h := (AdjoinRoot.mk_eq_zero (f := checkPolynomial (s + 1))).mpr
    (checkPolynomial_dvd_period (s + 1))
  simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X] at h
  change seedRoot s ^ period (s + 1) + 1 = 0 at h
  exact eq_neg_of_add_eq_zero_left h |>.trans (CharTwo.neg_eq _)

/-- Exponents may be reduced modulo the physical cyclic period. -/
theorem seedRoot_pow_mod (s n : ℕ) :
    seedRoot s ^ n = seedRoot s ^ (n % period (s + 1)) :=
  pow_eq_pow_mod n (seedRoot_period s)

end Quantum.Stabilizer.Homological.BB.Fractal
