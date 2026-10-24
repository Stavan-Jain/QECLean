import QEC.Stabilizer.Framework.Homological.Certificate.PairPlaneCoverage
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.DualConstraints

noncomputable section

namespace Quantum.Stabilizer.Homological.F2Mask

/-- Per-plane dual data checked against the actual compressed matrix columns. -/
noncomputable def dualPlaneCertificate (n k : Nat) (columns : List (Nat × Nat)) (beta : Nat) :
    List (Nat × Nat) → Nat → Prop
  | [], _ => True
  | (coeff, plane) :: rest, target =>
      plane < 2^n ∧
      reconX columns coeff &&& (2^n-1) = plane ∧
      reconX columns coeff &&& beta = 0 ∧
      parityFold k ((reconX columns coeff >>> n) &&& beta) =
        (if target.testBit 0 then 1 else 0) ∧
      dualPlaneCertificate n k columns beta rest (target >>> 1)

noncomputable instance (n k : Nat) (columns : List (Nat × Nat)) (beta target : Nat)
    (planes : List (Nat × Nat)) : Decidable (dualPlaneCertificate n k columns beta planes target) := by
  induction planes generalizing target with
  | nil => exact isTrue trivial
  | cons p ps ih =>
      unfold dualPlaneCertificate
      infer_instance

/-- Every plane certified by a matrix dual fits in the ambient mask. -/
theorem dualPlaneCertificate_bounded (n k : Nat) (columns : List (Nat × Nat)) (beta : Nat)
    (planes : List (Nat × Nat)) (target : Nat)
    (h : dualPlaneCertificate n k columns beta planes target) :
    ∀ p ∈ planes.map Prod.snd, p < 2^n := by
  induction planes generalizing target with
  | nil => simp
  | cons a as ih =>
      intro p hp
      simp only [List.map_cons,List.mem_cons] at hp
      rcases hp with rfl | hp
      · exact h.1
      · exact ih _ h.2.2.2.2 p hp

/-- Actual linear constraints imply all the certified parity plane requirements. -/
theorem dualPlaneCertificate_constraints (n k : Nat) (columns : List (Nat × Nat))
    (beta word : Nat) (planes : List (Nat × Nat)) (target : Nat) (hw : word < 2^n)
    (hlinear : ∀ coeff, reconX columns coeff &&& beta = 0 →
      parityFold k (reconX columns coeff &&& word) =
        parityFold k ((reconX columns coeff >>> n) &&& beta))
    (h : dualPlaneCertificate n k columns beta planes target) :
    planeConstraints k (planes.map Prod.snd) target word := by
  induction planes generalizing target with
  | nil => trivial
  | cons a as ih =>
      refine ⟨?_,ih _ h.2.2.2.2⟩
      have hlow : a.2 &&& word = reconX columns a.1 &&& word := by
        rw [← h.2.1,Nat.and_assoc,Nat.and_comm (2^n-1) word,
          Nat.and_two_pow_sub_one_of_lt_two_pow hw]
      rw [hlow,hlinear a.1 h.2.2.1]
      exact h.2.2.2.1

/-- The support outside a shadow stays bounded and is disjoint from the shadow. -/
theorem outsideMask_bounded_disjoint (n word beta : Nat) (hw : word < 2^n) :
    outsideMask word beta < 2^n ∧ outsideMask word beta &&& beta = 0 := by
  constructor
  · rw [outsideMask_eq_and_complement hw]
    exact lt_of_le_of_lt Nat.and_le_left hw
  · apply Nat.eq_of_testBit_eq
    intro i
    simp only [outsideMask,Nat.testBit_and,Nat.testBit_xor,Nat.zero_testBit]
    cases word.testBit i <;> cases beta.testBit i <;> decide

/-- Valid combined dual images specify the required bits without redoing matrix multiplication. -/
noncomputable def taggedPlaneCertificate (n k beta : Nat) : List Nat → Nat → Prop
  | [], _ => True
  | row :: rest, target =>
      row &&& beta = 0 ∧
      parityFold k ((row >>> n) &&& beta) = (if target.testBit 0 then 1 else 0) ∧
      taggedPlaneCertificate n k beta rest (target >>> 1)

noncomputable instance (n k beta target : Nat) (rows : List Nat) :
    Decidable (taggedPlaneCertificate n k beta rows target) := by
  induction rows generalizing target with
  | nil => exact isTrue trivial
  | cons row rows ih => unfold taggedPlaneCertificate; infer_instance

/-- The low-coordinate parts of valid combined dual images satisfy the plane constraints. -/
theorem taggedPlaneCertificate_constraints (n k beta word : Nat) (rows : List Nat)
    (target : Nat) (hw : word < 2^n)
    (hlinear : ∀ row ∈ rows, row &&& beta = 0 →
      parityFold k (row &&& word) = parityFold k ((row >>> n) &&& beta))
    (h : taggedPlaneCertificate n k beta rows target) :
    planeConstraints k (rows.map (fun row => row &&& (2^n-1))) target word := by
  induction rows generalizing target with
  | nil => trivial
  | cons row rows ih =>
      refine ⟨?_,ih _ (fun a ha => hlinear a (by simp [ha])) h.2.2⟩
      change parityFold k ((row &&& (2^n-1)) &&& word) = _
      rw [Nat.and_assoc,Nat.and_comm (2^n-1) word,
        Nat.and_two_pow_sub_one_of_lt_two_pow hw,hlinear row (by simp) h.1]
      exact h.2.1

end Quantum.Stabilizer.Homological.F2Mask
