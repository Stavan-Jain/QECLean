import QEC.Stabilizer.Framework.Homological.Certificate.MaskedAffine

namespace Quantum.Stabilizer.Homological.F2Mask

/-- Intersecting a point mass with a mask keeps it exactly when that bit is set. -/
theorem two_pow_and_mask (i beta : Nat) :
    (2 ^ i) &&& beta = if beta.testBit i then 2 ^ i else 0 := by
  apply Nat.eq_of_testBit_eq
  intro j
  simp only [Nat.testBit_and, Nat.testBit_two_pow]
  by_cases h : i = j
  · subst j
    cases beta.testBit i <;> simp
  · cases beta.testBit i <;> simp [h]

/-- Check only the nonzero point-mass columns inside a fixed support. -/
def affineColumnsCheck (n beta : Nat) (E P K D : List (Nat × Nat)) : Bool :=
  (List.range n).all fun i => if beta.testBit i then
    Nat.beq (reconX P (reconX E (2 ^ i)) ^^^ reconX K (reconX D (2 ^ i))) (2 ^ i)
  else true

/-- Skipping columns outside the support preserves the full reconstruction identity. -/
theorem affineColumnsCheck_sound (n beta : Nat) (E P K D : List (Nat × Nat))
    (h : affineColumnsCheck n beta E P K D = true) :
    (List.range n).all (fun i => decide
      (reconX P (reconX E ((2 ^ i) &&& beta)) ^^^
        reconX K (reconX D ((2 ^ i) &&& beta)) = (2 ^ i) &&& beta)) = true := by
  apply List.all_eq_true.mpr
  intro i hi
  have hc := (List.all_eq_true.mp h) i hi
  rw [two_pow_and_mask]
  cases hb : beta.testBit i
  · simp [hb, reconX_zero]
  · simp only [hb, if_true, Nat.beq_eq] at hc ⊢
    exact decide_eq_true hc

/-- Finite reconstruction data and boundary witnesses for one affine support fiber. -/
structure AffineMaskCertificate where
  /-- The fixed shadow support. -/
  beta : Nat
  /-- A right inverse on the constrained columns. -/
  sectionColumns : List (Nat × Nat)
  /-- Free directions in the constrained variables. -/
  kernelColumns : List (Nat × Nat)
  /-- Coordinates reading the free variables. -/
  decoderColumns : List (Nat × Nat)
  /-- Number of free coefficient bits. -/
  dimension : Nat
  /-- Outside masks paired with boundary coefficients for every free assignment. -/
  seeds : List (Nat × List Nat)

namespace AffineMaskCertificate

/-- The candidate reconstructed from an outside support and its free coefficients. -/
def candidate (C : AffineMaskCertificate) (E R : List (Nat × Nat)) (off k : Nat) : Nat :=
  off ^^^ reconX C.sectionColumns (reconX R C.beta ^^^ reconX E off) ^^^
    reconX C.kernelColumns k

/-- Check reconstruction and all boundary witnesses for a finite affine fiber. -/
def checkBoundary (C : AffineMaskCertificate) (n : Nat)
    (E R G : List (Nat × Nat)) (join : Nat → Nat → Nat) : Bool :=
  affineColumnsCheck n C.beta E C.sectionColumns C.kernelColumns C.decoderColumns &&
    C.decoderColumns.all (fun p => decide (p.2 < 2 ^ C.dimension)) &&
    C.seeds.all (fun seed => (List.range (2 ^ C.dimension)).all (fun k =>
      Nat.beq (reconX G (seed.2[k]!)) (join (C.candidate E R seed.1 k) C.beta)))

/-- Every solution with a certified outside support reconstructs from boundary generators. -/
theorem boundary_of_check (C : AffineMaskCertificate) (n : Nat)
    (E R G : List (Nat × Nat)) (join : Nat → Nat → Nat)
    (h : C.checkBoundary n E R G join = true)
    {word : Nat} (hword : word < 2 ^ n)
    (hequation : reconX E word = reconX R C.beta)
    (hoff : outsideMask word C.beta ∈ C.seeds.map Prod.fst) :
    ∃ coefficient : Nat, reconX G coefficient = join word C.beta := by
  simp only [checkBoundary, Bool.and_eq_true] at h
  apply masked_affine_forall n C.beta (reconX R C.beta) C.dimension
    E C.sectionColumns C.kernelColumns C.decoderColumns
    (affineColumnsCheck_sound _ _ _ _ _ _ h.1.1)
    (fun p hp => of_decide_eq_true ((List.all_eq_true.mp h.1.2) p hp))
    (C.seeds.map Prod.fst) (fun v => ∃ coefficient, reconX G coefficient = join v C.beta)
    ?_ hword hequation hoff
  intro off ho k hk
  obtain ⟨seed, hs, rfl⟩ := List.mem_map.mp ho
  have hc := (List.all_eq_true.mp ((List.all_eq_true.mp h.2) seed hs)) k
    (List.mem_range.mpr hk)
  exact ⟨seed.2[k]!, Nat.beq_eq.mp hc⟩

/-- Check a finite affine fiber against a census up to its deck involution. -/
def checkCensus (C : AffineMaskCertificate) (n : Nat) (E R : List (Nat × Nat))
    (census : List Nat) : Bool :=
  affineColumnsCheck n C.beta E C.sectionColumns C.kernelColumns C.decoderColumns &&
    C.decoderColumns.all (fun p => decide (p.2 < 2 ^ C.dimension)) &&
    C.seeds.all (fun seed => (List.range (2 ^ C.dimension)).all (fun k =>
      census.contains (C.candidate E R seed.1 k) ||
        census.contains ((C.candidate E R seed.1 k) ^^^ C.beta)))

/-- Every affine solution appears in a checked census, possibly after the deck involution. -/
theorem census_of_check (C : AffineMaskCertificate) (n : Nat) (E R : List (Nat × Nat))
    (census : List Nat) (h : C.checkCensus n E R census = true)
    {word : Nat} (hword : word < 2 ^ n)
    (hequation : reconX E word = reconX R C.beta)
    (hoff : outsideMask word C.beta ∈ C.seeds.map Prod.fst) :
    word ∈ census ∨ (word ^^^ C.beta) ∈ census := by
  simp only [checkCensus, Bool.and_eq_true] at h
  apply masked_affine_forall n C.beta (reconX R C.beta) C.dimension
    E C.sectionColumns C.kernelColumns C.decoderColumns
    (affineColumnsCheck_sound _ _ _ _ _ _ h.1.1)
    (fun p hp => of_decide_eq_true ((List.all_eq_true.mp h.1.2) p hp))
    (C.seeds.map Prod.fst) (fun v => v ∈ census ∨ (v ^^^ C.beta) ∈ census)
    ?_ hword hequation hoff
  intro off ho k hk
  obtain ⟨seed, hs, rfl⟩ := List.mem_map.mp ho
  have hc := (List.all_eq_true.mp ((List.all_eq_true.mp h.2) seed hs)) k
    (List.mem_range.mpr hk)
  simpa only [Bool.or_eq_true, List.contains_iff_mem] using hc

end AffineMaskCertificate
#print axioms AffineMaskCertificate.boundary_of_check
end Quantum.Stabilizer.Homological.F2Mask
