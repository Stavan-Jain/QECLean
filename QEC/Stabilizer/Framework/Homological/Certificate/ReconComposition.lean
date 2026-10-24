import QEC.Stabilizer.Framework.Homological.Certificate.ReconWalk
import QEC.Stabilizer.Framework.Homological.Certificate.ParityFold

namespace Quantum.Stabilizer.Homological.F2Mask

/-- Composition of binary column reconstructions is reconstruction of the composed columns. -/
theorem reconX_comp (outer inner : List (Nat × Nat)) (value : Nat) :
    reconX outer (reconX inner value) =
      reconX (inner.map fun p => (p.1,reconX outer p.2)) value := by
  have hcons : ∀ (p : Nat × Nat) (ps : List (Nat × Nat)), reconX (p::ps) value =
      if value.testBit p.1 then p.2 ^^^ reconX ps value else reconX ps value := by
    intro p ps
    simp only [reconX,List.filter_cons]
    cases value.testBit p.1 <;> simp [xorList_cons]
  induction inner with
  | nil => simp [reconX,reconX_zero]
  | cons p ps ih =>
    rw [hcons,List.map_cons,hcons]
    cases h : value.testBit p.1
    · simpa only [h,if_false] using ih
    · simp only [h,if_true]
      rw [reconX_xor,ih]

/-- Fast parity is unchanged when both counting widths contain a bounded mask. -/
theorem parityFold_change_width (n k l x : Nat) (hnk : n ≤ 2^k) (hnl : n ≤ 2^l)
    (hx : x < 2^n) : parityFold k x = parityFold l x := by
  rw [parityFold_eq,parityFold_eq,bitCount_extend n (2^k) x hnk hx,
    bitCount_extend n (2^l) x hnl hx]

/-- A single annihilating dual with odd right-hand side excludes an on-shadow solution. -/
theorem no_supported_solution_of_raw_dual (k : Nat) (E R TE TR : List (Nat × Nat))
    (hE : ∀ l v, parityFold k (reconX TE l &&& v) = parityFold k (l &&& reconX E v))
    (hR : ∀ l v, parityFold k (reconX TR l &&& v) = parityFold k (l &&& reconX R v))
    (lam beta word : Nat) (hann : reconX TE lam &&& beta = 0)
    (hodd : parityFold k (reconX TR lam &&& beta) = 1)
    (hs : word &&& beta = word) : reconX E word ≠ reconX R beta := by
  intro he
  have hz : reconX TE lam &&& word = 0 := by
    calc
      reconX TE lam &&& word = reconX TE lam &&& (word &&& beta) := by rw [hs]
      _ = (reconX TE lam &&& beta) &&& word := by ac_rfl
      _ = 0 := by simp [hann]
  have hp : parityFold k 0 = 1 := by
    rw [← hz,hE,he,← hR]
    exact hodd
  have hzero : parityFold k 0 = 0 := by simp [parityFold_eq,bitCount_eq_card]
  omega

#print axioms reconX_comp
#print axioms no_supported_solution_of_raw_dual
end Quantum.Stabilizer.Homological.F2Mask
