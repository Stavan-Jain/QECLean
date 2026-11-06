import QEC.Stabilizer.Framework.Homological.Certificate.PackedPopcount

/-!
# Parallel popcounts for thirty-bit masks

Five pair-summing stages compute the population count of every thirty-bit
mask packed into thirty-two-bit lanes. The generic popcount tree proves
the executable operation correct.
-/

namespace PackedDigits

open Quantum.Stabilizer.Homological.F2Mask

/-- The five masks used by the thirty-two-bit parallel popcount. -/
def popcountMask32 (k : Fin 5) : Nat :=
  packF (2 ^ (k.val + 1)) (2 ^ (4 - k.val)) (fun _ => 2 ^ (2 ^ k.val) - 1)

/-- Evaluate a natural before reusing it in a kernel computation. -/
def forceNat (value : Nat) (f : Nat → Nat) : Nat :=
  match value with
  | 0 => f 0
  | n + 1 => f (n + 1)

/-- Forcing evaluation preserves the value of an arithmetic expression. -/
theorem forceNat_eq (value : Nat) (f : Nat → Nat) : forceNat value f = f value := by
  cases value <;> rfl

/-- One executable pair-summing stage on thirty-two-bit lanes. -/
def popcountStep32 (r value k : Nat) : Nat :=
  forceNat value fun value =>
  let mask := r * popcountMask32 ⟨k % 5, Nat.mod_lt _ (by decide)⟩
  (value &&& mask) + ((value >>> (2 ^ k)) &&& mask)

/-- Compute thirty-two-bit lane popcounts with five parallel stages. -/
def popcount32 (r value : Nat) : Nat :=
  popcountStep32 r (popcountStep32 r (popcountStep32 r
    (popcountStep32 r (popcountStep32 r value 0) 1) 2) 3) 4

/-- Each pair-summing mask fits one thirty-two-bit word. -/
theorem popcountMask32_lt : ∀ k : Fin 5, popcountMask32 k < 2 ^ 32 := by
  decide +kernel

/-- Each mask repeats its smaller pair-summing pattern across the batch. -/
theorem popcountMask32_repeated (size : Nat) (k : Fin 5) :
    packF 32 size (fun _ => 1) * popcountMask32 k =
      packF (2 ^ (k.val + 1)) (2 ^ (4 - k.val) * size)
        (fun _ => 2 ^ (2 ^ k.val) - 1) := by
  rw [repeat_mul_eq_packF, packF_constant_group]
  have he : 2 ^ (k.val + 1) * 2 ^ (4 - k.val) = 32 := by
    fin_cases k <;> decide
  rw [he]
  rfl

/-- The executable five-stage operation is the proved pair-summing tree. -/
theorem popcount32_eq_tree (size value : Nat) :
    popcount32 (packF 32 size (fun _ => 1)) value = popcountTree 5 size value := by
  unfold popcount32 popcountStep32
  simp only [forceNat_eq, popcountMask32_repeated]
  simp only [popcountTree, Nat.reduceMod, Nat.reducePow,
    Nat.reduceAdd, Nat.reduceSub, ← Nat.mul_assoc, Nat.reduceMul, Nat.one_mul]

/-- Parallel popcount returns each thirty-bit mask's weight in its own lane. -/
theorem popcount32_packF (size : Nat) (f : Nat → Nat)
    (hf : ∀ i < size, f i < 2 ^ 30) :
    popcount32 (packF 32 size (fun _ => 1)) (packF 32 size f) =
      packF 32 size (fun i => bitCount 30 (f i)) := by
  have hfit : ∀ i < size, f i < 2 ^ 32 :=
    fun i hi => lt_trans (hf i hi) (by norm_num)
  rw [popcount32_eq_tree, popcountTree_eq 5 size _
    (by simpa using packF_lt 32 size f (by decide) hfit)]
  change packF 32 size (fun i => bitCount 32 (packF 32 size f >>> (32 * i))) = _
  apply packF_congr
  intro i hi
  rw [← bitCount_mod]
  simp only [Nat.shiftRight_eq_div_pow]
  rw [← lane_eq_div_mod]
  rw [lane_packF 32 size i f hfit, if_pos hi]
  exact bitCount_extend 30 2 (f i) (hf i hi)

end PackedDigits

#print axioms PackedDigits.popcount32_packF
