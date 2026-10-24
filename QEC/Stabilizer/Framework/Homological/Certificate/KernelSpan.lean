import QEC.Stabilizer.Framework.Homological.Certificate.MaskLinear
import QEC.Stabilizer.Framework.Homological.Trellis

namespace Quantum.Stabilizer.Homological.F2Mask

/-- Two XOR-linear functions agreeing on the bit basis agree on all bounded masks. -/
theorem xor_map_eq_of_basis (f g : Nat → Nat) (n : Nat)
    (hf0 : f 0 = 0) (hg0 : g 0 = 0)
    (hfx : ∀ a b, f (a ^^^ b) = f a ^^^ f b)
    (hgx : ∀ a b, g (a ^^^ b) = g a ^^^ g b)
    (hbasis : ∀ i < n, f (2 ^ i) = g (2 ^ i)) :
    ∀ word < 2 ^ n, f word = g word := by
  induction n with
  | zero =>
    intro word hw
    have : word = 0 := by simpa using hw
    simp [this, hf0, hg0]
  | succ n ih =>
    intro word hw
    by_cases hlow : word < 2 ^ n
    · exact ih (fun i hi => hbasis i (by omega)) word hlow
    · have hrest : word - 2 ^ n < 2 ^ n := by
        rw [pow_succ, Nat.mul_two] at hw
        omega
      have hword : word = (word - 2 ^ n) ^^^ 2 ^ n := by
        rw [Trellis.xor_two_pow_of_lt hrest]
        omega
      rw [hword, hfx, hgx, ih (fun i hi => hbasis i (by omega)) _ hrest,
        hbasis n (by omega)]

/-- A checked decomposition into free directions and a syndrome section reconstructs every mask. -/
theorem kernel_reconstruct_of_columns (n : Nat)
    (G D P E : List (Nat × Nat))
    (hcolumns : (List.range n).all (fun i => decide
      (reconX G (reconX D (2 ^ i)) ^^^ reconX P (reconX E (2 ^ i)) = 2 ^ i)) = true)
    {word : Nat} (hword : word < 2 ^ n) :
    reconX G (reconX D word) ^^^ reconX P (reconX E word) = word := by
  apply xor_map_eq_of_basis
    (fun word => reconX G (reconX D word) ^^^ reconX P (reconX E word)) id n
    (by simp [reconX_zero]) rfl ?_ (fun _ _ => rfl) ?_ word hword
  · intro a b
    simp only [reconX_xor]
    ac_rfl
  · intro i hi
    exact of_decide_eq_true ((List.all_eq_true.mp hcolumns) i (List.mem_range.mpr hi))

/-- The kernel of a checked syndrome map lies in the span of the certified free directions. -/
theorem kernel_span_of_columns (n : Nat)
    (G D P E : List (Nat × Nat))
    (hcolumns : (List.range n).all (fun i => decide
      (reconX G (reconX D (2 ^ i)) ^^^ reconX P (reconX E (2 ^ i)) = 2 ^ i)) = true)
    {word : Nat} (hword : word < 2 ^ n) (hcycle : reconX E word = 0) :
    XorSpan (G.map Prod.snd) word := by
  have heq := kernel_reconstruct_of_columns n G D P E hcolumns hword
  simp only [hcycle, reconX_zero, Nat.xor_zero] at heq
  rw [← heq]
  exact reconX_mem_span G (reconX D word)

#print axioms kernel_span_of_columns
end Quantum.Stabilizer.Homological.F2Mask
