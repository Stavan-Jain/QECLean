import QEC.Stabilizer.Framework.Homological.Certificate.MaskLinear

namespace Quantum.Stabilizer.Homological.F2Mask

/-- Reconstruction ignores coefficient bits beyond every named pivot. -/
theorem reconX_mod (rows : List (Nat × Nat)) (n value : Nat)
    (hp : ∀ p ∈ rows, p.1 < n) : reconX rows (value % 2^n) = reconX rows value := by
  unfold reconX
  congr 2
  apply List.filter_congr
  intro p hm
  simp only [Nat.testBit_mod_two_pow, hp p hm, decide_true, Bool.true_and]

/-- A finite chain ignores mask bits beyond its coordinate range. -/
theorem chainOfMask_mod {ι : Type} {n : Nat} (e : ι ≃ Fin n) (value : Nat) :
    chainOfMask e (value % 2^n) = chainOfMask e value := by
  ext q
  simp [chainOfMask, Nat.testBit_mod_two_pow, (e q).isLt]

/-- Re-encoding a decoded mask truncates precisely its unused high bits. -/
theorem maskOf_chainOfMask_mod {ι : Type} {n : Nat} (e : ι ≃ Fin n) (value : Nat) :
    maskOf e (chainOfMask e value) = value % 2^n := by
  rw [← chainOfMask_mod e value]
  exact maskOf_chainOfMask e (Nat.mod_lt _ (Nat.two_pow_pos _))

/-- A bounded-pivot reconstruction evaluates directly on any natural mask. -/
theorem reconLinear_chainOfMask {ι κ : Type} {n m : Nat}
    (e : ι ≃ Fin n) (f : κ ≃ Fin m) (rows : List (Nat × Nat))
    (hp : ∀ p ∈ rows, p.1 < n) (value : Nat) :
    reconLinear e f rows (chainOfMask e value) = chainOfMask f (reconX rows value) := by
  change chainOfMask f (reconX rows (maskOf e (chainOfMask e value))) = _
  rw [maskOf_chainOfMask_mod, reconX_mod rows n value hp]

#print axioms reconLinear_chainOfMask
end Quantum.Stabilizer.Homological.F2Mask
