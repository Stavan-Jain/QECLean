import QEC.Stabilizer.Framework.Homological.Certificate.PackedProgram
import QEC.Stabilizer.Framework.Homological.Certificate.SwapNumeric

namespace Quantum.Stabilizer.Homological.F2Mask.Trellis

/-- Move a chosen coefficient to the top state bit using a verified packed permutation. -/
def swapPermutation (lane position high : Nat) : PackedPermutation lane (high + 1) where
  source := PackedSwap.source position high
  numeric := PackedSwap.numeric lane position high
  range := PackedSwap.source_lt position high
  involution i _ := PackedSwap.source_involutive position high i
  sound := PackedSwap.numeric_eq_packF lane position high

/-- Forget one state coordinate using the efficient verified swap implementation. -/
def PackedProgram.forgetBitFast {slot degree width finalWidth : Nat} (position : Nat)
    (tail : PackedProgram slot degree width finalWidth) :
    PackedProgram slot degree (width + 1) finalWidth :=
  PackedProgram.forget position (swapPermutation (slot * (degree + 1)) position width)
    (fun i _ => PackedSwap.forgetBit_eq_source_mod position width i) tail

#print axioms PackedProgram.forgetBitFast
end Quantum.Stabilizer.Homological.F2Mask.Trellis
