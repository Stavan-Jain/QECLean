import QEC.Stabilizer.Framework.Homological.Certificate.PackedDigits

noncomputable section
namespace PackedDigits
/-- Retain alternating blocks while inserting zero padding into a packed data constant. -/
noncomputable def expandMask (block depth group : Nat) : Nat :=
  Nat.mul (Nat.div (Nat.sub (Nat.shiftLeft 1 (2*block*2^depth)) 1)
    (Nat.sub (Nat.shiftLeft 1 (2*block*group)) 1))
    (Nat.sub (Nat.shiftLeft 1 (block*group)) 1)
/-- Double the lane width of a data constant using a logarithmic sequence of bit operations. -/
noncomputable def expandDataAux (block depth : Nat) : Nat → Nat → Nat
  | 0,x => x
  | k+1,x => expandDataAux block depth k
      (Nat.land (Nat.lor x (Nat.shiftLeft x (block*2^k))) (expandMask block depth (2^k)))
/-- A compact data spelling whose value has twice the original lane width. -/
noncomputable def expandData (block depth x : Nat) : Nat := expandDataAux block depth depth x
end PackedDigits
