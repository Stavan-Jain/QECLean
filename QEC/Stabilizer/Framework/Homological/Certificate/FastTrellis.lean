import QEC.Stabilizer.Framework.Homological.Certificate.PackedSwapPermutation

namespace Quantum.Stabilizer.Homological.F2Mask.Trellis

/-- One coordinate's numerical update metadata. -/
abbrev PackedStep := Nat × Bool × List Nat × Nat × Bool

/-- A flattened packed update: introduce a bit, emit one output, and optionally forget a bit. -/
def packedStep (slot degree : Nat) (table : Nat) (s : PackedStep) : Nat :=
  let width := s.1
  let start := s.2.1
  let positions := s.2.2.1
  let drop := s.2.2.2.1
  let offset := s.2.2.2.2
  let lane := slot * (degree + 1)
  let table := if start then table ||| (table <<< (lane * 2 ^ (width - 1))) else table
  let mask := PackedProgram.outputMask lane width positions offset
  let full := 2 ^ (lane * 2 ^ width) - 1
  let clip := PackedDigits.repeatBlock (2 ^ (slot * degree) - 1) lane width
  let table := (table &&& (full ^^^ mask)) ||| (((table &&& mask) &&& clip) <<< slot)
  if drop < width then
    let table := PackedSwap.numeric lane drop (width - 1) table
    let half := lane * 2 ^ (width - 1)
    (table &&& (2 ^ half - 1)) + (table >>> half)
  else table

/-- Efficient kernel representation of a power of two. -/
def fastPowTwo (n : Nat) : Nat := Nat.shiftLeft 1 n

/-- Shifting one left computes the corresponding power of two. -/
theorem fastPowTwo_eq (n : Nat) : fastPowTwo n = 2 ^ n := by
  simp [fastPowTwo, Nat.shiftLeft_eq]

/-- Efficient periodic zero-bit mask using primitive shifts for large powers. -/
def fastBitZeroMask (lane width position : Nat) : Nat :=
  PackedDigits.repeatBlock (fastPowTwo (lane * fastPowTwo position) - 1)
    (lane * fastPowTwo (position + 1)) (width - position - 1)

/-- The efficient periodic mask has the same lane semantics as the abstract mask. -/
theorem fastBitZeroMask_eq (lane width position : Nat) :
    fastBitZeroMask lane width position = PackedDigits.bitZeroMask lane width position := by
  simp only [fastBitZeroMask, fastPowTwo_eq, PackedDigits.bitZeroMask]

/-- Efficient affine output mask using primitive shifts for large powers. -/
def fastOutputMask (lane width : Nat) (positions : List Nat) (offset : Bool) : Nat :=
  positions.foldr (fun p acc => fastBitZeroMask lane width p ^^^ acc)
    (if offset then fastPowTwo (lane * fastPowTwo width) - 1 else 0)

/-- The efficient affine mask equals the proved abstract mask. -/
theorem fastOutputMask_eq (lane width : Nat) (positions : List Nat) (offset : Bool) :
    fastOutputMask lane width positions offset = PackedProgram.outputMask lane width positions offset := by
  simp only [fastOutputMask, fastBitZeroMask_eq, fastPowTwo_eq, PackedProgram.outputMask]

/-- Efficient whole-table coordinate permutation using primitive shifts. -/
def fastSwap (lane position high table : Nat) : Nat :=
  if position < high then
    let full := fastPowTwo (lane * fastPowTwo (high + 1)) - 1
    let low := fastPowTwo (lane * fastPowTwo high) - 1
    let mask := fastBitZeroMask lane (high + 1) position
    let upMask := low &&& (full ^^^ mask)
    let downMask := (full ^^^ low) &&& mask
    let shift := lane * (fastPowTwo high - fastPowTwo position)
    (table &&& (full ^^^ upMask ^^^ downMask)) |||
      ((table &&& upMask) <<< shift) ||| ((table &&& downMask) >>> shift)
  else table

/-- The efficient state permutation equals the proved abstract permutation. -/
theorem fastSwap_eq (lane position high table : Nat) :
    fastSwap lane position high table = PackedSwap.numeric lane position high table := by
  simp only [fastSwap, fastPowTwo_eq, fastBitZeroMask_eq, PackedSwap.numeric]

/-- The flattened numerical step evaluated with primitive power-of-two operations. -/
def fastPackedStep (slot degree : Nat) (table : Nat) (s : PackedStep) : Nat :=
  let width := s.1
  let start := s.2.1
  let positions := s.2.2.1
  let drop := s.2.2.2.1
  let offset := s.2.2.2.2
  let lane := slot * (degree + 1)
  let table := if start then table ||| (table <<< (lane * fastPowTwo (width - 1))) else table
  let mask := fastOutputMask lane width positions offset
  let full := fastPowTwo (lane * fastPowTwo width) - 1
  let clip := PackedDigits.repeatBlock (fastPowTwo (slot * degree) - 1) lane width
  let table := (table &&& (full ^^^ mask)) ||| (((table &&& mask) &&& clip) <<< slot)
  if drop < width then
    let table := fastSwap lane drop (width - 1) table
    let half := lane * fastPowTwo (width - 1)
    (table &&& (fastPowTwo half - 1)) + (table >>> half)
  else table

/-- The optimized numerical step has exactly the same semantics as the abstract packed step. -/
theorem fastPackedStep_eq (slot degree table : Nat) (s : PackedStep) :
    fastPackedStep slot degree table s = packedStep slot degree table s := by
  simp only [fastPackedStep, fastPowTwo_eq, fastOutputMask_eq, fastSwap_eq, packedStep]

/-- Fast and abstract numerical folds agree for arbitrary coordinate metadata. -/
theorem fastPackedFold_eq (slot degree : Nat) (steps : List PackedStep) (table : Nat) :
    steps.foldl (fastPackedStep slot degree) table = steps.foldl (packedStep slot degree) table := by
  have h : fastPackedStep slot degree = packedStep slot degree := by
    funext table step
    exact fastPackedStep_eq slot degree table step
  rw [h]

/-- Replacing implementation fields by definitionally equal flattened fields preserves soundness. -/
def PackedProgram.flatten {slot degree : Nat} (C : PackedProgram slot degree 0 0)
    (program : List Instruction) (numeric : Nat → Nat) (merges : Nat)
    (hprogram : C.certificate.program = program)
    (hnumeric : C.numeric = numeric) (hmerges : C.merges = merges) :
    PackedProgram slot degree 0 0 where
  certificate := {
    program := program
    network := C.certificate.network
    backward_one := by
      intro state hstate
      rw [← hprogram]
      exact C.certificate.backward_one state hstate }
  numeric := numeric
  merges := merges
  sound := by
    intro bound f hs hb hf
    obtain ⟨g, hg, hnum, hsem⟩ := C.sound bound f hs (by simpa only [hmerges] using hb) hf
    exact ⟨g, by simpa only [hmerges] using hg, by simpa only [hnumeric] using hnum, hsem⟩

end Quantum.Stabilizer.Homological.F2Mask.Trellis
