import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.BottomShallowLinkCheck

noncomputable section
namespace Quantum.Stabilizer.Homological.BB.Bravyi360.BottomShallow
open F2Mask PackedDigits
set_option maxRecDepth 100000
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Check one row against fixed census and case chunks, avoiding repeated table dispatch. -/
noncomputable def linkChunkCheck (orbitWords caseWords base row : Nat) : Bool :=
  let beta := lane 128 row orbitWords
  let entry := lane 24 row caseWords
  let index := entry / 8
  let family := if entry % 8 = 5 then
      if index < 28 ∧ base + row = BottomCase.deepOrbitIndex index then 5 else 4
    else min (entry % 8) 4
  match family with
  | 0 => Nat.blt index 224352 && Nat.beq beta (BottomEmpty.beta0 index)
  | 1 => Nat.blt index 20904 && Nat.beq beta (BottomEmpty.beta1 index)
  | 2 => Nat.blt index 859 && Nat.beq beta (BottomEmpty.beta2 index)
  | 3 => forestLinkCheck beta index
  | 4 => Nat.beq beta 0
  | 5 => true
  | _ => false
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The fixed-chunk checker is exactly the global family checker on that chunk. -/
theorem linkChunkCheck_eq (batch row : Nat) (hrow : row < 1024) :
    linkChunkCheck (OrbitBatchData.wordsAt batch) (BottomCase.wordsAt batch)
      (1024*batch) row = linkCheck (1024*batch+row) := by
  have hd : (1024*batch+row)/1024 = batch := by omega
  have hm : (1024*batch+row)%1024 = row := by omega
  simp only [linkChunkCheck,linkCheck,OrbitBatchData.repAt,BottomCase.tag,
    BottomCase.localIndex,BottomCase.entry,hd,hm]
  rfl
#print axioms linkChunkCheck_eq
end Quantum.Stabilizer.Homological.BB.Bravyi360.BottomShallow
