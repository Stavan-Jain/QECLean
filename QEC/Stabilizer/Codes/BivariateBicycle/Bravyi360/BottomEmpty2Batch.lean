/-
GENERATED FILE — DO NOT HAND-EDIT
Generator: qec-lab:experiments/bb_lab/scripts/bravyi360_kernel/generate.py
Emitter, relative to generator directory:
  emitters/mark_research_noncomputable.py
Data and SHA-256 hashes: research_manifest.json
Regenerate:
  QECLEAN_ROOT=/path/to/QECLean \
    python3 experiments/bb_lab/scripts/bravyi360_kernel/generate.py --force
-/

import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.BottomEmpty2BatchData0
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.BottomEmpty2BatchData1
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.BottomEmpty2BatchData2
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.BottomEmpty2BatchData3
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.BottomEmpty2BatchData4
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.BottomEmpty2BatchData5
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.BottomEmpty2BatchData6
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.BottomEmpty2BatchData7
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.BottomEmpty2BatchData8
import Mathlib.Tactic.FinCases

noncomputable section
set_option maxRecDepth 100000
namespace Quantum.Stabilizer.Homological.BB.Bravyi360.BottomEmpty
open F2Mask FiberData PackedDigits BottomForest
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Select one bounded batch of actual cap-two records. -/
noncomputable def batchTwoRecordsAt : Nat → List TwoRecord
  | 0 => batchTwoRecords0
  | 1 => batchTwoRecords1
  | 2 => batchTwoRecords2
  | 3 => batchTwoRecords3
  | 4 => batchTwoRecords4
  | 5 => batchTwoRecords5
  | 6 => batchTwoRecords6
  | 7 => batchTwoRecords7
  | 8 => batchTwoRecords8
  | _ => []
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Select a cap-two record at its canonical empty-fiber index. -/
noncomputable def batchTwoRecordAt (i : Nat) : TwoRecord := (batchTwoRecordsAt (i/100)).getD (i%100) default
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Batch records use exactly the shared empty-fiber shadow order. -/
theorem batchTwoBeta : ∀ i : Fin 859, (batchTwoRecordAt i.val).beta = beta2 i.val := by
  decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every valid batch has the expected number of records. -/
theorem batchTwoLength (b : Fin 9) :
    (batchTwoRecordsAt b.val).length = if b.val < 8 then 100 else 59 := by
  fin_cases b
  · exact batchTwoLength0
  · exact batchTwoLength1
  · exact batchTwoLength2
  · exact batchTwoLength3
  · exact batchTwoLength4
  · exact batchTwoLength5
  · exact batchTwoLength6
  · exact batchTwoLength7
  · exact batchTwoLength8
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every canonical empty cap-two index denotes a member of its bounded batch. -/
theorem batchTwoRecordAt_mem (i : Fin 859) :
    batchTwoRecordAt i.val ∈ batchTwoRecordsAt (i.val/100) := by
  have hb : i.val/100 < 9 := by omega
  have hi : i.val%100 < (batchTwoRecordsAt (i.val/100)).length := by
    rw [batchTwoLength ⟨i.val/100,hb⟩]
    change i.val%100 < if i.val/100 < 8 then 100 else 59
    have hilim := i.isLt
    have hdecomp := Nat.mod_add_div i.val 100
    split_ifs <;> omega
  unfold batchTwoRecordAt
  rw [List.getD_eq_getElem _ _ hi]
  exact List.getElem_mem hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every listed batch excludes all solutions with outside weight at most two. -/
theorem batchTwoRecords_impossible (b : Fin 9) (r : TwoRecord)
    (hr : r ∈ batchTwoRecordsAt b.val) (word : Nat) (hw : word < 2^90)
    (he : reconX bottomEColumns word = reconX bottomRColumns r.beta)
    (hoff : bitCount 90 (outsideMask word r.beta) ≤ 2) : False := by
  fin_cases b
  · exact twoBatch_impossible bottomPairSpreadTable bottomPairRep bottomPair_lookup bottomPair_rep
      batchTwoRecords0 batchTwoPacking0 batchTwoChecked0 r hr word hw he hoff
  · exact twoBatch_impossible bottomPairSpreadTable bottomPairRep bottomPair_lookup bottomPair_rep
      batchTwoRecords1 batchTwoPacking1 batchTwoChecked1 r hr word hw he hoff
  · exact twoBatch_impossible bottomPairSpreadTable bottomPairRep bottomPair_lookup bottomPair_rep
      batchTwoRecords2 batchTwoPacking2 batchTwoChecked2 r hr word hw he hoff
  · exact twoBatch_impossible bottomPairSpreadTable bottomPairRep bottomPair_lookup bottomPair_rep
      batchTwoRecords3 batchTwoPacking3 batchTwoChecked3 r hr word hw he hoff
  · exact twoBatch_impossible bottomPairSpreadTable bottomPairRep bottomPair_lookup bottomPair_rep
      batchTwoRecords4 batchTwoPacking4 batchTwoChecked4 r hr word hw he hoff
  · exact twoBatch_impossible bottomPairSpreadTable bottomPairRep bottomPair_lookup bottomPair_rep
      batchTwoRecords5 batchTwoPacking5 batchTwoChecked5 r hr word hw he hoff
  · exact twoBatch_impossible bottomPairSpreadTable bottomPairRep bottomPair_lookup bottomPair_rep
      batchTwoRecords6 batchTwoPacking6 batchTwoChecked6 r hr word hw he hoff
  · exact twoBatch_impossible bottomPairSpreadTable bottomPairRep bottomPair_lookup bottomPair_rep
      batchTwoRecords7 batchTwoPacking7 batchTwoChecked7 r hr word hw he hoff
  · exact twoBatch_impossible bottomPairSpreadTable bottomPairRep bottomPair_lookup bottomPair_rep
      batchTwoRecords8 batchTwoPacking8 batchTwoChecked8 r hr word hw he hoff
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every listed bottom cap-two fiber is impossible with at most two outside coordinates. -/
theorem cap2_impossible (i : Fin 859) (word : Nat) (hw : word < 2^90)
    (he : reconX bottomEColumns word = reconX bottomRColumns (beta2 i.val))
    (hoff : bitCount 90 (outsideMask word (beta2 i.val)) ≤ 2) : False :=
  batchTwoRecords_impossible ⟨i.val/100,by omega⟩ (batchTwoRecordAt i.val)
    (batchTwoRecordAt_mem i) word hw
    (by simpa only [batchTwoBeta i] using he) (by simpa only [batchTwoBeta i] using hoff)
#print axioms cap2_impossible
end Quantum.Stabilizer.Homological.BB.Bravyi360.BottomEmpty
