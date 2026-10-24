/-
GENERATED FILE — DO NOT HAND-EDIT
Generator: qec-lab:experiments/bb_lab/scripts/bravyi360_kernel/generate.py
Emitter, relative to generator directory:
  emitters/compression_shallow_links.py
Data and SHA-256 hashes: compression_manifest.json
Regenerate:
  QECLEAN_ROOT=/path/to/QECLean \
    python3 experiments/bb_lab/scripts/bravyi360_kernel/generate.py --force
-/

import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.BottomCaseData
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.BottomBetaCache
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.BottomEmptyData

noncomputable section
namespace Quantum.Stabilizer.Homological.BB.Bravyi360.BottomShallow
open F2Mask PackedDigits
set_option maxRecDepth 100000
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The forest association uses the already checked packed shadow cache. -/
noncomputable def forestLinkCheck (beta index : Nat) : Bool :=
  Nat.blt index 27867 && Nat.beq beta (BottomForest.betaAtFast index)
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- A packed forest association has the original canonical-record meaning. -/
theorem forestLinkCheck_eq_true (beta index : Nat) :
    forestLinkCheck beta index = true ↔
      index < 27867 ∧ beta = (BottomForest.fiberAt index).beta := by
  simp only [forestLinkCheck,Bool.and_eq_true,Nat.blt_eq,Nat.beq_eq]
  constructor
  · rintro ⟨hi,hb⟩
    exact ⟨hi,by simpa only [BottomForest.betaAtFast_eq ⟨index,hi⟩] using hb⟩
  · rintro ⟨hi,hb⟩
    exact ⟨hi,by simpa only [BottomForest.betaAtFast_eq ⟨index,hi⟩] using hb⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- A bottom census representative is identified with its precise non-deep certificate family. -/
noncomputable def linkCheck (i : Nat) : Bool :=
  let b := OrbitBatchData.repAt i
  let j := BottomCase.localIndex i
  match BottomCase.tag i with
  | 0 => Nat.blt j 224352 && Nat.beq b (BottomEmpty.beta0 j)
  | 1 => Nat.blt j 20904 && Nat.beq b (BottomEmpty.beta1 j)
  | 2 => Nat.blt j 859 && Nat.beq b (BottomEmpty.beta2 j)
  | 3 => forestLinkCheck b j
  | 4 => Nat.beq b 0
  | 5 => true
  | _ => false

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Direct interpretation of a checked shallow-family association. -/
theorem linkCheck_sound (i : Nat) (h : linkCheck i = true) :
    (BottomCase.tag i = 0 ∧ BottomCase.localIndex i < 224352 ∧
      OrbitBatchData.repAt i = BottomEmpty.beta0 (BottomCase.localIndex i)) ∨
    (BottomCase.tag i = 1 ∧ BottomCase.localIndex i < 20904 ∧
      OrbitBatchData.repAt i = BottomEmpty.beta1 (BottomCase.localIndex i)) ∨
    (BottomCase.tag i = 2 ∧ BottomCase.localIndex i < 859 ∧
      OrbitBatchData.repAt i = BottomEmpty.beta2 (BottomCase.localIndex i)) ∨
    (BottomCase.tag i = 3 ∧ BottomCase.localIndex i < 27867 ∧
      OrbitBatchData.repAt i = (BottomForest.fiberAt (BottomCase.localIndex i)).beta) ∨
    (BottomCase.tag i = 4 ∧ OrbitBatchData.repAt i = 0) ∨ BottomCase.tag i = 5 := by
  unfold linkCheck at h
  split at h <;> simp_all [forestLinkCheck_eq_true,Bool.and_eq_true,Nat.blt_eq,Nat.beq_eq]
end Quantum.Stabilizer.Homological.BB.Bravyi360.BottomShallow
