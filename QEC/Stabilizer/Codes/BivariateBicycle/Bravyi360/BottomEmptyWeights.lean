/-
GENERATED FILE — DO NOT HAND-EDIT
Generator: qec-lab:experiments/bb_lab/scripts/bravyi360_kernel/generate.py
Emitter, relative to generator directory:
  emitters/compression_bottom_empty_weights.py
Data and SHA-256 hashes: compression_manifest.json
Regenerate:
  QECLEAN_ROOT=/path/to/QECLean \
    python3 experiments/bb_lab/scripts/bravyi360_kernel/generate.py --force
-/

import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.BottomEmptyData
import QEC.Stabilizer.Framework.Homological.Certificate.BatchWidePopcount

noncomputable section
set_option maxRecDepth 100000
namespace Quantum.Stabilizer.Homological.BB.Bravyi360.BottomEmpty
open F2Mask PackedDigits
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 0. -/
theorem weights0_0 : beta0Words0 < 2^(256*1024) ∧
    beta0Words0 &&& ((rep256 1024)*(2^90-1)) = beta0Words0 ∧
    popcount256 (rep256 1024) beta0Words0 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 0 has the exact claimed weight. -/
theorem weight0_0 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words0) = 22 := by
  have h := weights0_0
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words0 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 1. -/
theorem weights0_1 : beta0Words1 < 2^(256*1024) ∧
    beta0Words1 &&& ((rep256 1024)*(2^90-1)) = beta0Words1 ∧
    popcount256 (rep256 1024) beta0Words1 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 1 has the exact claimed weight. -/
theorem weight0_1 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words1) = 22 := by
  have h := weights0_1
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words1 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 2. -/
theorem weights0_2 : beta0Words2 < 2^(256*1024) ∧
    beta0Words2 &&& ((rep256 1024)*(2^90-1)) = beta0Words2 ∧
    popcount256 (rep256 1024) beta0Words2 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 2 has the exact claimed weight. -/
theorem weight0_2 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words2) = 22 := by
  have h := weights0_2
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words2 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 3. -/
theorem weights0_3 : beta0Words3 < 2^(256*1024) ∧
    beta0Words3 &&& ((rep256 1024)*(2^90-1)) = beta0Words3 ∧
    popcount256 (rep256 1024) beta0Words3 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 3 has the exact claimed weight. -/
theorem weight0_3 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words3) = 22 := by
  have h := weights0_3
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words3 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 4. -/
theorem weights0_4 : beta0Words4 < 2^(256*1024) ∧
    beta0Words4 &&& ((rep256 1024)*(2^90-1)) = beta0Words4 ∧
    popcount256 (rep256 1024) beta0Words4 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 4 has the exact claimed weight. -/
theorem weight0_4 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words4) = 22 := by
  have h := weights0_4
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words4 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 5. -/
theorem weights0_5 : beta0Words5 < 2^(256*1024) ∧
    beta0Words5 &&& ((rep256 1024)*(2^90-1)) = beta0Words5 ∧
    popcount256 (rep256 1024) beta0Words5 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 5 has the exact claimed weight. -/
theorem weight0_5 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words5) = 22 := by
  have h := weights0_5
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words5 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 6. -/
theorem weights0_6 : beta0Words6 < 2^(256*1024) ∧
    beta0Words6 &&& ((rep256 1024)*(2^90-1)) = beta0Words6 ∧
    popcount256 (rep256 1024) beta0Words6 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 6 has the exact claimed weight. -/
theorem weight0_6 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words6) = 22 := by
  have h := weights0_6
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words6 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 7. -/
theorem weights0_7 : beta0Words7 < 2^(256*1024) ∧
    beta0Words7 &&& ((rep256 1024)*(2^90-1)) = beta0Words7 ∧
    popcount256 (rep256 1024) beta0Words7 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 7 has the exact claimed weight. -/
theorem weight0_7 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words7) = 22 := by
  have h := weights0_7
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words7 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 8. -/
theorem weights0_8 : beta0Words8 < 2^(256*1024) ∧
    beta0Words8 &&& ((rep256 1024)*(2^90-1)) = beta0Words8 ∧
    popcount256 (rep256 1024) beta0Words8 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 8 has the exact claimed weight. -/
theorem weight0_8 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words8) = 22 := by
  have h := weights0_8
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words8 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 9. -/
theorem weights0_9 : beta0Words9 < 2^(256*1024) ∧
    beta0Words9 &&& ((rep256 1024)*(2^90-1)) = beta0Words9 ∧
    popcount256 (rep256 1024) beta0Words9 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 9 has the exact claimed weight. -/
theorem weight0_9 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words9) = 22 := by
  have h := weights0_9
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words9 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 10. -/
theorem weights0_10 : beta0Words10 < 2^(256*1024) ∧
    beta0Words10 &&& ((rep256 1024)*(2^90-1)) = beta0Words10 ∧
    popcount256 (rep256 1024) beta0Words10 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 10 has the exact claimed weight. -/
theorem weight0_10 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words10) = 22 := by
  have h := weights0_10
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words10 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 11. -/
theorem weights0_11 : beta0Words11 < 2^(256*1024) ∧
    beta0Words11 &&& ((rep256 1024)*(2^90-1)) = beta0Words11 ∧
    popcount256 (rep256 1024) beta0Words11 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 11 has the exact claimed weight. -/
theorem weight0_11 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words11) = 22 := by
  have h := weights0_11
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words11 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 12. -/
theorem weights0_12 : beta0Words12 < 2^(256*1024) ∧
    beta0Words12 &&& ((rep256 1024)*(2^90-1)) = beta0Words12 ∧
    popcount256 (rep256 1024) beta0Words12 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 12 has the exact claimed weight. -/
theorem weight0_12 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words12) = 22 := by
  have h := weights0_12
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words12 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 13. -/
theorem weights0_13 : beta0Words13 < 2^(256*1024) ∧
    beta0Words13 &&& ((rep256 1024)*(2^90-1)) = beta0Words13 ∧
    popcount256 (rep256 1024) beta0Words13 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 13 has the exact claimed weight. -/
theorem weight0_13 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words13) = 22 := by
  have h := weights0_13
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words13 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 14. -/
theorem weights0_14 : beta0Words14 < 2^(256*1024) ∧
    beta0Words14 &&& ((rep256 1024)*(2^90-1)) = beta0Words14 ∧
    popcount256 (rep256 1024) beta0Words14 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 14 has the exact claimed weight. -/
theorem weight0_14 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words14) = 22 := by
  have h := weights0_14
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words14 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 15. -/
theorem weights0_15 : beta0Words15 < 2^(256*1024) ∧
    beta0Words15 &&& ((rep256 1024)*(2^90-1)) = beta0Words15 ∧
    popcount256 (rep256 1024) beta0Words15 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 15 has the exact claimed weight. -/
theorem weight0_15 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words15) = 22 := by
  have h := weights0_15
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words15 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 16. -/
theorem weights0_16 : beta0Words16 < 2^(256*1024) ∧
    beta0Words16 &&& ((rep256 1024)*(2^90-1)) = beta0Words16 ∧
    popcount256 (rep256 1024) beta0Words16 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 16 has the exact claimed weight. -/
theorem weight0_16 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words16) = 22 := by
  have h := weights0_16
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words16 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 17. -/
theorem weights0_17 : beta0Words17 < 2^(256*1024) ∧
    beta0Words17 &&& ((rep256 1024)*(2^90-1)) = beta0Words17 ∧
    popcount256 (rep256 1024) beta0Words17 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 17 has the exact claimed weight. -/
theorem weight0_17 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words17) = 22 := by
  have h := weights0_17
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words17 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 18. -/
theorem weights0_18 : beta0Words18 < 2^(256*1024) ∧
    beta0Words18 &&& ((rep256 1024)*(2^90-1)) = beta0Words18 ∧
    popcount256 (rep256 1024) beta0Words18 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 18 has the exact claimed weight. -/
theorem weight0_18 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words18) = 22 := by
  have h := weights0_18
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words18 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 19. -/
theorem weights0_19 : beta0Words19 < 2^(256*1024) ∧
    beta0Words19 &&& ((rep256 1024)*(2^90-1)) = beta0Words19 ∧
    popcount256 (rep256 1024) beta0Words19 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 19 has the exact claimed weight. -/
theorem weight0_19 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words19) = 22 := by
  have h := weights0_19
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words19 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 20. -/
theorem weights0_20 : beta0Words20 < 2^(256*1024) ∧
    beta0Words20 &&& ((rep256 1024)*(2^90-1)) = beta0Words20 ∧
    popcount256 (rep256 1024) beta0Words20 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 20 has the exact claimed weight. -/
theorem weight0_20 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words20) = 22 := by
  have h := weights0_20
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words20 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 21. -/
theorem weights0_21 : beta0Words21 < 2^(256*1024) ∧
    beta0Words21 &&& ((rep256 1024)*(2^90-1)) = beta0Words21 ∧
    popcount256 (rep256 1024) beta0Words21 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 21 has the exact claimed weight. -/
theorem weight0_21 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words21) = 22 := by
  have h := weights0_21
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words21 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 22. -/
theorem weights0_22 : beta0Words22 < 2^(256*1024) ∧
    beta0Words22 &&& ((rep256 1024)*(2^90-1)) = beta0Words22 ∧
    popcount256 (rep256 1024) beta0Words22 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 22 has the exact claimed weight. -/
theorem weight0_22 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words22) = 22 := by
  have h := weights0_22
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words22 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 23. -/
theorem weights0_23 : beta0Words23 < 2^(256*1024) ∧
    beta0Words23 &&& ((rep256 1024)*(2^90-1)) = beta0Words23 ∧
    popcount256 (rep256 1024) beta0Words23 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 23 has the exact claimed weight. -/
theorem weight0_23 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words23) = 22 := by
  have h := weights0_23
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words23 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 24. -/
theorem weights0_24 : beta0Words24 < 2^(256*1024) ∧
    beta0Words24 &&& ((rep256 1024)*(2^90-1)) = beta0Words24 ∧
    popcount256 (rep256 1024) beta0Words24 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 24 has the exact claimed weight. -/
theorem weight0_24 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words24) = 22 := by
  have h := weights0_24
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words24 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 25. -/
theorem weights0_25 : beta0Words25 < 2^(256*1024) ∧
    beta0Words25 &&& ((rep256 1024)*(2^90-1)) = beta0Words25 ∧
    popcount256 (rep256 1024) beta0Words25 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 25 has the exact claimed weight. -/
theorem weight0_25 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words25) = 22 := by
  have h := weights0_25
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words25 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 26. -/
theorem weights0_26 : beta0Words26 < 2^(256*1024) ∧
    beta0Words26 &&& ((rep256 1024)*(2^90-1)) = beta0Words26 ∧
    popcount256 (rep256 1024) beta0Words26 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 26 has the exact claimed weight. -/
theorem weight0_26 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words26) = 22 := by
  have h := weights0_26
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words26 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 27. -/
theorem weights0_27 : beta0Words27 < 2^(256*1024) ∧
    beta0Words27 &&& ((rep256 1024)*(2^90-1)) = beta0Words27 ∧
    popcount256 (rep256 1024) beta0Words27 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 27 has the exact claimed weight. -/
theorem weight0_27 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words27) = 22 := by
  have h := weights0_27
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words27 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 28. -/
theorem weights0_28 : beta0Words28 < 2^(256*1024) ∧
    beta0Words28 &&& ((rep256 1024)*(2^90-1)) = beta0Words28 ∧
    popcount256 (rep256 1024) beta0Words28 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 28 has the exact claimed weight. -/
theorem weight0_28 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words28) = 22 := by
  have h := weights0_28
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words28 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 29. -/
theorem weights0_29 : beta0Words29 < 2^(256*1024) ∧
    beta0Words29 &&& ((rep256 1024)*(2^90-1)) = beta0Words29 ∧
    popcount256 (rep256 1024) beta0Words29 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 29 has the exact claimed weight. -/
theorem weight0_29 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words29) = 22 := by
  have h := weights0_29
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words29 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 30. -/
theorem weights0_30 : beta0Words30 < 2^(256*1024) ∧
    beta0Words30 &&& ((rep256 1024)*(2^90-1)) = beta0Words30 ∧
    popcount256 (rep256 1024) beta0Words30 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 30 has the exact claimed weight. -/
theorem weight0_30 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words30) = 22 := by
  have h := weights0_30
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words30 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 31. -/
theorem weights0_31 : beta0Words31 < 2^(256*1024) ∧
    beta0Words31 &&& ((rep256 1024)*(2^90-1)) = beta0Words31 ∧
    popcount256 (rep256 1024) beta0Words31 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 31 has the exact claimed weight. -/
theorem weight0_31 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words31) = 22 := by
  have h := weights0_31
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words31 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 32. -/
theorem weights0_32 : beta0Words32 < 2^(256*1024) ∧
    beta0Words32 &&& ((rep256 1024)*(2^90-1)) = beta0Words32 ∧
    popcount256 (rep256 1024) beta0Words32 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 32 has the exact claimed weight. -/
theorem weight0_32 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words32) = 22 := by
  have h := weights0_32
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words32 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 33. -/
theorem weights0_33 : beta0Words33 < 2^(256*1024) ∧
    beta0Words33 &&& ((rep256 1024)*(2^90-1)) = beta0Words33 ∧
    popcount256 (rep256 1024) beta0Words33 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 33 has the exact claimed weight. -/
theorem weight0_33 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words33) = 22 := by
  have h := weights0_33
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words33 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 34. -/
theorem weights0_34 : beta0Words34 < 2^(256*1024) ∧
    beta0Words34 &&& ((rep256 1024)*(2^90-1)) = beta0Words34 ∧
    popcount256 (rep256 1024) beta0Words34 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 34 has the exact claimed weight. -/
theorem weight0_34 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words34) = 22 := by
  have h := weights0_34
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words34 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 35. -/
theorem weights0_35 : beta0Words35 < 2^(256*1024) ∧
    beta0Words35 &&& ((rep256 1024)*(2^90-1)) = beta0Words35 ∧
    popcount256 (rep256 1024) beta0Words35 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 35 has the exact claimed weight. -/
theorem weight0_35 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words35) = 22 := by
  have h := weights0_35
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words35 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 36. -/
theorem weights0_36 : beta0Words36 < 2^(256*1024) ∧
    beta0Words36 &&& ((rep256 1024)*(2^90-1)) = beta0Words36 ∧
    popcount256 (rep256 1024) beta0Words36 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 36 has the exact claimed weight. -/
theorem weight0_36 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words36) = 22 := by
  have h := weights0_36
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words36 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 37. -/
theorem weights0_37 : beta0Words37 < 2^(256*1024) ∧
    beta0Words37 &&& ((rep256 1024)*(2^90-1)) = beta0Words37 ∧
    popcount256 (rep256 1024) beta0Words37 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 37 has the exact claimed weight. -/
theorem weight0_37 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words37) = 22 := by
  have h := weights0_37
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words37 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 38. -/
theorem weights0_38 : beta0Words38 < 2^(256*1024) ∧
    beta0Words38 &&& ((rep256 1024)*(2^90-1)) = beta0Words38 ∧
    popcount256 (rep256 1024) beta0Words38 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 38 has the exact claimed weight. -/
theorem weight0_38 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words38) = 22 := by
  have h := weights0_38
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words38 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 39. -/
theorem weights0_39 : beta0Words39 < 2^(256*1024) ∧
    beta0Words39 &&& ((rep256 1024)*(2^90-1)) = beta0Words39 ∧
    popcount256 (rep256 1024) beta0Words39 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 39 has the exact claimed weight. -/
theorem weight0_39 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words39) = 22 := by
  have h := weights0_39
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words39 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 40. -/
theorem weights0_40 : beta0Words40 < 2^(256*1024) ∧
    beta0Words40 &&& ((rep256 1024)*(2^90-1)) = beta0Words40 ∧
    popcount256 (rep256 1024) beta0Words40 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 40 has the exact claimed weight. -/
theorem weight0_40 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words40) = 22 := by
  have h := weights0_40
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words40 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 41. -/
theorem weights0_41 : beta0Words41 < 2^(256*1024) ∧
    beta0Words41 &&& ((rep256 1024)*(2^90-1)) = beta0Words41 ∧
    popcount256 (rep256 1024) beta0Words41 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 41 has the exact claimed weight. -/
theorem weight0_41 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words41) = 22 := by
  have h := weights0_41
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words41 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 42. -/
theorem weights0_42 : beta0Words42 < 2^(256*1024) ∧
    beta0Words42 &&& ((rep256 1024)*(2^90-1)) = beta0Words42 ∧
    popcount256 (rep256 1024) beta0Words42 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 42 has the exact claimed weight. -/
theorem weight0_42 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words42) = 22 := by
  have h := weights0_42
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words42 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 43. -/
theorem weights0_43 : beta0Words43 < 2^(256*1024) ∧
    beta0Words43 &&& ((rep256 1024)*(2^90-1)) = beta0Words43 ∧
    popcount256 (rep256 1024) beta0Words43 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 43 has the exact claimed weight. -/
theorem weight0_43 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words43) = 22 := by
  have h := weights0_43
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words43 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 44. -/
theorem weights0_44 : beta0Words44 < 2^(256*1024) ∧
    beta0Words44 &&& ((rep256 1024)*(2^90-1)) = beta0Words44 ∧
    popcount256 (rep256 1024) beta0Words44 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 44 has the exact claimed weight. -/
theorem weight0_44 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words44) = 22 := by
  have h := weights0_44
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words44 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 45. -/
theorem weights0_45 : beta0Words45 < 2^(256*1024) ∧
    beta0Words45 &&& ((rep256 1024)*(2^90-1)) = beta0Words45 ∧
    popcount256 (rep256 1024) beta0Words45 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 45 has the exact claimed weight. -/
theorem weight0_45 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words45) = 22 := by
  have h := weights0_45
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words45 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 46. -/
theorem weights0_46 : beta0Words46 < 2^(256*1024) ∧
    beta0Words46 &&& ((rep256 1024)*(2^90-1)) = beta0Words46 ∧
    popcount256 (rep256 1024) beta0Words46 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 46 has the exact claimed weight. -/
theorem weight0_46 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words46) = 22 := by
  have h := weights0_46
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words46 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 47. -/
theorem weights0_47 : beta0Words47 < 2^(256*1024) ∧
    beta0Words47 &&& ((rep256 1024)*(2^90-1)) = beta0Words47 ∧
    popcount256 (rep256 1024) beta0Words47 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 47 has the exact claimed weight. -/
theorem weight0_47 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words47) = 22 := by
  have h := weights0_47
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words47 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 48. -/
theorem weights0_48 : beta0Words48 < 2^(256*1024) ∧
    beta0Words48 &&& ((rep256 1024)*(2^90-1)) = beta0Words48 ∧
    popcount256 (rep256 1024) beta0Words48 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 48 has the exact claimed weight. -/
theorem weight0_48 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words48) = 22 := by
  have h := weights0_48
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words48 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 49. -/
theorem weights0_49 : beta0Words49 < 2^(256*1024) ∧
    beta0Words49 &&& ((rep256 1024)*(2^90-1)) = beta0Words49 ∧
    popcount256 (rep256 1024) beta0Words49 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 49 has the exact claimed weight. -/
theorem weight0_49 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words49) = 22 := by
  have h := weights0_49
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words49 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 50. -/
theorem weights0_50 : beta0Words50 < 2^(256*1024) ∧
    beta0Words50 &&& ((rep256 1024)*(2^90-1)) = beta0Words50 ∧
    popcount256 (rep256 1024) beta0Words50 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 50 has the exact claimed weight. -/
theorem weight0_50 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words50) = 22 := by
  have h := weights0_50
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words50 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 51. -/
theorem weights0_51 : beta0Words51 < 2^(256*1024) ∧
    beta0Words51 &&& ((rep256 1024)*(2^90-1)) = beta0Words51 ∧
    popcount256 (rep256 1024) beta0Words51 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 51 has the exact claimed weight. -/
theorem weight0_51 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words51) = 22 := by
  have h := weights0_51
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words51 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 52. -/
theorem weights0_52 : beta0Words52 < 2^(256*1024) ∧
    beta0Words52 &&& ((rep256 1024)*(2^90-1)) = beta0Words52 ∧
    popcount256 (rep256 1024) beta0Words52 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 52 has the exact claimed weight. -/
theorem weight0_52 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words52) = 22 := by
  have h := weights0_52
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words52 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 53. -/
theorem weights0_53 : beta0Words53 < 2^(256*1024) ∧
    beta0Words53 &&& ((rep256 1024)*(2^90-1)) = beta0Words53 ∧
    popcount256 (rep256 1024) beta0Words53 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 53 has the exact claimed weight. -/
theorem weight0_53 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words53) = 22 := by
  have h := weights0_53
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words53 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 54. -/
theorem weights0_54 : beta0Words54 < 2^(256*1024) ∧
    beta0Words54 &&& ((rep256 1024)*(2^90-1)) = beta0Words54 ∧
    popcount256 (rep256 1024) beta0Words54 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 54 has the exact claimed weight. -/
theorem weight0_54 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words54) = 22 := by
  have h := weights0_54
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words54 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 55. -/
theorem weights0_55 : beta0Words55 < 2^(256*1024) ∧
    beta0Words55 &&& ((rep256 1024)*(2^90-1)) = beta0Words55 ∧
    popcount256 (rep256 1024) beta0Words55 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 55 has the exact claimed weight. -/
theorem weight0_55 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words55) = 22 := by
  have h := weights0_55
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words55 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 56. -/
theorem weights0_56 : beta0Words56 < 2^(256*1024) ∧
    beta0Words56 &&& ((rep256 1024)*(2^90-1)) = beta0Words56 ∧
    popcount256 (rep256 1024) beta0Words56 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 56 has the exact claimed weight. -/
theorem weight0_56 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words56) = 22 := by
  have h := weights0_56
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words56 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 57. -/
theorem weights0_57 : beta0Words57 < 2^(256*1024) ∧
    beta0Words57 &&& ((rep256 1024)*(2^90-1)) = beta0Words57 ∧
    popcount256 (rep256 1024) beta0Words57 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 57 has the exact claimed weight. -/
theorem weight0_57 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words57) = 22 := by
  have h := weights0_57
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words57 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 58. -/
theorem weights0_58 : beta0Words58 < 2^(256*1024) ∧
    beta0Words58 &&& ((rep256 1024)*(2^90-1)) = beta0Words58 ∧
    popcount256 (rep256 1024) beta0Words58 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 58 has the exact claimed weight. -/
theorem weight0_58 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words58) = 22 := by
  have h := weights0_58
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words58 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 59. -/
theorem weights0_59 : beta0Words59 < 2^(256*1024) ∧
    beta0Words59 &&& ((rep256 1024)*(2^90-1)) = beta0Words59 ∧
    popcount256 (rep256 1024) beta0Words59 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 59 has the exact claimed weight. -/
theorem weight0_59 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words59) = 22 := by
  have h := weights0_59
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words59 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 60. -/
theorem weights0_60 : beta0Words60 < 2^(256*1024) ∧
    beta0Words60 &&& ((rep256 1024)*(2^90-1)) = beta0Words60 ∧
    popcount256 (rep256 1024) beta0Words60 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 60 has the exact claimed weight. -/
theorem weight0_60 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words60) = 22 := by
  have h := weights0_60
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words60 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 61. -/
theorem weights0_61 : beta0Words61 < 2^(256*1024) ∧
    beta0Words61 &&& ((rep256 1024)*(2^90-1)) = beta0Words61 ∧
    popcount256 (rep256 1024) beta0Words61 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 61 has the exact claimed weight. -/
theorem weight0_61 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words61) = 22 := by
  have h := weights0_61
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words61 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 62. -/
theorem weights0_62 : beta0Words62 < 2^(256*1024) ∧
    beta0Words62 &&& ((rep256 1024)*(2^90-1)) = beta0Words62 ∧
    popcount256 (rep256 1024) beta0Words62 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 62 has the exact claimed weight. -/
theorem weight0_62 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words62) = 22 := by
  have h := weights0_62
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words62 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 63. -/
theorem weights0_63 : beta0Words63 < 2^(256*1024) ∧
    beta0Words63 &&& ((rep256 1024)*(2^90-1)) = beta0Words63 ∧
    popcount256 (rep256 1024) beta0Words63 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 63 has the exact claimed weight. -/
theorem weight0_63 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words63) = 22 := by
  have h := weights0_63
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words63 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 64. -/
theorem weights0_64 : beta0Words64 < 2^(256*1024) ∧
    beta0Words64 &&& ((rep256 1024)*(2^90-1)) = beta0Words64 ∧
    popcount256 (rep256 1024) beta0Words64 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 64 has the exact claimed weight. -/
theorem weight0_64 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words64) = 22 := by
  have h := weights0_64
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words64 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 65. -/
theorem weights0_65 : beta0Words65 < 2^(256*1024) ∧
    beta0Words65 &&& ((rep256 1024)*(2^90-1)) = beta0Words65 ∧
    popcount256 (rep256 1024) beta0Words65 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 65 has the exact claimed weight. -/
theorem weight0_65 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words65) = 22 := by
  have h := weights0_65
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words65 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 66. -/
theorem weights0_66 : beta0Words66 < 2^(256*1024) ∧
    beta0Words66 &&& ((rep256 1024)*(2^90-1)) = beta0Words66 ∧
    popcount256 (rep256 1024) beta0Words66 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 66 has the exact claimed weight. -/
theorem weight0_66 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words66) = 22 := by
  have h := weights0_66
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words66 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 67. -/
theorem weights0_67 : beta0Words67 < 2^(256*1024) ∧
    beta0Words67 &&& ((rep256 1024)*(2^90-1)) = beta0Words67 ∧
    popcount256 (rep256 1024) beta0Words67 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 67 has the exact claimed weight. -/
theorem weight0_67 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words67) = 22 := by
  have h := weights0_67
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words67 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 68. -/
theorem weights0_68 : beta0Words68 < 2^(256*1024) ∧
    beta0Words68 &&& ((rep256 1024)*(2^90-1)) = beta0Words68 ∧
    popcount256 (rep256 1024) beta0Words68 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 68 has the exact claimed weight. -/
theorem weight0_68 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words68) = 22 := by
  have h := weights0_68
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words68 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 69. -/
theorem weights0_69 : beta0Words69 < 2^(256*1024) ∧
    beta0Words69 &&& ((rep256 1024)*(2^90-1)) = beta0Words69 ∧
    popcount256 (rep256 1024) beta0Words69 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 69 has the exact claimed weight. -/
theorem weight0_69 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words69) = 22 := by
  have h := weights0_69
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words69 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 70. -/
theorem weights0_70 : beta0Words70 < 2^(256*1024) ∧
    beta0Words70 &&& ((rep256 1024)*(2^90-1)) = beta0Words70 ∧
    popcount256 (rep256 1024) beta0Words70 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 70 has the exact claimed weight. -/
theorem weight0_70 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words70) = 22 := by
  have h := weights0_70
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words70 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 71. -/
theorem weights0_71 : beta0Words71 < 2^(256*1024) ∧
    beta0Words71 &&& ((rep256 1024)*(2^90-1)) = beta0Words71 ∧
    popcount256 (rep256 1024) beta0Words71 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 71 has the exact claimed weight. -/
theorem weight0_71 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words71) = 22 := by
  have h := weights0_71
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words71 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 72. -/
theorem weights0_72 : beta0Words72 < 2^(256*1024) ∧
    beta0Words72 &&& ((rep256 1024)*(2^90-1)) = beta0Words72 ∧
    popcount256 (rep256 1024) beta0Words72 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 72 has the exact claimed weight. -/
theorem weight0_72 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words72) = 22 := by
  have h := weights0_72
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words72 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 73. -/
theorem weights0_73 : beta0Words73 < 2^(256*1024) ∧
    beta0Words73 &&& ((rep256 1024)*(2^90-1)) = beta0Words73 ∧
    popcount256 (rep256 1024) beta0Words73 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 73 has the exact claimed weight. -/
theorem weight0_73 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words73) = 22 := by
  have h := weights0_73
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words73 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 74. -/
theorem weights0_74 : beta0Words74 < 2^(256*1024) ∧
    beta0Words74 &&& ((rep256 1024)*(2^90-1)) = beta0Words74 ∧
    popcount256 (rep256 1024) beta0Words74 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 74 has the exact claimed weight. -/
theorem weight0_74 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words74) = 22 := by
  have h := weights0_74
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words74 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 75. -/
theorem weights0_75 : beta0Words75 < 2^(256*1024) ∧
    beta0Words75 &&& ((rep256 1024)*(2^90-1)) = beta0Words75 ∧
    popcount256 (rep256 1024) beta0Words75 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 75 has the exact claimed weight. -/
theorem weight0_75 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words75) = 22 := by
  have h := weights0_75
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words75 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 76. -/
theorem weights0_76 : beta0Words76 < 2^(256*1024) ∧
    beta0Words76 &&& ((rep256 1024)*(2^90-1)) = beta0Words76 ∧
    popcount256 (rep256 1024) beta0Words76 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 76 has the exact claimed weight. -/
theorem weight0_76 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words76) = 22 := by
  have h := weights0_76
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words76 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 77. -/
theorem weights0_77 : beta0Words77 < 2^(256*1024) ∧
    beta0Words77 &&& ((rep256 1024)*(2^90-1)) = beta0Words77 ∧
    popcount256 (rep256 1024) beta0Words77 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 77 has the exact claimed weight. -/
theorem weight0_77 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words77) = 22 := by
  have h := weights0_77
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words77 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 78. -/
theorem weights0_78 : beta0Words78 < 2^(256*1024) ∧
    beta0Words78 &&& ((rep256 1024)*(2^90-1)) = beta0Words78 ∧
    popcount256 (rep256 1024) beta0Words78 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 78 has the exact claimed weight. -/
theorem weight0_78 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words78) = 22 := by
  have h := weights0_78
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words78 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 79. -/
theorem weights0_79 : beta0Words79 < 2^(256*1024) ∧
    beta0Words79 &&& ((rep256 1024)*(2^90-1)) = beta0Words79 ∧
    popcount256 (rep256 1024) beta0Words79 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 79 has the exact claimed weight. -/
theorem weight0_79 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words79) = 22 := by
  have h := weights0_79
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words79 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 80. -/
theorem weights0_80 : beta0Words80 < 2^(256*1024) ∧
    beta0Words80 &&& ((rep256 1024)*(2^90-1)) = beta0Words80 ∧
    popcount256 (rep256 1024) beta0Words80 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 80 has the exact claimed weight. -/
theorem weight0_80 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words80) = 22 := by
  have h := weights0_80
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words80 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 81. -/
theorem weights0_81 : beta0Words81 < 2^(256*1024) ∧
    beta0Words81 &&& ((rep256 1024)*(2^90-1)) = beta0Words81 ∧
    popcount256 (rep256 1024) beta0Words81 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 81 has the exact claimed weight. -/
theorem weight0_81 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words81) = 22 := by
  have h := weights0_81
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words81 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 82. -/
theorem weights0_82 : beta0Words82 < 2^(256*1024) ∧
    beta0Words82 &&& ((rep256 1024)*(2^90-1)) = beta0Words82 ∧
    popcount256 (rep256 1024) beta0Words82 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 82 has the exact claimed weight. -/
theorem weight0_82 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words82) = 22 := by
  have h := weights0_82
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words82 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 83. -/
theorem weights0_83 : beta0Words83 < 2^(256*1024) ∧
    beta0Words83 &&& ((rep256 1024)*(2^90-1)) = beta0Words83 ∧
    popcount256 (rep256 1024) beta0Words83 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 83 has the exact claimed weight. -/
theorem weight0_83 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words83) = 22 := by
  have h := weights0_83
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words83 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 84. -/
theorem weights0_84 : beta0Words84 < 2^(256*1024) ∧
    beta0Words84 &&& ((rep256 1024)*(2^90-1)) = beta0Words84 ∧
    popcount256 (rep256 1024) beta0Words84 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 84 has the exact claimed weight. -/
theorem weight0_84 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words84) = 22 := by
  have h := weights0_84
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words84 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 85. -/
theorem weights0_85 : beta0Words85 < 2^(256*1024) ∧
    beta0Words85 &&& ((rep256 1024)*(2^90-1)) = beta0Words85 ∧
    popcount256 (rep256 1024) beta0Words85 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 85 has the exact claimed weight. -/
theorem weight0_85 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words85) = 22 := by
  have h := weights0_85
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words85 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 86. -/
theorem weights0_86 : beta0Words86 < 2^(256*1024) ∧
    beta0Words86 &&& ((rep256 1024)*(2^90-1)) = beta0Words86 ∧
    popcount256 (rep256 1024) beta0Words86 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 86 has the exact claimed weight. -/
theorem weight0_86 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words86) = 22 := by
  have h := weights0_86
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words86 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 87. -/
theorem weights0_87 : beta0Words87 < 2^(256*1024) ∧
    beta0Words87 &&& ((rep256 1024)*(2^90-1)) = beta0Words87 ∧
    popcount256 (rep256 1024) beta0Words87 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 87 has the exact claimed weight. -/
theorem weight0_87 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words87) = 22 := by
  have h := weights0_87
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words87 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 88. -/
theorem weights0_88 : beta0Words88 < 2^(256*1024) ∧
    beta0Words88 &&& ((rep256 1024)*(2^90-1)) = beta0Words88 ∧
    popcount256 (rep256 1024) beta0Words88 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 88 has the exact claimed weight. -/
theorem weight0_88 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words88) = 22 := by
  have h := weights0_88
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words88 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 89. -/
theorem weights0_89 : beta0Words89 < 2^(256*1024) ∧
    beta0Words89 &&& ((rep256 1024)*(2^90-1)) = beta0Words89 ∧
    popcount256 (rep256 1024) beta0Words89 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 89 has the exact claimed weight. -/
theorem weight0_89 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words89) = 22 := by
  have h := weights0_89
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words89 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 90. -/
theorem weights0_90 : beta0Words90 < 2^(256*1024) ∧
    beta0Words90 &&& ((rep256 1024)*(2^90-1)) = beta0Words90 ∧
    popcount256 (rep256 1024) beta0Words90 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 90 has the exact claimed weight. -/
theorem weight0_90 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words90) = 22 := by
  have h := weights0_90
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words90 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 91. -/
theorem weights0_91 : beta0Words91 < 2^(256*1024) ∧
    beta0Words91 &&& ((rep256 1024)*(2^90-1)) = beta0Words91 ∧
    popcount256 (rep256 1024) beta0Words91 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 91 has the exact claimed weight. -/
theorem weight0_91 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words91) = 22 := by
  have h := weights0_91
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words91 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 92. -/
theorem weights0_92 : beta0Words92 < 2^(256*1024) ∧
    beta0Words92 &&& ((rep256 1024)*(2^90-1)) = beta0Words92 ∧
    popcount256 (rep256 1024) beta0Words92 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 92 has the exact claimed weight. -/
theorem weight0_92 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words92) = 22 := by
  have h := weights0_92
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words92 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 93. -/
theorem weights0_93 : beta0Words93 < 2^(256*1024) ∧
    beta0Words93 &&& ((rep256 1024)*(2^90-1)) = beta0Words93 ∧
    popcount256 (rep256 1024) beta0Words93 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 93 has the exact claimed weight. -/
theorem weight0_93 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words93) = 22 := by
  have h := weights0_93
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words93 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 94. -/
theorem weights0_94 : beta0Words94 < 2^(256*1024) ∧
    beta0Words94 &&& ((rep256 1024)*(2^90-1)) = beta0Words94 ∧
    popcount256 (rep256 1024) beta0Words94 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 94 has the exact claimed weight. -/
theorem weight0_94 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words94) = 22 := by
  have h := weights0_94
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words94 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 95. -/
theorem weights0_95 : beta0Words95 < 2^(256*1024) ∧
    beta0Words95 &&& ((rep256 1024)*(2^90-1)) = beta0Words95 ∧
    popcount256 (rep256 1024) beta0Words95 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 95 has the exact claimed weight. -/
theorem weight0_95 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words95) = 22 := by
  have h := weights0_95
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words95 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 96. -/
theorem weights0_96 : beta0Words96 < 2^(256*1024) ∧
    beta0Words96 &&& ((rep256 1024)*(2^90-1)) = beta0Words96 ∧
    popcount256 (rep256 1024) beta0Words96 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 96 has the exact claimed weight. -/
theorem weight0_96 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words96) = 22 := by
  have h := weights0_96
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words96 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 97. -/
theorem weights0_97 : beta0Words97 < 2^(256*1024) ∧
    beta0Words97 &&& ((rep256 1024)*(2^90-1)) = beta0Words97 ∧
    popcount256 (rep256 1024) beta0Words97 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 97 has the exact claimed weight. -/
theorem weight0_97 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words97) = 22 := by
  have h := weights0_97
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words97 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 98. -/
theorem weights0_98 : beta0Words98 < 2^(256*1024) ∧
    beta0Words98 &&& ((rep256 1024)*(2^90-1)) = beta0Words98 ∧
    popcount256 (rep256 1024) beta0Words98 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 98 has the exact claimed weight. -/
theorem weight0_98 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words98) = 22 := by
  have h := weights0_98
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words98 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 99. -/
theorem weights0_99 : beta0Words99 < 2^(256*1024) ∧
    beta0Words99 &&& ((rep256 1024)*(2^90-1)) = beta0Words99 ∧
    popcount256 (rep256 1024) beta0Words99 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 99 has the exact claimed weight. -/
theorem weight0_99 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words99) = 22 := by
  have h := weights0_99
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words99 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 100. -/
theorem weights0_100 : beta0Words100 < 2^(256*1024) ∧
    beta0Words100 &&& ((rep256 1024)*(2^90-1)) = beta0Words100 ∧
    popcount256 (rep256 1024) beta0Words100 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 100 has the exact claimed weight. -/
theorem weight0_100 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words100) = 22 := by
  have h := weights0_100
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words100 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 101. -/
theorem weights0_101 : beta0Words101 < 2^(256*1024) ∧
    beta0Words101 &&& ((rep256 1024)*(2^90-1)) = beta0Words101 ∧
    popcount256 (rep256 1024) beta0Words101 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 101 has the exact claimed weight. -/
theorem weight0_101 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words101) = 22 := by
  have h := weights0_101
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words101 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 102. -/
theorem weights0_102 : beta0Words102 < 2^(256*1024) ∧
    beta0Words102 &&& ((rep256 1024)*(2^90-1)) = beta0Words102 ∧
    popcount256 (rep256 1024) beta0Words102 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 102 has the exact claimed weight. -/
theorem weight0_102 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words102) = 22 := by
  have h := weights0_102
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words102 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 103. -/
theorem weights0_103 : beta0Words103 < 2^(256*1024) ∧
    beta0Words103 &&& ((rep256 1024)*(2^90-1)) = beta0Words103 ∧
    popcount256 (rep256 1024) beta0Words103 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 103 has the exact claimed weight. -/
theorem weight0_103 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words103) = 22 := by
  have h := weights0_103
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words103 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 104. -/
theorem weights0_104 : beta0Words104 < 2^(256*1024) ∧
    beta0Words104 &&& ((rep256 1024)*(2^90-1)) = beta0Words104 ∧
    popcount256 (rep256 1024) beta0Words104 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 104 has the exact claimed weight. -/
theorem weight0_104 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words104) = 22 := by
  have h := weights0_104
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words104 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 105. -/
theorem weights0_105 : beta0Words105 < 2^(256*1024) ∧
    beta0Words105 &&& ((rep256 1024)*(2^90-1)) = beta0Words105 ∧
    popcount256 (rep256 1024) beta0Words105 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 105 has the exact claimed weight. -/
theorem weight0_105 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words105) = 22 := by
  have h := weights0_105
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words105 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 106. -/
theorem weights0_106 : beta0Words106 < 2^(256*1024) ∧
    beta0Words106 &&& ((rep256 1024)*(2^90-1)) = beta0Words106 ∧
    popcount256 (rep256 1024) beta0Words106 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 106 has the exact claimed weight. -/
theorem weight0_106 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words106) = 22 := by
  have h := weights0_106
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words106 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 107. -/
theorem weights0_107 : beta0Words107 < 2^(256*1024) ∧
    beta0Words107 &&& ((rep256 1024)*(2^90-1)) = beta0Words107 ∧
    popcount256 (rep256 1024) beta0Words107 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 107 has the exact claimed weight. -/
theorem weight0_107 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words107) = 22 := by
  have h := weights0_107
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words107 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 108. -/
theorem weights0_108 : beta0Words108 < 2^(256*1024) ∧
    beta0Words108 &&& ((rep256 1024)*(2^90-1)) = beta0Words108 ∧
    popcount256 (rep256 1024) beta0Words108 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 108 has the exact claimed weight. -/
theorem weight0_108 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words108) = 22 := by
  have h := weights0_108
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words108 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 109. -/
theorem weights0_109 : beta0Words109 < 2^(256*1024) ∧
    beta0Words109 &&& ((rep256 1024)*(2^90-1)) = beta0Words109 ∧
    popcount256 (rep256 1024) beta0Words109 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 109 has the exact claimed weight. -/
theorem weight0_109 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words109) = 22 := by
  have h := weights0_109
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words109 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 110. -/
theorem weights0_110 : beta0Words110 < 2^(256*1024) ∧
    beta0Words110 &&& ((rep256 1024)*(2^90-1)) = beta0Words110 ∧
    popcount256 (rep256 1024) beta0Words110 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 110 has the exact claimed weight. -/
theorem weight0_110 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words110) = 22 := by
  have h := weights0_110
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words110 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 111. -/
theorem weights0_111 : beta0Words111 < 2^(256*1024) ∧
    beta0Words111 &&& ((rep256 1024)*(2^90-1)) = beta0Words111 ∧
    popcount256 (rep256 1024) beta0Words111 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 111 has the exact claimed weight. -/
theorem weight0_111 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words111) = 22 := by
  have h := weights0_111
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words111 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 112. -/
theorem weights0_112 : beta0Words112 < 2^(256*1024) ∧
    beta0Words112 &&& ((rep256 1024)*(2^90-1)) = beta0Words112 ∧
    popcount256 (rep256 1024) beta0Words112 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 112 has the exact claimed weight. -/
theorem weight0_112 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words112) = 22 := by
  have h := weights0_112
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words112 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 113. -/
theorem weights0_113 : beta0Words113 < 2^(256*1024) ∧
    beta0Words113 &&& ((rep256 1024)*(2^90-1)) = beta0Words113 ∧
    popcount256 (rep256 1024) beta0Words113 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 113 has the exact claimed weight. -/
theorem weight0_113 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words113) = 22 := by
  have h := weights0_113
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words113 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 114. -/
theorem weights0_114 : beta0Words114 < 2^(256*1024) ∧
    beta0Words114 &&& ((rep256 1024)*(2^90-1)) = beta0Words114 ∧
    popcount256 (rep256 1024) beta0Words114 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 114 has the exact claimed weight. -/
theorem weight0_114 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words114) = 22 := by
  have h := weights0_114
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words114 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 115. -/
theorem weights0_115 : beta0Words115 < 2^(256*1024) ∧
    beta0Words115 &&& ((rep256 1024)*(2^90-1)) = beta0Words115 ∧
    popcount256 (rep256 1024) beta0Words115 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 115 has the exact claimed weight. -/
theorem weight0_115 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words115) = 22 := by
  have h := weights0_115
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words115 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 116. -/
theorem weights0_116 : beta0Words116 < 2^(256*1024) ∧
    beta0Words116 &&& ((rep256 1024)*(2^90-1)) = beta0Words116 ∧
    popcount256 (rep256 1024) beta0Words116 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 116 has the exact claimed weight. -/
theorem weight0_116 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words116) = 22 := by
  have h := weights0_116
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words116 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 117. -/
theorem weights0_117 : beta0Words117 < 2^(256*1024) ∧
    beta0Words117 &&& ((rep256 1024)*(2^90-1)) = beta0Words117 ∧
    popcount256 (rep256 1024) beta0Words117 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 117 has the exact claimed weight. -/
theorem weight0_117 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words117) = 22 := by
  have h := weights0_117
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words117 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 118. -/
theorem weights0_118 : beta0Words118 < 2^(256*1024) ∧
    beta0Words118 &&& ((rep256 1024)*(2^90-1)) = beta0Words118 ∧
    popcount256 (rep256 1024) beta0Words118 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 118 has the exact claimed weight. -/
theorem weight0_118 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words118) = 22 := by
  have h := weights0_118
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words118 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 119. -/
theorem weights0_119 : beta0Words119 < 2^(256*1024) ∧
    beta0Words119 &&& ((rep256 1024)*(2^90-1)) = beta0Words119 ∧
    popcount256 (rep256 1024) beta0Words119 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 119 has the exact claimed weight. -/
theorem weight0_119 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words119) = 22 := by
  have h := weights0_119
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words119 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 120. -/
theorem weights0_120 : beta0Words120 < 2^(256*1024) ∧
    beta0Words120 &&& ((rep256 1024)*(2^90-1)) = beta0Words120 ∧
    popcount256 (rep256 1024) beta0Words120 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 120 has the exact claimed weight. -/
theorem weight0_120 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words120) = 22 := by
  have h := weights0_120
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words120 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 121. -/
theorem weights0_121 : beta0Words121 < 2^(256*1024) ∧
    beta0Words121 &&& ((rep256 1024)*(2^90-1)) = beta0Words121 ∧
    popcount256 (rep256 1024) beta0Words121 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 121 has the exact claimed weight. -/
theorem weight0_121 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words121) = 22 := by
  have h := weights0_121
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words121 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 122. -/
theorem weights0_122 : beta0Words122 < 2^(256*1024) ∧
    beta0Words122 &&& ((rep256 1024)*(2^90-1)) = beta0Words122 ∧
    popcount256 (rep256 1024) beta0Words122 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 122 has the exact claimed weight. -/
theorem weight0_122 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words122) = 22 := by
  have h := weights0_122
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words122 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 123. -/
theorem weights0_123 : beta0Words123 < 2^(256*1024) ∧
    beta0Words123 &&& ((rep256 1024)*(2^90-1)) = beta0Words123 ∧
    popcount256 (rep256 1024) beta0Words123 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 123 has the exact claimed weight. -/
theorem weight0_123 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words123) = 22 := by
  have h := weights0_123
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words123 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 124. -/
theorem weights0_124 : beta0Words124 < 2^(256*1024) ∧
    beta0Words124 &&& ((rep256 1024)*(2^90-1)) = beta0Words124 ∧
    popcount256 (rep256 1024) beta0Words124 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 124 has the exact claimed weight. -/
theorem weight0_124 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words124) = 22 := by
  have h := weights0_124
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words124 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 125. -/
theorem weights0_125 : beta0Words125 < 2^(256*1024) ∧
    beta0Words125 &&& ((rep256 1024)*(2^90-1)) = beta0Words125 ∧
    popcount256 (rep256 1024) beta0Words125 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 125 has the exact claimed weight. -/
theorem weight0_125 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words125) = 22 := by
  have h := weights0_125
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words125 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 126. -/
theorem weights0_126 : beta0Words126 < 2^(256*1024) ∧
    beta0Words126 &&& ((rep256 1024)*(2^90-1)) = beta0Words126 ∧
    popcount256 (rep256 1024) beta0Words126 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 126 has the exact claimed weight. -/
theorem weight0_126 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words126) = 22 := by
  have h := weights0_126
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words126 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 127. -/
theorem weights0_127 : beta0Words127 < 2^(256*1024) ∧
    beta0Words127 &&& ((rep256 1024)*(2^90-1)) = beta0Words127 ∧
    popcount256 (rep256 1024) beta0Words127 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 127 has the exact claimed weight. -/
theorem weight0_127 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words127) = 22 := by
  have h := weights0_127
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words127 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 128. -/
theorem weights0_128 : beta0Words128 < 2^(256*1024) ∧
    beta0Words128 &&& ((rep256 1024)*(2^90-1)) = beta0Words128 ∧
    popcount256 (rep256 1024) beta0Words128 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 128 has the exact claimed weight. -/
theorem weight0_128 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words128) = 22 := by
  have h := weights0_128
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words128 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 129. -/
theorem weights0_129 : beta0Words129 < 2^(256*1024) ∧
    beta0Words129 &&& ((rep256 1024)*(2^90-1)) = beta0Words129 ∧
    popcount256 (rep256 1024) beta0Words129 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 129 has the exact claimed weight. -/
theorem weight0_129 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words129) = 22 := by
  have h := weights0_129
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words129 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 130. -/
theorem weights0_130 : beta0Words130 < 2^(256*1024) ∧
    beta0Words130 &&& ((rep256 1024)*(2^90-1)) = beta0Words130 ∧
    popcount256 (rep256 1024) beta0Words130 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 130 has the exact claimed weight. -/
theorem weight0_130 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words130) = 22 := by
  have h := weights0_130
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words130 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 131. -/
theorem weights0_131 : beta0Words131 < 2^(256*1024) ∧
    beta0Words131 &&& ((rep256 1024)*(2^90-1)) = beta0Words131 ∧
    popcount256 (rep256 1024) beta0Words131 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 131 has the exact claimed weight. -/
theorem weight0_131 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words131) = 22 := by
  have h := weights0_131
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words131 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 132. -/
theorem weights0_132 : beta0Words132 < 2^(256*1024) ∧
    beta0Words132 &&& ((rep256 1024)*(2^90-1)) = beta0Words132 ∧
    popcount256 (rep256 1024) beta0Words132 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 132 has the exact claimed weight. -/
theorem weight0_132 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words132) = 22 := by
  have h := weights0_132
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words132 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 133. -/
theorem weights0_133 : beta0Words133 < 2^(256*1024) ∧
    beta0Words133 &&& ((rep256 1024)*(2^90-1)) = beta0Words133 ∧
    popcount256 (rep256 1024) beta0Words133 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 133 has the exact claimed weight. -/
theorem weight0_133 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words133) = 22 := by
  have h := weights0_133
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words133 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 134. -/
theorem weights0_134 : beta0Words134 < 2^(256*1024) ∧
    beta0Words134 &&& ((rep256 1024)*(2^90-1)) = beta0Words134 ∧
    popcount256 (rep256 1024) beta0Words134 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 134 has the exact claimed weight. -/
theorem weight0_134 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words134) = 22 := by
  have h := weights0_134
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words134 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 135. -/
theorem weights0_135 : beta0Words135 < 2^(256*1024) ∧
    beta0Words135 &&& ((rep256 1024)*(2^90-1)) = beta0Words135 ∧
    popcount256 (rep256 1024) beta0Words135 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 135 has the exact claimed weight. -/
theorem weight0_135 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words135) = 22 := by
  have h := weights0_135
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words135 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 136. -/
theorem weights0_136 : beta0Words136 < 2^(256*1024) ∧
    beta0Words136 &&& ((rep256 1024)*(2^90-1)) = beta0Words136 ∧
    popcount256 (rep256 1024) beta0Words136 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 136 has the exact claimed weight. -/
theorem weight0_136 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words136) = 22 := by
  have h := weights0_136
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words136 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 137. -/
theorem weights0_137 : beta0Words137 < 2^(256*1024) ∧
    beta0Words137 &&& ((rep256 1024)*(2^90-1)) = beta0Words137 ∧
    popcount256 (rep256 1024) beta0Words137 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 137 has the exact claimed weight. -/
theorem weight0_137 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words137) = 22 := by
  have h := weights0_137
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words137 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 138. -/
theorem weights0_138 : beta0Words138 < 2^(256*1024) ∧
    beta0Words138 &&& ((rep256 1024)*(2^90-1)) = beta0Words138 ∧
    popcount256 (rep256 1024) beta0Words138 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 138 has the exact claimed weight. -/
theorem weight0_138 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words138) = 22 := by
  have h := weights0_138
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words138 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 139. -/
theorem weights0_139 : beta0Words139 < 2^(256*1024) ∧
    beta0Words139 &&& ((rep256 1024)*(2^90-1)) = beta0Words139 ∧
    popcount256 (rep256 1024) beta0Words139 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 139 has the exact claimed weight. -/
theorem weight0_139 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words139) = 22 := by
  have h := weights0_139
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words139 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 140. -/
theorem weights0_140 : beta0Words140 < 2^(256*1024) ∧
    beta0Words140 &&& ((rep256 1024)*(2^90-1)) = beta0Words140 ∧
    popcount256 (rep256 1024) beta0Words140 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 140 has the exact claimed weight. -/
theorem weight0_140 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words140) = 22 := by
  have h := weights0_140
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words140 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 141. -/
theorem weights0_141 : beta0Words141 < 2^(256*1024) ∧
    beta0Words141 &&& ((rep256 1024)*(2^90-1)) = beta0Words141 ∧
    popcount256 (rep256 1024) beta0Words141 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 141 has the exact claimed weight. -/
theorem weight0_141 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words141) = 22 := by
  have h := weights0_141
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words141 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 142. -/
theorem weights0_142 : beta0Words142 < 2^(256*1024) ∧
    beta0Words142 &&& ((rep256 1024)*(2^90-1)) = beta0Words142 ∧
    popcount256 (rep256 1024) beta0Words142 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 142 has the exact claimed weight. -/
theorem weight0_142 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words142) = 22 := by
  have h := weights0_142
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words142 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 143. -/
theorem weights0_143 : beta0Words143 < 2^(256*1024) ∧
    beta0Words143 &&& ((rep256 1024)*(2^90-1)) = beta0Words143 ∧
    popcount256 (rep256 1024) beta0Words143 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 143 has the exact claimed weight. -/
theorem weight0_143 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words143) = 22 := by
  have h := weights0_143
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words143 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 144. -/
theorem weights0_144 : beta0Words144 < 2^(256*1024) ∧
    beta0Words144 &&& ((rep256 1024)*(2^90-1)) = beta0Words144 ∧
    popcount256 (rep256 1024) beta0Words144 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 144 has the exact claimed weight. -/
theorem weight0_144 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words144) = 22 := by
  have h := weights0_144
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words144 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 145. -/
theorem weights0_145 : beta0Words145 < 2^(256*1024) ∧
    beta0Words145 &&& ((rep256 1024)*(2^90-1)) = beta0Words145 ∧
    popcount256 (rep256 1024) beta0Words145 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 145 has the exact claimed weight. -/
theorem weight0_145 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words145) = 22 := by
  have h := weights0_145
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words145 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 146. -/
theorem weights0_146 : beta0Words146 < 2^(256*1024) ∧
    beta0Words146 &&& ((rep256 1024)*(2^90-1)) = beta0Words146 ∧
    popcount256 (rep256 1024) beta0Words146 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 146 has the exact claimed weight. -/
theorem weight0_146 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words146) = 22 := by
  have h := weights0_146
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words146 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 147. -/
theorem weights0_147 : beta0Words147 < 2^(256*1024) ∧
    beta0Words147 &&& ((rep256 1024)*(2^90-1)) = beta0Words147 ∧
    popcount256 (rep256 1024) beta0Words147 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 147 has the exact claimed weight. -/
theorem weight0_147 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words147) = 22 := by
  have h := weights0_147
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words147 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 148. -/
theorem weights0_148 : beta0Words148 < 2^(256*1024) ∧
    beta0Words148 &&& ((rep256 1024)*(2^90-1)) = beta0Words148 ∧
    popcount256 (rep256 1024) beta0Words148 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 148 has the exact claimed weight. -/
theorem weight0_148 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words148) = 22 := by
  have h := weights0_148
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words148 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 149. -/
theorem weights0_149 : beta0Words149 < 2^(256*1024) ∧
    beta0Words149 &&& ((rep256 1024)*(2^90-1)) = beta0Words149 ∧
    popcount256 (rep256 1024) beta0Words149 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 149 has the exact claimed weight. -/
theorem weight0_149 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words149) = 22 := by
  have h := weights0_149
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words149 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 150. -/
theorem weights0_150 : beta0Words150 < 2^(256*1024) ∧
    beta0Words150 &&& ((rep256 1024)*(2^90-1)) = beta0Words150 ∧
    popcount256 (rep256 1024) beta0Words150 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 150 has the exact claimed weight. -/
theorem weight0_150 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words150) = 22 := by
  have h := weights0_150
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words150 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 151. -/
theorem weights0_151 : beta0Words151 < 2^(256*1024) ∧
    beta0Words151 &&& ((rep256 1024)*(2^90-1)) = beta0Words151 ∧
    popcount256 (rep256 1024) beta0Words151 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 151 has the exact claimed weight. -/
theorem weight0_151 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words151) = 22 := by
  have h := weights0_151
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words151 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 152. -/
theorem weights0_152 : beta0Words152 < 2^(256*1024) ∧
    beta0Words152 &&& ((rep256 1024)*(2^90-1)) = beta0Words152 ∧
    popcount256 (rep256 1024) beta0Words152 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 152 has the exact claimed weight. -/
theorem weight0_152 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words152) = 22 := by
  have h := weights0_152
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words152 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 153. -/
theorem weights0_153 : beta0Words153 < 2^(256*1024) ∧
    beta0Words153 &&& ((rep256 1024)*(2^90-1)) = beta0Words153 ∧
    popcount256 (rep256 1024) beta0Words153 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 153 has the exact claimed weight. -/
theorem weight0_153 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words153) = 22 := by
  have h := weights0_153
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words153 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 154. -/
theorem weights0_154 : beta0Words154 < 2^(256*1024) ∧
    beta0Words154 &&& ((rep256 1024)*(2^90-1)) = beta0Words154 ∧
    popcount256 (rep256 1024) beta0Words154 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 154 has the exact claimed weight. -/
theorem weight0_154 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words154) = 22 := by
  have h := weights0_154
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words154 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 155. -/
theorem weights0_155 : beta0Words155 < 2^(256*1024) ∧
    beta0Words155 &&& ((rep256 1024)*(2^90-1)) = beta0Words155 ∧
    popcount256 (rep256 1024) beta0Words155 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 155 has the exact claimed weight. -/
theorem weight0_155 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words155) = 22 := by
  have h := weights0_155
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words155 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 156. -/
theorem weights0_156 : beta0Words156 < 2^(256*1024) ∧
    beta0Words156 &&& ((rep256 1024)*(2^90-1)) = beta0Words156 ∧
    popcount256 (rep256 1024) beta0Words156 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 156 has the exact claimed weight. -/
theorem weight0_156 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words156) = 22 := by
  have h := weights0_156
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words156 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 157. -/
theorem weights0_157 : beta0Words157 < 2^(256*1024) ∧
    beta0Words157 &&& ((rep256 1024)*(2^90-1)) = beta0Words157 ∧
    popcount256 (rep256 1024) beta0Words157 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 157 has the exact claimed weight. -/
theorem weight0_157 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words157) = 22 := by
  have h := weights0_157
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words157 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 158. -/
theorem weights0_158 : beta0Words158 < 2^(256*1024) ∧
    beta0Words158 &&& ((rep256 1024)*(2^90-1)) = beta0Words158 ∧
    popcount256 (rep256 1024) beta0Words158 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 158 has the exact claimed weight. -/
theorem weight0_158 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words158) = 22 := by
  have h := weights0_158
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words158 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 159. -/
theorem weights0_159 : beta0Words159 < 2^(256*1024) ∧
    beta0Words159 &&& ((rep256 1024)*(2^90-1)) = beta0Words159 ∧
    popcount256 (rep256 1024) beta0Words159 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 159 has the exact claimed weight. -/
theorem weight0_159 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words159) = 22 := by
  have h := weights0_159
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words159 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 160. -/
theorem weights0_160 : beta0Words160 < 2^(256*1024) ∧
    beta0Words160 &&& ((rep256 1024)*(2^90-1)) = beta0Words160 ∧
    popcount256 (rep256 1024) beta0Words160 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 160 has the exact claimed weight. -/
theorem weight0_160 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words160) = 22 := by
  have h := weights0_160
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words160 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 161. -/
theorem weights0_161 : beta0Words161 < 2^(256*1024) ∧
    beta0Words161 &&& ((rep256 1024)*(2^90-1)) = beta0Words161 ∧
    popcount256 (rep256 1024) beta0Words161 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 161 has the exact claimed weight. -/
theorem weight0_161 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words161) = 22 := by
  have h := weights0_161
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words161 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 162. -/
theorem weights0_162 : beta0Words162 < 2^(256*1024) ∧
    beta0Words162 &&& ((rep256 1024)*(2^90-1)) = beta0Words162 ∧
    popcount256 (rep256 1024) beta0Words162 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 162 has the exact claimed weight. -/
theorem weight0_162 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words162) = 22 := by
  have h := weights0_162
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words162 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 163. -/
theorem weights0_163 : beta0Words163 < 2^(256*1024) ∧
    beta0Words163 &&& ((rep256 1024)*(2^90-1)) = beta0Words163 ∧
    popcount256 (rep256 1024) beta0Words163 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 163 has the exact claimed weight. -/
theorem weight0_163 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words163) = 22 := by
  have h := weights0_163
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words163 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 164. -/
theorem weights0_164 : beta0Words164 < 2^(256*1024) ∧
    beta0Words164 &&& ((rep256 1024)*(2^90-1)) = beta0Words164 ∧
    popcount256 (rep256 1024) beta0Words164 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 164 has the exact claimed weight. -/
theorem weight0_164 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words164) = 22 := by
  have h := weights0_164
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words164 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 165. -/
theorem weights0_165 : beta0Words165 < 2^(256*1024) ∧
    beta0Words165 &&& ((rep256 1024)*(2^90-1)) = beta0Words165 ∧
    popcount256 (rep256 1024) beta0Words165 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 165 has the exact claimed weight. -/
theorem weight0_165 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words165) = 22 := by
  have h := weights0_165
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words165 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 166. -/
theorem weights0_166 : beta0Words166 < 2^(256*1024) ∧
    beta0Words166 &&& ((rep256 1024)*(2^90-1)) = beta0Words166 ∧
    popcount256 (rep256 1024) beta0Words166 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 166 has the exact claimed weight. -/
theorem weight0_166 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words166) = 22 := by
  have h := weights0_166
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words166 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 167. -/
theorem weights0_167 : beta0Words167 < 2^(256*1024) ∧
    beta0Words167 &&& ((rep256 1024)*(2^90-1)) = beta0Words167 ∧
    popcount256 (rep256 1024) beta0Words167 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 167 has the exact claimed weight. -/
theorem weight0_167 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words167) = 22 := by
  have h := weights0_167
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words167 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 168. -/
theorem weights0_168 : beta0Words168 < 2^(256*1024) ∧
    beta0Words168 &&& ((rep256 1024)*(2^90-1)) = beta0Words168 ∧
    popcount256 (rep256 1024) beta0Words168 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 168 has the exact claimed weight. -/
theorem weight0_168 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words168) = 22 := by
  have h := weights0_168
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words168 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 169. -/
theorem weights0_169 : beta0Words169 < 2^(256*1024) ∧
    beta0Words169 &&& ((rep256 1024)*(2^90-1)) = beta0Words169 ∧
    popcount256 (rep256 1024) beta0Words169 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 169 has the exact claimed weight. -/
theorem weight0_169 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words169) = 22 := by
  have h := weights0_169
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words169 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 170. -/
theorem weights0_170 : beta0Words170 < 2^(256*1024) ∧
    beta0Words170 &&& ((rep256 1024)*(2^90-1)) = beta0Words170 ∧
    popcount256 (rep256 1024) beta0Words170 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 170 has the exact claimed weight. -/
theorem weight0_170 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words170) = 22 := by
  have h := weights0_170
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words170 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 171. -/
theorem weights0_171 : beta0Words171 < 2^(256*1024) ∧
    beta0Words171 &&& ((rep256 1024)*(2^90-1)) = beta0Words171 ∧
    popcount256 (rep256 1024) beta0Words171 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 171 has the exact claimed weight. -/
theorem weight0_171 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words171) = 22 := by
  have h := weights0_171
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words171 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 172. -/
theorem weights0_172 : beta0Words172 < 2^(256*1024) ∧
    beta0Words172 &&& ((rep256 1024)*(2^90-1)) = beta0Words172 ∧
    popcount256 (rep256 1024) beta0Words172 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 172 has the exact claimed weight. -/
theorem weight0_172 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words172) = 22 := by
  have h := weights0_172
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words172 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 173. -/
theorem weights0_173 : beta0Words173 < 2^(256*1024) ∧
    beta0Words173 &&& ((rep256 1024)*(2^90-1)) = beta0Words173 ∧
    popcount256 (rep256 1024) beta0Words173 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 173 has the exact claimed weight. -/
theorem weight0_173 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words173) = 22 := by
  have h := weights0_173
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words173 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 174. -/
theorem weights0_174 : beta0Words174 < 2^(256*1024) ∧
    beta0Words174 &&& ((rep256 1024)*(2^90-1)) = beta0Words174 ∧
    popcount256 (rep256 1024) beta0Words174 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 174 has the exact claimed weight. -/
theorem weight0_174 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words174) = 22 := by
  have h := weights0_174
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words174 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 175. -/
theorem weights0_175 : beta0Words175 < 2^(256*1024) ∧
    beta0Words175 &&& ((rep256 1024)*(2^90-1)) = beta0Words175 ∧
    popcount256 (rep256 1024) beta0Words175 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 175 has the exact claimed weight. -/
theorem weight0_175 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words175) = 22 := by
  have h := weights0_175
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words175 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 176. -/
theorem weights0_176 : beta0Words176 < 2^(256*1024) ∧
    beta0Words176 &&& ((rep256 1024)*(2^90-1)) = beta0Words176 ∧
    popcount256 (rep256 1024) beta0Words176 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 176 has the exact claimed weight. -/
theorem weight0_176 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words176) = 22 := by
  have h := weights0_176
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words176 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 177. -/
theorem weights0_177 : beta0Words177 < 2^(256*1024) ∧
    beta0Words177 &&& ((rep256 1024)*(2^90-1)) = beta0Words177 ∧
    popcount256 (rep256 1024) beta0Words177 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 177 has the exact claimed weight. -/
theorem weight0_177 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words177) = 22 := by
  have h := weights0_177
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words177 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 178. -/
theorem weights0_178 : beta0Words178 < 2^(256*1024) ∧
    beta0Words178 &&& ((rep256 1024)*(2^90-1)) = beta0Words178 ∧
    popcount256 (rep256 1024) beta0Words178 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 178 has the exact claimed weight. -/
theorem weight0_178 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words178) = 22 := by
  have h := weights0_178
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words178 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 179. -/
theorem weights0_179 : beta0Words179 < 2^(256*1024) ∧
    beta0Words179 &&& ((rep256 1024)*(2^90-1)) = beta0Words179 ∧
    popcount256 (rep256 1024) beta0Words179 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 179 has the exact claimed weight. -/
theorem weight0_179 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words179) = 22 := by
  have h := weights0_179
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words179 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 180. -/
theorem weights0_180 : beta0Words180 < 2^(256*1024) ∧
    beta0Words180 &&& ((rep256 1024)*(2^90-1)) = beta0Words180 ∧
    popcount256 (rep256 1024) beta0Words180 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 180 has the exact claimed weight. -/
theorem weight0_180 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words180) = 22 := by
  have h := weights0_180
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words180 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 181. -/
theorem weights0_181 : beta0Words181 < 2^(256*1024) ∧
    beta0Words181 &&& ((rep256 1024)*(2^90-1)) = beta0Words181 ∧
    popcount256 (rep256 1024) beta0Words181 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 181 has the exact claimed weight. -/
theorem weight0_181 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words181) = 22 := by
  have h := weights0_181
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words181 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 182. -/
theorem weights0_182 : beta0Words182 < 2^(256*1024) ∧
    beta0Words182 &&& ((rep256 1024)*(2^90-1)) = beta0Words182 ∧
    popcount256 (rep256 1024) beta0Words182 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 182 has the exact claimed weight. -/
theorem weight0_182 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words182) = 22 := by
  have h := weights0_182
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words182 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 183. -/
theorem weights0_183 : beta0Words183 < 2^(256*1024) ∧
    beta0Words183 &&& ((rep256 1024)*(2^90-1)) = beta0Words183 ∧
    popcount256 (rep256 1024) beta0Words183 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 183 has the exact claimed weight. -/
theorem weight0_183 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words183) = 22 := by
  have h := weights0_183
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words183 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 184. -/
theorem weights0_184 : beta0Words184 < 2^(256*1024) ∧
    beta0Words184 &&& ((rep256 1024)*(2^90-1)) = beta0Words184 ∧
    popcount256 (rep256 1024) beta0Words184 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 184 has the exact claimed weight. -/
theorem weight0_184 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words184) = 22 := by
  have h := weights0_184
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words184 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 185. -/
theorem weights0_185 : beta0Words185 < 2^(256*1024) ∧
    beta0Words185 &&& ((rep256 1024)*(2^90-1)) = beta0Words185 ∧
    popcount256 (rep256 1024) beta0Words185 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 185 has the exact claimed weight. -/
theorem weight0_185 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words185) = 22 := by
  have h := weights0_185
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words185 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 186. -/
theorem weights0_186 : beta0Words186 < 2^(256*1024) ∧
    beta0Words186 &&& ((rep256 1024)*(2^90-1)) = beta0Words186 ∧
    popcount256 (rep256 1024) beta0Words186 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 186 has the exact claimed weight. -/
theorem weight0_186 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words186) = 22 := by
  have h := weights0_186
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words186 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 187. -/
theorem weights0_187 : beta0Words187 < 2^(256*1024) ∧
    beta0Words187 &&& ((rep256 1024)*(2^90-1)) = beta0Words187 ∧
    popcount256 (rep256 1024) beta0Words187 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 187 has the exact claimed weight. -/
theorem weight0_187 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words187) = 22 := by
  have h := weights0_187
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words187 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 188. -/
theorem weights0_188 : beta0Words188 < 2^(256*1024) ∧
    beta0Words188 &&& ((rep256 1024)*(2^90-1)) = beta0Words188 ∧
    popcount256 (rep256 1024) beta0Words188 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 188 has the exact claimed weight. -/
theorem weight0_188 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words188) = 22 := by
  have h := weights0_188
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words188 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 189. -/
theorem weights0_189 : beta0Words189 < 2^(256*1024) ∧
    beta0Words189 &&& ((rep256 1024)*(2^90-1)) = beta0Words189 ∧
    popcount256 (rep256 1024) beta0Words189 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 189 has the exact claimed weight. -/
theorem weight0_189 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words189) = 22 := by
  have h := weights0_189
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words189 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 190. -/
theorem weights0_190 : beta0Words190 < 2^(256*1024) ∧
    beta0Words190 &&& ((rep256 1024)*(2^90-1)) = beta0Words190 ∧
    popcount256 (rep256 1024) beta0Words190 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 190 has the exact claimed weight. -/
theorem weight0_190 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words190) = 22 := by
  have h := weights0_190
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words190 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 191. -/
theorem weights0_191 : beta0Words191 < 2^(256*1024) ∧
    beta0Words191 &&& ((rep256 1024)*(2^90-1)) = beta0Words191 ∧
    popcount256 (rep256 1024) beta0Words191 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 191 has the exact claimed weight. -/
theorem weight0_191 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words191) = 22 := by
  have h := weights0_191
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words191 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 192. -/
theorem weights0_192 : beta0Words192 < 2^(256*1024) ∧
    beta0Words192 &&& ((rep256 1024)*(2^90-1)) = beta0Words192 ∧
    popcount256 (rep256 1024) beta0Words192 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 192 has the exact claimed weight. -/
theorem weight0_192 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words192) = 22 := by
  have h := weights0_192
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words192 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 193. -/
theorem weights0_193 : beta0Words193 < 2^(256*1024) ∧
    beta0Words193 &&& ((rep256 1024)*(2^90-1)) = beta0Words193 ∧
    popcount256 (rep256 1024) beta0Words193 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 193 has the exact claimed weight. -/
theorem weight0_193 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words193) = 22 := by
  have h := weights0_193
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words193 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 194. -/
theorem weights0_194 : beta0Words194 < 2^(256*1024) ∧
    beta0Words194 &&& ((rep256 1024)*(2^90-1)) = beta0Words194 ∧
    popcount256 (rep256 1024) beta0Words194 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 194 has the exact claimed weight. -/
theorem weight0_194 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words194) = 22 := by
  have h := weights0_194
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words194 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 195. -/
theorem weights0_195 : beta0Words195 < 2^(256*1024) ∧
    beta0Words195 &&& ((rep256 1024)*(2^90-1)) = beta0Words195 ∧
    popcount256 (rep256 1024) beta0Words195 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 195 has the exact claimed weight. -/
theorem weight0_195 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words195) = 22 := by
  have h := weights0_195
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words195 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 196. -/
theorem weights0_196 : beta0Words196 < 2^(256*1024) ∧
    beta0Words196 &&& ((rep256 1024)*(2^90-1)) = beta0Words196 ∧
    popcount256 (rep256 1024) beta0Words196 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 196 has the exact claimed weight. -/
theorem weight0_196 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words196) = 22 := by
  have h := weights0_196
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words196 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 197. -/
theorem weights0_197 : beta0Words197 < 2^(256*1024) ∧
    beta0Words197 &&& ((rep256 1024)*(2^90-1)) = beta0Words197 ∧
    popcount256 (rep256 1024) beta0Words197 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 197 has the exact claimed weight. -/
theorem weight0_197 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words197) = 22 := by
  have h := weights0_197
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words197 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 198. -/
theorem weights0_198 : beta0Words198 < 2^(256*1024) ∧
    beta0Words198 &&& ((rep256 1024)*(2^90-1)) = beta0Words198 ∧
    popcount256 (rep256 1024) beta0Words198 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 198 has the exact claimed weight. -/
theorem weight0_198 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words198) = 22 := by
  have h := weights0_198
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words198 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 199. -/
theorem weights0_199 : beta0Words199 < 2^(256*1024) ∧
    beta0Words199 &&& ((rep256 1024)*(2^90-1)) = beta0Words199 ∧
    popcount256 (rep256 1024) beta0Words199 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 199 has the exact claimed weight. -/
theorem weight0_199 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words199) = 22 := by
  have h := weights0_199
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words199 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 200. -/
theorem weights0_200 : beta0Words200 < 2^(256*1024) ∧
    beta0Words200 &&& ((rep256 1024)*(2^90-1)) = beta0Words200 ∧
    popcount256 (rep256 1024) beta0Words200 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 200 has the exact claimed weight. -/
theorem weight0_200 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words200) = 22 := by
  have h := weights0_200
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words200 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 201. -/
theorem weights0_201 : beta0Words201 < 2^(256*1024) ∧
    beta0Words201 &&& ((rep256 1024)*(2^90-1)) = beta0Words201 ∧
    popcount256 (rep256 1024) beta0Words201 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 201 has the exact claimed weight. -/
theorem weight0_201 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words201) = 22 := by
  have h := weights0_201
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words201 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 202. -/
theorem weights0_202 : beta0Words202 < 2^(256*1024) ∧
    beta0Words202 &&& ((rep256 1024)*(2^90-1)) = beta0Words202 ∧
    popcount256 (rep256 1024) beta0Words202 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 202 has the exact claimed weight. -/
theorem weight0_202 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words202) = 22 := by
  have h := weights0_202
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words202 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 203. -/
theorem weights0_203 : beta0Words203 < 2^(256*1024) ∧
    beta0Words203 &&& ((rep256 1024)*(2^90-1)) = beta0Words203 ∧
    popcount256 (rep256 1024) beta0Words203 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 203 has the exact claimed weight. -/
theorem weight0_203 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words203) = 22 := by
  have h := weights0_203
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words203 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 204. -/
theorem weights0_204 : beta0Words204 < 2^(256*1024) ∧
    beta0Words204 &&& ((rep256 1024)*(2^90-1)) = beta0Words204 ∧
    popcount256 (rep256 1024) beta0Words204 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 204 has the exact claimed weight. -/
theorem weight0_204 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words204) = 22 := by
  have h := weights0_204
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words204 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 205. -/
theorem weights0_205 : beta0Words205 < 2^(256*1024) ∧
    beta0Words205 &&& ((rep256 1024)*(2^90-1)) = beta0Words205 ∧
    popcount256 (rep256 1024) beta0Words205 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 205 has the exact claimed weight. -/
theorem weight0_205 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words205) = 22 := by
  have h := weights0_205
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words205 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 206. -/
theorem weights0_206 : beta0Words206 < 2^(256*1024) ∧
    beta0Words206 &&& ((rep256 1024)*(2^90-1)) = beta0Words206 ∧
    popcount256 (rep256 1024) beta0Words206 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 206 has the exact claimed weight. -/
theorem weight0_206 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words206) = 22 := by
  have h := weights0_206
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words206 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 207. -/
theorem weights0_207 : beta0Words207 < 2^(256*1024) ∧
    beta0Words207 &&& ((rep256 1024)*(2^90-1)) = beta0Words207 ∧
    popcount256 (rep256 1024) beta0Words207 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 207 has the exact claimed weight. -/
theorem weight0_207 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words207) = 22 := by
  have h := weights0_207
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words207 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 208. -/
theorem weights0_208 : beta0Words208 < 2^(256*1024) ∧
    beta0Words208 &&& ((rep256 1024)*(2^90-1)) = beta0Words208 ∧
    popcount256 (rep256 1024) beta0Words208 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 208 has the exact claimed weight. -/
theorem weight0_208 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words208) = 22 := by
  have h := weights0_208
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words208 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 209. -/
theorem weights0_209 : beta0Words209 < 2^(256*1024) ∧
    beta0Words209 &&& ((rep256 1024)*(2^90-1)) = beta0Words209 ∧
    popcount256 (rep256 1024) beta0Words209 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 209 has the exact claimed weight. -/
theorem weight0_209 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words209) = 22 := by
  have h := weights0_209
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words209 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 210. -/
theorem weights0_210 : beta0Words210 < 2^(256*1024) ∧
    beta0Words210 &&& ((rep256 1024)*(2^90-1)) = beta0Words210 ∧
    popcount256 (rep256 1024) beta0Words210 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 210 has the exact claimed weight. -/
theorem weight0_210 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words210) = 22 := by
  have h := weights0_210
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words210 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 211. -/
theorem weights0_211 : beta0Words211 < 2^(256*1024) ∧
    beta0Words211 &&& ((rep256 1024)*(2^90-1)) = beta0Words211 ∧
    popcount256 (rep256 1024) beta0Words211 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 211 has the exact claimed weight. -/
theorem weight0_211 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words211) = 22 := by
  have h := weights0_211
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words211 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 212. -/
theorem weights0_212 : beta0Words212 < 2^(256*1024) ∧
    beta0Words212 &&& ((rep256 1024)*(2^90-1)) = beta0Words212 ∧
    popcount256 (rep256 1024) beta0Words212 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 212 has the exact claimed weight. -/
theorem weight0_212 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words212) = 22 := by
  have h := weights0_212
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words212 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 213. -/
theorem weights0_213 : beta0Words213 < 2^(256*1024) ∧
    beta0Words213 &&& ((rep256 1024)*(2^90-1)) = beta0Words213 ∧
    popcount256 (rep256 1024) beta0Words213 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 213 has the exact claimed weight. -/
theorem weight0_213 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words213) = 22 := by
  have h := weights0_213
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words213 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 214. -/
theorem weights0_214 : beta0Words214 < 2^(256*1024) ∧
    beta0Words214 &&& ((rep256 1024)*(2^90-1)) = beta0Words214 ∧
    popcount256 (rep256 1024) beta0Words214 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 214 has the exact claimed weight. -/
theorem weight0_214 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words214) = 22 := by
  have h := weights0_214
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words214 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 215. -/
theorem weights0_215 : beta0Words215 < 2^(256*1024) ∧
    beta0Words215 &&& ((rep256 1024)*(2^90-1)) = beta0Words215 ∧
    popcount256 (rep256 1024) beta0Words215 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 215 has the exact claimed weight. -/
theorem weight0_215 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words215) = 22 := by
  have h := weights0_215
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words215 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 216. -/
theorem weights0_216 : beta0Words216 < 2^(256*1024) ∧
    beta0Words216 &&& ((rep256 1024)*(2^90-1)) = beta0Words216 ∧
    popcount256 (rep256 1024) beta0Words216 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 216 has the exact claimed weight. -/
theorem weight0_216 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words216) = 22 := by
  have h := weights0_216
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words216 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 217. -/
theorem weights0_217 : beta0Words217 < 2^(256*1024) ∧
    beta0Words217 &&& ((rep256 1024)*(2^90-1)) = beta0Words217 ∧
    popcount256 (rep256 1024) beta0Words217 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 217 has the exact claimed weight. -/
theorem weight0_217 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words217) = 22 := by
  have h := weights0_217
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words217 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 218. -/
theorem weights0_218 : beta0Words218 < 2^(256*1024) ∧
    beta0Words218 &&& ((rep256 1024)*(2^90-1)) = beta0Words218 ∧
    popcount256 (rep256 1024) beta0Words218 = (rep256 1024)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 218 has the exact claimed weight. -/
theorem weight0_218 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta0Words218) = 22 := by
  have h := weights0_218
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta0Words218 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap0 batch 219. -/
theorem weights0_219 : beta0Words219 < 2^(256*96) ∧
    beta0Words219 &&& ((rep256 96)*(2^90-1)) = beta0Words219 ∧
    popcount256 (rep256 96) beta0Words219 = (rep256 96)*22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap0 batch 219 has the exact claimed weight. -/
theorem weight0_219 (i : Nat) (hi : i < 96) : bitCount 90 (lane 256 i beta0Words219) = 22 := by
  have h := weights0_219
  rw [rep96_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 96 90 beta0Words219 22 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact weights for all cap0 chunks. -/
theorem weight0_batch (b : Nat) (hb : b < 220) (i : Nat)
    (hi : i < if b < 219 then 1024 else 96) :
    bitCount 90 (lane 256 i (beta0Words b)) = 22 := by
  by_cases h110 : b < 110
  · by_cases h55 : b < 55
    · by_cases h27 : b < 27
      · by_cases h13 : b < 13
        · by_cases h6 : b < 6
          · by_cases h3 : b < 3
            · by_cases h1 : b < 1
              · have heq : b = 0 := by omega
                subst b
                exact weight0_0 i hi
              · by_cases h2 : b < 2
                · have heq : b = 1 := by omega
                  subst b
                  exact weight0_1 i hi
                · have heq : b = 2 := by omega
                  subst b
                  exact weight0_2 i hi
            · by_cases h4 : b < 4
              · have heq : b = 3 := by omega
                subst b
                exact weight0_3 i hi
              · by_cases h5 : b < 5
                · have heq : b = 4 := by omega
                  subst b
                  exact weight0_4 i hi
                · have heq : b = 5 := by omega
                  subst b
                  exact weight0_5 i hi
          · by_cases h9 : b < 9
            · by_cases h7 : b < 7
              · have heq : b = 6 := by omega
                subst b
                exact weight0_6 i hi
              · by_cases h8 : b < 8
                · have heq : b = 7 := by omega
                  subst b
                  exact weight0_7 i hi
                · have heq : b = 8 := by omega
                  subst b
                  exact weight0_8 i hi
            · by_cases h11 : b < 11
              · by_cases h10 : b < 10
                · have heq : b = 9 := by omega
                  subst b
                  exact weight0_9 i hi
                · have heq : b = 10 := by omega
                  subst b
                  exact weight0_10 i hi
              · by_cases h12 : b < 12
                · have heq : b = 11 := by omega
                  subst b
                  exact weight0_11 i hi
                · have heq : b = 12 := by omega
                  subst b
                  exact weight0_12 i hi
        · by_cases h20 : b < 20
          · by_cases h16 : b < 16
            · by_cases h14 : b < 14
              · have heq : b = 13 := by omega
                subst b
                exact weight0_13 i hi
              · by_cases h15 : b < 15
                · have heq : b = 14 := by omega
                  subst b
                  exact weight0_14 i hi
                · have heq : b = 15 := by omega
                  subst b
                  exact weight0_15 i hi
            · by_cases h18 : b < 18
              · by_cases h17 : b < 17
                · have heq : b = 16 := by omega
                  subst b
                  exact weight0_16 i hi
                · have heq : b = 17 := by omega
                  subst b
                  exact weight0_17 i hi
              · by_cases h19 : b < 19
                · have heq : b = 18 := by omega
                  subst b
                  exact weight0_18 i hi
                · have heq : b = 19 := by omega
                  subst b
                  exact weight0_19 i hi
          · by_cases h23 : b < 23
            · by_cases h21 : b < 21
              · have heq : b = 20 := by omega
                subst b
                exact weight0_20 i hi
              · by_cases h22 : b < 22
                · have heq : b = 21 := by omega
                  subst b
                  exact weight0_21 i hi
                · have heq : b = 22 := by omega
                  subst b
                  exact weight0_22 i hi
            · by_cases h25 : b < 25
              · by_cases h24 : b < 24
                · have heq : b = 23 := by omega
                  subst b
                  exact weight0_23 i hi
                · have heq : b = 24 := by omega
                  subst b
                  exact weight0_24 i hi
              · by_cases h26 : b < 26
                · have heq : b = 25 := by omega
                  subst b
                  exact weight0_25 i hi
                · have heq : b = 26 := by omega
                  subst b
                  exact weight0_26 i hi
      · by_cases h41 : b < 41
        · by_cases h34 : b < 34
          · by_cases h30 : b < 30
            · by_cases h28 : b < 28
              · have heq : b = 27 := by omega
                subst b
                exact weight0_27 i hi
              · by_cases h29 : b < 29
                · have heq : b = 28 := by omega
                  subst b
                  exact weight0_28 i hi
                · have heq : b = 29 := by omega
                  subst b
                  exact weight0_29 i hi
            · by_cases h32 : b < 32
              · by_cases h31 : b < 31
                · have heq : b = 30 := by omega
                  subst b
                  exact weight0_30 i hi
                · have heq : b = 31 := by omega
                  subst b
                  exact weight0_31 i hi
              · by_cases h33 : b < 33
                · have heq : b = 32 := by omega
                  subst b
                  exact weight0_32 i hi
                · have heq : b = 33 := by omega
                  subst b
                  exact weight0_33 i hi
          · by_cases h37 : b < 37
            · by_cases h35 : b < 35
              · have heq : b = 34 := by omega
                subst b
                exact weight0_34 i hi
              · by_cases h36 : b < 36
                · have heq : b = 35 := by omega
                  subst b
                  exact weight0_35 i hi
                · have heq : b = 36 := by omega
                  subst b
                  exact weight0_36 i hi
            · by_cases h39 : b < 39
              · by_cases h38 : b < 38
                · have heq : b = 37 := by omega
                  subst b
                  exact weight0_37 i hi
                · have heq : b = 38 := by omega
                  subst b
                  exact weight0_38 i hi
              · by_cases h40 : b < 40
                · have heq : b = 39 := by omega
                  subst b
                  exact weight0_39 i hi
                · have heq : b = 40 := by omega
                  subst b
                  exact weight0_40 i hi
        · by_cases h48 : b < 48
          · by_cases h44 : b < 44
            · by_cases h42 : b < 42
              · have heq : b = 41 := by omega
                subst b
                exact weight0_41 i hi
              · by_cases h43 : b < 43
                · have heq : b = 42 := by omega
                  subst b
                  exact weight0_42 i hi
                · have heq : b = 43 := by omega
                  subst b
                  exact weight0_43 i hi
            · by_cases h46 : b < 46
              · by_cases h45 : b < 45
                · have heq : b = 44 := by omega
                  subst b
                  exact weight0_44 i hi
                · have heq : b = 45 := by omega
                  subst b
                  exact weight0_45 i hi
              · by_cases h47 : b < 47
                · have heq : b = 46 := by omega
                  subst b
                  exact weight0_46 i hi
                · have heq : b = 47 := by omega
                  subst b
                  exact weight0_47 i hi
          · by_cases h51 : b < 51
            · by_cases h49 : b < 49
              · have heq : b = 48 := by omega
                subst b
                exact weight0_48 i hi
              · by_cases h50 : b < 50
                · have heq : b = 49 := by omega
                  subst b
                  exact weight0_49 i hi
                · have heq : b = 50 := by omega
                  subst b
                  exact weight0_50 i hi
            · by_cases h53 : b < 53
              · by_cases h52 : b < 52
                · have heq : b = 51 := by omega
                  subst b
                  exact weight0_51 i hi
                · have heq : b = 52 := by omega
                  subst b
                  exact weight0_52 i hi
              · by_cases h54 : b < 54
                · have heq : b = 53 := by omega
                  subst b
                  exact weight0_53 i hi
                · have heq : b = 54 := by omega
                  subst b
                  exact weight0_54 i hi
    · by_cases h82 : b < 82
      · by_cases h68 : b < 68
        · by_cases h61 : b < 61
          · by_cases h58 : b < 58
            · by_cases h56 : b < 56
              · have heq : b = 55 := by omega
                subst b
                exact weight0_55 i hi
              · by_cases h57 : b < 57
                · have heq : b = 56 := by omega
                  subst b
                  exact weight0_56 i hi
                · have heq : b = 57 := by omega
                  subst b
                  exact weight0_57 i hi
            · by_cases h59 : b < 59
              · have heq : b = 58 := by omega
                subst b
                exact weight0_58 i hi
              · by_cases h60 : b < 60
                · have heq : b = 59 := by omega
                  subst b
                  exact weight0_59 i hi
                · have heq : b = 60 := by omega
                  subst b
                  exact weight0_60 i hi
          · by_cases h64 : b < 64
            · by_cases h62 : b < 62
              · have heq : b = 61 := by omega
                subst b
                exact weight0_61 i hi
              · by_cases h63 : b < 63
                · have heq : b = 62 := by omega
                  subst b
                  exact weight0_62 i hi
                · have heq : b = 63 := by omega
                  subst b
                  exact weight0_63 i hi
            · by_cases h66 : b < 66
              · by_cases h65 : b < 65
                · have heq : b = 64 := by omega
                  subst b
                  exact weight0_64 i hi
                · have heq : b = 65 := by omega
                  subst b
                  exact weight0_65 i hi
              · by_cases h67 : b < 67
                · have heq : b = 66 := by omega
                  subst b
                  exact weight0_66 i hi
                · have heq : b = 67 := by omega
                  subst b
                  exact weight0_67 i hi
        · by_cases h75 : b < 75
          · by_cases h71 : b < 71
            · by_cases h69 : b < 69
              · have heq : b = 68 := by omega
                subst b
                exact weight0_68 i hi
              · by_cases h70 : b < 70
                · have heq : b = 69 := by omega
                  subst b
                  exact weight0_69 i hi
                · have heq : b = 70 := by omega
                  subst b
                  exact weight0_70 i hi
            · by_cases h73 : b < 73
              · by_cases h72 : b < 72
                · have heq : b = 71 := by omega
                  subst b
                  exact weight0_71 i hi
                · have heq : b = 72 := by omega
                  subst b
                  exact weight0_72 i hi
              · by_cases h74 : b < 74
                · have heq : b = 73 := by omega
                  subst b
                  exact weight0_73 i hi
                · have heq : b = 74 := by omega
                  subst b
                  exact weight0_74 i hi
          · by_cases h78 : b < 78
            · by_cases h76 : b < 76
              · have heq : b = 75 := by omega
                subst b
                exact weight0_75 i hi
              · by_cases h77 : b < 77
                · have heq : b = 76 := by omega
                  subst b
                  exact weight0_76 i hi
                · have heq : b = 77 := by omega
                  subst b
                  exact weight0_77 i hi
            · by_cases h80 : b < 80
              · by_cases h79 : b < 79
                · have heq : b = 78 := by omega
                  subst b
                  exact weight0_78 i hi
                · have heq : b = 79 := by omega
                  subst b
                  exact weight0_79 i hi
              · by_cases h81 : b < 81
                · have heq : b = 80 := by omega
                  subst b
                  exact weight0_80 i hi
                · have heq : b = 81 := by omega
                  subst b
                  exact weight0_81 i hi
      · by_cases h96 : b < 96
        · by_cases h89 : b < 89
          · by_cases h85 : b < 85
            · by_cases h83 : b < 83
              · have heq : b = 82 := by omega
                subst b
                exact weight0_82 i hi
              · by_cases h84 : b < 84
                · have heq : b = 83 := by omega
                  subst b
                  exact weight0_83 i hi
                · have heq : b = 84 := by omega
                  subst b
                  exact weight0_84 i hi
            · by_cases h87 : b < 87
              · by_cases h86 : b < 86
                · have heq : b = 85 := by omega
                  subst b
                  exact weight0_85 i hi
                · have heq : b = 86 := by omega
                  subst b
                  exact weight0_86 i hi
              · by_cases h88 : b < 88
                · have heq : b = 87 := by omega
                  subst b
                  exact weight0_87 i hi
                · have heq : b = 88 := by omega
                  subst b
                  exact weight0_88 i hi
          · by_cases h92 : b < 92
            · by_cases h90 : b < 90
              · have heq : b = 89 := by omega
                subst b
                exact weight0_89 i hi
              · by_cases h91 : b < 91
                · have heq : b = 90 := by omega
                  subst b
                  exact weight0_90 i hi
                · have heq : b = 91 := by omega
                  subst b
                  exact weight0_91 i hi
            · by_cases h94 : b < 94
              · by_cases h93 : b < 93
                · have heq : b = 92 := by omega
                  subst b
                  exact weight0_92 i hi
                · have heq : b = 93 := by omega
                  subst b
                  exact weight0_93 i hi
              · by_cases h95 : b < 95
                · have heq : b = 94 := by omega
                  subst b
                  exact weight0_94 i hi
                · have heq : b = 95 := by omega
                  subst b
                  exact weight0_95 i hi
        · by_cases h103 : b < 103
          · by_cases h99 : b < 99
            · by_cases h97 : b < 97
              · have heq : b = 96 := by omega
                subst b
                exact weight0_96 i hi
              · by_cases h98 : b < 98
                · have heq : b = 97 := by omega
                  subst b
                  exact weight0_97 i hi
                · have heq : b = 98 := by omega
                  subst b
                  exact weight0_98 i hi
            · by_cases h101 : b < 101
              · by_cases h100 : b < 100
                · have heq : b = 99 := by omega
                  subst b
                  exact weight0_99 i hi
                · have heq : b = 100 := by omega
                  subst b
                  exact weight0_100 i hi
              · by_cases h102 : b < 102
                · have heq : b = 101 := by omega
                  subst b
                  exact weight0_101 i hi
                · have heq : b = 102 := by omega
                  subst b
                  exact weight0_102 i hi
          · by_cases h106 : b < 106
            · by_cases h104 : b < 104
              · have heq : b = 103 := by omega
                subst b
                exact weight0_103 i hi
              · by_cases h105 : b < 105
                · have heq : b = 104 := by omega
                  subst b
                  exact weight0_104 i hi
                · have heq : b = 105 := by omega
                  subst b
                  exact weight0_105 i hi
            · by_cases h108 : b < 108
              · by_cases h107 : b < 107
                · have heq : b = 106 := by omega
                  subst b
                  exact weight0_106 i hi
                · have heq : b = 107 := by omega
                  subst b
                  exact weight0_107 i hi
              · by_cases h109 : b < 109
                · have heq : b = 108 := by omega
                  subst b
                  exact weight0_108 i hi
                · have heq : b = 109 := by omega
                  subst b
                  exact weight0_109 i hi
  · by_cases h165 : b < 165
    · by_cases h137 : b < 137
      · by_cases h123 : b < 123
        · by_cases h116 : b < 116
          · by_cases h113 : b < 113
            · by_cases h111 : b < 111
              · have heq : b = 110 := by omega
                subst b
                exact weight0_110 i hi
              · by_cases h112 : b < 112
                · have heq : b = 111 := by omega
                  subst b
                  exact weight0_111 i hi
                · have heq : b = 112 := by omega
                  subst b
                  exact weight0_112 i hi
            · by_cases h114 : b < 114
              · have heq : b = 113 := by omega
                subst b
                exact weight0_113 i hi
              · by_cases h115 : b < 115
                · have heq : b = 114 := by omega
                  subst b
                  exact weight0_114 i hi
                · have heq : b = 115 := by omega
                  subst b
                  exact weight0_115 i hi
          · by_cases h119 : b < 119
            · by_cases h117 : b < 117
              · have heq : b = 116 := by omega
                subst b
                exact weight0_116 i hi
              · by_cases h118 : b < 118
                · have heq : b = 117 := by omega
                  subst b
                  exact weight0_117 i hi
                · have heq : b = 118 := by omega
                  subst b
                  exact weight0_118 i hi
            · by_cases h121 : b < 121
              · by_cases h120 : b < 120
                · have heq : b = 119 := by omega
                  subst b
                  exact weight0_119 i hi
                · have heq : b = 120 := by omega
                  subst b
                  exact weight0_120 i hi
              · by_cases h122 : b < 122
                · have heq : b = 121 := by omega
                  subst b
                  exact weight0_121 i hi
                · have heq : b = 122 := by omega
                  subst b
                  exact weight0_122 i hi
        · by_cases h130 : b < 130
          · by_cases h126 : b < 126
            · by_cases h124 : b < 124
              · have heq : b = 123 := by omega
                subst b
                exact weight0_123 i hi
              · by_cases h125 : b < 125
                · have heq : b = 124 := by omega
                  subst b
                  exact weight0_124 i hi
                · have heq : b = 125 := by omega
                  subst b
                  exact weight0_125 i hi
            · by_cases h128 : b < 128
              · by_cases h127 : b < 127
                · have heq : b = 126 := by omega
                  subst b
                  exact weight0_126 i hi
                · have heq : b = 127 := by omega
                  subst b
                  exact weight0_127 i hi
              · by_cases h129 : b < 129
                · have heq : b = 128 := by omega
                  subst b
                  exact weight0_128 i hi
                · have heq : b = 129 := by omega
                  subst b
                  exact weight0_129 i hi
          · by_cases h133 : b < 133
            · by_cases h131 : b < 131
              · have heq : b = 130 := by omega
                subst b
                exact weight0_130 i hi
              · by_cases h132 : b < 132
                · have heq : b = 131 := by omega
                  subst b
                  exact weight0_131 i hi
                · have heq : b = 132 := by omega
                  subst b
                  exact weight0_132 i hi
            · by_cases h135 : b < 135
              · by_cases h134 : b < 134
                · have heq : b = 133 := by omega
                  subst b
                  exact weight0_133 i hi
                · have heq : b = 134 := by omega
                  subst b
                  exact weight0_134 i hi
              · by_cases h136 : b < 136
                · have heq : b = 135 := by omega
                  subst b
                  exact weight0_135 i hi
                · have heq : b = 136 := by omega
                  subst b
                  exact weight0_136 i hi
      · by_cases h151 : b < 151
        · by_cases h144 : b < 144
          · by_cases h140 : b < 140
            · by_cases h138 : b < 138
              · have heq : b = 137 := by omega
                subst b
                exact weight0_137 i hi
              · by_cases h139 : b < 139
                · have heq : b = 138 := by omega
                  subst b
                  exact weight0_138 i hi
                · have heq : b = 139 := by omega
                  subst b
                  exact weight0_139 i hi
            · by_cases h142 : b < 142
              · by_cases h141 : b < 141
                · have heq : b = 140 := by omega
                  subst b
                  exact weight0_140 i hi
                · have heq : b = 141 := by omega
                  subst b
                  exact weight0_141 i hi
              · by_cases h143 : b < 143
                · have heq : b = 142 := by omega
                  subst b
                  exact weight0_142 i hi
                · have heq : b = 143 := by omega
                  subst b
                  exact weight0_143 i hi
          · by_cases h147 : b < 147
            · by_cases h145 : b < 145
              · have heq : b = 144 := by omega
                subst b
                exact weight0_144 i hi
              · by_cases h146 : b < 146
                · have heq : b = 145 := by omega
                  subst b
                  exact weight0_145 i hi
                · have heq : b = 146 := by omega
                  subst b
                  exact weight0_146 i hi
            · by_cases h149 : b < 149
              · by_cases h148 : b < 148
                · have heq : b = 147 := by omega
                  subst b
                  exact weight0_147 i hi
                · have heq : b = 148 := by omega
                  subst b
                  exact weight0_148 i hi
              · by_cases h150 : b < 150
                · have heq : b = 149 := by omega
                  subst b
                  exact weight0_149 i hi
                · have heq : b = 150 := by omega
                  subst b
                  exact weight0_150 i hi
        · by_cases h158 : b < 158
          · by_cases h154 : b < 154
            · by_cases h152 : b < 152
              · have heq : b = 151 := by omega
                subst b
                exact weight0_151 i hi
              · by_cases h153 : b < 153
                · have heq : b = 152 := by omega
                  subst b
                  exact weight0_152 i hi
                · have heq : b = 153 := by omega
                  subst b
                  exact weight0_153 i hi
            · by_cases h156 : b < 156
              · by_cases h155 : b < 155
                · have heq : b = 154 := by omega
                  subst b
                  exact weight0_154 i hi
                · have heq : b = 155 := by omega
                  subst b
                  exact weight0_155 i hi
              · by_cases h157 : b < 157
                · have heq : b = 156 := by omega
                  subst b
                  exact weight0_156 i hi
                · have heq : b = 157 := by omega
                  subst b
                  exact weight0_157 i hi
          · by_cases h161 : b < 161
            · by_cases h159 : b < 159
              · have heq : b = 158 := by omega
                subst b
                exact weight0_158 i hi
              · by_cases h160 : b < 160
                · have heq : b = 159 := by omega
                  subst b
                  exact weight0_159 i hi
                · have heq : b = 160 := by omega
                  subst b
                  exact weight0_160 i hi
            · by_cases h163 : b < 163
              · by_cases h162 : b < 162
                · have heq : b = 161 := by omega
                  subst b
                  exact weight0_161 i hi
                · have heq : b = 162 := by omega
                  subst b
                  exact weight0_162 i hi
              · by_cases h164 : b < 164
                · have heq : b = 163 := by omega
                  subst b
                  exact weight0_163 i hi
                · have heq : b = 164 := by omega
                  subst b
                  exact weight0_164 i hi
    · by_cases h192 : b < 192
      · by_cases h178 : b < 178
        · by_cases h171 : b < 171
          · by_cases h168 : b < 168
            · by_cases h166 : b < 166
              · have heq : b = 165 := by omega
                subst b
                exact weight0_165 i hi
              · by_cases h167 : b < 167
                · have heq : b = 166 := by omega
                  subst b
                  exact weight0_166 i hi
                · have heq : b = 167 := by omega
                  subst b
                  exact weight0_167 i hi
            · by_cases h169 : b < 169
              · have heq : b = 168 := by omega
                subst b
                exact weight0_168 i hi
              · by_cases h170 : b < 170
                · have heq : b = 169 := by omega
                  subst b
                  exact weight0_169 i hi
                · have heq : b = 170 := by omega
                  subst b
                  exact weight0_170 i hi
          · by_cases h174 : b < 174
            · by_cases h172 : b < 172
              · have heq : b = 171 := by omega
                subst b
                exact weight0_171 i hi
              · by_cases h173 : b < 173
                · have heq : b = 172 := by omega
                  subst b
                  exact weight0_172 i hi
                · have heq : b = 173 := by omega
                  subst b
                  exact weight0_173 i hi
            · by_cases h176 : b < 176
              · by_cases h175 : b < 175
                · have heq : b = 174 := by omega
                  subst b
                  exact weight0_174 i hi
                · have heq : b = 175 := by omega
                  subst b
                  exact weight0_175 i hi
              · by_cases h177 : b < 177
                · have heq : b = 176 := by omega
                  subst b
                  exact weight0_176 i hi
                · have heq : b = 177 := by omega
                  subst b
                  exact weight0_177 i hi
        · by_cases h185 : b < 185
          · by_cases h181 : b < 181
            · by_cases h179 : b < 179
              · have heq : b = 178 := by omega
                subst b
                exact weight0_178 i hi
              · by_cases h180 : b < 180
                · have heq : b = 179 := by omega
                  subst b
                  exact weight0_179 i hi
                · have heq : b = 180 := by omega
                  subst b
                  exact weight0_180 i hi
            · by_cases h183 : b < 183
              · by_cases h182 : b < 182
                · have heq : b = 181 := by omega
                  subst b
                  exact weight0_181 i hi
                · have heq : b = 182 := by omega
                  subst b
                  exact weight0_182 i hi
              · by_cases h184 : b < 184
                · have heq : b = 183 := by omega
                  subst b
                  exact weight0_183 i hi
                · have heq : b = 184 := by omega
                  subst b
                  exact weight0_184 i hi
          · by_cases h188 : b < 188
            · by_cases h186 : b < 186
              · have heq : b = 185 := by omega
                subst b
                exact weight0_185 i hi
              · by_cases h187 : b < 187
                · have heq : b = 186 := by omega
                  subst b
                  exact weight0_186 i hi
                · have heq : b = 187 := by omega
                  subst b
                  exact weight0_187 i hi
            · by_cases h190 : b < 190
              · by_cases h189 : b < 189
                · have heq : b = 188 := by omega
                  subst b
                  exact weight0_188 i hi
                · have heq : b = 189 := by omega
                  subst b
                  exact weight0_189 i hi
              · by_cases h191 : b < 191
                · have heq : b = 190 := by omega
                  subst b
                  exact weight0_190 i hi
                · have heq : b = 191 := by omega
                  subst b
                  exact weight0_191 i hi
      · by_cases h206 : b < 206
        · by_cases h199 : b < 199
          · by_cases h195 : b < 195
            · by_cases h193 : b < 193
              · have heq : b = 192 := by omega
                subst b
                exact weight0_192 i hi
              · by_cases h194 : b < 194
                · have heq : b = 193 := by omega
                  subst b
                  exact weight0_193 i hi
                · have heq : b = 194 := by omega
                  subst b
                  exact weight0_194 i hi
            · by_cases h197 : b < 197
              · by_cases h196 : b < 196
                · have heq : b = 195 := by omega
                  subst b
                  exact weight0_195 i hi
                · have heq : b = 196 := by omega
                  subst b
                  exact weight0_196 i hi
              · by_cases h198 : b < 198
                · have heq : b = 197 := by omega
                  subst b
                  exact weight0_197 i hi
                · have heq : b = 198 := by omega
                  subst b
                  exact weight0_198 i hi
          · by_cases h202 : b < 202
            · by_cases h200 : b < 200
              · have heq : b = 199 := by omega
                subst b
                exact weight0_199 i hi
              · by_cases h201 : b < 201
                · have heq : b = 200 := by omega
                  subst b
                  exact weight0_200 i hi
                · have heq : b = 201 := by omega
                  subst b
                  exact weight0_201 i hi
            · by_cases h204 : b < 204
              · by_cases h203 : b < 203
                · have heq : b = 202 := by omega
                  subst b
                  exact weight0_202 i hi
                · have heq : b = 203 := by omega
                  subst b
                  exact weight0_203 i hi
              · by_cases h205 : b < 205
                · have heq : b = 204 := by omega
                  subst b
                  exact weight0_204 i hi
                · have heq : b = 205 := by omega
                  subst b
                  exact weight0_205 i hi
        · by_cases h213 : b < 213
          · by_cases h209 : b < 209
            · by_cases h207 : b < 207
              · have heq : b = 206 := by omega
                subst b
                exact weight0_206 i hi
              · by_cases h208 : b < 208
                · have heq : b = 207 := by omega
                  subst b
                  exact weight0_207 i hi
                · have heq : b = 208 := by omega
                  subst b
                  exact weight0_208 i hi
            · by_cases h211 : b < 211
              · by_cases h210 : b < 210
                · have heq : b = 209 := by omega
                  subst b
                  exact weight0_209 i hi
                · have heq : b = 210 := by omega
                  subst b
                  exact weight0_210 i hi
              · by_cases h212 : b < 212
                · have heq : b = 211 := by omega
                  subst b
                  exact weight0_211 i hi
                · have heq : b = 212 := by omega
                  subst b
                  exact weight0_212 i hi
          · by_cases h216 : b < 216
            · by_cases h214 : b < 214
              · have heq : b = 213 := by omega
                subst b
                exact weight0_213 i hi
              · by_cases h215 : b < 215
                · have heq : b = 214 := by omega
                  subst b
                  exact weight0_214 i hi
                · have heq : b = 215 := by omega
                  subst b
                  exact weight0_215 i hi
            · by_cases h218 : b < 218
              · by_cases h217 : b < 217
                · have heq : b = 216 := by omega
                  subst b
                  exact weight0_216 i hi
                · have heq : b = 217 := by omega
                  subst b
                  exact weight0_217 i hi
              · by_cases h219 : b < 219
                · have heq : b = 218 := by omega
                  subst b
                  exact weight0_218 i hi
                · have heq : b = 219 := by omega
                  subst b
                  exact weight0_219 i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact shadow weight throughout the cap0 family. -/
theorem beta0_weight (i : Fin 224352) : bitCount 90 (beta0 i.val) = 22 := by
  have hm := Nat.mod_lt i.val (by decide : 0 < 1024)
  have heq := Nat.mod_add_div i.val 1024
  have hb : i.val / 1024 < 220 := by omega
  have hl : i.val % 1024 < (if i.val / 1024 < 219 then 1024 else 96) := by
    split_ifs <;> omega
  exact weight0_batch _ hb _ hl
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap1 batch 0. -/
theorem weights1_0 : beta1Words0 < 2^(256*1024) ∧
    beta1Words0 &&& ((rep256 1024)*(2^90-1)) = beta1Words0 ∧
    popcount256 (rep256 1024) beta1Words0 = (rep256 1024)*20 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap1 batch 0 has the exact claimed weight. -/
theorem weight1_0 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta1Words0) = 20 := by
  have h := weights1_0
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta1Words0 20 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap1 batch 1. -/
theorem weights1_1 : beta1Words1 < 2^(256*1024) ∧
    beta1Words1 &&& ((rep256 1024)*(2^90-1)) = beta1Words1 ∧
    popcount256 (rep256 1024) beta1Words1 = (rep256 1024)*20 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap1 batch 1 has the exact claimed weight. -/
theorem weight1_1 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta1Words1) = 20 := by
  have h := weights1_1
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta1Words1 20 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap1 batch 2. -/
theorem weights1_2 : beta1Words2 < 2^(256*1024) ∧
    beta1Words2 &&& ((rep256 1024)*(2^90-1)) = beta1Words2 ∧
    popcount256 (rep256 1024) beta1Words2 = (rep256 1024)*20 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap1 batch 2 has the exact claimed weight. -/
theorem weight1_2 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta1Words2) = 20 := by
  have h := weights1_2
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta1Words2 20 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap1 batch 3. -/
theorem weights1_3 : beta1Words3 < 2^(256*1024) ∧
    beta1Words3 &&& ((rep256 1024)*(2^90-1)) = beta1Words3 ∧
    popcount256 (rep256 1024) beta1Words3 = (rep256 1024)*20 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap1 batch 3 has the exact claimed weight. -/
theorem weight1_3 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta1Words3) = 20 := by
  have h := weights1_3
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta1Words3 20 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap1 batch 4. -/
theorem weights1_4 : beta1Words4 < 2^(256*1024) ∧
    beta1Words4 &&& ((rep256 1024)*(2^90-1)) = beta1Words4 ∧
    popcount256 (rep256 1024) beta1Words4 = (rep256 1024)*20 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap1 batch 4 has the exact claimed weight. -/
theorem weight1_4 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta1Words4) = 20 := by
  have h := weights1_4
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta1Words4 20 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap1 batch 5. -/
theorem weights1_5 : beta1Words5 < 2^(256*1024) ∧
    beta1Words5 &&& ((rep256 1024)*(2^90-1)) = beta1Words5 ∧
    popcount256 (rep256 1024) beta1Words5 = (rep256 1024)*20 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap1 batch 5 has the exact claimed weight. -/
theorem weight1_5 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta1Words5) = 20 := by
  have h := weights1_5
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta1Words5 20 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap1 batch 6. -/
theorem weights1_6 : beta1Words6 < 2^(256*1024) ∧
    beta1Words6 &&& ((rep256 1024)*(2^90-1)) = beta1Words6 ∧
    popcount256 (rep256 1024) beta1Words6 = (rep256 1024)*20 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap1 batch 6 has the exact claimed weight. -/
theorem weight1_6 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta1Words6) = 20 := by
  have h := weights1_6
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta1Words6 20 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap1 batch 7. -/
theorem weights1_7 : beta1Words7 < 2^(256*1024) ∧
    beta1Words7 &&& ((rep256 1024)*(2^90-1)) = beta1Words7 ∧
    popcount256 (rep256 1024) beta1Words7 = (rep256 1024)*20 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap1 batch 7 has the exact claimed weight. -/
theorem weight1_7 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta1Words7) = 20 := by
  have h := weights1_7
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta1Words7 20 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap1 batch 8. -/
theorem weights1_8 : beta1Words8 < 2^(256*1024) ∧
    beta1Words8 &&& ((rep256 1024)*(2^90-1)) = beta1Words8 ∧
    popcount256 (rep256 1024) beta1Words8 = (rep256 1024)*20 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap1 batch 8 has the exact claimed weight. -/
theorem weight1_8 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta1Words8) = 20 := by
  have h := weights1_8
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta1Words8 20 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap1 batch 9. -/
theorem weights1_9 : beta1Words9 < 2^(256*1024) ∧
    beta1Words9 &&& ((rep256 1024)*(2^90-1)) = beta1Words9 ∧
    popcount256 (rep256 1024) beta1Words9 = (rep256 1024)*20 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap1 batch 9 has the exact claimed weight. -/
theorem weight1_9 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta1Words9) = 20 := by
  have h := weights1_9
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta1Words9 20 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap1 batch 10. -/
theorem weights1_10 : beta1Words10 < 2^(256*1024) ∧
    beta1Words10 &&& ((rep256 1024)*(2^90-1)) = beta1Words10 ∧
    popcount256 (rep256 1024) beta1Words10 = (rep256 1024)*20 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap1 batch 10 has the exact claimed weight. -/
theorem weight1_10 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta1Words10) = 20 := by
  have h := weights1_10
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta1Words10 20 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap1 batch 11. -/
theorem weights1_11 : beta1Words11 < 2^(256*1024) ∧
    beta1Words11 &&& ((rep256 1024)*(2^90-1)) = beta1Words11 ∧
    popcount256 (rep256 1024) beta1Words11 = (rep256 1024)*20 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap1 batch 11 has the exact claimed weight. -/
theorem weight1_11 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta1Words11) = 20 := by
  have h := weights1_11
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta1Words11 20 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap1 batch 12. -/
theorem weights1_12 : beta1Words12 < 2^(256*1024) ∧
    beta1Words12 &&& ((rep256 1024)*(2^90-1)) = beta1Words12 ∧
    popcount256 (rep256 1024) beta1Words12 = (rep256 1024)*20 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap1 batch 12 has the exact claimed weight. -/
theorem weight1_12 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta1Words12) = 20 := by
  have h := weights1_12
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta1Words12 20 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap1 batch 13. -/
theorem weights1_13 : beta1Words13 < 2^(256*1024) ∧
    beta1Words13 &&& ((rep256 1024)*(2^90-1)) = beta1Words13 ∧
    popcount256 (rep256 1024) beta1Words13 = (rep256 1024)*20 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap1 batch 13 has the exact claimed weight. -/
theorem weight1_13 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta1Words13) = 20 := by
  have h := weights1_13
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta1Words13 20 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap1 batch 14. -/
theorem weights1_14 : beta1Words14 < 2^(256*1024) ∧
    beta1Words14 &&& ((rep256 1024)*(2^90-1)) = beta1Words14 ∧
    popcount256 (rep256 1024) beta1Words14 = (rep256 1024)*20 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap1 batch 14 has the exact claimed weight. -/
theorem weight1_14 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta1Words14) = 20 := by
  have h := weights1_14
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta1Words14 20 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap1 batch 15. -/
theorem weights1_15 : beta1Words15 < 2^(256*1024) ∧
    beta1Words15 &&& ((rep256 1024)*(2^90-1)) = beta1Words15 ∧
    popcount256 (rep256 1024) beta1Words15 = (rep256 1024)*20 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap1 batch 15 has the exact claimed weight. -/
theorem weight1_15 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta1Words15) = 20 := by
  have h := weights1_15
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta1Words15 20 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap1 batch 16. -/
theorem weights1_16 : beta1Words16 < 2^(256*1024) ∧
    beta1Words16 &&& ((rep256 1024)*(2^90-1)) = beta1Words16 ∧
    popcount256 (rep256 1024) beta1Words16 = (rep256 1024)*20 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap1 batch 16 has the exact claimed weight. -/
theorem weight1_16 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta1Words16) = 20 := by
  have h := weights1_16
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta1Words16 20 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap1 batch 17. -/
theorem weights1_17 : beta1Words17 < 2^(256*1024) ∧
    beta1Words17 &&& ((rep256 1024)*(2^90-1)) = beta1Words17 ∧
    popcount256 (rep256 1024) beta1Words17 = (rep256 1024)*20 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap1 batch 17 has the exact claimed weight. -/
theorem weight1_17 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta1Words17) = 20 := by
  have h := weights1_17
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta1Words17 20 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap1 batch 18. -/
theorem weights1_18 : beta1Words18 < 2^(256*1024) ∧
    beta1Words18 &&& ((rep256 1024)*(2^90-1)) = beta1Words18 ∧
    popcount256 (rep256 1024) beta1Words18 = (rep256 1024)*20 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap1 batch 18 has the exact claimed weight. -/
theorem weight1_18 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta1Words18) = 20 := by
  have h := weights1_18
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta1Words18 20 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap1 batch 19. -/
theorem weights1_19 : beta1Words19 < 2^(256*1024) ∧
    beta1Words19 &&& ((rep256 1024)*(2^90-1)) = beta1Words19 ∧
    popcount256 (rep256 1024) beta1Words19 = (rep256 1024)*20 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap1 batch 19 has the exact claimed weight. -/
theorem weight1_19 (i : Nat) (hi : i < 1024) : bitCount 90 (lane 256 i beta1Words19) = 20 := by
  have h := weights1_19
  rw [rep1024_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 1024 90 beta1Words19 20 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap1 batch 20. -/
theorem weights1_20 : beta1Words20 < 2^(256*424) ∧
    beta1Words20 &&& ((rep256 424)*(2^90-1)) = beta1Words20 ∧
    popcount256 (rep256 424) beta1Words20 = (rep256 424)*20 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap1 batch 20 has the exact claimed weight. -/
theorem weight1_20 (i : Nat) (hi : i < 424) : bitCount 90 (lane 256 i beta1Words20) = 20 := by
  have h := weights1_20
  rw [rep424_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 424 90 beta1Words20 20 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact weights for all cap1 chunks. -/
theorem weight1_batch (b : Nat) (hb : b < 21) (i : Nat)
    (hi : i < if b < 20 then 1024 else 424) :
    bitCount 90 (lane 256 i (beta1Words b)) = 20 := by
  by_cases h10 : b < 10
  · by_cases h5 : b < 5
    · by_cases h2 : b < 2
      · by_cases h1 : b < 1
        · have heq : b = 0 := by omega
          subst b
          exact weight1_0 i hi
        · have heq : b = 1 := by omega
          subst b
          exact weight1_1 i hi
      · by_cases h3 : b < 3
        · have heq : b = 2 := by omega
          subst b
          exact weight1_2 i hi
        · by_cases h4 : b < 4
          · have heq : b = 3 := by omega
            subst b
            exact weight1_3 i hi
          · have heq : b = 4 := by omega
            subst b
            exact weight1_4 i hi
    · by_cases h7 : b < 7
      · by_cases h6 : b < 6
        · have heq : b = 5 := by omega
          subst b
          exact weight1_5 i hi
        · have heq : b = 6 := by omega
          subst b
          exact weight1_6 i hi
      · by_cases h8 : b < 8
        · have heq : b = 7 := by omega
          subst b
          exact weight1_7 i hi
        · by_cases h9 : b < 9
          · have heq : b = 8 := by omega
            subst b
            exact weight1_8 i hi
          · have heq : b = 9 := by omega
            subst b
            exact weight1_9 i hi
  · by_cases h15 : b < 15
    · by_cases h12 : b < 12
      · by_cases h11 : b < 11
        · have heq : b = 10 := by omega
          subst b
          exact weight1_10 i hi
        · have heq : b = 11 := by omega
          subst b
          exact weight1_11 i hi
      · by_cases h13 : b < 13
        · have heq : b = 12 := by omega
          subst b
          exact weight1_12 i hi
        · by_cases h14 : b < 14
          · have heq : b = 13 := by omega
            subst b
            exact weight1_13 i hi
          · have heq : b = 14 := by omega
            subst b
            exact weight1_14 i hi
    · by_cases h18 : b < 18
      · by_cases h16 : b < 16
        · have heq : b = 15 := by omega
          subst b
          exact weight1_15 i hi
        · by_cases h17 : b < 17
          · have heq : b = 16 := by omega
            subst b
            exact weight1_16 i hi
          · have heq : b = 17 := by omega
            subst b
            exact weight1_17 i hi
      · by_cases h19 : b < 19
        · have heq : b = 18 := by omega
          subst b
          exact weight1_18 i hi
        · by_cases h20 : b < 20
          · have heq : b = 19 := by omega
            subst b
            exact weight1_19 i hi
          · have heq : b = 20 := by omega
            subst b
            exact weight1_20 i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact shadow weight throughout the cap1 family. -/
theorem beta1_weight (i : Fin 20904) : bitCount 90 (beta1 i.val) = 20 := by
  have hm := Nat.mod_lt i.val (by decide : 0 < 1024)
  have heq := Nat.mod_add_div i.val 1024
  have hb : i.val / 1024 < 21 := by omega
  have hl : i.val % 1024 < (if i.val / 1024 < 20 then 1024 else 424) := by
    split_ifs <;> omega
  exact weight1_batch _ hb _ hl
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed exact shadow weights in cap2 batch 0. -/
theorem weights2_0 : beta2Words0 < 2^(256*859) ∧
    beta2Words0 &&& ((rep256 859)*(2^90-1)) = beta2Words0 ∧
    popcount256 (rep256 859) beta2Words0 = (rep256 859)*18 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shadow in cap2 batch 0 has the exact claimed weight. -/
theorem weight2_0 (i : Nat) (hi : i < 859) : bitCount 90 (lane 256 i beta2Words0) = 18 := by
  have h := weights2_0
  rw [rep859_eq] at h
  have hp := h.2.2
  rw [repeat_mul_eq_packF] at hp
  exact popcount256_weight 859 90 beta2Words0 18 (by decide) h.1 h.2.1 hp (by decide) i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact weights for all cap2 chunks. -/
theorem weight2_batch (b : Nat) (hb : b < 1) (i : Nat)
    (hi : i < if b < 0 then 1024 else 859) :
    bitCount 90 (lane 256 i (beta2Words b)) = 18 := by
  have heq : b = 0 := by omega
  subst b
  exact weight2_0 i hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact shadow weight throughout the cap2 family. -/
theorem beta2_weight (i : Fin 859) : bitCount 90 (beta2 i.val) = 18 := by
  have hm := Nat.mod_lt i.val (by decide : 0 < 1024)
  have heq := Nat.mod_add_div i.val 1024
  have hb : i.val / 1024 < 1 := by omega
  have hl : i.val % 1024 < (if i.val / 1024 < 0 then 1024 else 859) := by
    split_ifs <;> omega
  exact weight2_batch _ hb _ hl
#print axioms beta0_weight
end Quantum.Stabilizer.Homological.BB.Bravyi360.BottomEmpty
