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

import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.BottomShallowCacheCheck

noncomputable section
namespace Quantum.Stabilizer.Homological.BB.Bravyi360.BottomShallow
set_option maxRecDepth 100000
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 0. -/
noncomputable def cache0_0 : LinkCache := ⟨0,BottomEmpty.beta0Words0,BottomEmpty.beta0Words1⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 0. -/
noncomputable def cache1_0 : LinkCache := ⟨0,BottomEmpty.beta1Words0,BottomEmpty.beta1Words1⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 0. -/
noncomputable def cache2_0 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 0. -/
noncomputable def cache3_0 : LinkCache := ⟨0,BottomForest.packed0.rInput,BottomForest.packed250.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 0. -/
theorem cachedLinkChecked0 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words0 BottomCase.words0 0 cache0_0 cache1_0 cache2_0 cache3_0 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 0. -/
theorem linkChecked0 : ((List.range 1024).all fun j => linkCheck (0+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked0 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words0 BottomCase.words0 0 row
    cache0_0 cache1_0 cache2_0 cache3_0 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 0) (BottomCase.wordsAt 0) (1024*0) row = true := hc
  rw [linkChunkCheck_eq 0 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 1. -/
noncomputable def cache0_1 : LinkCache := ⟨0,BottomEmpty.beta0Words0,BottomEmpty.beta0Words1⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 1. -/
noncomputable def cache1_1 : LinkCache := ⟨0,BottomEmpty.beta1Words0,BottomEmpty.beta1Words1⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 1. -/
noncomputable def cache2_1 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 1. -/
noncomputable def cache3_1 : LinkCache := ⟨0,BottomForest.packed0.rInput,BottomForest.packed250.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 1. -/
theorem cachedLinkChecked1 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words1 BottomCase.words1 1024 cache0_1 cache1_1 cache2_1 cache3_1 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 1. -/
theorem linkChecked1 : ((List.range 1024).all fun j => linkCheck (1024+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked1 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words1 BottomCase.words1 1024 row
    cache0_1 cache1_1 cache2_1 cache3_1 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 1) (BottomCase.wordsAt 1) (1024*1) row = true := hc
  rw [linkChunkCheck_eq 1 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 2. -/
noncomputable def cache0_2 : LinkCache := ⟨1,BottomEmpty.beta0Words1,BottomEmpty.beta0Words2⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 2. -/
noncomputable def cache1_2 : LinkCache := ⟨0,BottomEmpty.beta1Words0,BottomEmpty.beta1Words1⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 2. -/
noncomputable def cache2_2 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 2. -/
noncomputable def cache3_2 : LinkCache := ⟨1,BottomForest.packed250.rInput,BottomForest.packed500.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 2. -/
theorem cachedLinkChecked2 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words2 BottomCase.words2 2048 cache0_2 cache1_2 cache2_2 cache3_2 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 2. -/
theorem linkChecked2 : ((List.range 1024).all fun j => linkCheck (2048+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked2 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words2 BottomCase.words2 2048 row
    cache0_2 cache1_2 cache2_2 cache3_2 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 2) (BottomCase.wordsAt 2) (1024*2) row = true := hc
  rw [linkChunkCheck_eq 2 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 3. -/
noncomputable def cache0_3 : LinkCache := ⟨2,BottomEmpty.beta0Words2,BottomEmpty.beta0Words3⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 3. -/
noncomputable def cache1_3 : LinkCache := ⟨0,BottomEmpty.beta1Words0,BottomEmpty.beta1Words1⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 3. -/
noncomputable def cache2_3 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 3. -/
noncomputable def cache3_3 : LinkCache := ⟨1,BottomForest.packed250.rInput,BottomForest.packed500.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 3. -/
theorem cachedLinkChecked3 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words3 BottomCase.words3 3072 cache0_3 cache1_3 cache2_3 cache3_3 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 3. -/
theorem linkChecked3 : ((List.range 1024).all fun j => linkCheck (3072+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked3 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words3 BottomCase.words3 3072 row
    cache0_3 cache1_3 cache2_3 cache3_3 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 3) (BottomCase.wordsAt 3) (1024*3) row = true := hc
  rw [linkChunkCheck_eq 3 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 4. -/
noncomputable def cache0_4 : LinkCache := ⟨2,BottomEmpty.beta0Words2,BottomEmpty.beta0Words3⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 4. -/
noncomputable def cache1_4 : LinkCache := ⟨0,BottomEmpty.beta1Words0,BottomEmpty.beta1Words1⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 4. -/
noncomputable def cache2_4 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 4. -/
noncomputable def cache3_4 : LinkCache := ⟨2,BottomForest.packed500.rInput,BottomForest.packed750.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 4. -/
theorem cachedLinkChecked4 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words4 BottomCase.words4 4096 cache0_4 cache1_4 cache2_4 cache3_4 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 4. -/
theorem linkChecked4 : ((List.range 1024).all fun j => linkCheck (4096+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked4 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words4 BottomCase.words4 4096 row
    cache0_4 cache1_4 cache2_4 cache3_4 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 4) (BottomCase.wordsAt 4) (1024*4) row = true := hc
  rw [linkChunkCheck_eq 4 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 5. -/
noncomputable def cache0_5 : LinkCache := ⟨3,BottomEmpty.beta0Words3,BottomEmpty.beta0Words4⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 5. -/
noncomputable def cache1_5 : LinkCache := ⟨0,BottomEmpty.beta1Words0,BottomEmpty.beta1Words1⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 5. -/
noncomputable def cache2_5 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 5. -/
noncomputable def cache3_5 : LinkCache := ⟨2,BottomForest.packed500.rInput,BottomForest.packed750.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 5. -/
theorem cachedLinkChecked5 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words5 BottomCase.words5 5120 cache0_5 cache1_5 cache2_5 cache3_5 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 5. -/
theorem linkChecked5 : ((List.range 1024).all fun j => linkCheck (5120+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked5 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words5 BottomCase.words5 5120 row
    cache0_5 cache1_5 cache2_5 cache3_5 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 5) (BottomCase.wordsAt 5) (1024*5) row = true := hc
  rw [linkChunkCheck_eq 5 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 6. -/
noncomputable def cache0_6 : LinkCache := ⟨4,BottomEmpty.beta0Words4,BottomEmpty.beta0Words5⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 6. -/
noncomputable def cache1_6 : LinkCache := ⟨0,BottomEmpty.beta1Words0,BottomEmpty.beta1Words1⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 6. -/
noncomputable def cache2_6 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 6. -/
noncomputable def cache3_6 : LinkCache := ⟨2,BottomForest.packed500.rInput,BottomForest.packed750.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 6. -/
theorem cachedLinkChecked6 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words6 BottomCase.words6 6144 cache0_6 cache1_6 cache2_6 cache3_6 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 6. -/
theorem linkChecked6 : ((List.range 1024).all fun j => linkCheck (6144+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked6 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words6 BottomCase.words6 6144 row
    cache0_6 cache1_6 cache2_6 cache3_6 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 6) (BottomCase.wordsAt 6) (1024*6) row = true := hc
  rw [linkChunkCheck_eq 6 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 7. -/
noncomputable def cache0_7 : LinkCache := ⟨5,BottomEmpty.beta0Words5,BottomEmpty.beta0Words6⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 7. -/
noncomputable def cache1_7 : LinkCache := ⟨0,BottomEmpty.beta1Words0,BottomEmpty.beta1Words1⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 7. -/
noncomputable def cache2_7 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 7. -/
noncomputable def cache3_7 : LinkCache := ⟨3,BottomForest.packed750.rInput,BottomForest.packed1000.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 7. -/
theorem cachedLinkChecked7 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words7 BottomCase.words7 7168 cache0_7 cache1_7 cache2_7 cache3_7 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 7. -/
theorem linkChecked7 : ((List.range 1024).all fun j => linkCheck (7168+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked7 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words7 BottomCase.words7 7168 row
    cache0_7 cache1_7 cache2_7 cache3_7 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 7) (BottomCase.wordsAt 7) (1024*7) row = true := hc
  rw [linkChunkCheck_eq 7 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 8. -/
noncomputable def cache0_8 : LinkCache := ⟨5,BottomEmpty.beta0Words5,BottomEmpty.beta0Words6⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 8. -/
noncomputable def cache1_8 : LinkCache := ⟨1,BottomEmpty.beta1Words1,BottomEmpty.beta1Words2⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 8. -/
noncomputable def cache2_8 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 8. -/
noncomputable def cache3_8 : LinkCache := ⟨3,BottomForest.packed750.rInput,BottomForest.packed1000.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 8. -/
theorem cachedLinkChecked8 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words8 BottomCase.words8 8192 cache0_8 cache1_8 cache2_8 cache3_8 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 8. -/
theorem linkChecked8 : ((List.range 1024).all fun j => linkCheck (8192+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked8 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words8 BottomCase.words8 8192 row
    cache0_8 cache1_8 cache2_8 cache3_8 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 8) (BottomCase.wordsAt 8) (1024*8) row = true := hc
  rw [linkChunkCheck_eq 8 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 9. -/
noncomputable def cache0_9 : LinkCache := ⟨6,BottomEmpty.beta0Words6,BottomEmpty.beta0Words7⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 9. -/
noncomputable def cache1_9 : LinkCache := ⟨1,BottomEmpty.beta1Words1,BottomEmpty.beta1Words2⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 9. -/
noncomputable def cache2_9 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 9. -/
noncomputable def cache3_9 : LinkCache := ⟨4,BottomForest.packed1000.rInput,BottomForest.packed1250.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 9. -/
theorem cachedLinkChecked9 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words9 BottomCase.words9 9216 cache0_9 cache1_9 cache2_9 cache3_9 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 9. -/
theorem linkChecked9 : ((List.range 1024).all fun j => linkCheck (9216+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked9 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words9 BottomCase.words9 9216 row
    cache0_9 cache1_9 cache2_9 cache3_9 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 9) (BottomCase.wordsAt 9) (1024*9) row = true := hc
  rw [linkChunkCheck_eq 9 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 10. -/
noncomputable def cache0_10 : LinkCache := ⟨7,BottomEmpty.beta0Words7,BottomEmpty.beta0Words8⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 10. -/
noncomputable def cache1_10 : LinkCache := ⟨1,BottomEmpty.beta1Words1,BottomEmpty.beta1Words2⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 10. -/
noncomputable def cache2_10 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 10. -/
noncomputable def cache3_10 : LinkCache := ⟨4,BottomForest.packed1000.rInput,BottomForest.packed1250.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 10. -/
theorem cachedLinkChecked10 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words10 BottomCase.words10 10240 cache0_10 cache1_10 cache2_10 cache3_10 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 10. -/
theorem linkChecked10 : ((List.range 1024).all fun j => linkCheck (10240+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked10 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words10 BottomCase.words10 10240 row
    cache0_10 cache1_10 cache2_10 cache3_10 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 10) (BottomCase.wordsAt 10) (1024*10) row = true := hc
  rw [linkChunkCheck_eq 10 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 11. -/
noncomputable def cache0_11 : LinkCache := ⟨8,BottomEmpty.beta0Words8,BottomEmpty.beta0Words9⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 11. -/
noncomputable def cache1_11 : LinkCache := ⟨1,BottomEmpty.beta1Words1,BottomEmpty.beta1Words2⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 11. -/
noncomputable def cache2_11 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 11. -/
noncomputable def cache3_11 : LinkCache := ⟨5,BottomForest.packed1250.rInput,BottomForest.packed1500.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 11. -/
theorem cachedLinkChecked11 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words11 BottomCase.words11 11264 cache0_11 cache1_11 cache2_11 cache3_11 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 11. -/
theorem linkChecked11 : ((List.range 1024).all fun j => linkCheck (11264+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked11 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words11 BottomCase.words11 11264 row
    cache0_11 cache1_11 cache2_11 cache3_11 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 11) (BottomCase.wordsAt 11) (1024*11) row = true := hc
  rw [linkChunkCheck_eq 11 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 12. -/
noncomputable def cache0_12 : LinkCache := ⟨8,BottomEmpty.beta0Words8,BottomEmpty.beta0Words9⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 12. -/
noncomputable def cache1_12 : LinkCache := ⟨1,BottomEmpty.beta1Words1,BottomEmpty.beta1Words2⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 12. -/
noncomputable def cache2_12 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 12. -/
noncomputable def cache3_12 : LinkCache := ⟨5,BottomForest.packed1250.rInput,BottomForest.packed1500.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 12. -/
theorem cachedLinkChecked12 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words12 BottomCase.words12 12288 cache0_12 cache1_12 cache2_12 cache3_12 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 12. -/
theorem linkChecked12 : ((List.range 1024).all fun j => linkCheck (12288+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked12 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words12 BottomCase.words12 12288 row
    cache0_12 cache1_12 cache2_12 cache3_12 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 12) (BottomCase.wordsAt 12) (1024*12) row = true := hc
  rw [linkChunkCheck_eq 12 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 13. -/
noncomputable def cache0_13 : LinkCache := ⟨9,BottomEmpty.beta0Words9,BottomEmpty.beta0Words10⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 13. -/
noncomputable def cache1_13 : LinkCache := ⟨1,BottomEmpty.beta1Words1,BottomEmpty.beta1Words2⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 13. -/
noncomputable def cache2_13 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 13. -/
noncomputable def cache3_13 : LinkCache := ⟨5,BottomForest.packed1250.rInput,BottomForest.packed1500.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 13. -/
theorem cachedLinkChecked13 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words13 BottomCase.words13 13312 cache0_13 cache1_13 cache2_13 cache3_13 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 13. -/
theorem linkChecked13 : ((List.range 1024).all fun j => linkCheck (13312+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked13 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words13 BottomCase.words13 13312 row
    cache0_13 cache1_13 cache2_13 cache3_13 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 13) (BottomCase.wordsAt 13) (1024*13) row = true := hc
  rw [linkChunkCheck_eq 13 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 14. -/
noncomputable def cache0_14 : LinkCache := ⟨10,BottomEmpty.beta0Words10,BottomEmpty.beta0Words11⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 14. -/
noncomputable def cache1_14 : LinkCache := ⟨1,BottomEmpty.beta1Words1,BottomEmpty.beta1Words2⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 14. -/
noncomputable def cache2_14 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 14. -/
noncomputable def cache3_14 : LinkCache := ⟨6,BottomForest.packed1500.rInput,BottomForest.packed1750.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 14. -/
theorem cachedLinkChecked14 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words14 BottomCase.words14 14336 cache0_14 cache1_14 cache2_14 cache3_14 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 14. -/
theorem linkChecked14 : ((List.range 1024).all fun j => linkCheck (14336+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked14 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words14 BottomCase.words14 14336 row
    cache0_14 cache1_14 cache2_14 cache3_14 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 14) (BottomCase.wordsAt 14) (1024*14) row = true := hc
  rw [linkChunkCheck_eq 14 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 15. -/
noncomputable def cache0_15 : LinkCache := ⟨11,BottomEmpty.beta0Words11,BottomEmpty.beta0Words12⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 15. -/
noncomputable def cache1_15 : LinkCache := ⟨1,BottomEmpty.beta1Words1,BottomEmpty.beta1Words2⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 15. -/
noncomputable def cache2_15 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 15. -/
noncomputable def cache3_15 : LinkCache := ⟨6,BottomForest.packed1500.rInput,BottomForest.packed1750.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 15. -/
theorem cachedLinkChecked15 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words15 BottomCase.words15 15360 cache0_15 cache1_15 cache2_15 cache3_15 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 15. -/
theorem linkChecked15 : ((List.range 1024).all fun j => linkCheck (15360+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked15 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words15 BottomCase.words15 15360 row
    cache0_15 cache1_15 cache2_15 cache3_15 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 15) (BottomCase.wordsAt 15) (1024*15) row = true := hc
  rw [linkChunkCheck_eq 15 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 16. -/
noncomputable def cache0_16 : LinkCache := ⟨12,BottomEmpty.beta0Words12,BottomEmpty.beta0Words13⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 16. -/
noncomputable def cache1_16 : LinkCache := ⟨1,BottomEmpty.beta1Words1,BottomEmpty.beta1Words2⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 16. -/
noncomputable def cache2_16 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 16. -/
noncomputable def cache3_16 : LinkCache := ⟨7,BottomForest.packed1750.rInput,BottomForest.packed2000.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 16. -/
theorem cachedLinkChecked16 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words16 BottomCase.words16 16384 cache0_16 cache1_16 cache2_16 cache3_16 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 16. -/
theorem linkChecked16 : ((List.range 1024).all fun j => linkCheck (16384+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked16 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words16 BottomCase.words16 16384 row
    cache0_16 cache1_16 cache2_16 cache3_16 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 16) (BottomCase.wordsAt 16) (1024*16) row = true := hc
  rw [linkChunkCheck_eq 16 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 17. -/
noncomputable def cache0_17 : LinkCache := ⟨12,BottomEmpty.beta0Words12,BottomEmpty.beta0Words13⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 17. -/
noncomputable def cache1_17 : LinkCache := ⟨2,BottomEmpty.beta1Words2,BottomEmpty.beta1Words3⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 17. -/
noncomputable def cache2_17 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 17. -/
noncomputable def cache3_17 : LinkCache := ⟨7,BottomForest.packed1750.rInput,BottomForest.packed2000.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 17. -/
theorem cachedLinkChecked17 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words17 BottomCase.words17 17408 cache0_17 cache1_17 cache2_17 cache3_17 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 17. -/
theorem linkChecked17 : ((List.range 1024).all fun j => linkCheck (17408+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked17 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words17 BottomCase.words17 17408 row
    cache0_17 cache1_17 cache2_17 cache3_17 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 17) (BottomCase.wordsAt 17) (1024*17) row = true := hc
  rw [linkChunkCheck_eq 17 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 18. -/
noncomputable def cache0_18 : LinkCache := ⟨13,BottomEmpty.beta0Words13,BottomEmpty.beta0Words14⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 18. -/
noncomputable def cache1_18 : LinkCache := ⟨2,BottomEmpty.beta1Words2,BottomEmpty.beta1Words3⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 18. -/
noncomputable def cache2_18 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 18. -/
noncomputable def cache3_18 : LinkCache := ⟨8,BottomForest.packed2000.rInput,BottomForest.packed2250.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 18. -/
theorem cachedLinkChecked18 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words18 BottomCase.words18 18432 cache0_18 cache1_18 cache2_18 cache3_18 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 18. -/
theorem linkChecked18 : ((List.range 1024).all fun j => linkCheck (18432+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked18 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words18 BottomCase.words18 18432 row
    cache0_18 cache1_18 cache2_18 cache3_18 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 18) (BottomCase.wordsAt 18) (1024*18) row = true := hc
  rw [linkChunkCheck_eq 18 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 19. -/
noncomputable def cache0_19 : LinkCache := ⟨14,BottomEmpty.beta0Words14,BottomEmpty.beta0Words15⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 19. -/
noncomputable def cache1_19 : LinkCache := ⟨2,BottomEmpty.beta1Words2,BottomEmpty.beta1Words3⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 19. -/
noncomputable def cache2_19 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 19. -/
noncomputable def cache3_19 : LinkCache := ⟨8,BottomForest.packed2000.rInput,BottomForest.packed2250.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 19. -/
theorem cachedLinkChecked19 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words19 BottomCase.words19 19456 cache0_19 cache1_19 cache2_19 cache3_19 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 19. -/
theorem linkChecked19 : ((List.range 1024).all fun j => linkCheck (19456+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked19 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words19 BottomCase.words19 19456 row
    cache0_19 cache1_19 cache2_19 cache3_19 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 19) (BottomCase.wordsAt 19) (1024*19) row = true := hc
  rw [linkChunkCheck_eq 19 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 20. -/
noncomputable def cache0_20 : LinkCache := ⟨15,BottomEmpty.beta0Words15,BottomEmpty.beta0Words16⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 20. -/
noncomputable def cache1_20 : LinkCache := ⟨2,BottomEmpty.beta1Words2,BottomEmpty.beta1Words3⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 20. -/
noncomputable def cache2_20 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 20. -/
noncomputable def cache3_20 : LinkCache := ⟨8,BottomForest.packed2000.rInput,BottomForest.packed2250.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 20. -/
theorem cachedLinkChecked20 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words20 BottomCase.words20 20480 cache0_20 cache1_20 cache2_20 cache3_20 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 20. -/
theorem linkChecked20 : ((List.range 1024).all fun j => linkCheck (20480+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked20 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words20 BottomCase.words20 20480 row
    cache0_20 cache1_20 cache2_20 cache3_20 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 20) (BottomCase.wordsAt 20) (1024*20) row = true := hc
  rw [linkChunkCheck_eq 20 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 21. -/
noncomputable def cache0_21 : LinkCache := ⟨16,BottomEmpty.beta0Words16,BottomEmpty.beta0Words17⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 21. -/
noncomputable def cache1_21 : LinkCache := ⟨2,BottomEmpty.beta1Words2,BottomEmpty.beta1Words3⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 21. -/
noncomputable def cache2_21 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 21. -/
noncomputable def cache3_21 : LinkCache := ⟨9,BottomForest.packed2250.rInput,BottomForest.packed2500.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 21. -/
theorem cachedLinkChecked21 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words21 BottomCase.words21 21504 cache0_21 cache1_21 cache2_21 cache3_21 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 21. -/
theorem linkChecked21 : ((List.range 1024).all fun j => linkCheck (21504+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked21 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words21 BottomCase.words21 21504 row
    cache0_21 cache1_21 cache2_21 cache3_21 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 21) (BottomCase.wordsAt 21) (1024*21) row = true := hc
  rw [linkChunkCheck_eq 21 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 22. -/
noncomputable def cache0_22 : LinkCache := ⟨16,BottomEmpty.beta0Words16,BottomEmpty.beta0Words17⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 22. -/
noncomputable def cache1_22 : LinkCache := ⟨2,BottomEmpty.beta1Words2,BottomEmpty.beta1Words3⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 22. -/
noncomputable def cache2_22 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 22. -/
noncomputable def cache3_22 : LinkCache := ⟨9,BottomForest.packed2250.rInput,BottomForest.packed2500.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 22. -/
theorem cachedLinkChecked22 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words22 BottomCase.words22 22528 cache0_22 cache1_22 cache2_22 cache3_22 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 22. -/
theorem linkChecked22 : ((List.range 1024).all fun j => linkCheck (22528+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked22 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words22 BottomCase.words22 22528 row
    cache0_22 cache1_22 cache2_22 cache3_22 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 22) (BottomCase.wordsAt 22) (1024*22) row = true := hc
  rw [linkChunkCheck_eq 22 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 23. -/
noncomputable def cache0_23 : LinkCache := ⟨17,BottomEmpty.beta0Words17,BottomEmpty.beta0Words18⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 23. -/
noncomputable def cache1_23 : LinkCache := ⟨2,BottomEmpty.beta1Words2,BottomEmpty.beta1Words3⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 23. -/
noncomputable def cache2_23 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 23. -/
noncomputable def cache3_23 : LinkCache := ⟨9,BottomForest.packed2250.rInput,BottomForest.packed2500.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 23. -/
theorem cachedLinkChecked23 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words23 BottomCase.words23 23552 cache0_23 cache1_23 cache2_23 cache3_23 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 23. -/
theorem linkChecked23 : ((List.range 1024).all fun j => linkCheck (23552+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked23 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words23 BottomCase.words23 23552 row
    cache0_23 cache1_23 cache2_23 cache3_23 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 23) (BottomCase.wordsAt 23) (1024*23) row = true := hc
  rw [linkChunkCheck_eq 23 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 24. -/
noncomputable def cache0_24 : LinkCache := ⟨18,BottomEmpty.beta0Words18,BottomEmpty.beta0Words19⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 24. -/
noncomputable def cache1_24 : LinkCache := ⟨2,BottomEmpty.beta1Words2,BottomEmpty.beta1Words3⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 24. -/
noncomputable def cache2_24 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 24. -/
noncomputable def cache3_24 : LinkCache := ⟨10,BottomForest.packed2500.rInput,BottomForest.packed2750.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 24. -/
theorem cachedLinkChecked24 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words24 BottomCase.words24 24576 cache0_24 cache1_24 cache2_24 cache3_24 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 24. -/
theorem linkChecked24 : ((List.range 1024).all fun j => linkCheck (24576+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked24 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words24 BottomCase.words24 24576 row
    cache0_24 cache1_24 cache2_24 cache3_24 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 24) (BottomCase.wordsAt 24) (1024*24) row = true := hc
  rw [linkChunkCheck_eq 24 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 25. -/
noncomputable def cache0_25 : LinkCache := ⟨19,BottomEmpty.beta0Words19,BottomEmpty.beta0Words20⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 25. -/
noncomputable def cache1_25 : LinkCache := ⟨2,BottomEmpty.beta1Words2,BottomEmpty.beta1Words3⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 25. -/
noncomputable def cache2_25 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 25. -/
noncomputable def cache3_25 : LinkCache := ⟨10,BottomForest.packed2500.rInput,BottomForest.packed2750.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 25. -/
theorem cachedLinkChecked25 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words25 BottomCase.words25 25600 cache0_25 cache1_25 cache2_25 cache3_25 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 25. -/
theorem linkChecked25 : ((List.range 1024).all fun j => linkCheck (25600+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked25 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words25 BottomCase.words25 25600 row
    cache0_25 cache1_25 cache2_25 cache3_25 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 25) (BottomCase.wordsAt 25) (1024*25) row = true := hc
  rw [linkChunkCheck_eq 25 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 26. -/
noncomputable def cache0_26 : LinkCache := ⟨20,BottomEmpty.beta0Words20,BottomEmpty.beta0Words21⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 26. -/
noncomputable def cache1_26 : LinkCache := ⟨3,BottomEmpty.beta1Words3,BottomEmpty.beta1Words4⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 26. -/
noncomputable def cache2_26 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 26. -/
noncomputable def cache3_26 : LinkCache := ⟨11,BottomForest.packed2750.rInput,BottomForest.packed3000.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 26. -/
theorem cachedLinkChecked26 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words26 BottomCase.words26 26624 cache0_26 cache1_26 cache2_26 cache3_26 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 26. -/
theorem linkChecked26 : ((List.range 1024).all fun j => linkCheck (26624+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked26 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words26 BottomCase.words26 26624 row
    cache0_26 cache1_26 cache2_26 cache3_26 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 26) (BottomCase.wordsAt 26) (1024*26) row = true := hc
  rw [linkChunkCheck_eq 26 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 27. -/
noncomputable def cache0_27 : LinkCache := ⟨20,BottomEmpty.beta0Words20,BottomEmpty.beta0Words21⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 27. -/
noncomputable def cache1_27 : LinkCache := ⟨3,BottomEmpty.beta1Words3,BottomEmpty.beta1Words4⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 27. -/
noncomputable def cache2_27 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 27. -/
noncomputable def cache3_27 : LinkCache := ⟨11,BottomForest.packed2750.rInput,BottomForest.packed3000.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 27. -/
theorem cachedLinkChecked27 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words27 BottomCase.words27 27648 cache0_27 cache1_27 cache2_27 cache3_27 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 27. -/
theorem linkChecked27 : ((List.range 1024).all fun j => linkCheck (27648+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked27 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words27 BottomCase.words27 27648 row
    cache0_27 cache1_27 cache2_27 cache3_27 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 27) (BottomCase.wordsAt 27) (1024*27) row = true := hc
  rw [linkChunkCheck_eq 27 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 28. -/
noncomputable def cache0_28 : LinkCache := ⟨21,BottomEmpty.beta0Words21,BottomEmpty.beta0Words22⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 28. -/
noncomputable def cache1_28 : LinkCache := ⟨3,BottomEmpty.beta1Words3,BottomEmpty.beta1Words4⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 28. -/
noncomputable def cache2_28 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 28. -/
noncomputable def cache3_28 : LinkCache := ⟨12,BottomForest.packed3000.rInput,BottomForest.packed3250.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 28. -/
theorem cachedLinkChecked28 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words28 BottomCase.words28 28672 cache0_28 cache1_28 cache2_28 cache3_28 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 28. -/
theorem linkChecked28 : ((List.range 1024).all fun j => linkCheck (28672+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked28 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words28 BottomCase.words28 28672 row
    cache0_28 cache1_28 cache2_28 cache3_28 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 28) (BottomCase.wordsAt 28) (1024*28) row = true := hc
  rw [linkChunkCheck_eq 28 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 29. -/
noncomputable def cache0_29 : LinkCache := ⟨22,BottomEmpty.beta0Words22,BottomEmpty.beta0Words23⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 29. -/
noncomputable def cache1_29 : LinkCache := ⟨3,BottomEmpty.beta1Words3,BottomEmpty.beta1Words4⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 29. -/
noncomputable def cache2_29 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 29. -/
noncomputable def cache3_29 : LinkCache := ⟨12,BottomForest.packed3000.rInput,BottomForest.packed3250.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 29. -/
theorem cachedLinkChecked29 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words29 BottomCase.words29 29696 cache0_29 cache1_29 cache2_29 cache3_29 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 29. -/
theorem linkChecked29 : ((List.range 1024).all fun j => linkCheck (29696+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked29 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words29 BottomCase.words29 29696 row
    cache0_29 cache1_29 cache2_29 cache3_29 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 29) (BottomCase.wordsAt 29) (1024*29) row = true := hc
  rw [linkChunkCheck_eq 29 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 30. -/
noncomputable def cache0_30 : LinkCache := ⟨23,BottomEmpty.beta0Words23,BottomEmpty.beta0Words24⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 30. -/
noncomputable def cache1_30 : LinkCache := ⟨3,BottomEmpty.beta1Words3,BottomEmpty.beta1Words4⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 30. -/
noncomputable def cache2_30 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 30. -/
noncomputable def cache3_30 : LinkCache := ⟨13,BottomForest.packed3250.rInput,BottomForest.packed3500.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 30. -/
theorem cachedLinkChecked30 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words30 BottomCase.words30 30720 cache0_30 cache1_30 cache2_30 cache3_30 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 30. -/
theorem linkChecked30 : ((List.range 1024).all fun j => linkCheck (30720+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked30 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words30 BottomCase.words30 30720 row
    cache0_30 cache1_30 cache2_30 cache3_30 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 30) (BottomCase.wordsAt 30) (1024*30) row = true := hc
  rw [linkChunkCheck_eq 30 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 31. -/
noncomputable def cache0_31 : LinkCache := ⟨23,BottomEmpty.beta0Words23,BottomEmpty.beta0Words24⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 31. -/
noncomputable def cache1_31 : LinkCache := ⟨3,BottomEmpty.beta1Words3,BottomEmpty.beta1Words4⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 31. -/
noncomputable def cache2_31 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 31. -/
noncomputable def cache3_31 : LinkCache := ⟨13,BottomForest.packed3250.rInput,BottomForest.packed3500.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 31. -/
theorem cachedLinkChecked31 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words31 BottomCase.words31 31744 cache0_31 cache1_31 cache2_31 cache3_31 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 31. -/
theorem linkChecked31 : ((List.range 1024).all fun j => linkCheck (31744+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked31 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words31 BottomCase.words31 31744 row
    cache0_31 cache1_31 cache2_31 cache3_31 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 31) (BottomCase.wordsAt 31) (1024*31) row = true := hc
  rw [linkChunkCheck_eq 31 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
#print axioms linkChecked0
end Quantum.Stabilizer.Homological.BB.Bravyi360.BottomShallow
