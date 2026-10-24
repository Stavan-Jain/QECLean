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
/-- Adjacent family 0 data blocks for census chunk 32. -/
noncomputable def cache0_32 : LinkCache := ⟨24,BottomEmpty.beta0Words24,BottomEmpty.beta0Words25⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 32. -/
noncomputable def cache1_32 : LinkCache := ⟨3,BottomEmpty.beta1Words3,BottomEmpty.beta1Words4⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 32. -/
noncomputable def cache2_32 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 32. -/
noncomputable def cache3_32 : LinkCache := ⟨14,BottomForest.packed3500.rInput,BottomForest.packed3750.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 32. -/
theorem cachedLinkChecked32 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words32 BottomCase.words32 32768 cache0_32 cache1_32 cache2_32 cache3_32 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 32. -/
theorem linkChecked32 : ((List.range 1024).all fun j => linkCheck (32768+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked32 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words32 BottomCase.words32 32768 row
    cache0_32 cache1_32 cache2_32 cache3_32 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 32) (BottomCase.wordsAt 32) (1024*32) row = true := hc
  rw [linkChunkCheck_eq 32 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 33. -/
noncomputable def cache0_33 : LinkCache := ⟨25,BottomEmpty.beta0Words25,BottomEmpty.beta0Words26⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 33. -/
noncomputable def cache1_33 : LinkCache := ⟨3,BottomEmpty.beta1Words3,BottomEmpty.beta1Words4⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 33. -/
noncomputable def cache2_33 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 33. -/
noncomputable def cache3_33 : LinkCache := ⟨14,BottomForest.packed3500.rInput,BottomForest.packed3750.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 33. -/
theorem cachedLinkChecked33 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words33 BottomCase.words33 33792 cache0_33 cache1_33 cache2_33 cache3_33 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 33. -/
theorem linkChecked33 : ((List.range 1024).all fun j => linkCheck (33792+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked33 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words33 BottomCase.words33 33792 row
    cache0_33 cache1_33 cache2_33 cache3_33 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 33) (BottomCase.wordsAt 33) (1024*33) row = true := hc
  rw [linkChunkCheck_eq 33 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 34. -/
noncomputable def cache0_34 : LinkCache := ⟨26,BottomEmpty.beta0Words26,BottomEmpty.beta0Words27⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 34. -/
noncomputable def cache1_34 : LinkCache := ⟨3,BottomEmpty.beta1Words3,BottomEmpty.beta1Words4⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 34. -/
noncomputable def cache2_34 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 34. -/
noncomputable def cache3_34 : LinkCache := ⟨14,BottomForest.packed3500.rInput,BottomForest.packed3750.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 34. -/
theorem cachedLinkChecked34 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words34 BottomCase.words34 34816 cache0_34 cache1_34 cache2_34 cache3_34 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 34. -/
theorem linkChecked34 : ((List.range 1024).all fun j => linkCheck (34816+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked34 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words34 BottomCase.words34 34816 row
    cache0_34 cache1_34 cache2_34 cache3_34 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 34) (BottomCase.wordsAt 34) (1024*34) row = true := hc
  rw [linkChunkCheck_eq 34 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 35. -/
noncomputable def cache0_35 : LinkCache := ⟨27,BottomEmpty.beta0Words27,BottomEmpty.beta0Words28⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 35. -/
noncomputable def cache1_35 : LinkCache := ⟨3,BottomEmpty.beta1Words3,BottomEmpty.beta1Words4⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 35. -/
noncomputable def cache2_35 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 35. -/
noncomputable def cache3_35 : LinkCache := ⟨15,BottomForest.packed3750.rInput,BottomForest.packed4000.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 35. -/
theorem cachedLinkChecked35 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words35 BottomCase.words35 35840 cache0_35 cache1_35 cache2_35 cache3_35 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 35. -/
theorem linkChecked35 : ((List.range 1024).all fun j => linkCheck (35840+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked35 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words35 BottomCase.words35 35840 row
    cache0_35 cache1_35 cache2_35 cache3_35 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 35) (BottomCase.wordsAt 35) (1024*35) row = true := hc
  rw [linkChunkCheck_eq 35 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 36. -/
noncomputable def cache0_36 : LinkCache := ⟨27,BottomEmpty.beta0Words27,BottomEmpty.beta0Words28⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 36. -/
noncomputable def cache1_36 : LinkCache := ⟨4,BottomEmpty.beta1Words4,BottomEmpty.beta1Words5⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 36. -/
noncomputable def cache2_36 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 36. -/
noncomputable def cache3_36 : LinkCache := ⟨15,BottomForest.packed3750.rInput,BottomForest.packed4000.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 36. -/
theorem cachedLinkChecked36 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words36 BottomCase.words36 36864 cache0_36 cache1_36 cache2_36 cache3_36 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 36. -/
theorem linkChecked36 : ((List.range 1024).all fun j => linkCheck (36864+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked36 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words36 BottomCase.words36 36864 row
    cache0_36 cache1_36 cache2_36 cache3_36 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 36) (BottomCase.wordsAt 36) (1024*36) row = true := hc
  rw [linkChunkCheck_eq 36 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 37. -/
noncomputable def cache0_37 : LinkCache := ⟨28,BottomEmpty.beta0Words28,BottomEmpty.beta0Words29⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 37. -/
noncomputable def cache1_37 : LinkCache := ⟨4,BottomEmpty.beta1Words4,BottomEmpty.beta1Words5⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 37. -/
noncomputable def cache2_37 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 37. -/
noncomputable def cache3_37 : LinkCache := ⟨15,BottomForest.packed3750.rInput,BottomForest.packed4000.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 37. -/
theorem cachedLinkChecked37 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words37 BottomCase.words37 37888 cache0_37 cache1_37 cache2_37 cache3_37 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 37. -/
theorem linkChecked37 : ((List.range 1024).all fun j => linkCheck (37888+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked37 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words37 BottomCase.words37 37888 row
    cache0_37 cache1_37 cache2_37 cache3_37 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 37) (BottomCase.wordsAt 37) (1024*37) row = true := hc
  rw [linkChunkCheck_eq 37 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 38. -/
noncomputable def cache0_38 : LinkCache := ⟨29,BottomEmpty.beta0Words29,BottomEmpty.beta0Words30⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 38. -/
noncomputable def cache1_38 : LinkCache := ⟨4,BottomEmpty.beta1Words4,BottomEmpty.beta1Words5⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 38. -/
noncomputable def cache2_38 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 38. -/
noncomputable def cache3_38 : LinkCache := ⟨16,BottomForest.packed4000.rInput,BottomForest.packed4250.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 38. -/
theorem cachedLinkChecked38 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words38 BottomCase.words38 38912 cache0_38 cache1_38 cache2_38 cache3_38 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 38. -/
theorem linkChecked38 : ((List.range 1024).all fun j => linkCheck (38912+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked38 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words38 BottomCase.words38 38912 row
    cache0_38 cache1_38 cache2_38 cache3_38 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 38) (BottomCase.wordsAt 38) (1024*38) row = true := hc
  rw [linkChunkCheck_eq 38 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 39. -/
noncomputable def cache0_39 : LinkCache := ⟨30,BottomEmpty.beta0Words30,BottomEmpty.beta0Words31⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 39. -/
noncomputable def cache1_39 : LinkCache := ⟨4,BottomEmpty.beta1Words4,BottomEmpty.beta1Words5⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 39. -/
noncomputable def cache2_39 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 39. -/
noncomputable def cache3_39 : LinkCache := ⟨17,BottomForest.packed4250.rInput,BottomForest.packed4500.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 39. -/
theorem cachedLinkChecked39 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words39 BottomCase.words39 39936 cache0_39 cache1_39 cache2_39 cache3_39 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 39. -/
theorem linkChecked39 : ((List.range 1024).all fun j => linkCheck (39936+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked39 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words39 BottomCase.words39 39936 row
    cache0_39 cache1_39 cache2_39 cache3_39 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 39) (BottomCase.wordsAt 39) (1024*39) row = true := hc
  rw [linkChunkCheck_eq 39 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 40. -/
noncomputable def cache0_40 : LinkCache := ⟨30,BottomEmpty.beta0Words30,BottomEmpty.beta0Words31⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 40. -/
noncomputable def cache1_40 : LinkCache := ⟨4,BottomEmpty.beta1Words4,BottomEmpty.beta1Words5⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 40. -/
noncomputable def cache2_40 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 40. -/
noncomputable def cache3_40 : LinkCache := ⟨17,BottomForest.packed4250.rInput,BottomForest.packed4500.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 40. -/
theorem cachedLinkChecked40 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words40 BottomCase.words40 40960 cache0_40 cache1_40 cache2_40 cache3_40 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 40. -/
theorem linkChecked40 : ((List.range 1024).all fun j => linkCheck (40960+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked40 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words40 BottomCase.words40 40960 row
    cache0_40 cache1_40 cache2_40 cache3_40 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 40) (BottomCase.wordsAt 40) (1024*40) row = true := hc
  rw [linkChunkCheck_eq 40 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 41. -/
noncomputable def cache0_41 : LinkCache := ⟨31,BottomEmpty.beta0Words31,BottomEmpty.beta0Words32⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 41. -/
noncomputable def cache1_41 : LinkCache := ⟨4,BottomEmpty.beta1Words4,BottomEmpty.beta1Words5⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 41. -/
noncomputable def cache2_41 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 41. -/
noncomputable def cache3_41 : LinkCache := ⟨18,BottomForest.packed4500.rInput,BottomForest.packed4750.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 41. -/
theorem cachedLinkChecked41 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words41 BottomCase.words41 41984 cache0_41 cache1_41 cache2_41 cache3_41 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 41. -/
theorem linkChecked41 : ((List.range 1024).all fun j => linkCheck (41984+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked41 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words41 BottomCase.words41 41984 row
    cache0_41 cache1_41 cache2_41 cache3_41 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 41) (BottomCase.wordsAt 41) (1024*41) row = true := hc
  rw [linkChunkCheck_eq 41 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 42. -/
noncomputable def cache0_42 : LinkCache := ⟨32,BottomEmpty.beta0Words32,BottomEmpty.beta0Words33⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 42. -/
noncomputable def cache1_42 : LinkCache := ⟨4,BottomEmpty.beta1Words4,BottomEmpty.beta1Words5⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 42. -/
noncomputable def cache2_42 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 42. -/
noncomputable def cache3_42 : LinkCache := ⟨18,BottomForest.packed4500.rInput,BottomForest.packed4750.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 42. -/
theorem cachedLinkChecked42 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words42 BottomCase.words42 43008 cache0_42 cache1_42 cache2_42 cache3_42 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 42. -/
theorem linkChecked42 : ((List.range 1024).all fun j => linkCheck (43008+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked42 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words42 BottomCase.words42 43008 row
    cache0_42 cache1_42 cache2_42 cache3_42 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 42) (BottomCase.wordsAt 42) (1024*42) row = true := hc
  rw [linkChunkCheck_eq 42 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 43. -/
noncomputable def cache0_43 : LinkCache := ⟨33,BottomEmpty.beta0Words33,BottomEmpty.beta0Words34⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 43. -/
noncomputable def cache1_43 : LinkCache := ⟨4,BottomEmpty.beta1Words4,BottomEmpty.beta1Words5⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 43. -/
noncomputable def cache2_43 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 43. -/
noncomputable def cache3_43 : LinkCache := ⟨18,BottomForest.packed4500.rInput,BottomForest.packed4750.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 43. -/
theorem cachedLinkChecked43 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words43 BottomCase.words43 44032 cache0_43 cache1_43 cache2_43 cache3_43 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 43. -/
theorem linkChecked43 : ((List.range 1024).all fun j => linkCheck (44032+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked43 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words43 BottomCase.words43 44032 row
    cache0_43 cache1_43 cache2_43 cache3_43 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 43) (BottomCase.wordsAt 43) (1024*43) row = true := hc
  rw [linkChunkCheck_eq 43 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 44. -/
noncomputable def cache0_44 : LinkCache := ⟨34,BottomEmpty.beta0Words34,BottomEmpty.beta0Words35⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 44. -/
noncomputable def cache1_44 : LinkCache := ⟨4,BottomEmpty.beta1Words4,BottomEmpty.beta1Words5⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 44. -/
noncomputable def cache2_44 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 44. -/
noncomputable def cache3_44 : LinkCache := ⟨19,BottomForest.packed4750.rInput,BottomForest.packed5000.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 44. -/
theorem cachedLinkChecked44 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words44 BottomCase.words44 45056 cache0_44 cache1_44 cache2_44 cache3_44 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 44. -/
theorem linkChecked44 : ((List.range 1024).all fun j => linkCheck (45056+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked44 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words44 BottomCase.words44 45056 row
    cache0_44 cache1_44 cache2_44 cache3_44 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 44) (BottomCase.wordsAt 44) (1024*44) row = true := hc
  rw [linkChunkCheck_eq 44 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 45. -/
noncomputable def cache0_45 : LinkCache := ⟨34,BottomEmpty.beta0Words34,BottomEmpty.beta0Words35⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 45. -/
noncomputable def cache1_45 : LinkCache := ⟨4,BottomEmpty.beta1Words4,BottomEmpty.beta1Words5⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 45. -/
noncomputable def cache2_45 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 45. -/
noncomputable def cache3_45 : LinkCache := ⟨19,BottomForest.packed4750.rInput,BottomForest.packed5000.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 45. -/
theorem cachedLinkChecked45 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words45 BottomCase.words45 46080 cache0_45 cache1_45 cache2_45 cache3_45 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 45. -/
theorem linkChecked45 : ((List.range 1024).all fun j => linkCheck (46080+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked45 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words45 BottomCase.words45 46080 row
    cache0_45 cache1_45 cache2_45 cache3_45 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 45) (BottomCase.wordsAt 45) (1024*45) row = true := hc
  rw [linkChunkCheck_eq 45 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 46. -/
noncomputable def cache0_46 : LinkCache := ⟨35,BottomEmpty.beta0Words35,BottomEmpty.beta0Words36⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 46. -/
noncomputable def cache1_46 : LinkCache := ⟨4,BottomEmpty.beta1Words4,BottomEmpty.beta1Words5⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 46. -/
noncomputable def cache2_46 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 46. -/
noncomputable def cache3_46 : LinkCache := ⟨20,BottomForest.packed5000.rInput,BottomForest.packed5250.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 46. -/
theorem cachedLinkChecked46 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words46 BottomCase.words46 47104 cache0_46 cache1_46 cache2_46 cache3_46 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 46. -/
theorem linkChecked46 : ((List.range 1024).all fun j => linkCheck (47104+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked46 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words46 BottomCase.words46 47104 row
    cache0_46 cache1_46 cache2_46 cache3_46 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 46) (BottomCase.wordsAt 46) (1024*46) row = true := hc
  rw [linkChunkCheck_eq 46 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 47. -/
noncomputable def cache0_47 : LinkCache := ⟨36,BottomEmpty.beta0Words36,BottomEmpty.beta0Words37⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 47. -/
noncomputable def cache1_47 : LinkCache := ⟨5,BottomEmpty.beta1Words5,BottomEmpty.beta1Words6⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 47. -/
noncomputable def cache2_47 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 47. -/
noncomputable def cache3_47 : LinkCache := ⟨20,BottomForest.packed5000.rInput,BottomForest.packed5250.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 47. -/
theorem cachedLinkChecked47 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words47 BottomCase.words47 48128 cache0_47 cache1_47 cache2_47 cache3_47 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 47. -/
theorem linkChecked47 : ((List.range 1024).all fun j => linkCheck (48128+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked47 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words47 BottomCase.words47 48128 row
    cache0_47 cache1_47 cache2_47 cache3_47 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 47) (BottomCase.wordsAt 47) (1024*47) row = true := hc
  rw [linkChunkCheck_eq 47 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 48. -/
noncomputable def cache0_48 : LinkCache := ⟨37,BottomEmpty.beta0Words37,BottomEmpty.beta0Words38⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 48. -/
noncomputable def cache1_48 : LinkCache := ⟨5,BottomEmpty.beta1Words5,BottomEmpty.beta1Words6⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 48. -/
noncomputable def cache2_48 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 48. -/
noncomputable def cache3_48 : LinkCache := ⟨21,BottomForest.packed5250.rInput,BottomForest.packed5500.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 48. -/
theorem cachedLinkChecked48 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words48 BottomCase.words48 49152 cache0_48 cache1_48 cache2_48 cache3_48 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 48. -/
theorem linkChecked48 : ((List.range 1024).all fun j => linkCheck (49152+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked48 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words48 BottomCase.words48 49152 row
    cache0_48 cache1_48 cache2_48 cache3_48 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 48) (BottomCase.wordsAt 48) (1024*48) row = true := hc
  rw [linkChunkCheck_eq 48 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 49. -/
noncomputable def cache0_49 : LinkCache := ⟨38,BottomEmpty.beta0Words38,BottomEmpty.beta0Words39⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 49. -/
noncomputable def cache1_49 : LinkCache := ⟨5,BottomEmpty.beta1Words5,BottomEmpty.beta1Words6⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 49. -/
noncomputable def cache2_49 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 49. -/
noncomputable def cache3_49 : LinkCache := ⟨21,BottomForest.packed5250.rInput,BottomForest.packed5500.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 49. -/
theorem cachedLinkChecked49 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words49 BottomCase.words49 50176 cache0_49 cache1_49 cache2_49 cache3_49 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 49. -/
theorem linkChecked49 : ((List.range 1024).all fun j => linkCheck (50176+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked49 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words49 BottomCase.words49 50176 row
    cache0_49 cache1_49 cache2_49 cache3_49 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 49) (BottomCase.wordsAt 49) (1024*49) row = true := hc
  rw [linkChunkCheck_eq 49 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 50. -/
noncomputable def cache0_50 : LinkCache := ⟨39,BottomEmpty.beta0Words39,BottomEmpty.beta0Words40⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 50. -/
noncomputable def cache1_50 : LinkCache := ⟨5,BottomEmpty.beta1Words5,BottomEmpty.beta1Words6⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 50. -/
noncomputable def cache2_50 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 50. -/
noncomputable def cache3_50 : LinkCache := ⟨21,BottomForest.packed5250.rInput,BottomForest.packed5500.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 50. -/
theorem cachedLinkChecked50 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words50 BottomCase.words50 51200 cache0_50 cache1_50 cache2_50 cache3_50 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 50. -/
theorem linkChecked50 : ((List.range 1024).all fun j => linkCheck (51200+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked50 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words50 BottomCase.words50 51200 row
    cache0_50 cache1_50 cache2_50 cache3_50 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 50) (BottomCase.wordsAt 50) (1024*50) row = true := hc
  rw [linkChunkCheck_eq 50 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 51. -/
noncomputable def cache0_51 : LinkCache := ⟨39,BottomEmpty.beta0Words39,BottomEmpty.beta0Words40⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 51. -/
noncomputable def cache1_51 : LinkCache := ⟨5,BottomEmpty.beta1Words5,BottomEmpty.beta1Words6⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 51. -/
noncomputable def cache2_51 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 51. -/
noncomputable def cache3_51 : LinkCache := ⟨21,BottomForest.packed5250.rInput,BottomForest.packed5500.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 51. -/
theorem cachedLinkChecked51 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words51 BottomCase.words51 52224 cache0_51 cache1_51 cache2_51 cache3_51 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 51. -/
theorem linkChecked51 : ((List.range 1024).all fun j => linkCheck (52224+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked51 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words51 BottomCase.words51 52224 row
    cache0_51 cache1_51 cache2_51 cache3_51 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 51) (BottomCase.wordsAt 51) (1024*51) row = true := hc
  rw [linkChunkCheck_eq 51 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 52. -/
noncomputable def cache0_52 : LinkCache := ⟨40,BottomEmpty.beta0Words40,BottomEmpty.beta0Words41⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 52. -/
noncomputable def cache1_52 : LinkCache := ⟨5,BottomEmpty.beta1Words5,BottomEmpty.beta1Words6⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 52. -/
noncomputable def cache2_52 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 52. -/
noncomputable def cache3_52 : LinkCache := ⟨22,BottomForest.packed5500.rInput,BottomForest.packed5750.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 52. -/
theorem cachedLinkChecked52 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words52 BottomCase.words52 53248 cache0_52 cache1_52 cache2_52 cache3_52 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 52. -/
theorem linkChecked52 : ((List.range 1024).all fun j => linkCheck (53248+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked52 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words52 BottomCase.words52 53248 row
    cache0_52 cache1_52 cache2_52 cache3_52 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 52) (BottomCase.wordsAt 52) (1024*52) row = true := hc
  rw [linkChunkCheck_eq 52 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 53. -/
noncomputable def cache0_53 : LinkCache := ⟨41,BottomEmpty.beta0Words41,BottomEmpty.beta0Words42⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 53. -/
noncomputable def cache1_53 : LinkCache := ⟨5,BottomEmpty.beta1Words5,BottomEmpty.beta1Words6⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 53. -/
noncomputable def cache2_53 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 53. -/
noncomputable def cache3_53 : LinkCache := ⟨22,BottomForest.packed5500.rInput,BottomForest.packed5750.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 53. -/
theorem cachedLinkChecked53 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words53 BottomCase.words53 54272 cache0_53 cache1_53 cache2_53 cache3_53 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 53. -/
theorem linkChecked53 : ((List.range 1024).all fun j => linkCheck (54272+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked53 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words53 BottomCase.words53 54272 row
    cache0_53 cache1_53 cache2_53 cache3_53 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 53) (BottomCase.wordsAt 53) (1024*53) row = true := hc
  rw [linkChunkCheck_eq 53 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 54. -/
noncomputable def cache0_54 : LinkCache := ⟨42,BottomEmpty.beta0Words42,BottomEmpty.beta0Words43⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 54. -/
noncomputable def cache1_54 : LinkCache := ⟨5,BottomEmpty.beta1Words5,BottomEmpty.beta1Words6⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 54. -/
noncomputable def cache2_54 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 54. -/
noncomputable def cache3_54 : LinkCache := ⟨23,BottomForest.packed5750.rInput,BottomForest.packed6000.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 54. -/
theorem cachedLinkChecked54 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words54 BottomCase.words54 55296 cache0_54 cache1_54 cache2_54 cache3_54 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 54. -/
theorem linkChecked54 : ((List.range 1024).all fun j => linkCheck (55296+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked54 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words54 BottomCase.words54 55296 row
    cache0_54 cache1_54 cache2_54 cache3_54 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 54) (BottomCase.wordsAt 54) (1024*54) row = true := hc
  rw [linkChunkCheck_eq 54 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 55. -/
noncomputable def cache0_55 : LinkCache := ⟨43,BottomEmpty.beta0Words43,BottomEmpty.beta0Words44⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 55. -/
noncomputable def cache1_55 : LinkCache := ⟨5,BottomEmpty.beta1Words5,BottomEmpty.beta1Words6⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 55. -/
noncomputable def cache2_55 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 55. -/
noncomputable def cache3_55 : LinkCache := ⟨23,BottomForest.packed5750.rInput,BottomForest.packed6000.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 55. -/
theorem cachedLinkChecked55 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words55 BottomCase.words55 56320 cache0_55 cache1_55 cache2_55 cache3_55 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 55. -/
theorem linkChecked55 : ((List.range 1024).all fun j => linkCheck (56320+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked55 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words55 BottomCase.words55 56320 row
    cache0_55 cache1_55 cache2_55 cache3_55 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 55) (BottomCase.wordsAt 55) (1024*55) row = true := hc
  rw [linkChunkCheck_eq 55 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 56. -/
noncomputable def cache0_56 : LinkCache := ⟨43,BottomEmpty.beta0Words43,BottomEmpty.beta0Words44⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 56. -/
noncomputable def cache1_56 : LinkCache := ⟨5,BottomEmpty.beta1Words5,BottomEmpty.beta1Words6⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 56. -/
noncomputable def cache2_56 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 56. -/
noncomputable def cache3_56 : LinkCache := ⟨23,BottomForest.packed5750.rInput,BottomForest.packed6000.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 56. -/
theorem cachedLinkChecked56 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words56 BottomCase.words56 57344 cache0_56 cache1_56 cache2_56 cache3_56 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 56. -/
theorem linkChecked56 : ((List.range 1024).all fun j => linkCheck (57344+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked56 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words56 BottomCase.words56 57344 row
    cache0_56 cache1_56 cache2_56 cache3_56 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 56) (BottomCase.wordsAt 56) (1024*56) row = true := hc
  rw [linkChunkCheck_eq 56 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 57. -/
noncomputable def cache0_57 : LinkCache := ⟨44,BottomEmpty.beta0Words44,BottomEmpty.beta0Words45⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 57. -/
noncomputable def cache1_57 : LinkCache := ⟨5,BottomEmpty.beta1Words5,BottomEmpty.beta1Words6⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 57. -/
noncomputable def cache2_57 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 57. -/
noncomputable def cache3_57 : LinkCache := ⟨24,BottomForest.packed6000.rInput,BottomForest.packed6250.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 57. -/
theorem cachedLinkChecked57 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words57 BottomCase.words57 58368 cache0_57 cache1_57 cache2_57 cache3_57 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 57. -/
theorem linkChecked57 : ((List.range 1024).all fun j => linkCheck (58368+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked57 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words57 BottomCase.words57 58368 row
    cache0_57 cache1_57 cache2_57 cache3_57 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 57) (BottomCase.wordsAt 57) (1024*57) row = true := hc
  rw [linkChunkCheck_eq 57 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 58. -/
noncomputable def cache0_58 : LinkCache := ⟨45,BottomEmpty.beta0Words45,BottomEmpty.beta0Words46⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 58. -/
noncomputable def cache1_58 : LinkCache := ⟨6,BottomEmpty.beta1Words6,BottomEmpty.beta1Words7⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 58. -/
noncomputable def cache2_58 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 58. -/
noncomputable def cache3_58 : LinkCache := ⟨24,BottomForest.packed6000.rInput,BottomForest.packed6250.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 58. -/
theorem cachedLinkChecked58 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words58 BottomCase.words58 59392 cache0_58 cache1_58 cache2_58 cache3_58 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 58. -/
theorem linkChecked58 : ((List.range 1024).all fun j => linkCheck (59392+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked58 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words58 BottomCase.words58 59392 row
    cache0_58 cache1_58 cache2_58 cache3_58 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 58) (BottomCase.wordsAt 58) (1024*58) row = true := hc
  rw [linkChunkCheck_eq 58 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 59. -/
noncomputable def cache0_59 : LinkCache := ⟨46,BottomEmpty.beta0Words46,BottomEmpty.beta0Words47⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 59. -/
noncomputable def cache1_59 : LinkCache := ⟨6,BottomEmpty.beta1Words6,BottomEmpty.beta1Words7⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 59. -/
noncomputable def cache2_59 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 59. -/
noncomputable def cache3_59 : LinkCache := ⟨25,BottomForest.packed6250.rInput,BottomForest.packed6500.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 59. -/
theorem cachedLinkChecked59 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words59 BottomCase.words59 60416 cache0_59 cache1_59 cache2_59 cache3_59 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 59. -/
theorem linkChecked59 : ((List.range 1024).all fun j => linkCheck (60416+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked59 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words59 BottomCase.words59 60416 row
    cache0_59 cache1_59 cache2_59 cache3_59 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 59) (BottomCase.wordsAt 59) (1024*59) row = true := hc
  rw [linkChunkCheck_eq 59 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 60. -/
noncomputable def cache0_60 : LinkCache := ⟨47,BottomEmpty.beta0Words47,BottomEmpty.beta0Words48⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 60. -/
noncomputable def cache1_60 : LinkCache := ⟨6,BottomEmpty.beta1Words6,BottomEmpty.beta1Words7⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 60. -/
noncomputable def cache2_60 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 60. -/
noncomputable def cache3_60 : LinkCache := ⟨25,BottomForest.packed6250.rInput,BottomForest.packed6500.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 60. -/
theorem cachedLinkChecked60 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words60 BottomCase.words60 61440 cache0_60 cache1_60 cache2_60 cache3_60 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 60. -/
theorem linkChecked60 : ((List.range 1024).all fun j => linkCheck (61440+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked60 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words60 BottomCase.words60 61440 row
    cache0_60 cache1_60 cache2_60 cache3_60 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 60) (BottomCase.wordsAt 60) (1024*60) row = true := hc
  rw [linkChunkCheck_eq 60 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 61. -/
noncomputable def cache0_61 : LinkCache := ⟨47,BottomEmpty.beta0Words47,BottomEmpty.beta0Words48⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 61. -/
noncomputable def cache1_61 : LinkCache := ⟨6,BottomEmpty.beta1Words6,BottomEmpty.beta1Words7⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 61. -/
noncomputable def cache2_61 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 61. -/
noncomputable def cache3_61 : LinkCache := ⟨26,BottomForest.packed6500.rInput,BottomForest.packed6750.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 61. -/
theorem cachedLinkChecked61 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words61 BottomCase.words61 62464 cache0_61 cache1_61 cache2_61 cache3_61 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 61. -/
theorem linkChecked61 : ((List.range 1024).all fun j => linkCheck (62464+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked61 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words61 BottomCase.words61 62464 row
    cache0_61 cache1_61 cache2_61 cache3_61 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 61) (BottomCase.wordsAt 61) (1024*61) row = true := hc
  rw [linkChunkCheck_eq 61 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 62. -/
noncomputable def cache0_62 : LinkCache := ⟨48,BottomEmpty.beta0Words48,BottomEmpty.beta0Words49⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 62. -/
noncomputable def cache1_62 : LinkCache := ⟨6,BottomEmpty.beta1Words6,BottomEmpty.beta1Words7⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 62. -/
noncomputable def cache2_62 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 62. -/
noncomputable def cache3_62 : LinkCache := ⟨26,BottomForest.packed6500.rInput,BottomForest.packed6750.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 62. -/
theorem cachedLinkChecked62 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words62 BottomCase.words62 63488 cache0_62 cache1_62 cache2_62 cache3_62 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 62. -/
theorem linkChecked62 : ((List.range 1024).all fun j => linkCheck (63488+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked62 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words62 BottomCase.words62 63488 row
    cache0_62 cache1_62 cache2_62 cache3_62 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 62) (BottomCase.wordsAt 62) (1024*62) row = true := hc
  rw [linkChunkCheck_eq 62 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 63. -/
noncomputable def cache0_63 : LinkCache := ⟨49,BottomEmpty.beta0Words49,BottomEmpty.beta0Words50⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 63. -/
noncomputable def cache1_63 : LinkCache := ⟨6,BottomEmpty.beta1Words6,BottomEmpty.beta1Words7⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 63. -/
noncomputable def cache2_63 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 63. -/
noncomputable def cache3_63 : LinkCache := ⟨26,BottomForest.packed6500.rInput,BottomForest.packed6750.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 63. -/
theorem cachedLinkChecked63 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words63 BottomCase.words63 64512 cache0_63 cache1_63 cache2_63 cache3_63 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 63. -/
theorem linkChecked63 : ((List.range 1024).all fun j => linkCheck (64512+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked63 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words63 BottomCase.words63 64512 row
    cache0_63 cache1_63 cache2_63 cache3_63 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 63) (BottomCase.wordsAt 63) (1024*63) row = true := hc
  rw [linkChunkCheck_eq 63 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
#print axioms linkChecked32
end Quantum.Stabilizer.Homological.BB.Bravyi360.BottomShallow
