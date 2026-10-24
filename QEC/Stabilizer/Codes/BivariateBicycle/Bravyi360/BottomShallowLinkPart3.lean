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
/-- Adjacent family 0 data blocks for census chunk 96. -/
noncomputable def cache0_96 : LinkCache := ⟨75,BottomEmpty.beta0Words75,BottomEmpty.beta0Words76⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 96. -/
noncomputable def cache1_96 : LinkCache := ⟨9,BottomEmpty.beta1Words9,BottomEmpty.beta1Words10⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 96. -/
noncomputable def cache2_96 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 96. -/
noncomputable def cache3_96 : LinkCache := ⟨41,BottomForest.packed10250.rInput,BottomForest.packed10500.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 96. -/
theorem cachedLinkChecked96 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words96 BottomCase.words96 98304 cache0_96 cache1_96 cache2_96 cache3_96 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 96. -/
theorem linkChecked96 : ((List.range 1024).all fun j => linkCheck (98304+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked96 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words96 BottomCase.words96 98304 row
    cache0_96 cache1_96 cache2_96 cache3_96 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 96) (BottomCase.wordsAt 96) (1024*96) row = true := hc
  rw [linkChunkCheck_eq 96 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 97. -/
noncomputable def cache0_97 : LinkCache := ⟨76,BottomEmpty.beta0Words76,BottomEmpty.beta0Words77⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 97. -/
noncomputable def cache1_97 : LinkCache := ⟨9,BottomEmpty.beta1Words9,BottomEmpty.beta1Words10⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 97. -/
noncomputable def cache2_97 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 97. -/
noncomputable def cache3_97 : LinkCache := ⟨42,BottomForest.packed10500.rInput,BottomForest.packed10750.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 97. -/
theorem cachedLinkChecked97 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words97 BottomCase.words97 99328 cache0_97 cache1_97 cache2_97 cache3_97 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 97. -/
theorem linkChecked97 : ((List.range 1024).all fun j => linkCheck (99328+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked97 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words97 BottomCase.words97 99328 row
    cache0_97 cache1_97 cache2_97 cache3_97 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 97) (BottomCase.wordsAt 97) (1024*97) row = true := hc
  rw [linkChunkCheck_eq 97 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 98. -/
noncomputable def cache0_98 : LinkCache := ⟨77,BottomEmpty.beta0Words77,BottomEmpty.beta0Words78⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 98. -/
noncomputable def cache1_98 : LinkCache := ⟨9,BottomEmpty.beta1Words9,BottomEmpty.beta1Words10⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 98. -/
noncomputable def cache2_98 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 98. -/
noncomputable def cache3_98 : LinkCache := ⟨42,BottomForest.packed10500.rInput,BottomForest.packed10750.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 98. -/
theorem cachedLinkChecked98 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words98 BottomCase.words98 100352 cache0_98 cache1_98 cache2_98 cache3_98 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 98. -/
theorem linkChecked98 : ((List.range 1024).all fun j => linkCheck (100352+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked98 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words98 BottomCase.words98 100352 row
    cache0_98 cache1_98 cache2_98 cache3_98 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 98) (BottomCase.wordsAt 98) (1024*98) row = true := hc
  rw [linkChunkCheck_eq 98 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 99. -/
noncomputable def cache0_99 : LinkCache := ⟨78,BottomEmpty.beta0Words78,BottomEmpty.beta0Words79⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 99. -/
noncomputable def cache1_99 : LinkCache := ⟨9,BottomEmpty.beta1Words9,BottomEmpty.beta1Words10⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 99. -/
noncomputable def cache2_99 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 99. -/
noncomputable def cache3_99 : LinkCache := ⟨43,BottomForest.packed10750.rInput,BottomForest.packed11000.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 99. -/
theorem cachedLinkChecked99 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words99 BottomCase.words99 101376 cache0_99 cache1_99 cache2_99 cache3_99 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 99. -/
theorem linkChecked99 : ((List.range 1024).all fun j => linkCheck (101376+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked99 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words99 BottomCase.words99 101376 row
    cache0_99 cache1_99 cache2_99 cache3_99 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 99) (BottomCase.wordsAt 99) (1024*99) row = true := hc
  rw [linkChunkCheck_eq 99 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 100. -/
noncomputable def cache0_100 : LinkCache := ⟨78,BottomEmpty.beta0Words78,BottomEmpty.beta0Words79⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 100. -/
noncomputable def cache1_100 : LinkCache := ⟨9,BottomEmpty.beta1Words9,BottomEmpty.beta1Words10⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 100. -/
noncomputable def cache2_100 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 100. -/
noncomputable def cache3_100 : LinkCache := ⟨43,BottomForest.packed10750.rInput,BottomForest.packed11000.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 100. -/
theorem cachedLinkChecked100 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words100 BottomCase.words100 102400 cache0_100 cache1_100 cache2_100 cache3_100 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 100. -/
theorem linkChecked100 : ((List.range 1024).all fun j => linkCheck (102400+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked100 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words100 BottomCase.words100 102400 row
    cache0_100 cache1_100 cache2_100 cache3_100 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 100) (BottomCase.wordsAt 100) (1024*100) row = true := hc
  rw [linkChunkCheck_eq 100 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 101. -/
noncomputable def cache0_101 : LinkCache := ⟨79,BottomEmpty.beta0Words79,BottomEmpty.beta0Words80⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 101. -/
noncomputable def cache1_101 : LinkCache := ⟨9,BottomEmpty.beta1Words9,BottomEmpty.beta1Words10⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 101. -/
noncomputable def cache2_101 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 101. -/
noncomputable def cache3_101 : LinkCache := ⟨44,BottomForest.packed11000.rInput,BottomForest.packed11250.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 101. -/
theorem cachedLinkChecked101 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words101 BottomCase.words101 103424 cache0_101 cache1_101 cache2_101 cache3_101 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 101. -/
theorem linkChecked101 : ((List.range 1024).all fun j => linkCheck (103424+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked101 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words101 BottomCase.words101 103424 row
    cache0_101 cache1_101 cache2_101 cache3_101 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 101) (BottomCase.wordsAt 101) (1024*101) row = true := hc
  rw [linkChunkCheck_eq 101 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 102. -/
noncomputable def cache0_102 : LinkCache := ⟨80,BottomEmpty.beta0Words80,BottomEmpty.beta0Words81⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 102. -/
noncomputable def cache1_102 : LinkCache := ⟨10,BottomEmpty.beta1Words10,BottomEmpty.beta1Words11⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 102. -/
noncomputable def cache2_102 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 102. -/
noncomputable def cache3_102 : LinkCache := ⟨44,BottomForest.packed11000.rInput,BottomForest.packed11250.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 102. -/
theorem cachedLinkChecked102 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words102 BottomCase.words102 104448 cache0_102 cache1_102 cache2_102 cache3_102 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 102. -/
theorem linkChecked102 : ((List.range 1024).all fun j => linkCheck (104448+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked102 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words102 BottomCase.words102 104448 row
    cache0_102 cache1_102 cache2_102 cache3_102 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 102) (BottomCase.wordsAt 102) (1024*102) row = true := hc
  rw [linkChunkCheck_eq 102 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 103. -/
noncomputable def cache0_103 : LinkCache := ⟨81,BottomEmpty.beta0Words81,BottomEmpty.beta0Words82⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 103. -/
noncomputable def cache1_103 : LinkCache := ⟨10,BottomEmpty.beta1Words10,BottomEmpty.beta1Words11⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 103. -/
noncomputable def cache2_103 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 103. -/
noncomputable def cache3_103 : LinkCache := ⟨45,BottomForest.packed11250.rInput,BottomForest.packed11500.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 103. -/
theorem cachedLinkChecked103 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words103 BottomCase.words103 105472 cache0_103 cache1_103 cache2_103 cache3_103 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 103. -/
theorem linkChecked103 : ((List.range 1024).all fun j => linkCheck (105472+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked103 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words103 BottomCase.words103 105472 row
    cache0_103 cache1_103 cache2_103 cache3_103 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 103) (BottomCase.wordsAt 103) (1024*103) row = true := hc
  rw [linkChunkCheck_eq 103 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 104. -/
noncomputable def cache0_104 : LinkCache := ⟨82,BottomEmpty.beta0Words82,BottomEmpty.beta0Words83⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 104. -/
noncomputable def cache1_104 : LinkCache := ⟨10,BottomEmpty.beta1Words10,BottomEmpty.beta1Words11⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 104. -/
noncomputable def cache2_104 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 104. -/
noncomputable def cache3_104 : LinkCache := ⟨45,BottomForest.packed11250.rInput,BottomForest.packed11500.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 104. -/
theorem cachedLinkChecked104 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words104 BottomCase.words104 106496 cache0_104 cache1_104 cache2_104 cache3_104 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 104. -/
theorem linkChecked104 : ((List.range 1024).all fun j => linkCheck (106496+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked104 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words104 BottomCase.words104 106496 row
    cache0_104 cache1_104 cache2_104 cache3_104 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 104) (BottomCase.wordsAt 104) (1024*104) row = true := hc
  rw [linkChunkCheck_eq 104 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 105. -/
noncomputable def cache0_105 : LinkCache := ⟨82,BottomEmpty.beta0Words82,BottomEmpty.beta0Words83⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 105. -/
noncomputable def cache1_105 : LinkCache := ⟨10,BottomEmpty.beta1Words10,BottomEmpty.beta1Words11⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 105. -/
noncomputable def cache2_105 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 105. -/
noncomputable def cache3_105 : LinkCache := ⟨46,BottomForest.packed11500.rInput,BottomForest.packed11750.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 105. -/
theorem cachedLinkChecked105 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words105 BottomCase.words105 107520 cache0_105 cache1_105 cache2_105 cache3_105 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 105. -/
theorem linkChecked105 : ((List.range 1024).all fun j => linkCheck (107520+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked105 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words105 BottomCase.words105 107520 row
    cache0_105 cache1_105 cache2_105 cache3_105 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 105) (BottomCase.wordsAt 105) (1024*105) row = true := hc
  rw [linkChunkCheck_eq 105 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 106. -/
noncomputable def cache0_106 : LinkCache := ⟨83,BottomEmpty.beta0Words83,BottomEmpty.beta0Words84⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 106. -/
noncomputable def cache1_106 : LinkCache := ⟨10,BottomEmpty.beta1Words10,BottomEmpty.beta1Words11⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 106. -/
noncomputable def cache2_106 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 106. -/
noncomputable def cache3_106 : LinkCache := ⟨46,BottomForest.packed11500.rInput,BottomForest.packed11750.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 106. -/
theorem cachedLinkChecked106 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words106 BottomCase.words106 108544 cache0_106 cache1_106 cache2_106 cache3_106 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 106. -/
theorem linkChecked106 : ((List.range 1024).all fun j => linkCheck (108544+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked106 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words106 BottomCase.words106 108544 row
    cache0_106 cache1_106 cache2_106 cache3_106 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 106) (BottomCase.wordsAt 106) (1024*106) row = true := hc
  rw [linkChunkCheck_eq 106 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 107. -/
noncomputable def cache0_107 : LinkCache := ⟨84,BottomEmpty.beta0Words84,BottomEmpty.beta0Words85⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 107. -/
noncomputable def cache1_107 : LinkCache := ⟨10,BottomEmpty.beta1Words10,BottomEmpty.beta1Words11⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 107. -/
noncomputable def cache2_107 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 107. -/
noncomputable def cache3_107 : LinkCache := ⟨47,BottomForest.packed11750.rInput,BottomForest.packed12000.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 107. -/
theorem cachedLinkChecked107 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words107 BottomCase.words107 109568 cache0_107 cache1_107 cache2_107 cache3_107 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 107. -/
theorem linkChecked107 : ((List.range 1024).all fun j => linkCheck (109568+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked107 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words107 BottomCase.words107 109568 row
    cache0_107 cache1_107 cache2_107 cache3_107 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 107) (BottomCase.wordsAt 107) (1024*107) row = true := hc
  rw [linkChunkCheck_eq 107 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 108. -/
noncomputable def cache0_108 : LinkCache := ⟨85,BottomEmpty.beta0Words85,BottomEmpty.beta0Words86⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 108. -/
noncomputable def cache1_108 : LinkCache := ⟨10,BottomEmpty.beta1Words10,BottomEmpty.beta1Words11⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 108. -/
noncomputable def cache2_108 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 108. -/
noncomputable def cache3_108 : LinkCache := ⟨47,BottomForest.packed11750.rInput,BottomForest.packed12000.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 108. -/
theorem cachedLinkChecked108 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words108 BottomCase.words108 110592 cache0_108 cache1_108 cache2_108 cache3_108 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 108. -/
theorem linkChecked108 : ((List.range 1024).all fun j => linkCheck (110592+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked108 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words108 BottomCase.words108 110592 row
    cache0_108 cache1_108 cache2_108 cache3_108 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 108) (BottomCase.wordsAt 108) (1024*108) row = true := hc
  rw [linkChunkCheck_eq 108 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 109. -/
noncomputable def cache0_109 : LinkCache := ⟨86,BottomEmpty.beta0Words86,BottomEmpty.beta0Words87⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 109. -/
noncomputable def cache1_109 : LinkCache := ⟨10,BottomEmpty.beta1Words10,BottomEmpty.beta1Words11⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 109. -/
noncomputable def cache2_109 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 109. -/
noncomputable def cache3_109 : LinkCache := ⟨48,BottomForest.packed12000.rInput,BottomForest.packed12250.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 109. -/
theorem cachedLinkChecked109 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words109 BottomCase.words109 111616 cache0_109 cache1_109 cache2_109 cache3_109 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 109. -/
theorem linkChecked109 : ((List.range 1024).all fun j => linkCheck (111616+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked109 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words109 BottomCase.words109 111616 row
    cache0_109 cache1_109 cache2_109 cache3_109 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 109) (BottomCase.wordsAt 109) (1024*109) row = true := hc
  rw [linkChunkCheck_eq 109 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 110. -/
noncomputable def cache0_110 : LinkCache := ⟨86,BottomEmpty.beta0Words86,BottomEmpty.beta0Words87⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 110. -/
noncomputable def cache1_110 : LinkCache := ⟨10,BottomEmpty.beta1Words10,BottomEmpty.beta1Words11⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 110. -/
noncomputable def cache2_110 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 110. -/
noncomputable def cache3_110 : LinkCache := ⟨48,BottomForest.packed12000.rInput,BottomForest.packed12250.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 110. -/
theorem cachedLinkChecked110 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words110 BottomCase.words110 112640 cache0_110 cache1_110 cache2_110 cache3_110 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 110. -/
theorem linkChecked110 : ((List.range 1024).all fun j => linkCheck (112640+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked110 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words110 BottomCase.words110 112640 row
    cache0_110 cache1_110 cache2_110 cache3_110 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 110) (BottomCase.wordsAt 110) (1024*110) row = true := hc
  rw [linkChunkCheck_eq 110 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 111. -/
noncomputable def cache0_111 : LinkCache := ⟨87,BottomEmpty.beta0Words87,BottomEmpty.beta0Words88⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 111. -/
noncomputable def cache1_111 : LinkCache := ⟨10,BottomEmpty.beta1Words10,BottomEmpty.beta1Words11⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 111. -/
noncomputable def cache2_111 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 111. -/
noncomputable def cache3_111 : LinkCache := ⟨48,BottomForest.packed12000.rInput,BottomForest.packed12250.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 111. -/
theorem cachedLinkChecked111 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words111 BottomCase.words111 113664 cache0_111 cache1_111 cache2_111 cache3_111 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 111. -/
theorem linkChecked111 : ((List.range 1024).all fun j => linkCheck (113664+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked111 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words111 BottomCase.words111 113664 row
    cache0_111 cache1_111 cache2_111 cache3_111 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 111) (BottomCase.wordsAt 111) (1024*111) row = true := hc
  rw [linkChunkCheck_eq 111 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 112. -/
noncomputable def cache0_112 : LinkCache := ⟨88,BottomEmpty.beta0Words88,BottomEmpty.beta0Words89⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 112. -/
noncomputable def cache1_112 : LinkCache := ⟨10,BottomEmpty.beta1Words10,BottomEmpty.beta1Words11⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 112. -/
noncomputable def cache2_112 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 112. -/
noncomputable def cache3_112 : LinkCache := ⟨49,BottomForest.packed12250.rInput,BottomForest.packed12500.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 112. -/
theorem cachedLinkChecked112 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words112 BottomCase.words112 114688 cache0_112 cache1_112 cache2_112 cache3_112 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 112. -/
theorem linkChecked112 : ((List.range 1024).all fun j => linkCheck (114688+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked112 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words112 BottomCase.words112 114688 row
    cache0_112 cache1_112 cache2_112 cache3_112 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 112) (BottomCase.wordsAt 112) (1024*112) row = true := hc
  rw [linkChunkCheck_eq 112 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 113. -/
noncomputable def cache0_113 : LinkCache := ⟨89,BottomEmpty.beta0Words89,BottomEmpty.beta0Words90⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 113. -/
noncomputable def cache1_113 : LinkCache := ⟨10,BottomEmpty.beta1Words10,BottomEmpty.beta1Words11⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 113. -/
noncomputable def cache2_113 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 113. -/
noncomputable def cache3_113 : LinkCache := ⟨49,BottomForest.packed12250.rInput,BottomForest.packed12500.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 113. -/
theorem cachedLinkChecked113 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words113 BottomCase.words113 115712 cache0_113 cache1_113 cache2_113 cache3_113 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 113. -/
theorem linkChecked113 : ((List.range 1024).all fun j => linkCheck (115712+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked113 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words113 BottomCase.words113 115712 row
    cache0_113 cache1_113 cache2_113 cache3_113 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 113) (BottomCase.wordsAt 113) (1024*113) row = true := hc
  rw [linkChunkCheck_eq 113 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 114. -/
noncomputable def cache0_114 : LinkCache := ⟨90,BottomEmpty.beta0Words90,BottomEmpty.beta0Words91⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 114. -/
noncomputable def cache1_114 : LinkCache := ⟨10,BottomEmpty.beta1Words10,BottomEmpty.beta1Words11⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 114. -/
noncomputable def cache2_114 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 114. -/
noncomputable def cache3_114 : LinkCache := ⟨50,BottomForest.packed12500.rInput,BottomForest.packed12750.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 114. -/
theorem cachedLinkChecked114 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words114 BottomCase.words114 116736 cache0_114 cache1_114 cache2_114 cache3_114 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 114. -/
theorem linkChecked114 : ((List.range 1024).all fun j => linkCheck (116736+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked114 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words114 BottomCase.words114 116736 row
    cache0_114 cache1_114 cache2_114 cache3_114 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 114) (BottomCase.wordsAt 114) (1024*114) row = true := hc
  rw [linkChunkCheck_eq 114 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 115. -/
noncomputable def cache0_115 : LinkCache := ⟨91,BottomEmpty.beta0Words91,BottomEmpty.beta0Words92⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 115. -/
noncomputable def cache1_115 : LinkCache := ⟨10,BottomEmpty.beta1Words10,BottomEmpty.beta1Words11⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 115. -/
noncomputable def cache2_115 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 115. -/
noncomputable def cache3_115 : LinkCache := ⟨50,BottomForest.packed12500.rInput,BottomForest.packed12750.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 115. -/
theorem cachedLinkChecked115 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words115 BottomCase.words115 117760 cache0_115 cache1_115 cache2_115 cache3_115 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 115. -/
theorem linkChecked115 : ((List.range 1024).all fun j => linkCheck (117760+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked115 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words115 BottomCase.words115 117760 row
    cache0_115 cache1_115 cache2_115 cache3_115 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 115) (BottomCase.wordsAt 115) (1024*115) row = true := hc
  rw [linkChunkCheck_eq 115 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 116. -/
noncomputable def cache0_116 : LinkCache := ⟨91,BottomEmpty.beta0Words91,BottomEmpty.beta0Words92⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 116. -/
noncomputable def cache1_116 : LinkCache := ⟨11,BottomEmpty.beta1Words11,BottomEmpty.beta1Words12⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 116. -/
noncomputable def cache2_116 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 116. -/
noncomputable def cache3_116 : LinkCache := ⟨50,BottomForest.packed12500.rInput,BottomForest.packed12750.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 116. -/
theorem cachedLinkChecked116 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words116 BottomCase.words116 118784 cache0_116 cache1_116 cache2_116 cache3_116 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 116. -/
theorem linkChecked116 : ((List.range 1024).all fun j => linkCheck (118784+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked116 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words116 BottomCase.words116 118784 row
    cache0_116 cache1_116 cache2_116 cache3_116 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 116) (BottomCase.wordsAt 116) (1024*116) row = true := hc
  rw [linkChunkCheck_eq 116 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 117. -/
noncomputable def cache0_117 : LinkCache := ⟨92,BottomEmpty.beta0Words92,BottomEmpty.beta0Words93⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 117. -/
noncomputable def cache1_117 : LinkCache := ⟨11,BottomEmpty.beta1Words11,BottomEmpty.beta1Words12⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 117. -/
noncomputable def cache2_117 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 117. -/
noncomputable def cache3_117 : LinkCache := ⟨51,BottomForest.packed12750.rInput,BottomForest.packed13000.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 117. -/
theorem cachedLinkChecked117 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words117 BottomCase.words117 119808 cache0_117 cache1_117 cache2_117 cache3_117 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 117. -/
theorem linkChecked117 : ((List.range 1024).all fun j => linkCheck (119808+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked117 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words117 BottomCase.words117 119808 row
    cache0_117 cache1_117 cache2_117 cache3_117 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 117) (BottomCase.wordsAt 117) (1024*117) row = true := hc
  rw [linkChunkCheck_eq 117 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 118. -/
noncomputable def cache0_118 : LinkCache := ⟨93,BottomEmpty.beta0Words93,BottomEmpty.beta0Words94⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 118. -/
noncomputable def cache1_118 : LinkCache := ⟨11,BottomEmpty.beta1Words11,BottomEmpty.beta1Words12⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 118. -/
noncomputable def cache2_118 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 118. -/
noncomputable def cache3_118 : LinkCache := ⟨51,BottomForest.packed12750.rInput,BottomForest.packed13000.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 118. -/
theorem cachedLinkChecked118 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words118 BottomCase.words118 120832 cache0_118 cache1_118 cache2_118 cache3_118 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 118. -/
theorem linkChecked118 : ((List.range 1024).all fun j => linkCheck (120832+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked118 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words118 BottomCase.words118 120832 row
    cache0_118 cache1_118 cache2_118 cache3_118 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 118) (BottomCase.wordsAt 118) (1024*118) row = true := hc
  rw [linkChunkCheck_eq 118 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 119. -/
noncomputable def cache0_119 : LinkCache := ⟨94,BottomEmpty.beta0Words94,BottomEmpty.beta0Words95⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 119. -/
noncomputable def cache1_119 : LinkCache := ⟨11,BottomEmpty.beta1Words11,BottomEmpty.beta1Words12⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 119. -/
noncomputable def cache2_119 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 119. -/
noncomputable def cache3_119 : LinkCache := ⟨52,BottomForest.packed13000.rInput,BottomForest.packed13250.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 119. -/
theorem cachedLinkChecked119 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words119 BottomCase.words119 121856 cache0_119 cache1_119 cache2_119 cache3_119 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 119. -/
theorem linkChecked119 : ((List.range 1024).all fun j => linkCheck (121856+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked119 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words119 BottomCase.words119 121856 row
    cache0_119 cache1_119 cache2_119 cache3_119 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 119) (BottomCase.wordsAt 119) (1024*119) row = true := hc
  rw [linkChunkCheck_eq 119 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 120. -/
noncomputable def cache0_120 : LinkCache := ⟨95,BottomEmpty.beta0Words95,BottomEmpty.beta0Words96⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 120. -/
noncomputable def cache1_120 : LinkCache := ⟨11,BottomEmpty.beta1Words11,BottomEmpty.beta1Words12⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 120. -/
noncomputable def cache2_120 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 120. -/
noncomputable def cache3_120 : LinkCache := ⟨53,BottomForest.packed13250.rInput,BottomForest.packed13500.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 120. -/
theorem cachedLinkChecked120 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words120 BottomCase.words120 122880 cache0_120 cache1_120 cache2_120 cache3_120 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 120. -/
theorem linkChecked120 : ((List.range 1024).all fun j => linkCheck (122880+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked120 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words120 BottomCase.words120 122880 row
    cache0_120 cache1_120 cache2_120 cache3_120 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 120) (BottomCase.wordsAt 120) (1024*120) row = true := hc
  rw [linkChunkCheck_eq 120 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 121. -/
noncomputable def cache0_121 : LinkCache := ⟨95,BottomEmpty.beta0Words95,BottomEmpty.beta0Words96⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 121. -/
noncomputable def cache1_121 : LinkCache := ⟨11,BottomEmpty.beta1Words11,BottomEmpty.beta1Words12⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 121. -/
noncomputable def cache2_121 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 121. -/
noncomputable def cache3_121 : LinkCache := ⟨53,BottomForest.packed13250.rInput,BottomForest.packed13500.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 121. -/
theorem cachedLinkChecked121 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words121 BottomCase.words121 123904 cache0_121 cache1_121 cache2_121 cache3_121 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 121. -/
theorem linkChecked121 : ((List.range 1024).all fun j => linkCheck (123904+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked121 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words121 BottomCase.words121 123904 row
    cache0_121 cache1_121 cache2_121 cache3_121 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 121) (BottomCase.wordsAt 121) (1024*121) row = true := hc
  rw [linkChunkCheck_eq 121 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 122. -/
noncomputable def cache0_122 : LinkCache := ⟨96,BottomEmpty.beta0Words96,BottomEmpty.beta0Words97⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 122. -/
noncomputable def cache1_122 : LinkCache := ⟨11,BottomEmpty.beta1Words11,BottomEmpty.beta1Words12⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 122. -/
noncomputable def cache2_122 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 122. -/
noncomputable def cache3_122 : LinkCache := ⟨53,BottomForest.packed13250.rInput,BottomForest.packed13500.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 122. -/
theorem cachedLinkChecked122 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words122 BottomCase.words122 124928 cache0_122 cache1_122 cache2_122 cache3_122 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 122. -/
theorem linkChecked122 : ((List.range 1024).all fun j => linkCheck (124928+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked122 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words122 BottomCase.words122 124928 row
    cache0_122 cache1_122 cache2_122 cache3_122 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 122) (BottomCase.wordsAt 122) (1024*122) row = true := hc
  rw [linkChunkCheck_eq 122 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 123. -/
noncomputable def cache0_123 : LinkCache := ⟨97,BottomEmpty.beta0Words97,BottomEmpty.beta0Words98⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 123. -/
noncomputable def cache1_123 : LinkCache := ⟨11,BottomEmpty.beta1Words11,BottomEmpty.beta1Words12⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 123. -/
noncomputable def cache2_123 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 123. -/
noncomputable def cache3_123 : LinkCache := ⟨54,BottomForest.packed13500.rInput,BottomForest.packed13750.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 123. -/
theorem cachedLinkChecked123 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words123 BottomCase.words123 125952 cache0_123 cache1_123 cache2_123 cache3_123 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 123. -/
theorem linkChecked123 : ((List.range 1024).all fun j => linkCheck (125952+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked123 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words123 BottomCase.words123 125952 row
    cache0_123 cache1_123 cache2_123 cache3_123 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 123) (BottomCase.wordsAt 123) (1024*123) row = true := hc
  rw [linkChunkCheck_eq 123 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 124. -/
noncomputable def cache0_124 : LinkCache := ⟨98,BottomEmpty.beta0Words98,BottomEmpty.beta0Words99⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 124. -/
noncomputable def cache1_124 : LinkCache := ⟨11,BottomEmpty.beta1Words11,BottomEmpty.beta1Words12⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 124. -/
noncomputable def cache2_124 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 124. -/
noncomputable def cache3_124 : LinkCache := ⟨54,BottomForest.packed13500.rInput,BottomForest.packed13750.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 124. -/
theorem cachedLinkChecked124 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words124 BottomCase.words124 126976 cache0_124 cache1_124 cache2_124 cache3_124 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 124. -/
theorem linkChecked124 : ((List.range 1024).all fun j => linkCheck (126976+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked124 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words124 BottomCase.words124 126976 row
    cache0_124 cache1_124 cache2_124 cache3_124 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 124) (BottomCase.wordsAt 124) (1024*124) row = true := hc
  rw [linkChunkCheck_eq 124 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 125. -/
noncomputable def cache0_125 : LinkCache := ⟨99,BottomEmpty.beta0Words99,BottomEmpty.beta0Words100⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 125. -/
noncomputable def cache1_125 : LinkCache := ⟨11,BottomEmpty.beta1Words11,BottomEmpty.beta1Words12⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 125. -/
noncomputable def cache2_125 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 125. -/
noncomputable def cache3_125 : LinkCache := ⟨54,BottomForest.packed13500.rInput,BottomForest.packed13750.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 125. -/
theorem cachedLinkChecked125 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words125 BottomCase.words125 128000 cache0_125 cache1_125 cache2_125 cache3_125 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 125. -/
theorem linkChecked125 : ((List.range 1024).all fun j => linkCheck (128000+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked125 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words125 BottomCase.words125 128000 row
    cache0_125 cache1_125 cache2_125 cache3_125 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 125) (BottomCase.wordsAt 125) (1024*125) row = true := hc
  rw [linkChunkCheck_eq 125 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 126. -/
noncomputable def cache0_126 : LinkCache := ⟨100,BottomEmpty.beta0Words100,BottomEmpty.beta0Words101⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 126. -/
noncomputable def cache1_126 : LinkCache := ⟨11,BottomEmpty.beta1Words11,BottomEmpty.beta1Words12⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 126. -/
noncomputable def cache2_126 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 126. -/
noncomputable def cache3_126 : LinkCache := ⟨55,BottomForest.packed13750.rInput,BottomForest.packed14000.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 126. -/
theorem cachedLinkChecked126 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words126 BottomCase.words126 129024 cache0_126 cache1_126 cache2_126 cache3_126 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 126. -/
theorem linkChecked126 : ((List.range 1024).all fun j => linkCheck (129024+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked126 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words126 BottomCase.words126 129024 row
    cache0_126 cache1_126 cache2_126 cache3_126 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 126) (BottomCase.wordsAt 126) (1024*126) row = true := hc
  rw [linkChunkCheck_eq 126 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 127. -/
noncomputable def cache0_127 : LinkCache := ⟨100,BottomEmpty.beta0Words100,BottomEmpty.beta0Words101⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 127. -/
noncomputable def cache1_127 : LinkCache := ⟨11,BottomEmpty.beta1Words11,BottomEmpty.beta1Words12⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 127. -/
noncomputable def cache2_127 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 127. -/
noncomputable def cache3_127 : LinkCache := ⟨55,BottomForest.packed13750.rInput,BottomForest.packed14000.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 127. -/
theorem cachedLinkChecked127 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words127 BottomCase.words127 130048 cache0_127 cache1_127 cache2_127 cache3_127 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 127. -/
theorem linkChecked127 : ((List.range 1024).all fun j => linkCheck (130048+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked127 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words127 BottomCase.words127 130048 row
    cache0_127 cache1_127 cache2_127 cache3_127 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 127) (BottomCase.wordsAt 127) (1024*127) row = true := hc
  rw [linkChunkCheck_eq 127 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
#print axioms linkChecked96
end Quantum.Stabilizer.Homological.BB.Bravyi360.BottomShallow
