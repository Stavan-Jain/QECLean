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
/-- Adjacent family 0 data blocks for census chunk 64. -/
noncomputable def cache0_64 : LinkCache := ⟨50,BottomEmpty.beta0Words50,BottomEmpty.beta0Words51⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 64. -/
noncomputable def cache1_64 : LinkCache := ⟨6,BottomEmpty.beta1Words6,BottomEmpty.beta1Words7⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 64. -/
noncomputable def cache2_64 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 64. -/
noncomputable def cache3_64 : LinkCache := ⟨27,BottomForest.packed6750.rInput,BottomForest.packed7000.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 64. -/
theorem cachedLinkChecked64 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words64 BottomCase.words64 65536 cache0_64 cache1_64 cache2_64 cache3_64 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 64. -/
theorem linkChecked64 : ((List.range 1024).all fun j => linkCheck (65536+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked64 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words64 BottomCase.words64 65536 row
    cache0_64 cache1_64 cache2_64 cache3_64 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 64) (BottomCase.wordsAt 64) (1024*64) row = true := hc
  rw [linkChunkCheck_eq 64 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 65. -/
noncomputable def cache0_65 : LinkCache := ⟨51,BottomEmpty.beta0Words51,BottomEmpty.beta0Words52⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 65. -/
noncomputable def cache1_65 : LinkCache := ⟨6,BottomEmpty.beta1Words6,BottomEmpty.beta1Words7⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 65. -/
noncomputable def cache2_65 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 65. -/
noncomputable def cache3_65 : LinkCache := ⟨28,BottomForest.packed7000.rInput,BottomForest.packed7250.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 65. -/
theorem cachedLinkChecked65 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words65 BottomCase.words65 66560 cache0_65 cache1_65 cache2_65 cache3_65 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 65. -/
theorem linkChecked65 : ((List.range 1024).all fun j => linkCheck (66560+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked65 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words65 BottomCase.words65 66560 row
    cache0_65 cache1_65 cache2_65 cache3_65 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 65) (BottomCase.wordsAt 65) (1024*65) row = true := hc
  rw [linkChunkCheck_eq 65 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 66. -/
noncomputable def cache0_66 : LinkCache := ⟨51,BottomEmpty.beta0Words51,BottomEmpty.beta0Words52⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 66. -/
noncomputable def cache1_66 : LinkCache := ⟨6,BottomEmpty.beta1Words6,BottomEmpty.beta1Words7⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 66. -/
noncomputable def cache2_66 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 66. -/
noncomputable def cache3_66 : LinkCache := ⟨28,BottomForest.packed7000.rInput,BottomForest.packed7250.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 66. -/
theorem cachedLinkChecked66 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words66 BottomCase.words66 67584 cache0_66 cache1_66 cache2_66 cache3_66 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 66. -/
theorem linkChecked66 : ((List.range 1024).all fun j => linkCheck (67584+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked66 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words66 BottomCase.words66 67584 row
    cache0_66 cache1_66 cache2_66 cache3_66 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 66) (BottomCase.wordsAt 66) (1024*66) row = true := hc
  rw [linkChunkCheck_eq 66 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 67. -/
noncomputable def cache0_67 : LinkCache := ⟨52,BottomEmpty.beta0Words52,BottomEmpty.beta0Words53⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 67. -/
noncomputable def cache1_67 : LinkCache := ⟨6,BottomEmpty.beta1Words6,BottomEmpty.beta1Words7⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 67. -/
noncomputable def cache2_67 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 67. -/
noncomputable def cache3_67 : LinkCache := ⟨28,BottomForest.packed7000.rInput,BottomForest.packed7250.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 67. -/
theorem cachedLinkChecked67 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words67 BottomCase.words67 68608 cache0_67 cache1_67 cache2_67 cache3_67 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 67. -/
theorem linkChecked67 : ((List.range 1024).all fun j => linkCheck (68608+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked67 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words67 BottomCase.words67 68608 row
    cache0_67 cache1_67 cache2_67 cache3_67 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 67) (BottomCase.wordsAt 67) (1024*67) row = true := hc
  rw [linkChunkCheck_eq 67 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 68. -/
noncomputable def cache0_68 : LinkCache := ⟨53,BottomEmpty.beta0Words53,BottomEmpty.beta0Words54⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 68. -/
noncomputable def cache1_68 : LinkCache := ⟨6,BottomEmpty.beta1Words6,BottomEmpty.beta1Words7⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 68. -/
noncomputable def cache2_68 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 68. -/
noncomputable def cache3_68 : LinkCache := ⟨29,BottomForest.packed7250.rInput,BottomForest.packed7500.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 68. -/
theorem cachedLinkChecked68 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words68 BottomCase.words68 69632 cache0_68 cache1_68 cache2_68 cache3_68 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 68. -/
theorem linkChecked68 : ((List.range 1024).all fun j => linkCheck (69632+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked68 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words68 BottomCase.words68 69632 row
    cache0_68 cache1_68 cache2_68 cache3_68 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 68) (BottomCase.wordsAt 68) (1024*68) row = true := hc
  rw [linkChunkCheck_eq 68 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 69. -/
noncomputable def cache0_69 : LinkCache := ⟨54,BottomEmpty.beta0Words54,BottomEmpty.beta0Words55⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 69. -/
noncomputable def cache1_69 : LinkCache := ⟨6,BottomEmpty.beta1Words6,BottomEmpty.beta1Words7⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 69. -/
noncomputable def cache2_69 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 69. -/
noncomputable def cache3_69 : LinkCache := ⟨30,BottomForest.packed7500.rInput,BottomForest.packed7750.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 69. -/
theorem cachedLinkChecked69 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words69 BottomCase.words69 70656 cache0_69 cache1_69 cache2_69 cache3_69 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 69. -/
theorem linkChecked69 : ((List.range 1024).all fun j => linkCheck (70656+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked69 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words69 BottomCase.words69 70656 row
    cache0_69 cache1_69 cache2_69 cache3_69 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 69) (BottomCase.wordsAt 69) (1024*69) row = true := hc
  rw [linkChunkCheck_eq 69 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 70. -/
noncomputable def cache0_70 : LinkCache := ⟨55,BottomEmpty.beta0Words55,BottomEmpty.beta0Words56⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 70. -/
noncomputable def cache1_70 : LinkCache := ⟨7,BottomEmpty.beta1Words7,BottomEmpty.beta1Words8⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 70. -/
noncomputable def cache2_70 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 70. -/
noncomputable def cache3_70 : LinkCache := ⟨30,BottomForest.packed7500.rInput,BottomForest.packed7750.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 70. -/
theorem cachedLinkChecked70 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words70 BottomCase.words70 71680 cache0_70 cache1_70 cache2_70 cache3_70 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 70. -/
theorem linkChecked70 : ((List.range 1024).all fun j => linkCheck (71680+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked70 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words70 BottomCase.words70 71680 row
    cache0_70 cache1_70 cache2_70 cache3_70 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 70) (BottomCase.wordsAt 70) (1024*70) row = true := hc
  rw [linkChunkCheck_eq 70 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 71. -/
noncomputable def cache0_71 : LinkCache := ⟨55,BottomEmpty.beta0Words55,BottomEmpty.beta0Words56⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 71. -/
noncomputable def cache1_71 : LinkCache := ⟨7,BottomEmpty.beta1Words7,BottomEmpty.beta1Words8⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 71. -/
noncomputable def cache2_71 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 71. -/
noncomputable def cache3_71 : LinkCache := ⟨31,BottomForest.packed7750.rInput,BottomForest.packed8000.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 71. -/
theorem cachedLinkChecked71 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words71 BottomCase.words71 72704 cache0_71 cache1_71 cache2_71 cache3_71 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 71. -/
theorem linkChecked71 : ((List.range 1024).all fun j => linkCheck (72704+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked71 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words71 BottomCase.words71 72704 row
    cache0_71 cache1_71 cache2_71 cache3_71 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 71) (BottomCase.wordsAt 71) (1024*71) row = true := hc
  rw [linkChunkCheck_eq 71 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 72. -/
noncomputable def cache0_72 : LinkCache := ⟨56,BottomEmpty.beta0Words56,BottomEmpty.beta0Words57⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 72. -/
noncomputable def cache1_72 : LinkCache := ⟨7,BottomEmpty.beta1Words7,BottomEmpty.beta1Words8⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 72. -/
noncomputable def cache2_72 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 72. -/
noncomputable def cache3_72 : LinkCache := ⟨32,BottomForest.packed8000.rInput,BottomForest.packed8250.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 72. -/
theorem cachedLinkChecked72 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words72 BottomCase.words72 73728 cache0_72 cache1_72 cache2_72 cache3_72 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 72. -/
theorem linkChecked72 : ((List.range 1024).all fun j => linkCheck (73728+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked72 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words72 BottomCase.words72 73728 row
    cache0_72 cache1_72 cache2_72 cache3_72 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 72) (BottomCase.wordsAt 72) (1024*72) row = true := hc
  rw [linkChunkCheck_eq 72 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 73. -/
noncomputable def cache0_73 : LinkCache := ⟨57,BottomEmpty.beta0Words57,BottomEmpty.beta0Words58⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 73. -/
noncomputable def cache1_73 : LinkCache := ⟨7,BottomEmpty.beta1Words7,BottomEmpty.beta1Words8⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 73. -/
noncomputable def cache2_73 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 73. -/
noncomputable def cache3_73 : LinkCache := ⟨32,BottomForest.packed8000.rInput,BottomForest.packed8250.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 73. -/
theorem cachedLinkChecked73 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words73 BottomCase.words73 74752 cache0_73 cache1_73 cache2_73 cache3_73 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 73. -/
theorem linkChecked73 : ((List.range 1024).all fun j => linkCheck (74752+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked73 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words73 BottomCase.words73 74752 row
    cache0_73 cache1_73 cache2_73 cache3_73 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 73) (BottomCase.wordsAt 73) (1024*73) row = true := hc
  rw [linkChunkCheck_eq 73 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 74. -/
noncomputable def cache0_74 : LinkCache := ⟨58,BottomEmpty.beta0Words58,BottomEmpty.beta0Words59⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 74. -/
noncomputable def cache1_74 : LinkCache := ⟨7,BottomEmpty.beta1Words7,BottomEmpty.beta1Words8⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 74. -/
noncomputable def cache2_74 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 74. -/
noncomputable def cache3_74 : LinkCache := ⟨33,BottomForest.packed8250.rInput,BottomForest.packed8500.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 74. -/
theorem cachedLinkChecked74 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words74 BottomCase.words74 75776 cache0_74 cache1_74 cache2_74 cache3_74 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 74. -/
theorem linkChecked74 : ((List.range 1024).all fun j => linkCheck (75776+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked74 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words74 BottomCase.words74 75776 row
    cache0_74 cache1_74 cache2_74 cache3_74 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 74) (BottomCase.wordsAt 74) (1024*74) row = true := hc
  rw [linkChunkCheck_eq 74 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 75. -/
noncomputable def cache0_75 : LinkCache := ⟨58,BottomEmpty.beta0Words58,BottomEmpty.beta0Words59⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 75. -/
noncomputable def cache1_75 : LinkCache := ⟨7,BottomEmpty.beta1Words7,BottomEmpty.beta1Words8⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 75. -/
noncomputable def cache2_75 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 75. -/
noncomputable def cache3_75 : LinkCache := ⟨33,BottomForest.packed8250.rInput,BottomForest.packed8500.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 75. -/
theorem cachedLinkChecked75 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words75 BottomCase.words75 76800 cache0_75 cache1_75 cache2_75 cache3_75 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 75. -/
theorem linkChecked75 : ((List.range 1024).all fun j => linkCheck (76800+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked75 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words75 BottomCase.words75 76800 row
    cache0_75 cache1_75 cache2_75 cache3_75 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 75) (BottomCase.wordsAt 75) (1024*75) row = true := hc
  rw [linkChunkCheck_eq 75 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 76. -/
noncomputable def cache0_76 : LinkCache := ⟨59,BottomEmpty.beta0Words59,BottomEmpty.beta0Words60⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 76. -/
noncomputable def cache1_76 : LinkCache := ⟨7,BottomEmpty.beta1Words7,BottomEmpty.beta1Words8⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 76. -/
noncomputable def cache2_76 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 76. -/
noncomputable def cache3_76 : LinkCache := ⟨33,BottomForest.packed8250.rInput,BottomForest.packed8500.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 76. -/
theorem cachedLinkChecked76 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words76 BottomCase.words76 77824 cache0_76 cache1_76 cache2_76 cache3_76 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 76. -/
theorem linkChecked76 : ((List.range 1024).all fun j => linkCheck (77824+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked76 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words76 BottomCase.words76 77824 row
    cache0_76 cache1_76 cache2_76 cache3_76 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 76) (BottomCase.wordsAt 76) (1024*76) row = true := hc
  rw [linkChunkCheck_eq 76 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 77. -/
noncomputable def cache0_77 : LinkCache := ⟨60,BottomEmpty.beta0Words60,BottomEmpty.beta0Words61⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 77. -/
noncomputable def cache1_77 : LinkCache := ⟨7,BottomEmpty.beta1Words7,BottomEmpty.beta1Words8⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 77. -/
noncomputable def cache2_77 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 77. -/
noncomputable def cache3_77 : LinkCache := ⟨34,BottomForest.packed8500.rInput,BottomForest.packed8750.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 77. -/
theorem cachedLinkChecked77 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words77 BottomCase.words77 78848 cache0_77 cache1_77 cache2_77 cache3_77 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 77. -/
theorem linkChecked77 : ((List.range 1024).all fun j => linkCheck (78848+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked77 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words77 BottomCase.words77 78848 row
    cache0_77 cache1_77 cache2_77 cache3_77 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 77) (BottomCase.wordsAt 77) (1024*77) row = true := hc
  rw [linkChunkCheck_eq 77 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 78. -/
noncomputable def cache0_78 : LinkCache := ⟨61,BottomEmpty.beta0Words61,BottomEmpty.beta0Words62⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 78. -/
noncomputable def cache1_78 : LinkCache := ⟨7,BottomEmpty.beta1Words7,BottomEmpty.beta1Words8⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 78. -/
noncomputable def cache2_78 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 78. -/
noncomputable def cache3_78 : LinkCache := ⟨34,BottomForest.packed8500.rInput,BottomForest.packed8750.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 78. -/
theorem cachedLinkChecked78 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words78 BottomCase.words78 79872 cache0_78 cache1_78 cache2_78 cache3_78 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 78. -/
theorem linkChecked78 : ((List.range 1024).all fun j => linkCheck (79872+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked78 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words78 BottomCase.words78 79872 row
    cache0_78 cache1_78 cache2_78 cache3_78 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 78) (BottomCase.wordsAt 78) (1024*78) row = true := hc
  rw [linkChunkCheck_eq 78 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 79. -/
noncomputable def cache0_79 : LinkCache := ⟨62,BottomEmpty.beta0Words62,BottomEmpty.beta0Words63⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 79. -/
noncomputable def cache1_79 : LinkCache := ⟨7,BottomEmpty.beta1Words7,BottomEmpty.beta1Words8⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 79. -/
noncomputable def cache2_79 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 79. -/
noncomputable def cache3_79 : LinkCache := ⟨35,BottomForest.packed8750.rInput,BottomForest.packed9000.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 79. -/
theorem cachedLinkChecked79 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words79 BottomCase.words79 80896 cache0_79 cache1_79 cache2_79 cache3_79 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 79. -/
theorem linkChecked79 : ((List.range 1024).all fun j => linkCheck (80896+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked79 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words79 BottomCase.words79 80896 row
    cache0_79 cache1_79 cache2_79 cache3_79 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 79) (BottomCase.wordsAt 79) (1024*79) row = true := hc
  rw [linkChunkCheck_eq 79 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 80. -/
noncomputable def cache0_80 : LinkCache := ⟨62,BottomEmpty.beta0Words62,BottomEmpty.beta0Words63⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 80. -/
noncomputable def cache1_80 : LinkCache := ⟨8,BottomEmpty.beta1Words8,BottomEmpty.beta1Words9⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 80. -/
noncomputable def cache2_80 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 80. -/
noncomputable def cache3_80 : LinkCache := ⟨35,BottomForest.packed8750.rInput,BottomForest.packed9000.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 80. -/
theorem cachedLinkChecked80 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words80 BottomCase.words80 81920 cache0_80 cache1_80 cache2_80 cache3_80 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 80. -/
theorem linkChecked80 : ((List.range 1024).all fun j => linkCheck (81920+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked80 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words80 BottomCase.words80 81920 row
    cache0_80 cache1_80 cache2_80 cache3_80 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 80) (BottomCase.wordsAt 80) (1024*80) row = true := hc
  rw [linkChunkCheck_eq 80 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 81. -/
noncomputable def cache0_81 : LinkCache := ⟨63,BottomEmpty.beta0Words63,BottomEmpty.beta0Words64⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 81. -/
noncomputable def cache1_81 : LinkCache := ⟨8,BottomEmpty.beta1Words8,BottomEmpty.beta1Words9⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 81. -/
noncomputable def cache2_81 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 81. -/
noncomputable def cache3_81 : LinkCache := ⟨36,BottomForest.packed9000.rInput,BottomForest.packed9250.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 81. -/
theorem cachedLinkChecked81 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words81 BottomCase.words81 82944 cache0_81 cache1_81 cache2_81 cache3_81 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 81. -/
theorem linkChecked81 : ((List.range 1024).all fun j => linkCheck (82944+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked81 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words81 BottomCase.words81 82944 row
    cache0_81 cache1_81 cache2_81 cache3_81 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 81) (BottomCase.wordsAt 81) (1024*81) row = true := hc
  rw [linkChunkCheck_eq 81 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 82. -/
noncomputable def cache0_82 : LinkCache := ⟨64,BottomEmpty.beta0Words64,BottomEmpty.beta0Words65⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 82. -/
noncomputable def cache1_82 : LinkCache := ⟨8,BottomEmpty.beta1Words8,BottomEmpty.beta1Words9⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 82. -/
noncomputable def cache2_82 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 82. -/
noncomputable def cache3_82 : LinkCache := ⟨36,BottomForest.packed9000.rInput,BottomForest.packed9250.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 82. -/
theorem cachedLinkChecked82 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words82 BottomCase.words82 83968 cache0_82 cache1_82 cache2_82 cache3_82 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 82. -/
theorem linkChecked82 : ((List.range 1024).all fun j => linkCheck (83968+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked82 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words82 BottomCase.words82 83968 row
    cache0_82 cache1_82 cache2_82 cache3_82 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 82) (BottomCase.wordsAt 82) (1024*82) row = true := hc
  rw [linkChunkCheck_eq 82 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 83. -/
noncomputable def cache0_83 : LinkCache := ⟨65,BottomEmpty.beta0Words65,BottomEmpty.beta0Words66⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 83. -/
noncomputable def cache1_83 : LinkCache := ⟨8,BottomEmpty.beta1Words8,BottomEmpty.beta1Words9⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 83. -/
noncomputable def cache2_83 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 83. -/
noncomputable def cache3_83 : LinkCache := ⟨37,BottomForest.packed9250.rInput,BottomForest.packed9500.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 83. -/
theorem cachedLinkChecked83 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words83 BottomCase.words83 84992 cache0_83 cache1_83 cache2_83 cache3_83 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 83. -/
theorem linkChecked83 : ((List.range 1024).all fun j => linkCheck (84992+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked83 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words83 BottomCase.words83 84992 row
    cache0_83 cache1_83 cache2_83 cache3_83 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 83) (BottomCase.wordsAt 83) (1024*83) row = true := hc
  rw [linkChunkCheck_eq 83 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 84. -/
noncomputable def cache0_84 : LinkCache := ⟨65,BottomEmpty.beta0Words65,BottomEmpty.beta0Words66⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 84. -/
noncomputable def cache1_84 : LinkCache := ⟨8,BottomEmpty.beta1Words8,BottomEmpty.beta1Words9⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 84. -/
noncomputable def cache2_84 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 84. -/
noncomputable def cache3_84 : LinkCache := ⟨37,BottomForest.packed9250.rInput,BottomForest.packed9500.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 84. -/
theorem cachedLinkChecked84 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words84 BottomCase.words84 86016 cache0_84 cache1_84 cache2_84 cache3_84 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 84. -/
theorem linkChecked84 : ((List.range 1024).all fun j => linkCheck (86016+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked84 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words84 BottomCase.words84 86016 row
    cache0_84 cache1_84 cache2_84 cache3_84 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 84) (BottomCase.wordsAt 84) (1024*84) row = true := hc
  rw [linkChunkCheck_eq 84 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 85. -/
noncomputable def cache0_85 : LinkCache := ⟨66,BottomEmpty.beta0Words66,BottomEmpty.beta0Words67⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 85. -/
noncomputable def cache1_85 : LinkCache := ⟨8,BottomEmpty.beta1Words8,BottomEmpty.beta1Words9⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 85. -/
noncomputable def cache2_85 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 85. -/
noncomputable def cache3_85 : LinkCache := ⟨37,BottomForest.packed9250.rInput,BottomForest.packed9500.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 85. -/
theorem cachedLinkChecked85 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words85 BottomCase.words85 87040 cache0_85 cache1_85 cache2_85 cache3_85 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 85. -/
theorem linkChecked85 : ((List.range 1024).all fun j => linkCheck (87040+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked85 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words85 BottomCase.words85 87040 row
    cache0_85 cache1_85 cache2_85 cache3_85 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 85) (BottomCase.wordsAt 85) (1024*85) row = true := hc
  rw [linkChunkCheck_eq 85 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 86. -/
noncomputable def cache0_86 : LinkCache := ⟨67,BottomEmpty.beta0Words67,BottomEmpty.beta0Words68⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 86. -/
noncomputable def cache1_86 : LinkCache := ⟨8,BottomEmpty.beta1Words8,BottomEmpty.beta1Words9⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 86. -/
noncomputable def cache2_86 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 86. -/
noncomputable def cache3_86 : LinkCache := ⟨38,BottomForest.packed9500.rInput,BottomForest.packed9750.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 86. -/
theorem cachedLinkChecked86 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words86 BottomCase.words86 88064 cache0_86 cache1_86 cache2_86 cache3_86 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 86. -/
theorem linkChecked86 : ((List.range 1024).all fun j => linkCheck (88064+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked86 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words86 BottomCase.words86 88064 row
    cache0_86 cache1_86 cache2_86 cache3_86 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 86) (BottomCase.wordsAt 86) (1024*86) row = true := hc
  rw [linkChunkCheck_eq 86 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 87. -/
noncomputable def cache0_87 : LinkCache := ⟨68,BottomEmpty.beta0Words68,BottomEmpty.beta0Words69⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 87. -/
noncomputable def cache1_87 : LinkCache := ⟨8,BottomEmpty.beta1Words8,BottomEmpty.beta1Words9⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 87. -/
noncomputable def cache2_87 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 87. -/
noncomputable def cache3_87 : LinkCache := ⟨38,BottomForest.packed9500.rInput,BottomForest.packed9750.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 87. -/
theorem cachedLinkChecked87 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words87 BottomCase.words87 89088 cache0_87 cache1_87 cache2_87 cache3_87 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 87. -/
theorem linkChecked87 : ((List.range 1024).all fun j => linkCheck (89088+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked87 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words87 BottomCase.words87 89088 row
    cache0_87 cache1_87 cache2_87 cache3_87 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 87) (BottomCase.wordsAt 87) (1024*87) row = true := hc
  rw [linkChunkCheck_eq 87 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 88. -/
noncomputable def cache0_88 : LinkCache := ⟨69,BottomEmpty.beta0Words69,BottomEmpty.beta0Words70⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 88. -/
noncomputable def cache1_88 : LinkCache := ⟨8,BottomEmpty.beta1Words8,BottomEmpty.beta1Words9⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 88. -/
noncomputable def cache2_88 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 88. -/
noncomputable def cache3_88 : LinkCache := ⟨39,BottomForest.packed9750.rInput,BottomForest.packed10000.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 88. -/
theorem cachedLinkChecked88 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words88 BottomCase.words88 90112 cache0_88 cache1_88 cache2_88 cache3_88 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 88. -/
theorem linkChecked88 : ((List.range 1024).all fun j => linkCheck (90112+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked88 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words88 BottomCase.words88 90112 row
    cache0_88 cache1_88 cache2_88 cache3_88 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 88) (BottomCase.wordsAt 88) (1024*88) row = true := hc
  rw [linkChunkCheck_eq 88 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 89. -/
noncomputable def cache0_89 : LinkCache := ⟨69,BottomEmpty.beta0Words69,BottomEmpty.beta0Words70⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 89. -/
noncomputable def cache1_89 : LinkCache := ⟨8,BottomEmpty.beta1Words8,BottomEmpty.beta1Words9⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 89. -/
noncomputable def cache2_89 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 89. -/
noncomputable def cache3_89 : LinkCache := ⟨39,BottomForest.packed9750.rInput,BottomForest.packed10000.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 89. -/
theorem cachedLinkChecked89 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words89 BottomCase.words89 91136 cache0_89 cache1_89 cache2_89 cache3_89 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 89. -/
theorem linkChecked89 : ((List.range 1024).all fun j => linkCheck (91136+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked89 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words89 BottomCase.words89 91136 row
    cache0_89 cache1_89 cache2_89 cache3_89 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 89) (BottomCase.wordsAt 89) (1024*89) row = true := hc
  rw [linkChunkCheck_eq 89 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 90. -/
noncomputable def cache0_90 : LinkCache := ⟨70,BottomEmpty.beta0Words70,BottomEmpty.beta0Words71⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 90. -/
noncomputable def cache1_90 : LinkCache := ⟨8,BottomEmpty.beta1Words8,BottomEmpty.beta1Words9⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 90. -/
noncomputable def cache2_90 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 90. -/
noncomputable def cache3_90 : LinkCache := ⟨39,BottomForest.packed9750.rInput,BottomForest.packed10000.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 90. -/
theorem cachedLinkChecked90 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words90 BottomCase.words90 92160 cache0_90 cache1_90 cache2_90 cache3_90 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 90. -/
theorem linkChecked90 : ((List.range 1024).all fun j => linkCheck (92160+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked90 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words90 BottomCase.words90 92160 row
    cache0_90 cache1_90 cache2_90 cache3_90 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 90) (BottomCase.wordsAt 90) (1024*90) row = true := hc
  rw [linkChunkCheck_eq 90 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 91. -/
noncomputable def cache0_91 : LinkCache := ⟨71,BottomEmpty.beta0Words71,BottomEmpty.beta0Words72⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 91. -/
noncomputable def cache1_91 : LinkCache := ⟨9,BottomEmpty.beta1Words9,BottomEmpty.beta1Words10⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 91. -/
noncomputable def cache2_91 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 91. -/
noncomputable def cache3_91 : LinkCache := ⟨40,BottomForest.packed10000.rInput,BottomForest.packed10250.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 91. -/
theorem cachedLinkChecked91 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words91 BottomCase.words91 93184 cache0_91 cache1_91 cache2_91 cache3_91 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 91. -/
theorem linkChecked91 : ((List.range 1024).all fun j => linkCheck (93184+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked91 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words91 BottomCase.words91 93184 row
    cache0_91 cache1_91 cache2_91 cache3_91 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 91) (BottomCase.wordsAt 91) (1024*91) row = true := hc
  rw [linkChunkCheck_eq 91 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 92. -/
noncomputable def cache0_92 : LinkCache := ⟨72,BottomEmpty.beta0Words72,BottomEmpty.beta0Words73⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 92. -/
noncomputable def cache1_92 : LinkCache := ⟨9,BottomEmpty.beta1Words9,BottomEmpty.beta1Words10⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 92. -/
noncomputable def cache2_92 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 92. -/
noncomputable def cache3_92 : LinkCache := ⟨40,BottomForest.packed10000.rInput,BottomForest.packed10250.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 92. -/
theorem cachedLinkChecked92 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words92 BottomCase.words92 94208 cache0_92 cache1_92 cache2_92 cache3_92 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 92. -/
theorem linkChecked92 : ((List.range 1024).all fun j => linkCheck (94208+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked92 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words92 BottomCase.words92 94208 row
    cache0_92 cache1_92 cache2_92 cache3_92 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 92) (BottomCase.wordsAt 92) (1024*92) row = true := hc
  rw [linkChunkCheck_eq 92 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 93. -/
noncomputable def cache0_93 : LinkCache := ⟨73,BottomEmpty.beta0Words73,BottomEmpty.beta0Words74⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 93. -/
noncomputable def cache1_93 : LinkCache := ⟨9,BottomEmpty.beta1Words9,BottomEmpty.beta1Words10⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 93. -/
noncomputable def cache2_93 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 93. -/
noncomputable def cache3_93 : LinkCache := ⟨40,BottomForest.packed10000.rInput,BottomForest.packed10250.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 93. -/
theorem cachedLinkChecked93 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words93 BottomCase.words93 95232 cache0_93 cache1_93 cache2_93 cache3_93 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 93. -/
theorem linkChecked93 : ((List.range 1024).all fun j => linkCheck (95232+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked93 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words93 BottomCase.words93 95232 row
    cache0_93 cache1_93 cache2_93 cache3_93 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 93) (BottomCase.wordsAt 93) (1024*93) row = true := hc
  rw [linkChunkCheck_eq 93 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 94. -/
noncomputable def cache0_94 : LinkCache := ⟨73,BottomEmpty.beta0Words73,BottomEmpty.beta0Words74⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 94. -/
noncomputable def cache1_94 : LinkCache := ⟨9,BottomEmpty.beta1Words9,BottomEmpty.beta1Words10⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 94. -/
noncomputable def cache2_94 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 94. -/
noncomputable def cache3_94 : LinkCache := ⟨41,BottomForest.packed10250.rInput,BottomForest.packed10500.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 94. -/
theorem cachedLinkChecked94 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words94 BottomCase.words94 96256 cache0_94 cache1_94 cache2_94 cache3_94 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 94. -/
theorem linkChecked94 : ((List.range 1024).all fun j => linkCheck (96256+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked94 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words94 BottomCase.words94 96256 row
    cache0_94 cache1_94 cache2_94 cache3_94 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 94) (BottomCase.wordsAt 94) (1024*94) row = true := hc
  rw [linkChunkCheck_eq 94 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 95. -/
noncomputable def cache0_95 : LinkCache := ⟨74,BottomEmpty.beta0Words74,BottomEmpty.beta0Words75⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 95. -/
noncomputable def cache1_95 : LinkCache := ⟨9,BottomEmpty.beta1Words9,BottomEmpty.beta1Words10⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 95. -/
noncomputable def cache2_95 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 95. -/
noncomputable def cache3_95 : LinkCache := ⟨41,BottomForest.packed10250.rInput,BottomForest.packed10500.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 95. -/
theorem cachedLinkChecked95 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words95 BottomCase.words95 97280 cache0_95 cache1_95 cache2_95 cache3_95 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 95. -/
theorem linkChecked95 : ((List.range 1024).all fun j => linkCheck (97280+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked95 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words95 BottomCase.words95 97280 row
    cache0_95 cache1_95 cache2_95 cache3_95 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 95) (BottomCase.wordsAt 95) (1024*95) row = true := hc
  rw [linkChunkCheck_eq 95 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
#print axioms linkChecked64
end Quantum.Stabilizer.Homological.BB.Bravyi360.BottomShallow
