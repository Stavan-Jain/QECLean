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
/-- Adjacent family 0 data blocks for census chunk 128. -/
noncomputable def cache0_128 : LinkCache := ⟨101,BottomEmpty.beta0Words101,BottomEmpty.beta0Words102⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 128. -/
noncomputable def cache1_128 : LinkCache := ⟨11,BottomEmpty.beta1Words11,BottomEmpty.beta1Words12⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 128. -/
noncomputable def cache2_128 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 128. -/
noncomputable def cache3_128 : LinkCache := ⟨56,BottomForest.packed14000.rInput,BottomForest.packed14250.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 128. -/
theorem cachedLinkChecked128 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words128 BottomCase.words128 131072 cache0_128 cache1_128 cache2_128 cache3_128 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 128. -/
theorem linkChecked128 : ((List.range 1024).all fun j => linkCheck (131072+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked128 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words128 BottomCase.words128 131072 row
    cache0_128 cache1_128 cache2_128 cache3_128 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 128) (BottomCase.wordsAt 128) (1024*128) row = true := hc
  rw [linkChunkCheck_eq 128 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 129. -/
noncomputable def cache0_129 : LinkCache := ⟨102,BottomEmpty.beta0Words102,BottomEmpty.beta0Words103⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 129. -/
noncomputable def cache1_129 : LinkCache := ⟨12,BottomEmpty.beta1Words12,BottomEmpty.beta1Words13⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 129. -/
noncomputable def cache2_129 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 129. -/
noncomputable def cache3_129 : LinkCache := ⟨56,BottomForest.packed14000.rInput,BottomForest.packed14250.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 129. -/
theorem cachedLinkChecked129 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words129 BottomCase.words129 132096 cache0_129 cache1_129 cache2_129 cache3_129 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 129. -/
theorem linkChecked129 : ((List.range 1024).all fun j => linkCheck (132096+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked129 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words129 BottomCase.words129 132096 row
    cache0_129 cache1_129 cache2_129 cache3_129 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 129) (BottomCase.wordsAt 129) (1024*129) row = true := hc
  rw [linkChunkCheck_eq 129 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 130. -/
noncomputable def cache0_130 : LinkCache := ⟨103,BottomEmpty.beta0Words103,BottomEmpty.beta0Words104⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 130. -/
noncomputable def cache1_130 : LinkCache := ⟨12,BottomEmpty.beta1Words12,BottomEmpty.beta1Words13⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 130. -/
noncomputable def cache2_130 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 130. -/
noncomputable def cache3_130 : LinkCache := ⟨57,BottomForest.packed14250.rInput,BottomForest.packed14500.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 130. -/
theorem cachedLinkChecked130 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words130 BottomCase.words130 133120 cache0_130 cache1_130 cache2_130 cache3_130 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 130. -/
theorem linkChecked130 : ((List.range 1024).all fun j => linkCheck (133120+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked130 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words130 BottomCase.words130 133120 row
    cache0_130 cache1_130 cache2_130 cache3_130 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 130) (BottomCase.wordsAt 130) (1024*130) row = true := hc
  rw [linkChunkCheck_eq 130 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 131. -/
noncomputable def cache0_131 : LinkCache := ⟨104,BottomEmpty.beta0Words104,BottomEmpty.beta0Words105⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 131. -/
noncomputable def cache1_131 : LinkCache := ⟨12,BottomEmpty.beta1Words12,BottomEmpty.beta1Words13⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 131. -/
noncomputable def cache2_131 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 131. -/
noncomputable def cache3_131 : LinkCache := ⟨57,BottomForest.packed14250.rInput,BottomForest.packed14500.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 131. -/
theorem cachedLinkChecked131 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words131 BottomCase.words131 134144 cache0_131 cache1_131 cache2_131 cache3_131 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 131. -/
theorem linkChecked131 : ((List.range 1024).all fun j => linkCheck (134144+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked131 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words131 BottomCase.words131 134144 row
    cache0_131 cache1_131 cache2_131 cache3_131 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 131) (BottomCase.wordsAt 131) (1024*131) row = true := hc
  rw [linkChunkCheck_eq 131 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 132. -/
noncomputable def cache0_132 : LinkCache := ⟨104,BottomEmpty.beta0Words104,BottomEmpty.beta0Words105⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 132. -/
noncomputable def cache1_132 : LinkCache := ⟨12,BottomEmpty.beta1Words12,BottomEmpty.beta1Words13⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 132. -/
noncomputable def cache2_132 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 132. -/
noncomputable def cache3_132 : LinkCache := ⟨58,BottomForest.packed14500.rInput,BottomForest.packed14750.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 132. -/
theorem cachedLinkChecked132 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words132 BottomCase.words132 135168 cache0_132 cache1_132 cache2_132 cache3_132 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 132. -/
theorem linkChecked132 : ((List.range 1024).all fun j => linkCheck (135168+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked132 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words132 BottomCase.words132 135168 row
    cache0_132 cache1_132 cache2_132 cache3_132 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 132) (BottomCase.wordsAt 132) (1024*132) row = true := hc
  rw [linkChunkCheck_eq 132 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 133. -/
noncomputable def cache0_133 : LinkCache := ⟨105,BottomEmpty.beta0Words105,BottomEmpty.beta0Words106⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 133. -/
noncomputable def cache1_133 : LinkCache := ⟨12,BottomEmpty.beta1Words12,BottomEmpty.beta1Words13⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 133. -/
noncomputable def cache2_133 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 133. -/
noncomputable def cache3_133 : LinkCache := ⟨58,BottomForest.packed14500.rInput,BottomForest.packed14750.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 133. -/
theorem cachedLinkChecked133 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words133 BottomCase.words133 136192 cache0_133 cache1_133 cache2_133 cache3_133 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 133. -/
theorem linkChecked133 : ((List.range 1024).all fun j => linkCheck (136192+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked133 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words133 BottomCase.words133 136192 row
    cache0_133 cache1_133 cache2_133 cache3_133 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 133) (BottomCase.wordsAt 133) (1024*133) row = true := hc
  rw [linkChunkCheck_eq 133 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 134. -/
noncomputable def cache0_134 : LinkCache := ⟨106,BottomEmpty.beta0Words106,BottomEmpty.beta0Words107⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 134. -/
noncomputable def cache1_134 : LinkCache := ⟨12,BottomEmpty.beta1Words12,BottomEmpty.beta1Words13⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 134. -/
noncomputable def cache2_134 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 134. -/
noncomputable def cache3_134 : LinkCache := ⟨59,BottomForest.packed14750.rInput,BottomForest.packed15000.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 134. -/
theorem cachedLinkChecked134 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words134 BottomCase.words134 137216 cache0_134 cache1_134 cache2_134 cache3_134 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 134. -/
theorem linkChecked134 : ((List.range 1024).all fun j => linkCheck (137216+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked134 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words134 BottomCase.words134 137216 row
    cache0_134 cache1_134 cache2_134 cache3_134 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 134) (BottomCase.wordsAt 134) (1024*134) row = true := hc
  rw [linkChunkCheck_eq 134 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 135. -/
noncomputable def cache0_135 : LinkCache := ⟨107,BottomEmpty.beta0Words107,BottomEmpty.beta0Words108⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 135. -/
noncomputable def cache1_135 : LinkCache := ⟨12,BottomEmpty.beta1Words12,BottomEmpty.beta1Words13⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 135. -/
noncomputable def cache2_135 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 135. -/
noncomputable def cache3_135 : LinkCache := ⟨59,BottomForest.packed14750.rInput,BottomForest.packed15000.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 135. -/
theorem cachedLinkChecked135 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words135 BottomCase.words135 138240 cache0_135 cache1_135 cache2_135 cache3_135 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 135. -/
theorem linkChecked135 : ((List.range 1024).all fun j => linkCheck (138240+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked135 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words135 BottomCase.words135 138240 row
    cache0_135 cache1_135 cache2_135 cache3_135 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 135) (BottomCase.wordsAt 135) (1024*135) row = true := hc
  rw [linkChunkCheck_eq 135 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 136. -/
noncomputable def cache0_136 : LinkCache := ⟨108,BottomEmpty.beta0Words108,BottomEmpty.beta0Words109⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 136. -/
noncomputable def cache1_136 : LinkCache := ⟨12,BottomEmpty.beta1Words12,BottomEmpty.beta1Words13⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 136. -/
noncomputable def cache2_136 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 136. -/
noncomputable def cache3_136 : LinkCache := ⟨60,BottomForest.packed15000.rInput,BottomForest.packed15250.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 136. -/
theorem cachedLinkChecked136 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words136 BottomCase.words136 139264 cache0_136 cache1_136 cache2_136 cache3_136 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 136. -/
theorem linkChecked136 : ((List.range 1024).all fun j => linkCheck (139264+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked136 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words136 BottomCase.words136 139264 row
    cache0_136 cache1_136 cache2_136 cache3_136 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 136) (BottomCase.wordsAt 136) (1024*136) row = true := hc
  rw [linkChunkCheck_eq 136 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 137. -/
noncomputable def cache0_137 : LinkCache := ⟨108,BottomEmpty.beta0Words108,BottomEmpty.beta0Words109⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 137. -/
noncomputable def cache1_137 : LinkCache := ⟨12,BottomEmpty.beta1Words12,BottomEmpty.beta1Words13⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 137. -/
noncomputable def cache2_137 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 137. -/
noncomputable def cache3_137 : LinkCache := ⟨61,BottomForest.packed15250.rInput,BottomForest.packed15500.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 137. -/
theorem cachedLinkChecked137 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words137 BottomCase.words137 140288 cache0_137 cache1_137 cache2_137 cache3_137 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 137. -/
theorem linkChecked137 : ((List.range 1024).all fun j => linkCheck (140288+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked137 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words137 BottomCase.words137 140288 row
    cache0_137 cache1_137 cache2_137 cache3_137 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 137) (BottomCase.wordsAt 137) (1024*137) row = true := hc
  rw [linkChunkCheck_eq 137 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 138. -/
noncomputable def cache0_138 : LinkCache := ⟨109,BottomEmpty.beta0Words109,BottomEmpty.beta0Words110⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 138. -/
noncomputable def cache1_138 : LinkCache := ⟨12,BottomEmpty.beta1Words12,BottomEmpty.beta1Words13⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 138. -/
noncomputable def cache2_138 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 138. -/
noncomputable def cache3_138 : LinkCache := ⟨62,BottomForest.packed15500.rInput,BottomForest.packed15750.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 138. -/
theorem cachedLinkChecked138 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words138 BottomCase.words138 141312 cache0_138 cache1_138 cache2_138 cache3_138 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 138. -/
theorem linkChecked138 : ((List.range 1024).all fun j => linkCheck (141312+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked138 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words138 BottomCase.words138 141312 row
    cache0_138 cache1_138 cache2_138 cache3_138 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 138) (BottomCase.wordsAt 138) (1024*138) row = true := hc
  rw [linkChunkCheck_eq 138 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 139. -/
noncomputable def cache0_139 : LinkCache := ⟨110,BottomEmpty.beta0Words110,BottomEmpty.beta0Words111⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 139. -/
noncomputable def cache1_139 : LinkCache := ⟨12,BottomEmpty.beta1Words12,BottomEmpty.beta1Words13⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 139. -/
noncomputable def cache2_139 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 139. -/
noncomputable def cache3_139 : LinkCache := ⟨62,BottomForest.packed15500.rInput,BottomForest.packed15750.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 139. -/
theorem cachedLinkChecked139 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words139 BottomCase.words139 142336 cache0_139 cache1_139 cache2_139 cache3_139 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 139. -/
theorem linkChecked139 : ((List.range 1024).all fun j => linkCheck (142336+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked139 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words139 BottomCase.words139 142336 row
    cache0_139 cache1_139 cache2_139 cache3_139 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 139) (BottomCase.wordsAt 139) (1024*139) row = true := hc
  rw [linkChunkCheck_eq 139 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 140. -/
noncomputable def cache0_140 : LinkCache := ⟨111,BottomEmpty.beta0Words111,BottomEmpty.beta0Words112⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 140. -/
noncomputable def cache1_140 : LinkCache := ⟨12,BottomEmpty.beta1Words12,BottomEmpty.beta1Words13⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 140. -/
noncomputable def cache2_140 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 140. -/
noncomputable def cache3_140 : LinkCache := ⟨63,BottomForest.packed15750.rInput,BottomForest.packed16000.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 140. -/
theorem cachedLinkChecked140 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words140 BottomCase.words140 143360 cache0_140 cache1_140 cache2_140 cache3_140 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 140. -/
theorem linkChecked140 : ((List.range 1024).all fun j => linkCheck (143360+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked140 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words140 BottomCase.words140 143360 row
    cache0_140 cache1_140 cache2_140 cache3_140 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 140) (BottomCase.wordsAt 140) (1024*140) row = true := hc
  rw [linkChunkCheck_eq 140 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 141. -/
noncomputable def cache0_141 : LinkCache := ⟨112,BottomEmpty.beta0Words112,BottomEmpty.beta0Words113⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 141. -/
noncomputable def cache1_141 : LinkCache := ⟨12,BottomEmpty.beta1Words12,BottomEmpty.beta1Words13⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 141. -/
noncomputable def cache2_141 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 141. -/
noncomputable def cache3_141 : LinkCache := ⟨63,BottomForest.packed15750.rInput,BottomForest.packed16000.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 141. -/
theorem cachedLinkChecked141 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words141 BottomCase.words141 144384 cache0_141 cache1_141 cache2_141 cache3_141 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 141. -/
theorem linkChecked141 : ((List.range 1024).all fun j => linkCheck (144384+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked141 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words141 BottomCase.words141 144384 row
    cache0_141 cache1_141 cache2_141 cache3_141 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 141) (BottomCase.wordsAt 141) (1024*141) row = true := hc
  rw [linkChunkCheck_eq 141 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 142. -/
noncomputable def cache0_142 : LinkCache := ⟨112,BottomEmpty.beta0Words112,BottomEmpty.beta0Words113⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 142. -/
noncomputable def cache1_142 : LinkCache := ⟨12,BottomEmpty.beta1Words12,BottomEmpty.beta1Words13⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 142. -/
noncomputable def cache2_142 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 142. -/
noncomputable def cache3_142 : LinkCache := ⟨63,BottomForest.packed15750.rInput,BottomForest.packed16000.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 142. -/
theorem cachedLinkChecked142 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words142 BottomCase.words142 145408 cache0_142 cache1_142 cache2_142 cache3_142 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 142. -/
theorem linkChecked142 : ((List.range 1024).all fun j => linkCheck (145408+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked142 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words142 BottomCase.words142 145408 row
    cache0_142 cache1_142 cache2_142 cache3_142 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 142) (BottomCase.wordsAt 142) (1024*142) row = true := hc
  rw [linkChunkCheck_eq 142 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 143. -/
noncomputable def cache0_143 : LinkCache := ⟨113,BottomEmpty.beta0Words113,BottomEmpty.beta0Words114⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 143. -/
noncomputable def cache1_143 : LinkCache := ⟨12,BottomEmpty.beta1Words12,BottomEmpty.beta1Words13⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 143. -/
noncomputable def cache2_143 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 143. -/
noncomputable def cache3_143 : LinkCache := ⟨64,BottomForest.packed16000.rInput,BottomForest.packed16250.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 143. -/
theorem cachedLinkChecked143 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words143 BottomCase.words143 146432 cache0_143 cache1_143 cache2_143 cache3_143 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 143. -/
theorem linkChecked143 : ((List.range 1024).all fun j => linkCheck (146432+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked143 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words143 BottomCase.words143 146432 row
    cache0_143 cache1_143 cache2_143 cache3_143 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 143) (BottomCase.wordsAt 143) (1024*143) row = true := hc
  rw [linkChunkCheck_eq 143 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 144. -/
noncomputable def cache0_144 : LinkCache := ⟨114,BottomEmpty.beta0Words114,BottomEmpty.beta0Words115⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 144. -/
noncomputable def cache1_144 : LinkCache := ⟨13,BottomEmpty.beta1Words13,BottomEmpty.beta1Words14⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 144. -/
noncomputable def cache2_144 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 144. -/
noncomputable def cache3_144 : LinkCache := ⟨64,BottomForest.packed16000.rInput,BottomForest.packed16250.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 144. -/
theorem cachedLinkChecked144 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words144 BottomCase.words144 147456 cache0_144 cache1_144 cache2_144 cache3_144 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 144. -/
theorem linkChecked144 : ((List.range 1024).all fun j => linkCheck (147456+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked144 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words144 BottomCase.words144 147456 row
    cache0_144 cache1_144 cache2_144 cache3_144 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 144) (BottomCase.wordsAt 144) (1024*144) row = true := hc
  rw [linkChunkCheck_eq 144 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 145. -/
noncomputable def cache0_145 : LinkCache := ⟨115,BottomEmpty.beta0Words115,BottomEmpty.beta0Words116⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 145. -/
noncomputable def cache1_145 : LinkCache := ⟨13,BottomEmpty.beta1Words13,BottomEmpty.beta1Words14⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 145. -/
noncomputable def cache2_145 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 145. -/
noncomputable def cache3_145 : LinkCache := ⟨64,BottomForest.packed16000.rInput,BottomForest.packed16250.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 145. -/
theorem cachedLinkChecked145 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words145 BottomCase.words145 148480 cache0_145 cache1_145 cache2_145 cache3_145 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 145. -/
theorem linkChecked145 : ((List.range 1024).all fun j => linkCheck (148480+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked145 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words145 BottomCase.words145 148480 row
    cache0_145 cache1_145 cache2_145 cache3_145 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 145) (BottomCase.wordsAt 145) (1024*145) row = true := hc
  rw [linkChunkCheck_eq 145 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 146. -/
noncomputable def cache0_146 : LinkCache := ⟨116,BottomEmpty.beta0Words116,BottomEmpty.beta0Words117⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 146. -/
noncomputable def cache1_146 : LinkCache := ⟨13,BottomEmpty.beta1Words13,BottomEmpty.beta1Words14⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 146. -/
noncomputable def cache2_146 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 146. -/
noncomputable def cache3_146 : LinkCache := ⟨65,BottomForest.packed16250.rInput,BottomForest.packed16500.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 146. -/
theorem cachedLinkChecked146 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words146 BottomCase.words146 149504 cache0_146 cache1_146 cache2_146 cache3_146 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 146. -/
theorem linkChecked146 : ((List.range 1024).all fun j => linkCheck (149504+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked146 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words146 BottomCase.words146 149504 row
    cache0_146 cache1_146 cache2_146 cache3_146 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 146) (BottomCase.wordsAt 146) (1024*146) row = true := hc
  rw [linkChunkCheck_eq 146 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 147. -/
noncomputable def cache0_147 : LinkCache := ⟨116,BottomEmpty.beta0Words116,BottomEmpty.beta0Words117⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 147. -/
noncomputable def cache1_147 : LinkCache := ⟨13,BottomEmpty.beta1Words13,BottomEmpty.beta1Words14⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 147. -/
noncomputable def cache2_147 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 147. -/
noncomputable def cache3_147 : LinkCache := ⟨66,BottomForest.packed16500.rInput,BottomForest.packed16750.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 147. -/
theorem cachedLinkChecked147 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words147 BottomCase.words147 150528 cache0_147 cache1_147 cache2_147 cache3_147 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 147. -/
theorem linkChecked147 : ((List.range 1024).all fun j => linkCheck (150528+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked147 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words147 BottomCase.words147 150528 row
    cache0_147 cache1_147 cache2_147 cache3_147 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 147) (BottomCase.wordsAt 147) (1024*147) row = true := hc
  rw [linkChunkCheck_eq 147 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 148. -/
noncomputable def cache0_148 : LinkCache := ⟨117,BottomEmpty.beta0Words117,BottomEmpty.beta0Words118⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 148. -/
noncomputable def cache1_148 : LinkCache := ⟨13,BottomEmpty.beta1Words13,BottomEmpty.beta1Words14⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 148. -/
noncomputable def cache2_148 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 148. -/
noncomputable def cache3_148 : LinkCache := ⟨66,BottomForest.packed16500.rInput,BottomForest.packed16750.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 148. -/
theorem cachedLinkChecked148 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words148 BottomCase.words148 151552 cache0_148 cache1_148 cache2_148 cache3_148 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 148. -/
theorem linkChecked148 : ((List.range 1024).all fun j => linkCheck (151552+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked148 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words148 BottomCase.words148 151552 row
    cache0_148 cache1_148 cache2_148 cache3_148 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 148) (BottomCase.wordsAt 148) (1024*148) row = true := hc
  rw [linkChunkCheck_eq 148 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 149. -/
noncomputable def cache0_149 : LinkCache := ⟨118,BottomEmpty.beta0Words118,BottomEmpty.beta0Words119⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 149. -/
noncomputable def cache1_149 : LinkCache := ⟨13,BottomEmpty.beta1Words13,BottomEmpty.beta1Words14⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 149. -/
noncomputable def cache2_149 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 149. -/
noncomputable def cache3_149 : LinkCache := ⟨67,BottomForest.packed16750.rInput,BottomForest.packed17000.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 149. -/
theorem cachedLinkChecked149 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words149 BottomCase.words149 152576 cache0_149 cache1_149 cache2_149 cache3_149 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 149. -/
theorem linkChecked149 : ((List.range 1024).all fun j => linkCheck (152576+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked149 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words149 BottomCase.words149 152576 row
    cache0_149 cache1_149 cache2_149 cache3_149 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 149) (BottomCase.wordsAt 149) (1024*149) row = true := hc
  rw [linkChunkCheck_eq 149 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 150. -/
noncomputable def cache0_150 : LinkCache := ⟨119,BottomEmpty.beta0Words119,BottomEmpty.beta0Words120⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 150. -/
noncomputable def cache1_150 : LinkCache := ⟨13,BottomEmpty.beta1Words13,BottomEmpty.beta1Words14⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 150. -/
noncomputable def cache2_150 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 150. -/
noncomputable def cache3_150 : LinkCache := ⟨67,BottomForest.packed16750.rInput,BottomForest.packed17000.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 150. -/
theorem cachedLinkChecked150 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words150 BottomCase.words150 153600 cache0_150 cache1_150 cache2_150 cache3_150 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 150. -/
theorem linkChecked150 : ((List.range 1024).all fun j => linkCheck (153600+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked150 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words150 BottomCase.words150 153600 row
    cache0_150 cache1_150 cache2_150 cache3_150 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 150) (BottomCase.wordsAt 150) (1024*150) row = true := hc
  rw [linkChunkCheck_eq 150 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 151. -/
noncomputable def cache0_151 : LinkCache := ⟨120,BottomEmpty.beta0Words120,BottomEmpty.beta0Words121⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 151. -/
noncomputable def cache1_151 : LinkCache := ⟨13,BottomEmpty.beta1Words13,BottomEmpty.beta1Words14⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 151. -/
noncomputable def cache2_151 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 151. -/
noncomputable def cache3_151 : LinkCache := ⟨68,BottomForest.packed17000.rInput,BottomForest.packed17250.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 151. -/
theorem cachedLinkChecked151 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words151 BottomCase.words151 154624 cache0_151 cache1_151 cache2_151 cache3_151 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 151. -/
theorem linkChecked151 : ((List.range 1024).all fun j => linkCheck (154624+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked151 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words151 BottomCase.words151 154624 row
    cache0_151 cache1_151 cache2_151 cache3_151 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 151) (BottomCase.wordsAt 151) (1024*151) row = true := hc
  rw [linkChunkCheck_eq 151 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 152. -/
noncomputable def cache0_152 : LinkCache := ⟨120,BottomEmpty.beta0Words120,BottomEmpty.beta0Words121⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 152. -/
noncomputable def cache1_152 : LinkCache := ⟨13,BottomEmpty.beta1Words13,BottomEmpty.beta1Words14⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 152. -/
noncomputable def cache2_152 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 152. -/
noncomputable def cache3_152 : LinkCache := ⟨68,BottomForest.packed17000.rInput,BottomForest.packed17250.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 152. -/
theorem cachedLinkChecked152 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words152 BottomCase.words152 155648 cache0_152 cache1_152 cache2_152 cache3_152 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 152. -/
theorem linkChecked152 : ((List.range 1024).all fun j => linkCheck (155648+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked152 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words152 BottomCase.words152 155648 row
    cache0_152 cache1_152 cache2_152 cache3_152 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 152) (BottomCase.wordsAt 152) (1024*152) row = true := hc
  rw [linkChunkCheck_eq 152 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 153. -/
noncomputable def cache0_153 : LinkCache := ⟨121,BottomEmpty.beta0Words121,BottomEmpty.beta0Words122⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 153. -/
noncomputable def cache1_153 : LinkCache := ⟨13,BottomEmpty.beta1Words13,BottomEmpty.beta1Words14⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 153. -/
noncomputable def cache2_153 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 153. -/
noncomputable def cache3_153 : LinkCache := ⟨69,BottomForest.packed17250.rInput,BottomForest.packed17500.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 153. -/
theorem cachedLinkChecked153 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words153 BottomCase.words153 156672 cache0_153 cache1_153 cache2_153 cache3_153 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 153. -/
theorem linkChecked153 : ((List.range 1024).all fun j => linkCheck (156672+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked153 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words153 BottomCase.words153 156672 row
    cache0_153 cache1_153 cache2_153 cache3_153 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 153) (BottomCase.wordsAt 153) (1024*153) row = true := hc
  rw [linkChunkCheck_eq 153 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 154. -/
noncomputable def cache0_154 : LinkCache := ⟨122,BottomEmpty.beta0Words122,BottomEmpty.beta0Words123⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 154. -/
noncomputable def cache1_154 : LinkCache := ⟨13,BottomEmpty.beta1Words13,BottomEmpty.beta1Words14⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 154. -/
noncomputable def cache2_154 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 154. -/
noncomputable def cache3_154 : LinkCache := ⟨70,BottomForest.packed17500.rInput,BottomForest.packed17750.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 154. -/
theorem cachedLinkChecked154 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words154 BottomCase.words154 157696 cache0_154 cache1_154 cache2_154 cache3_154 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 154. -/
theorem linkChecked154 : ((List.range 1024).all fun j => linkCheck (157696+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked154 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words154 BottomCase.words154 157696 row
    cache0_154 cache1_154 cache2_154 cache3_154 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 154) (BottomCase.wordsAt 154) (1024*154) row = true := hc
  rw [linkChunkCheck_eq 154 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 155. -/
noncomputable def cache0_155 : LinkCache := ⟨123,BottomEmpty.beta0Words123,BottomEmpty.beta0Words124⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 155. -/
noncomputable def cache1_155 : LinkCache := ⟨13,BottomEmpty.beta1Words13,BottomEmpty.beta1Words14⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 155. -/
noncomputable def cache2_155 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 155. -/
noncomputable def cache3_155 : LinkCache := ⟨70,BottomForest.packed17500.rInput,BottomForest.packed17750.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 155. -/
theorem cachedLinkChecked155 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words155 BottomCase.words155 158720 cache0_155 cache1_155 cache2_155 cache3_155 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 155. -/
theorem linkChecked155 : ((List.range 1024).all fun j => linkCheck (158720+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked155 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words155 BottomCase.words155 158720 row
    cache0_155 cache1_155 cache2_155 cache3_155 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 155) (BottomCase.wordsAt 155) (1024*155) row = true := hc
  rw [linkChunkCheck_eq 155 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 156. -/
noncomputable def cache0_156 : LinkCache := ⟨124,BottomEmpty.beta0Words124,BottomEmpty.beta0Words125⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 156. -/
noncomputable def cache1_156 : LinkCache := ⟨13,BottomEmpty.beta1Words13,BottomEmpty.beta1Words14⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 156. -/
noncomputable def cache2_156 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 156. -/
noncomputable def cache3_156 : LinkCache := ⟨70,BottomForest.packed17500.rInput,BottomForest.packed17750.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 156. -/
theorem cachedLinkChecked156 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words156 BottomCase.words156 159744 cache0_156 cache1_156 cache2_156 cache3_156 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 156. -/
theorem linkChecked156 : ((List.range 1024).all fun j => linkCheck (159744+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked156 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words156 BottomCase.words156 159744 row
    cache0_156 cache1_156 cache2_156 cache3_156 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 156) (BottomCase.wordsAt 156) (1024*156) row = true := hc
  rw [linkChunkCheck_eq 156 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 157. -/
noncomputable def cache0_157 : LinkCache := ⟨124,BottomEmpty.beta0Words124,BottomEmpty.beta0Words125⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 157. -/
noncomputable def cache1_157 : LinkCache := ⟨13,BottomEmpty.beta1Words13,BottomEmpty.beta1Words14⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 157. -/
noncomputable def cache2_157 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 157. -/
noncomputable def cache3_157 : LinkCache := ⟨71,BottomForest.packed17750.rInput,BottomForest.packed18000.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 157. -/
theorem cachedLinkChecked157 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words157 BottomCase.words157 160768 cache0_157 cache1_157 cache2_157 cache3_157 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 157. -/
theorem linkChecked157 : ((List.range 1024).all fun j => linkCheck (160768+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked157 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words157 BottomCase.words157 160768 row
    cache0_157 cache1_157 cache2_157 cache3_157 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 157) (BottomCase.wordsAt 157) (1024*157) row = true := hc
  rw [linkChunkCheck_eq 157 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 158. -/
noncomputable def cache0_158 : LinkCache := ⟨125,BottomEmpty.beta0Words125,BottomEmpty.beta0Words126⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 158. -/
noncomputable def cache1_158 : LinkCache := ⟨13,BottomEmpty.beta1Words13,BottomEmpty.beta1Words14⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 158. -/
noncomputable def cache2_158 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 158. -/
noncomputable def cache3_158 : LinkCache := ⟨71,BottomForest.packed17750.rInput,BottomForest.packed18000.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 158. -/
theorem cachedLinkChecked158 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words158 BottomCase.words158 161792 cache0_158 cache1_158 cache2_158 cache3_158 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 158. -/
theorem linkChecked158 : ((List.range 1024).all fun j => linkCheck (161792+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked158 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words158 BottomCase.words158 161792 row
    cache0_158 cache1_158 cache2_158 cache3_158 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 158) (BottomCase.wordsAt 158) (1024*158) row = true := hc
  rw [linkChunkCheck_eq 158 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 159. -/
noncomputable def cache0_159 : LinkCache := ⟨126,BottomEmpty.beta0Words126,BottomEmpty.beta0Words127⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 159. -/
noncomputable def cache1_159 : LinkCache := ⟨14,BottomEmpty.beta1Words14,BottomEmpty.beta1Words15⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 159. -/
noncomputable def cache2_159 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 159. -/
noncomputable def cache3_159 : LinkCache := ⟨72,BottomForest.packed18000.rInput,BottomForest.packed18250.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 159. -/
theorem cachedLinkChecked159 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words159 BottomCase.words159 162816 cache0_159 cache1_159 cache2_159 cache3_159 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 159. -/
theorem linkChecked159 : ((List.range 1024).all fun j => linkCheck (162816+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked159 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words159 BottomCase.words159 162816 row
    cache0_159 cache1_159 cache2_159 cache3_159 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 159) (BottomCase.wordsAt 159) (1024*159) row = true := hc
  rw [linkChunkCheck_eq 159 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
#print axioms linkChecked128
end Quantum.Stabilizer.Homological.BB.Bravyi360.BottomShallow
