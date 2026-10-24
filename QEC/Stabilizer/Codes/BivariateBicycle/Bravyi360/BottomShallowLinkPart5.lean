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
/-- Adjacent family 0 data blocks for census chunk 160. -/
noncomputable def cache0_160 : LinkCache := ⟨127,BottomEmpty.beta0Words127,BottomEmpty.beta0Words128⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 160. -/
noncomputable def cache1_160 : LinkCache := ⟨14,BottomEmpty.beta1Words14,BottomEmpty.beta1Words15⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 160. -/
noncomputable def cache2_160 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 160. -/
noncomputable def cache3_160 : LinkCache := ⟨73,BottomForest.packed18250.rInput,BottomForest.packed18500.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 160. -/
theorem cachedLinkChecked160 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words160 BottomCase.words160 163840 cache0_160 cache1_160 cache2_160 cache3_160 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 160. -/
theorem linkChecked160 : ((List.range 1024).all fun j => linkCheck (163840+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked160 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words160 BottomCase.words160 163840 row
    cache0_160 cache1_160 cache2_160 cache3_160 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 160) (BottomCase.wordsAt 160) (1024*160) row = true := hc
  rw [linkChunkCheck_eq 160 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 161. -/
noncomputable def cache0_161 : LinkCache := ⟨128,BottomEmpty.beta0Words128,BottomEmpty.beta0Words129⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 161. -/
noncomputable def cache1_161 : LinkCache := ⟨14,BottomEmpty.beta1Words14,BottomEmpty.beta1Words15⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 161. -/
noncomputable def cache2_161 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 161. -/
noncomputable def cache3_161 : LinkCache := ⟨73,BottomForest.packed18250.rInput,BottomForest.packed18500.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 161. -/
theorem cachedLinkChecked161 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words161 BottomCase.words161 164864 cache0_161 cache1_161 cache2_161 cache3_161 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 161. -/
theorem linkChecked161 : ((List.range 1024).all fun j => linkCheck (164864+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked161 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words161 BottomCase.words161 164864 row
    cache0_161 cache1_161 cache2_161 cache3_161 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 161) (BottomCase.wordsAt 161) (1024*161) row = true := hc
  rw [linkChunkCheck_eq 161 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 162. -/
noncomputable def cache0_162 : LinkCache := ⟨128,BottomEmpty.beta0Words128,BottomEmpty.beta0Words129⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 162. -/
noncomputable def cache1_162 : LinkCache := ⟨14,BottomEmpty.beta1Words14,BottomEmpty.beta1Words15⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 162. -/
noncomputable def cache2_162 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 162. -/
noncomputable def cache3_162 : LinkCache := ⟨74,BottomForest.packed18500.rInput,BottomForest.packed18750.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 162. -/
theorem cachedLinkChecked162 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words162 BottomCase.words162 165888 cache0_162 cache1_162 cache2_162 cache3_162 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 162. -/
theorem linkChecked162 : ((List.range 1024).all fun j => linkCheck (165888+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked162 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words162 BottomCase.words162 165888 row
    cache0_162 cache1_162 cache2_162 cache3_162 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 162) (BottomCase.wordsAt 162) (1024*162) row = true := hc
  rw [linkChunkCheck_eq 162 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 163. -/
noncomputable def cache0_163 : LinkCache := ⟨129,BottomEmpty.beta0Words129,BottomEmpty.beta0Words130⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 163. -/
noncomputable def cache1_163 : LinkCache := ⟨14,BottomEmpty.beta1Words14,BottomEmpty.beta1Words15⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 163. -/
noncomputable def cache2_163 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 163. -/
noncomputable def cache3_163 : LinkCache := ⟨74,BottomForest.packed18500.rInput,BottomForest.packed18750.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 163. -/
theorem cachedLinkChecked163 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words163 BottomCase.words163 166912 cache0_163 cache1_163 cache2_163 cache3_163 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 163. -/
theorem linkChecked163 : ((List.range 1024).all fun j => linkCheck (166912+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked163 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words163 BottomCase.words163 166912 row
    cache0_163 cache1_163 cache2_163 cache3_163 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 163) (BottomCase.wordsAt 163) (1024*163) row = true := hc
  rw [linkChunkCheck_eq 163 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 164. -/
noncomputable def cache0_164 : LinkCache := ⟨130,BottomEmpty.beta0Words130,BottomEmpty.beta0Words131⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 164. -/
noncomputable def cache1_164 : LinkCache := ⟨14,BottomEmpty.beta1Words14,BottomEmpty.beta1Words15⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 164. -/
noncomputable def cache2_164 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 164. -/
noncomputable def cache3_164 : LinkCache := ⟨75,BottomForest.packed18750.rInput,BottomForest.packed19000.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 164. -/
theorem cachedLinkChecked164 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words164 BottomCase.words164 167936 cache0_164 cache1_164 cache2_164 cache3_164 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 164. -/
theorem linkChecked164 : ((List.range 1024).all fun j => linkCheck (167936+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked164 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words164 BottomCase.words164 167936 row
    cache0_164 cache1_164 cache2_164 cache3_164 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 164) (BottomCase.wordsAt 164) (1024*164) row = true := hc
  rw [linkChunkCheck_eq 164 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 165. -/
noncomputable def cache0_165 : LinkCache := ⟨131,BottomEmpty.beta0Words131,BottomEmpty.beta0Words132⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 165. -/
noncomputable def cache1_165 : LinkCache := ⟨14,BottomEmpty.beta1Words14,BottomEmpty.beta1Words15⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 165. -/
noncomputable def cache2_165 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 165. -/
noncomputable def cache3_165 : LinkCache := ⟨75,BottomForest.packed18750.rInput,BottomForest.packed19000.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 165. -/
theorem cachedLinkChecked165 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words165 BottomCase.words165 168960 cache0_165 cache1_165 cache2_165 cache3_165 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 165. -/
theorem linkChecked165 : ((List.range 1024).all fun j => linkCheck (168960+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked165 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words165 BottomCase.words165 168960 row
    cache0_165 cache1_165 cache2_165 cache3_165 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 165) (BottomCase.wordsAt 165) (1024*165) row = true := hc
  rw [linkChunkCheck_eq 165 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 166. -/
noncomputable def cache0_166 : LinkCache := ⟨132,BottomEmpty.beta0Words132,BottomEmpty.beta0Words133⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 166. -/
noncomputable def cache1_166 : LinkCache := ⟨14,BottomEmpty.beta1Words14,BottomEmpty.beta1Words15⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 166. -/
noncomputable def cache2_166 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 166. -/
noncomputable def cache3_166 : LinkCache := ⟨75,BottomForest.packed18750.rInput,BottomForest.packed19000.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 166. -/
theorem cachedLinkChecked166 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words166 BottomCase.words166 169984 cache0_166 cache1_166 cache2_166 cache3_166 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 166. -/
theorem linkChecked166 : ((List.range 1024).all fun j => linkCheck (169984+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked166 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words166 BottomCase.words166 169984 row
    cache0_166 cache1_166 cache2_166 cache3_166 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 166) (BottomCase.wordsAt 166) (1024*166) row = true := hc
  rw [linkChunkCheck_eq 166 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 167. -/
noncomputable def cache0_167 : LinkCache := ⟨132,BottomEmpty.beta0Words132,BottomEmpty.beta0Words133⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 167. -/
noncomputable def cache1_167 : LinkCache := ⟨14,BottomEmpty.beta1Words14,BottomEmpty.beta1Words15⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 167. -/
noncomputable def cache2_167 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 167. -/
noncomputable def cache3_167 : LinkCache := ⟨76,BottomForest.packed19000.rInput,BottomForest.packed19250.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 167. -/
theorem cachedLinkChecked167 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words167 BottomCase.words167 171008 cache0_167 cache1_167 cache2_167 cache3_167 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 167. -/
theorem linkChecked167 : ((List.range 1024).all fun j => linkCheck (171008+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked167 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words167 BottomCase.words167 171008 row
    cache0_167 cache1_167 cache2_167 cache3_167 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 167) (BottomCase.wordsAt 167) (1024*167) row = true := hc
  rw [linkChunkCheck_eq 167 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 168. -/
noncomputable def cache0_168 : LinkCache := ⟨133,BottomEmpty.beta0Words133,BottomEmpty.beta0Words134⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 168. -/
noncomputable def cache1_168 : LinkCache := ⟨14,BottomEmpty.beta1Words14,BottomEmpty.beta1Words15⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 168. -/
noncomputable def cache2_168 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 168. -/
noncomputable def cache3_168 : LinkCache := ⟨76,BottomForest.packed19000.rInput,BottomForest.packed19250.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 168. -/
theorem cachedLinkChecked168 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words168 BottomCase.words168 172032 cache0_168 cache1_168 cache2_168 cache3_168 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 168. -/
theorem linkChecked168 : ((List.range 1024).all fun j => linkCheck (172032+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked168 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words168 BottomCase.words168 172032 row
    cache0_168 cache1_168 cache2_168 cache3_168 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 168) (BottomCase.wordsAt 168) (1024*168) row = true := hc
  rw [linkChunkCheck_eq 168 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 169. -/
noncomputable def cache0_169 : LinkCache := ⟨134,BottomEmpty.beta0Words134,BottomEmpty.beta0Words135⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 169. -/
noncomputable def cache1_169 : LinkCache := ⟨14,BottomEmpty.beta1Words14,BottomEmpty.beta1Words15⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 169. -/
noncomputable def cache2_169 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 169. -/
noncomputable def cache3_169 : LinkCache := ⟨76,BottomForest.packed19000.rInput,BottomForest.packed19250.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 169. -/
theorem cachedLinkChecked169 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words169 BottomCase.words169 173056 cache0_169 cache1_169 cache2_169 cache3_169 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 169. -/
theorem linkChecked169 : ((List.range 1024).all fun j => linkCheck (173056+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked169 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words169 BottomCase.words169 173056 row
    cache0_169 cache1_169 cache2_169 cache3_169 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 169) (BottomCase.wordsAt 169) (1024*169) row = true := hc
  rw [linkChunkCheck_eq 169 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 170. -/
noncomputable def cache0_170 : LinkCache := ⟨135,BottomEmpty.beta0Words135,BottomEmpty.beta0Words136⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 170. -/
noncomputable def cache1_170 : LinkCache := ⟨15,BottomEmpty.beta1Words15,BottomEmpty.beta1Words16⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 170. -/
noncomputable def cache2_170 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 170. -/
noncomputable def cache3_170 : LinkCache := ⟨76,BottomForest.packed19000.rInput,BottomForest.packed19250.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 170. -/
theorem cachedLinkChecked170 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words170 BottomCase.words170 174080 cache0_170 cache1_170 cache2_170 cache3_170 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 170. -/
theorem linkChecked170 : ((List.range 1024).all fun j => linkCheck (174080+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked170 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words170 BottomCase.words170 174080 row
    cache0_170 cache1_170 cache2_170 cache3_170 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 170) (BottomCase.wordsAt 170) (1024*170) row = true := hc
  rw [linkChunkCheck_eq 170 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 171. -/
noncomputable def cache0_171 : LinkCache := ⟨136,BottomEmpty.beta0Words136,BottomEmpty.beta0Words137⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 171. -/
noncomputable def cache1_171 : LinkCache := ⟨15,BottomEmpty.beta1Words15,BottomEmpty.beta1Words16⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 171. -/
noncomputable def cache2_171 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 171. -/
noncomputable def cache3_171 : LinkCache := ⟨77,BottomForest.packed19250.rInput,BottomForest.packed19500.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 171. -/
theorem cachedLinkChecked171 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words171 BottomCase.words171 175104 cache0_171 cache1_171 cache2_171 cache3_171 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 171. -/
theorem linkChecked171 : ((List.range 1024).all fun j => linkCheck (175104+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked171 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words171 BottomCase.words171 175104 row
    cache0_171 cache1_171 cache2_171 cache3_171 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 171) (BottomCase.wordsAt 171) (1024*171) row = true := hc
  rw [linkChunkCheck_eq 171 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 172. -/
noncomputable def cache0_172 : LinkCache := ⟨137,BottomEmpty.beta0Words137,BottomEmpty.beta0Words138⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 172. -/
noncomputable def cache1_172 : LinkCache := ⟨15,BottomEmpty.beta1Words15,BottomEmpty.beta1Words16⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 172. -/
noncomputable def cache2_172 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 172. -/
noncomputable def cache3_172 : LinkCache := ⟨77,BottomForest.packed19250.rInput,BottomForest.packed19500.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 172. -/
theorem cachedLinkChecked172 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words172 BottomCase.words172 176128 cache0_172 cache1_172 cache2_172 cache3_172 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 172. -/
theorem linkChecked172 : ((List.range 1024).all fun j => linkCheck (176128+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked172 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words172 BottomCase.words172 176128 row
    cache0_172 cache1_172 cache2_172 cache3_172 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 172) (BottomCase.wordsAt 172) (1024*172) row = true := hc
  rw [linkChunkCheck_eq 172 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 173. -/
noncomputable def cache0_173 : LinkCache := ⟨137,BottomEmpty.beta0Words137,BottomEmpty.beta0Words138⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 173. -/
noncomputable def cache1_173 : LinkCache := ⟨15,BottomEmpty.beta1Words15,BottomEmpty.beta1Words16⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 173. -/
noncomputable def cache2_173 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 173. -/
noncomputable def cache3_173 : LinkCache := ⟨77,BottomForest.packed19250.rInput,BottomForest.packed19500.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 173. -/
theorem cachedLinkChecked173 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words173 BottomCase.words173 177152 cache0_173 cache1_173 cache2_173 cache3_173 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 173. -/
theorem linkChecked173 : ((List.range 1024).all fun j => linkCheck (177152+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked173 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words173 BottomCase.words173 177152 row
    cache0_173 cache1_173 cache2_173 cache3_173 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 173) (BottomCase.wordsAt 173) (1024*173) row = true := hc
  rw [linkChunkCheck_eq 173 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 174. -/
noncomputable def cache0_174 : LinkCache := ⟨138,BottomEmpty.beta0Words138,BottomEmpty.beta0Words139⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 174. -/
noncomputable def cache1_174 : LinkCache := ⟨15,BottomEmpty.beta1Words15,BottomEmpty.beta1Words16⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 174. -/
noncomputable def cache2_174 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 174. -/
noncomputable def cache3_174 : LinkCache := ⟨78,BottomForest.packed19500.rInput,BottomForest.packed19750.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 174. -/
theorem cachedLinkChecked174 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words174 BottomCase.words174 178176 cache0_174 cache1_174 cache2_174 cache3_174 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 174. -/
theorem linkChecked174 : ((List.range 1024).all fun j => linkCheck (178176+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked174 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words174 BottomCase.words174 178176 row
    cache0_174 cache1_174 cache2_174 cache3_174 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 174) (BottomCase.wordsAt 174) (1024*174) row = true := hc
  rw [linkChunkCheck_eq 174 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 175. -/
noncomputable def cache0_175 : LinkCache := ⟨139,BottomEmpty.beta0Words139,BottomEmpty.beta0Words140⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 175. -/
noncomputable def cache1_175 : LinkCache := ⟨15,BottomEmpty.beta1Words15,BottomEmpty.beta1Words16⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 175. -/
noncomputable def cache2_175 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 175. -/
noncomputable def cache3_175 : LinkCache := ⟨78,BottomForest.packed19500.rInput,BottomForest.packed19750.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 175. -/
theorem cachedLinkChecked175 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words175 BottomCase.words175 179200 cache0_175 cache1_175 cache2_175 cache3_175 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 175. -/
theorem linkChecked175 : ((List.range 1024).all fun j => linkCheck (179200+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked175 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words175 BottomCase.words175 179200 row
    cache0_175 cache1_175 cache2_175 cache3_175 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 175) (BottomCase.wordsAt 175) (1024*175) row = true := hc
  rw [linkChunkCheck_eq 175 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 176. -/
noncomputable def cache0_176 : LinkCache := ⟨140,BottomEmpty.beta0Words140,BottomEmpty.beta0Words141⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 176. -/
noncomputable def cache1_176 : LinkCache := ⟨15,BottomEmpty.beta1Words15,BottomEmpty.beta1Words16⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 176. -/
noncomputable def cache2_176 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 176. -/
noncomputable def cache3_176 : LinkCache := ⟨78,BottomForest.packed19500.rInput,BottomForest.packed19750.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 176. -/
theorem cachedLinkChecked176 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words176 BottomCase.words176 180224 cache0_176 cache1_176 cache2_176 cache3_176 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 176. -/
theorem linkChecked176 : ((List.range 1024).all fun j => linkCheck (180224+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked176 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words176 BottomCase.words176 180224 row
    cache0_176 cache1_176 cache2_176 cache3_176 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 176) (BottomCase.wordsAt 176) (1024*176) row = true := hc
  rw [linkChunkCheck_eq 176 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 177. -/
noncomputable def cache0_177 : LinkCache := ⟨141,BottomEmpty.beta0Words141,BottomEmpty.beta0Words142⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 177. -/
noncomputable def cache1_177 : LinkCache := ⟨15,BottomEmpty.beta1Words15,BottomEmpty.beta1Words16⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 177. -/
noncomputable def cache2_177 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 177. -/
noncomputable def cache3_177 : LinkCache := ⟨79,BottomForest.packed19750.rInput,BottomForest.packed20000.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 177. -/
theorem cachedLinkChecked177 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words177 BottomCase.words177 181248 cache0_177 cache1_177 cache2_177 cache3_177 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 177. -/
theorem linkChecked177 : ((List.range 1024).all fun j => linkCheck (181248+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked177 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words177 BottomCase.words177 181248 row
    cache0_177 cache1_177 cache2_177 cache3_177 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 177) (BottomCase.wordsAt 177) (1024*177) row = true := hc
  rw [linkChunkCheck_eq 177 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 178. -/
noncomputable def cache0_178 : LinkCache := ⟨142,BottomEmpty.beta0Words142,BottomEmpty.beta0Words143⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 178. -/
noncomputable def cache1_178 : LinkCache := ⟨15,BottomEmpty.beta1Words15,BottomEmpty.beta1Words16⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 178. -/
noncomputable def cache2_178 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 178. -/
noncomputable def cache3_178 : LinkCache := ⟨79,BottomForest.packed19750.rInput,BottomForest.packed20000.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 178. -/
theorem cachedLinkChecked178 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words178 BottomCase.words178 182272 cache0_178 cache1_178 cache2_178 cache3_178 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 178. -/
theorem linkChecked178 : ((List.range 1024).all fun j => linkCheck (182272+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked178 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words178 BottomCase.words178 182272 row
    cache0_178 cache1_178 cache2_178 cache3_178 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 178) (BottomCase.wordsAt 178) (1024*178) row = true := hc
  rw [linkChunkCheck_eq 178 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 179. -/
noncomputable def cache0_179 : LinkCache := ⟨142,BottomEmpty.beta0Words142,BottomEmpty.beta0Words143⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 179. -/
noncomputable def cache1_179 : LinkCache := ⟨15,BottomEmpty.beta1Words15,BottomEmpty.beta1Words16⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 179. -/
noncomputable def cache2_179 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 179. -/
noncomputable def cache3_179 : LinkCache := ⟨80,BottomForest.packed20000.rInput,BottomForest.packed20250.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 179. -/
theorem cachedLinkChecked179 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words179 BottomCase.words179 183296 cache0_179 cache1_179 cache2_179 cache3_179 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 179. -/
theorem linkChecked179 : ((List.range 1024).all fun j => linkCheck (183296+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked179 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words179 BottomCase.words179 183296 row
    cache0_179 cache1_179 cache2_179 cache3_179 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 179) (BottomCase.wordsAt 179) (1024*179) row = true := hc
  rw [linkChunkCheck_eq 179 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 180. -/
noncomputable def cache0_180 : LinkCache := ⟨143,BottomEmpty.beta0Words143,BottomEmpty.beta0Words144⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 180. -/
noncomputable def cache1_180 : LinkCache := ⟨15,BottomEmpty.beta1Words15,BottomEmpty.beta1Words16⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 180. -/
noncomputable def cache2_180 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 180. -/
noncomputable def cache3_180 : LinkCache := ⟨80,BottomForest.packed20000.rInput,BottomForest.packed20250.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 180. -/
theorem cachedLinkChecked180 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words180 BottomCase.words180 184320 cache0_180 cache1_180 cache2_180 cache3_180 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 180. -/
theorem linkChecked180 : ((List.range 1024).all fun j => linkCheck (184320+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked180 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words180 BottomCase.words180 184320 row
    cache0_180 cache1_180 cache2_180 cache3_180 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 180) (BottomCase.wordsAt 180) (1024*180) row = true := hc
  rw [linkChunkCheck_eq 180 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 181. -/
noncomputable def cache0_181 : LinkCache := ⟨144,BottomEmpty.beta0Words144,BottomEmpty.beta0Words145⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 181. -/
noncomputable def cache1_181 : LinkCache := ⟨15,BottomEmpty.beta1Words15,BottomEmpty.beta1Words16⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 181. -/
noncomputable def cache2_181 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 181. -/
noncomputable def cache3_181 : LinkCache := ⟨80,BottomForest.packed20000.rInput,BottomForest.packed20250.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 181. -/
theorem cachedLinkChecked181 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words181 BottomCase.words181 185344 cache0_181 cache1_181 cache2_181 cache3_181 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 181. -/
theorem linkChecked181 : ((List.range 1024).all fun j => linkCheck (185344+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked181 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words181 BottomCase.words181 185344 row
    cache0_181 cache1_181 cache2_181 cache3_181 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 181) (BottomCase.wordsAt 181) (1024*181) row = true := hc
  rw [linkChunkCheck_eq 181 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 182. -/
noncomputable def cache0_182 : LinkCache := ⟨145,BottomEmpty.beta0Words145,BottomEmpty.beta0Words146⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 182. -/
noncomputable def cache1_182 : LinkCache := ⟨15,BottomEmpty.beta1Words15,BottomEmpty.beta1Words16⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 182. -/
noncomputable def cache2_182 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 182. -/
noncomputable def cache3_182 : LinkCache := ⟨81,BottomForest.packed20250.rInput,BottomForest.packed20500.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 182. -/
theorem cachedLinkChecked182 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words182 BottomCase.words182 186368 cache0_182 cache1_182 cache2_182 cache3_182 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 182. -/
theorem linkChecked182 : ((List.range 1024).all fun j => linkCheck (186368+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked182 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words182 BottomCase.words182 186368 row
    cache0_182 cache1_182 cache2_182 cache3_182 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 182) (BottomCase.wordsAt 182) (1024*182) row = true := hc
  rw [linkChunkCheck_eq 182 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 183. -/
noncomputable def cache0_183 : LinkCache := ⟨146,BottomEmpty.beta0Words146,BottomEmpty.beta0Words147⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 183. -/
noncomputable def cache1_183 : LinkCache := ⟨15,BottomEmpty.beta1Words15,BottomEmpty.beta1Words16⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 183. -/
noncomputable def cache2_183 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 183. -/
noncomputable def cache3_183 : LinkCache := ⟨81,BottomForest.packed20250.rInput,BottomForest.packed20500.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 183. -/
theorem cachedLinkChecked183 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words183 BottomCase.words183 187392 cache0_183 cache1_183 cache2_183 cache3_183 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 183. -/
theorem linkChecked183 : ((List.range 1024).all fun j => linkCheck (187392+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked183 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words183 BottomCase.words183 187392 row
    cache0_183 cache1_183 cache2_183 cache3_183 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 183) (BottomCase.wordsAt 183) (1024*183) row = true := hc
  rw [linkChunkCheck_eq 183 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 184. -/
noncomputable def cache0_184 : LinkCache := ⟨147,BottomEmpty.beta0Words147,BottomEmpty.beta0Words148⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 184. -/
noncomputable def cache1_184 : LinkCache := ⟨16,BottomEmpty.beta1Words16,BottomEmpty.beta1Words17⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 184. -/
noncomputable def cache2_184 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 184. -/
noncomputable def cache3_184 : LinkCache := ⟨82,BottomForest.packed20500.rInput,BottomForest.packed20750.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 184. -/
theorem cachedLinkChecked184 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words184 BottomCase.words184 188416 cache0_184 cache1_184 cache2_184 cache3_184 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 184. -/
theorem linkChecked184 : ((List.range 1024).all fun j => linkCheck (188416+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked184 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words184 BottomCase.words184 188416 row
    cache0_184 cache1_184 cache2_184 cache3_184 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 184) (BottomCase.wordsAt 184) (1024*184) row = true := hc
  rw [linkChunkCheck_eq 184 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 185. -/
noncomputable def cache0_185 : LinkCache := ⟨147,BottomEmpty.beta0Words147,BottomEmpty.beta0Words148⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 185. -/
noncomputable def cache1_185 : LinkCache := ⟨16,BottomEmpty.beta1Words16,BottomEmpty.beta1Words17⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 185. -/
noncomputable def cache2_185 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 185. -/
noncomputable def cache3_185 : LinkCache := ⟨82,BottomForest.packed20500.rInput,BottomForest.packed20750.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 185. -/
theorem cachedLinkChecked185 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words185 BottomCase.words185 189440 cache0_185 cache1_185 cache2_185 cache3_185 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 185. -/
theorem linkChecked185 : ((List.range 1024).all fun j => linkCheck (189440+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked185 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words185 BottomCase.words185 189440 row
    cache0_185 cache1_185 cache2_185 cache3_185 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 185) (BottomCase.wordsAt 185) (1024*185) row = true := hc
  rw [linkChunkCheck_eq 185 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 186. -/
noncomputable def cache0_186 : LinkCache := ⟨148,BottomEmpty.beta0Words148,BottomEmpty.beta0Words149⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 186. -/
noncomputable def cache1_186 : LinkCache := ⟨16,BottomEmpty.beta1Words16,BottomEmpty.beta1Words17⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 186. -/
noncomputable def cache2_186 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 186. -/
noncomputable def cache3_186 : LinkCache := ⟨82,BottomForest.packed20500.rInput,BottomForest.packed20750.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 186. -/
theorem cachedLinkChecked186 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words186 BottomCase.words186 190464 cache0_186 cache1_186 cache2_186 cache3_186 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 186. -/
theorem linkChecked186 : ((List.range 1024).all fun j => linkCheck (190464+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked186 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words186 BottomCase.words186 190464 row
    cache0_186 cache1_186 cache2_186 cache3_186 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 186) (BottomCase.wordsAt 186) (1024*186) row = true := hc
  rw [linkChunkCheck_eq 186 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 187. -/
noncomputable def cache0_187 : LinkCache := ⟨149,BottomEmpty.beta0Words149,BottomEmpty.beta0Words150⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 187. -/
noncomputable def cache1_187 : LinkCache := ⟨16,BottomEmpty.beta1Words16,BottomEmpty.beta1Words17⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 187. -/
noncomputable def cache2_187 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 187. -/
noncomputable def cache3_187 : LinkCache := ⟨83,BottomForest.packed20750.rInput,BottomForest.packed21000.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 187. -/
theorem cachedLinkChecked187 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words187 BottomCase.words187 191488 cache0_187 cache1_187 cache2_187 cache3_187 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 187. -/
theorem linkChecked187 : ((List.range 1024).all fun j => linkCheck (191488+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked187 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words187 BottomCase.words187 191488 row
    cache0_187 cache1_187 cache2_187 cache3_187 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 187) (BottomCase.wordsAt 187) (1024*187) row = true := hc
  rw [linkChunkCheck_eq 187 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 188. -/
noncomputable def cache0_188 : LinkCache := ⟨150,BottomEmpty.beta0Words150,BottomEmpty.beta0Words151⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 188. -/
noncomputable def cache1_188 : LinkCache := ⟨16,BottomEmpty.beta1Words16,BottomEmpty.beta1Words17⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 188. -/
noncomputable def cache2_188 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 188. -/
noncomputable def cache3_188 : LinkCache := ⟨83,BottomForest.packed20750.rInput,BottomForest.packed21000.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 188. -/
theorem cachedLinkChecked188 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words188 BottomCase.words188 192512 cache0_188 cache1_188 cache2_188 cache3_188 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 188. -/
theorem linkChecked188 : ((List.range 1024).all fun j => linkCheck (192512+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked188 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words188 BottomCase.words188 192512 row
    cache0_188 cache1_188 cache2_188 cache3_188 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 188) (BottomCase.wordsAt 188) (1024*188) row = true := hc
  rw [linkChunkCheck_eq 188 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 189. -/
noncomputable def cache0_189 : LinkCache := ⟨151,BottomEmpty.beta0Words151,BottomEmpty.beta0Words152⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 189. -/
noncomputable def cache1_189 : LinkCache := ⟨16,BottomEmpty.beta1Words16,BottomEmpty.beta1Words17⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 189. -/
noncomputable def cache2_189 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 189. -/
noncomputable def cache3_189 : LinkCache := ⟨83,BottomForest.packed20750.rInput,BottomForest.packed21000.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 189. -/
theorem cachedLinkChecked189 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words189 BottomCase.words189 193536 cache0_189 cache1_189 cache2_189 cache3_189 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 189. -/
theorem linkChecked189 : ((List.range 1024).all fun j => linkCheck (193536+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked189 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words189 BottomCase.words189 193536 row
    cache0_189 cache1_189 cache2_189 cache3_189 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 189) (BottomCase.wordsAt 189) (1024*189) row = true := hc
  rw [linkChunkCheck_eq 189 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 190. -/
noncomputable def cache0_190 : LinkCache := ⟨152,BottomEmpty.beta0Words152,BottomEmpty.beta0Words153⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 190. -/
noncomputable def cache1_190 : LinkCache := ⟨16,BottomEmpty.beta1Words16,BottomEmpty.beta1Words17⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 190. -/
noncomputable def cache2_190 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 190. -/
noncomputable def cache3_190 : LinkCache := ⟨84,BottomForest.packed21000.rInput,BottomForest.packed21250.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 190. -/
theorem cachedLinkChecked190 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words190 BottomCase.words190 194560 cache0_190 cache1_190 cache2_190 cache3_190 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 190. -/
theorem linkChecked190 : ((List.range 1024).all fun j => linkCheck (194560+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked190 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words190 BottomCase.words190 194560 row
    cache0_190 cache1_190 cache2_190 cache3_190 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 190) (BottomCase.wordsAt 190) (1024*190) row = true := hc
  rw [linkChunkCheck_eq 190 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 191. -/
noncomputable def cache0_191 : LinkCache := ⟨153,BottomEmpty.beta0Words153,BottomEmpty.beta0Words154⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 191. -/
noncomputable def cache1_191 : LinkCache := ⟨16,BottomEmpty.beta1Words16,BottomEmpty.beta1Words17⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 191. -/
noncomputable def cache2_191 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 191. -/
noncomputable def cache3_191 : LinkCache := ⟨84,BottomForest.packed21000.rInput,BottomForest.packed21250.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 191. -/
theorem cachedLinkChecked191 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words191 BottomCase.words191 195584 cache0_191 cache1_191 cache2_191 cache3_191 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 191. -/
theorem linkChecked191 : ((List.range 1024).all fun j => linkCheck (195584+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked191 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words191 BottomCase.words191 195584 row
    cache0_191 cache1_191 cache2_191 cache3_191 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 191) (BottomCase.wordsAt 191) (1024*191) row = true := hc
  rw [linkChunkCheck_eq 191 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
#print axioms linkChecked160
end Quantum.Stabilizer.Homological.BB.Bravyi360.BottomShallow
