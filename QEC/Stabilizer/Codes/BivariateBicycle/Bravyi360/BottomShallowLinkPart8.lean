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
/-- Adjacent family 0 data blocks for census chunk 256. -/
noncomputable def cache0_256 : LinkCache := ⟨208,BottomEmpty.beta0Words208,BottomEmpty.beta0Words209⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 256. -/
noncomputable def cache1_256 : LinkCache := ⟨19,BottomEmpty.beta1Words19,BottomEmpty.beta1Words20⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 256. -/
noncomputable def cache2_256 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 256. -/
noncomputable def cache3_256 : LinkCache := ⟨107,BottomForest.packed26750.rInput,BottomForest.packed27000.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 256. -/
theorem cachedLinkChecked256 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words256 BottomCase.words256 262144 cache0_256 cache1_256 cache2_256 cache3_256 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 256. -/
theorem linkChecked256 : ((List.range 1024).all fun j => linkCheck (262144+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked256 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words256 BottomCase.words256 262144 row
    cache0_256 cache1_256 cache2_256 cache3_256 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 256) (BottomCase.wordsAt 256) (1024*256) row = true := hc
  rw [linkChunkCheck_eq 256 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 257. -/
noncomputable def cache0_257 : LinkCache := ⟨209,BottomEmpty.beta0Words209,BottomEmpty.beta0Words210⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 257. -/
noncomputable def cache1_257 : LinkCache := ⟨20,BottomEmpty.beta1Words20,BottomEmpty.beta1Words20⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 257. -/
noncomputable def cache2_257 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 257. -/
noncomputable def cache3_257 : LinkCache := ⟨107,BottomForest.packed26750.rInput,BottomForest.packed27000.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 257. -/
theorem cachedLinkChecked257 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words257 BottomCase.words257 263168 cache0_257 cache1_257 cache2_257 cache3_257 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 257. -/
theorem linkChecked257 : ((List.range 1024).all fun j => linkCheck (263168+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked257 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words257 BottomCase.words257 263168 row
    cache0_257 cache1_257 cache2_257 cache3_257 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 257) (BottomCase.wordsAt 257) (1024*257) row = true := hc
  rw [linkChunkCheck_eq 257 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 258. -/
noncomputable def cache0_258 : LinkCache := ⟨210,BottomEmpty.beta0Words210,BottomEmpty.beta0Words211⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 258. -/
noncomputable def cache1_258 : LinkCache := ⟨20,BottomEmpty.beta1Words20,BottomEmpty.beta1Words20⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 258. -/
noncomputable def cache2_258 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 258. -/
noncomputable def cache3_258 : LinkCache := ⟨108,BottomForest.packed27000.rInput,BottomForest.packed27250.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 258. -/
theorem cachedLinkChecked258 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words258 BottomCase.words258 264192 cache0_258 cache1_258 cache2_258 cache3_258 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 258. -/
theorem linkChecked258 : ((List.range 1024).all fun j => linkCheck (264192+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked258 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words258 BottomCase.words258 264192 row
    cache0_258 cache1_258 cache2_258 cache3_258 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 258) (BottomCase.wordsAt 258) (1024*258) row = true := hc
  rw [linkChunkCheck_eq 258 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 259. -/
noncomputable def cache0_259 : LinkCache := ⟨211,BottomEmpty.beta0Words211,BottomEmpty.beta0Words212⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 259. -/
noncomputable def cache1_259 : LinkCache := ⟨20,BottomEmpty.beta1Words20,BottomEmpty.beta1Words20⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 259. -/
noncomputable def cache2_259 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 259. -/
noncomputable def cache3_259 : LinkCache := ⟨108,BottomForest.packed27000.rInput,BottomForest.packed27250.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 259. -/
theorem cachedLinkChecked259 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words259 BottomCase.words259 265216 cache0_259 cache1_259 cache2_259 cache3_259 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 259. -/
theorem linkChecked259 : ((List.range 1024).all fun j => linkCheck (265216+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked259 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words259 BottomCase.words259 265216 row
    cache0_259 cache1_259 cache2_259 cache3_259 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 259) (BottomCase.wordsAt 259) (1024*259) row = true := hc
  rw [linkChunkCheck_eq 259 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 260. -/
noncomputable def cache0_260 : LinkCache := ⟨212,BottomEmpty.beta0Words212,BottomEmpty.beta0Words213⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 260. -/
noncomputable def cache1_260 : LinkCache := ⟨20,BottomEmpty.beta1Words20,BottomEmpty.beta1Words20⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 260. -/
noncomputable def cache2_260 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 260. -/
noncomputable def cache3_260 : LinkCache := ⟨108,BottomForest.packed27000.rInput,BottomForest.packed27250.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 260. -/
theorem cachedLinkChecked260 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words260 BottomCase.words260 266240 cache0_260 cache1_260 cache2_260 cache3_260 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 260. -/
theorem linkChecked260 : ((List.range 1024).all fun j => linkCheck (266240+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked260 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words260 BottomCase.words260 266240 row
    cache0_260 cache1_260 cache2_260 cache3_260 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 260) (BottomCase.wordsAt 260) (1024*260) row = true := hc
  rw [linkChunkCheck_eq 260 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 261. -/
noncomputable def cache0_261 : LinkCache := ⟨213,BottomEmpty.beta0Words213,BottomEmpty.beta0Words214⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 261. -/
noncomputable def cache1_261 : LinkCache := ⟨20,BottomEmpty.beta1Words20,BottomEmpty.beta1Words20⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 261. -/
noncomputable def cache2_261 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 261. -/
noncomputable def cache3_261 : LinkCache := ⟨109,BottomForest.packed27250.rInput,BottomForest.packed27500.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 261. -/
theorem cachedLinkChecked261 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words261 BottomCase.words261 267264 cache0_261 cache1_261 cache2_261 cache3_261 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 261. -/
theorem linkChecked261 : ((List.range 1024).all fun j => linkCheck (267264+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked261 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words261 BottomCase.words261 267264 row
    cache0_261 cache1_261 cache2_261 cache3_261 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 261) (BottomCase.wordsAt 261) (1024*261) row = true := hc
  rw [linkChunkCheck_eq 261 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 262. -/
noncomputable def cache0_262 : LinkCache := ⟨214,BottomEmpty.beta0Words214,BottomEmpty.beta0Words215⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 262. -/
noncomputable def cache1_262 : LinkCache := ⟨20,BottomEmpty.beta1Words20,BottomEmpty.beta1Words20⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 262. -/
noncomputable def cache2_262 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 262. -/
noncomputable def cache3_262 : LinkCache := ⟨109,BottomForest.packed27250.rInput,BottomForest.packed27500.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 262. -/
theorem cachedLinkChecked262 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words262 BottomCase.words262 268288 cache0_262 cache1_262 cache2_262 cache3_262 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 262. -/
theorem linkChecked262 : ((List.range 1024).all fun j => linkCheck (268288+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked262 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words262 BottomCase.words262 268288 row
    cache0_262 cache1_262 cache2_262 cache3_262 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 262) (BottomCase.wordsAt 262) (1024*262) row = true := hc
  rw [linkChunkCheck_eq 262 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 263. -/
noncomputable def cache0_263 : LinkCache := ⟨215,BottomEmpty.beta0Words215,BottomEmpty.beta0Words216⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 263. -/
noncomputable def cache1_263 : LinkCache := ⟨20,BottomEmpty.beta1Words20,BottomEmpty.beta1Words20⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 263. -/
noncomputable def cache2_263 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 263. -/
noncomputable def cache3_263 : LinkCache := ⟨109,BottomForest.packed27250.rInput,BottomForest.packed27500.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 263. -/
theorem cachedLinkChecked263 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words263 BottomCase.words263 269312 cache0_263 cache1_263 cache2_263 cache3_263 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 263. -/
theorem linkChecked263 : ((List.range 1024).all fun j => linkCheck (269312+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked263 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words263 BottomCase.words263 269312 row
    cache0_263 cache1_263 cache2_263 cache3_263 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 263) (BottomCase.wordsAt 263) (1024*263) row = true := hc
  rw [linkChunkCheck_eq 263 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 264. -/
noncomputable def cache0_264 : LinkCache := ⟨215,BottomEmpty.beta0Words215,BottomEmpty.beta0Words216⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 264. -/
noncomputable def cache1_264 : LinkCache := ⟨20,BottomEmpty.beta1Words20,BottomEmpty.beta1Words20⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 264. -/
noncomputable def cache2_264 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 264. -/
noncomputable def cache3_264 : LinkCache := ⟨110,BottomForest.packed27500.rInput,BottomForest.packed27750.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 264. -/
theorem cachedLinkChecked264 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words264 BottomCase.words264 270336 cache0_264 cache1_264 cache2_264 cache3_264 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 264. -/
theorem linkChecked264 : ((List.range 1024).all fun j => linkCheck (270336+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked264 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words264 BottomCase.words264 270336 row
    cache0_264 cache1_264 cache2_264 cache3_264 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 264) (BottomCase.wordsAt 264) (1024*264) row = true := hc
  rw [linkChunkCheck_eq 264 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 265. -/
noncomputable def cache0_265 : LinkCache := ⟨216,BottomEmpty.beta0Words216,BottomEmpty.beta0Words217⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 265. -/
noncomputable def cache1_265 : LinkCache := ⟨20,BottomEmpty.beta1Words20,BottomEmpty.beta1Words20⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 265. -/
noncomputable def cache2_265 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 265. -/
noncomputable def cache3_265 : LinkCache := ⟨110,BottomForest.packed27500.rInput,BottomForest.packed27750.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 265. -/
theorem cachedLinkChecked265 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words265 BottomCase.words265 271360 cache0_265 cache1_265 cache2_265 cache3_265 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 265. -/
theorem linkChecked265 : ((List.range 1024).all fun j => linkCheck (271360+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked265 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words265 BottomCase.words265 271360 row
    cache0_265 cache1_265 cache2_265 cache3_265 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 265) (BottomCase.wordsAt 265) (1024*265) row = true := hc
  rw [linkChunkCheck_eq 265 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 266. -/
noncomputable def cache0_266 : LinkCache := ⟨217,BottomEmpty.beta0Words217,BottomEmpty.beta0Words218⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 266. -/
noncomputable def cache1_266 : LinkCache := ⟨20,BottomEmpty.beta1Words20,BottomEmpty.beta1Words20⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 266. -/
noncomputable def cache2_266 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 266. -/
noncomputable def cache3_266 : LinkCache := ⟨110,BottomForest.packed27500.rInput,BottomForest.packed27750.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 266. -/
theorem cachedLinkChecked266 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words266 BottomCase.words266 272384 cache0_266 cache1_266 cache2_266 cache3_266 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 266. -/
theorem linkChecked266 : ((List.range 1024).all fun j => linkCheck (272384+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked266 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words266 BottomCase.words266 272384 row
    cache0_266 cache1_266 cache2_266 cache3_266 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 266) (BottomCase.wordsAt 266) (1024*266) row = true := hc
  rw [linkChunkCheck_eq 266 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 267. -/
noncomputable def cache0_267 : LinkCache := ⟨218,BottomEmpty.beta0Words218,BottomEmpty.beta0Words219⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 267. -/
noncomputable def cache1_267 : LinkCache := ⟨20,BottomEmpty.beta1Words20,BottomEmpty.beta1Words20⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 267. -/
noncomputable def cache2_267 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 267. -/
noncomputable def cache3_267 : LinkCache := ⟨111,BottomForest.packed27750.rInput,BottomForest.packed27750.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 267. -/
theorem cachedLinkChecked267 : ((List.range 603).all fun j => linkCachedCheck OrbitBatchData.words267 BottomCase.words267 273408 cache0_267 cache1_267 cache2_267 cache3_267 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 267. -/
theorem linkChecked267 : ((List.range 603).all fun j => linkCheck (273408+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked267 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words267 BottomCase.words267 273408 row
    cache0_267 cache1_267 cache2_267 cache3_267 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 267) (BottomCase.wordsAt 267) (1024*267) row = true := hc
  rw [linkChunkCheck_eq 267 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
#print axioms linkChecked256
end Quantum.Stabilizer.Homological.BB.Bravyi360.BottomShallow
