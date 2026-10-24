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
/-- Adjacent family 0 data blocks for census chunk 224. -/
noncomputable def cache0_224 : LinkCache := ⟨181,BottomEmpty.beta0Words181,BottomEmpty.beta0Words182⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 224. -/
noncomputable def cache1_224 : LinkCache := ⟨18,BottomEmpty.beta1Words18,BottomEmpty.beta1Words19⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 224. -/
noncomputable def cache2_224 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 224. -/
noncomputable def cache3_224 : LinkCache := ⟨96,BottomForest.packed24000.rInput,BottomForest.packed24250.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 224. -/
theorem cachedLinkChecked224 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words224 BottomCase.words224 229376 cache0_224 cache1_224 cache2_224 cache3_224 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 224. -/
theorem linkChecked224 : ((List.range 1024).all fun j => linkCheck (229376+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked224 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words224 BottomCase.words224 229376 row
    cache0_224 cache1_224 cache2_224 cache3_224 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 224) (BottomCase.wordsAt 224) (1024*224) row = true := hc
  rw [linkChunkCheck_eq 224 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 225. -/
noncomputable def cache0_225 : LinkCache := ⟨181,BottomEmpty.beta0Words181,BottomEmpty.beta0Words182⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 225. -/
noncomputable def cache1_225 : LinkCache := ⟨18,BottomEmpty.beta1Words18,BottomEmpty.beta1Words19⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 225. -/
noncomputable def cache2_225 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 225. -/
noncomputable def cache3_225 : LinkCache := ⟨96,BottomForest.packed24000.rInput,BottomForest.packed24250.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 225. -/
theorem cachedLinkChecked225 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words225 BottomCase.words225 230400 cache0_225 cache1_225 cache2_225 cache3_225 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 225. -/
theorem linkChecked225 : ((List.range 1024).all fun j => linkCheck (230400+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked225 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words225 BottomCase.words225 230400 row
    cache0_225 cache1_225 cache2_225 cache3_225 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 225) (BottomCase.wordsAt 225) (1024*225) row = true := hc
  rw [linkChunkCheck_eq 225 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 226. -/
noncomputable def cache0_226 : LinkCache := ⟨182,BottomEmpty.beta0Words182,BottomEmpty.beta0Words183⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 226. -/
noncomputable def cache1_226 : LinkCache := ⟨18,BottomEmpty.beta1Words18,BottomEmpty.beta1Words19⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 226. -/
noncomputable def cache2_226 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 226. -/
noncomputable def cache3_226 : LinkCache := ⟨97,BottomForest.packed24250.rInput,BottomForest.packed24500.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 226. -/
theorem cachedLinkChecked226 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words226 BottomCase.words226 231424 cache0_226 cache1_226 cache2_226 cache3_226 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 226. -/
theorem linkChecked226 : ((List.range 1024).all fun j => linkCheck (231424+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked226 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words226 BottomCase.words226 231424 row
    cache0_226 cache1_226 cache2_226 cache3_226 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 226) (BottomCase.wordsAt 226) (1024*226) row = true := hc
  rw [linkChunkCheck_eq 226 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 227. -/
noncomputable def cache0_227 : LinkCache := ⟨183,BottomEmpty.beta0Words183,BottomEmpty.beta0Words184⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 227. -/
noncomputable def cache1_227 : LinkCache := ⟨18,BottomEmpty.beta1Words18,BottomEmpty.beta1Words19⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 227. -/
noncomputable def cache2_227 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 227. -/
noncomputable def cache3_227 : LinkCache := ⟨97,BottomForest.packed24250.rInput,BottomForest.packed24500.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 227. -/
theorem cachedLinkChecked227 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words227 BottomCase.words227 232448 cache0_227 cache1_227 cache2_227 cache3_227 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 227. -/
theorem linkChecked227 : ((List.range 1024).all fun j => linkCheck (232448+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked227 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words227 BottomCase.words227 232448 row
    cache0_227 cache1_227 cache2_227 cache3_227 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 227) (BottomCase.wordsAt 227) (1024*227) row = true := hc
  rw [linkChunkCheck_eq 227 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 228. -/
noncomputable def cache0_228 : LinkCache := ⟨184,BottomEmpty.beta0Words184,BottomEmpty.beta0Words185⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 228. -/
noncomputable def cache1_228 : LinkCache := ⟨18,BottomEmpty.beta1Words18,BottomEmpty.beta1Words19⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 228. -/
noncomputable def cache2_228 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 228. -/
noncomputable def cache3_228 : LinkCache := ⟨98,BottomForest.packed24500.rInput,BottomForest.packed24750.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 228. -/
theorem cachedLinkChecked228 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words228 BottomCase.words228 233472 cache0_228 cache1_228 cache2_228 cache3_228 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 228. -/
theorem linkChecked228 : ((List.range 1024).all fun j => linkCheck (233472+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked228 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words228 BottomCase.words228 233472 row
    cache0_228 cache1_228 cache2_228 cache3_228 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 228) (BottomCase.wordsAt 228) (1024*228) row = true := hc
  rw [linkChunkCheck_eq 228 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 229. -/
noncomputable def cache0_229 : LinkCache := ⟨185,BottomEmpty.beta0Words185,BottomEmpty.beta0Words186⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 229. -/
noncomputable def cache1_229 : LinkCache := ⟨18,BottomEmpty.beta1Words18,BottomEmpty.beta1Words19⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 229. -/
noncomputable def cache2_229 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 229. -/
noncomputable def cache3_229 : LinkCache := ⟨98,BottomForest.packed24500.rInput,BottomForest.packed24750.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 229. -/
theorem cachedLinkChecked229 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words229 BottomCase.words229 234496 cache0_229 cache1_229 cache2_229 cache3_229 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 229. -/
theorem linkChecked229 : ((List.range 1024).all fun j => linkCheck (234496+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked229 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words229 BottomCase.words229 234496 row
    cache0_229 cache1_229 cache2_229 cache3_229 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 229) (BottomCase.wordsAt 229) (1024*229) row = true := hc
  rw [linkChunkCheck_eq 229 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 230. -/
noncomputable def cache0_230 : LinkCache := ⟨186,BottomEmpty.beta0Words186,BottomEmpty.beta0Words187⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 230. -/
noncomputable def cache1_230 : LinkCache := ⟨18,BottomEmpty.beta1Words18,BottomEmpty.beta1Words19⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 230. -/
noncomputable def cache2_230 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 230. -/
noncomputable def cache3_230 : LinkCache := ⟨98,BottomForest.packed24500.rInput,BottomForest.packed24750.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 230. -/
theorem cachedLinkChecked230 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words230 BottomCase.words230 235520 cache0_230 cache1_230 cache2_230 cache3_230 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 230. -/
theorem linkChecked230 : ((List.range 1024).all fun j => linkCheck (235520+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked230 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words230 BottomCase.words230 235520 row
    cache0_230 cache1_230 cache2_230 cache3_230 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 230) (BottomCase.wordsAt 230) (1024*230) row = true := hc
  rw [linkChunkCheck_eq 230 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 231. -/
noncomputable def cache0_231 : LinkCache := ⟨187,BottomEmpty.beta0Words187,BottomEmpty.beta0Words188⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 231. -/
noncomputable def cache1_231 : LinkCache := ⟨18,BottomEmpty.beta1Words18,BottomEmpty.beta1Words19⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 231. -/
noncomputable def cache2_231 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 231. -/
noncomputable def cache3_231 : LinkCache := ⟨99,BottomForest.packed24750.rInput,BottomForest.packed25000.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 231. -/
theorem cachedLinkChecked231 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words231 BottomCase.words231 236544 cache0_231 cache1_231 cache2_231 cache3_231 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 231. -/
theorem linkChecked231 : ((List.range 1024).all fun j => linkCheck (236544+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked231 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words231 BottomCase.words231 236544 row
    cache0_231 cache1_231 cache2_231 cache3_231 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 231) (BottomCase.wordsAt 231) (1024*231) row = true := hc
  rw [linkChunkCheck_eq 231 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 232. -/
noncomputable def cache0_232 : LinkCache := ⟨188,BottomEmpty.beta0Words188,BottomEmpty.beta0Words189⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 232. -/
noncomputable def cache1_232 : LinkCache := ⟨18,BottomEmpty.beta1Words18,BottomEmpty.beta1Words19⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 232. -/
noncomputable def cache2_232 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 232. -/
noncomputable def cache3_232 : LinkCache := ⟨99,BottomForest.packed24750.rInput,BottomForest.packed25000.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 232. -/
theorem cachedLinkChecked232 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words232 BottomCase.words232 237568 cache0_232 cache1_232 cache2_232 cache3_232 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 232. -/
theorem linkChecked232 : ((List.range 1024).all fun j => linkCheck (237568+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked232 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words232 BottomCase.words232 237568 row
    cache0_232 cache1_232 cache2_232 cache3_232 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 232) (BottomCase.wordsAt 232) (1024*232) row = true := hc
  rw [linkChunkCheck_eq 232 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 233. -/
noncomputable def cache0_233 : LinkCache := ⟨188,BottomEmpty.beta0Words188,BottomEmpty.beta0Words189⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 233. -/
noncomputable def cache1_233 : LinkCache := ⟨18,BottomEmpty.beta1Words18,BottomEmpty.beta1Words19⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 233. -/
noncomputable def cache2_233 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 233. -/
noncomputable def cache3_233 : LinkCache := ⟨99,BottomForest.packed24750.rInput,BottomForest.packed25000.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 233. -/
theorem cachedLinkChecked233 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words233 BottomCase.words233 238592 cache0_233 cache1_233 cache2_233 cache3_233 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 233. -/
theorem linkChecked233 : ((List.range 1024).all fun j => linkCheck (238592+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked233 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words233 BottomCase.words233 238592 row
    cache0_233 cache1_233 cache2_233 cache3_233 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 233) (BottomCase.wordsAt 233) (1024*233) row = true := hc
  rw [linkChunkCheck_eq 233 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 234. -/
noncomputable def cache0_234 : LinkCache := ⟨189,BottomEmpty.beta0Words189,BottomEmpty.beta0Words190⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 234. -/
noncomputable def cache1_234 : LinkCache := ⟨18,BottomEmpty.beta1Words18,BottomEmpty.beta1Words19⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 234. -/
noncomputable def cache2_234 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 234. -/
noncomputable def cache3_234 : LinkCache := ⟨100,BottomForest.packed25000.rInput,BottomForest.packed25250.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 234. -/
theorem cachedLinkChecked234 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words234 BottomCase.words234 239616 cache0_234 cache1_234 cache2_234 cache3_234 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 234. -/
theorem linkChecked234 : ((List.range 1024).all fun j => linkCheck (239616+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked234 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words234 BottomCase.words234 239616 row
    cache0_234 cache1_234 cache2_234 cache3_234 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 234) (BottomCase.wordsAt 234) (1024*234) row = true := hc
  rw [linkChunkCheck_eq 234 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 235. -/
noncomputable def cache0_235 : LinkCache := ⟨190,BottomEmpty.beta0Words190,BottomEmpty.beta0Words191⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 235. -/
noncomputable def cache1_235 : LinkCache := ⟨19,BottomEmpty.beta1Words19,BottomEmpty.beta1Words20⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 235. -/
noncomputable def cache2_235 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 235. -/
noncomputable def cache3_235 : LinkCache := ⟨100,BottomForest.packed25000.rInput,BottomForest.packed25250.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 235. -/
theorem cachedLinkChecked235 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words235 BottomCase.words235 240640 cache0_235 cache1_235 cache2_235 cache3_235 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 235. -/
theorem linkChecked235 : ((List.range 1024).all fun j => linkCheck (240640+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked235 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words235 BottomCase.words235 240640 row
    cache0_235 cache1_235 cache2_235 cache3_235 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 235) (BottomCase.wordsAt 235) (1024*235) row = true := hc
  rw [linkChunkCheck_eq 235 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 236. -/
noncomputable def cache0_236 : LinkCache := ⟨191,BottomEmpty.beta0Words191,BottomEmpty.beta0Words192⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 236. -/
noncomputable def cache1_236 : LinkCache := ⟨19,BottomEmpty.beta1Words19,BottomEmpty.beta1Words20⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 236. -/
noncomputable def cache2_236 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 236. -/
noncomputable def cache3_236 : LinkCache := ⟨100,BottomForest.packed25000.rInput,BottomForest.packed25250.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 236. -/
theorem cachedLinkChecked236 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words236 BottomCase.words236 241664 cache0_236 cache1_236 cache2_236 cache3_236 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 236. -/
theorem linkChecked236 : ((List.range 1024).all fun j => linkCheck (241664+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked236 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words236 BottomCase.words236 241664 row
    cache0_236 cache1_236 cache2_236 cache3_236 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 236) (BottomCase.wordsAt 236) (1024*236) row = true := hc
  rw [linkChunkCheck_eq 236 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 237. -/
noncomputable def cache0_237 : LinkCache := ⟨192,BottomEmpty.beta0Words192,BottomEmpty.beta0Words193⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 237. -/
noncomputable def cache1_237 : LinkCache := ⟨19,BottomEmpty.beta1Words19,BottomEmpty.beta1Words20⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 237. -/
noncomputable def cache2_237 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 237. -/
noncomputable def cache3_237 : LinkCache := ⟨101,BottomForest.packed25250.rInput,BottomForest.packed25500.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 237. -/
theorem cachedLinkChecked237 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words237 BottomCase.words237 242688 cache0_237 cache1_237 cache2_237 cache3_237 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 237. -/
theorem linkChecked237 : ((List.range 1024).all fun j => linkCheck (242688+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked237 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words237 BottomCase.words237 242688 row
    cache0_237 cache1_237 cache2_237 cache3_237 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 237) (BottomCase.wordsAt 237) (1024*237) row = true := hc
  rw [linkChunkCheck_eq 237 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 238. -/
noncomputable def cache0_238 : LinkCache := ⟨193,BottomEmpty.beta0Words193,BottomEmpty.beta0Words194⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 238. -/
noncomputable def cache1_238 : LinkCache := ⟨19,BottomEmpty.beta1Words19,BottomEmpty.beta1Words20⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 238. -/
noncomputable def cache2_238 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 238. -/
noncomputable def cache3_238 : LinkCache := ⟨101,BottomForest.packed25250.rInput,BottomForest.packed25500.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 238. -/
theorem cachedLinkChecked238 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words238 BottomCase.words238 243712 cache0_238 cache1_238 cache2_238 cache3_238 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 238. -/
theorem linkChecked238 : ((List.range 1024).all fun j => linkCheck (243712+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked238 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words238 BottomCase.words238 243712 row
    cache0_238 cache1_238 cache2_238 cache3_238 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 238) (BottomCase.wordsAt 238) (1024*238) row = true := hc
  rw [linkChunkCheck_eq 238 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 239. -/
noncomputable def cache0_239 : LinkCache := ⟨194,BottomEmpty.beta0Words194,BottomEmpty.beta0Words195⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 239. -/
noncomputable def cache1_239 : LinkCache := ⟨19,BottomEmpty.beta1Words19,BottomEmpty.beta1Words20⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 239. -/
noncomputable def cache2_239 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 239. -/
noncomputable def cache3_239 : LinkCache := ⟨101,BottomForest.packed25250.rInput,BottomForest.packed25500.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 239. -/
theorem cachedLinkChecked239 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words239 BottomCase.words239 244736 cache0_239 cache1_239 cache2_239 cache3_239 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 239. -/
theorem linkChecked239 : ((List.range 1024).all fun j => linkCheck (244736+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked239 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words239 BottomCase.words239 244736 row
    cache0_239 cache1_239 cache2_239 cache3_239 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 239) (BottomCase.wordsAt 239) (1024*239) row = true := hc
  rw [linkChunkCheck_eq 239 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 240. -/
noncomputable def cache0_240 : LinkCache := ⟨195,BottomEmpty.beta0Words195,BottomEmpty.beta0Words196⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 240. -/
noncomputable def cache1_240 : LinkCache := ⟨19,BottomEmpty.beta1Words19,BottomEmpty.beta1Words20⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 240. -/
noncomputable def cache2_240 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 240. -/
noncomputable def cache3_240 : LinkCache := ⟨102,BottomForest.packed25500.rInput,BottomForest.packed25750.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 240. -/
theorem cachedLinkChecked240 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words240 BottomCase.words240 245760 cache0_240 cache1_240 cache2_240 cache3_240 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 240. -/
theorem linkChecked240 : ((List.range 1024).all fun j => linkCheck (245760+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked240 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words240 BottomCase.words240 245760 row
    cache0_240 cache1_240 cache2_240 cache3_240 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 240) (BottomCase.wordsAt 240) (1024*240) row = true := hc
  rw [linkChunkCheck_eq 240 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 241. -/
noncomputable def cache0_241 : LinkCache := ⟨195,BottomEmpty.beta0Words195,BottomEmpty.beta0Words196⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 241. -/
noncomputable def cache1_241 : LinkCache := ⟨19,BottomEmpty.beta1Words19,BottomEmpty.beta1Words20⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 241. -/
noncomputable def cache2_241 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 241. -/
noncomputable def cache3_241 : LinkCache := ⟨102,BottomForest.packed25500.rInput,BottomForest.packed25750.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 241. -/
theorem cachedLinkChecked241 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words241 BottomCase.words241 246784 cache0_241 cache1_241 cache2_241 cache3_241 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 241. -/
theorem linkChecked241 : ((List.range 1024).all fun j => linkCheck (246784+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked241 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words241 BottomCase.words241 246784 row
    cache0_241 cache1_241 cache2_241 cache3_241 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 241) (BottomCase.wordsAt 241) (1024*241) row = true := hc
  rw [linkChunkCheck_eq 241 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 242. -/
noncomputable def cache0_242 : LinkCache := ⟨196,BottomEmpty.beta0Words196,BottomEmpty.beta0Words197⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 242. -/
noncomputable def cache1_242 : LinkCache := ⟨19,BottomEmpty.beta1Words19,BottomEmpty.beta1Words20⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 242. -/
noncomputable def cache2_242 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 242. -/
noncomputable def cache3_242 : LinkCache := ⟨102,BottomForest.packed25500.rInput,BottomForest.packed25750.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 242. -/
theorem cachedLinkChecked242 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words242 BottomCase.words242 247808 cache0_242 cache1_242 cache2_242 cache3_242 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 242. -/
theorem linkChecked242 : ((List.range 1024).all fun j => linkCheck (247808+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked242 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words242 BottomCase.words242 247808 row
    cache0_242 cache1_242 cache2_242 cache3_242 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 242) (BottomCase.wordsAt 242) (1024*242) row = true := hc
  rw [linkChunkCheck_eq 242 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 243. -/
noncomputable def cache0_243 : LinkCache := ⟨197,BottomEmpty.beta0Words197,BottomEmpty.beta0Words198⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 243. -/
noncomputable def cache1_243 : LinkCache := ⟨19,BottomEmpty.beta1Words19,BottomEmpty.beta1Words20⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 243. -/
noncomputable def cache2_243 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 243. -/
noncomputable def cache3_243 : LinkCache := ⟨103,BottomForest.packed25750.rInput,BottomForest.packed26000.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 243. -/
theorem cachedLinkChecked243 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words243 BottomCase.words243 248832 cache0_243 cache1_243 cache2_243 cache3_243 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 243. -/
theorem linkChecked243 : ((List.range 1024).all fun j => linkCheck (248832+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked243 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words243 BottomCase.words243 248832 row
    cache0_243 cache1_243 cache2_243 cache3_243 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 243) (BottomCase.wordsAt 243) (1024*243) row = true := hc
  rw [linkChunkCheck_eq 243 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 244. -/
noncomputable def cache0_244 : LinkCache := ⟨198,BottomEmpty.beta0Words198,BottomEmpty.beta0Words199⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 244. -/
noncomputable def cache1_244 : LinkCache := ⟨19,BottomEmpty.beta1Words19,BottomEmpty.beta1Words20⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 244. -/
noncomputable def cache2_244 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 244. -/
noncomputable def cache3_244 : LinkCache := ⟨103,BottomForest.packed25750.rInput,BottomForest.packed26000.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 244. -/
theorem cachedLinkChecked244 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words244 BottomCase.words244 249856 cache0_244 cache1_244 cache2_244 cache3_244 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 244. -/
theorem linkChecked244 : ((List.range 1024).all fun j => linkCheck (249856+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked244 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words244 BottomCase.words244 249856 row
    cache0_244 cache1_244 cache2_244 cache3_244 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 244) (BottomCase.wordsAt 244) (1024*244) row = true := hc
  rw [linkChunkCheck_eq 244 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 245. -/
noncomputable def cache0_245 : LinkCache := ⟨199,BottomEmpty.beta0Words199,BottomEmpty.beta0Words200⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 245. -/
noncomputable def cache1_245 : LinkCache := ⟨19,BottomEmpty.beta1Words19,BottomEmpty.beta1Words20⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 245. -/
noncomputable def cache2_245 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 245. -/
noncomputable def cache3_245 : LinkCache := ⟨104,BottomForest.packed26000.rInput,BottomForest.packed26250.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 245. -/
theorem cachedLinkChecked245 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words245 BottomCase.words245 250880 cache0_245 cache1_245 cache2_245 cache3_245 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 245. -/
theorem linkChecked245 : ((List.range 1024).all fun j => linkCheck (250880+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked245 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words245 BottomCase.words245 250880 row
    cache0_245 cache1_245 cache2_245 cache3_245 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 245) (BottomCase.wordsAt 245) (1024*245) row = true := hc
  rw [linkChunkCheck_eq 245 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 246. -/
noncomputable def cache0_246 : LinkCache := ⟨200,BottomEmpty.beta0Words200,BottomEmpty.beta0Words201⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 246. -/
noncomputable def cache1_246 : LinkCache := ⟨19,BottomEmpty.beta1Words19,BottomEmpty.beta1Words20⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 246. -/
noncomputable def cache2_246 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 246. -/
noncomputable def cache3_246 : LinkCache := ⟨104,BottomForest.packed26000.rInput,BottomForest.packed26250.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 246. -/
theorem cachedLinkChecked246 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words246 BottomCase.words246 251904 cache0_246 cache1_246 cache2_246 cache3_246 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 246. -/
theorem linkChecked246 : ((List.range 1024).all fun j => linkCheck (251904+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked246 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words246 BottomCase.words246 251904 row
    cache0_246 cache1_246 cache2_246 cache3_246 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 246) (BottomCase.wordsAt 246) (1024*246) row = true := hc
  rw [linkChunkCheck_eq 246 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 247. -/
noncomputable def cache0_247 : LinkCache := ⟨200,BottomEmpty.beta0Words200,BottomEmpty.beta0Words201⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 247. -/
noncomputable def cache1_247 : LinkCache := ⟨19,BottomEmpty.beta1Words19,BottomEmpty.beta1Words20⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 247. -/
noncomputable def cache2_247 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 247. -/
noncomputable def cache3_247 : LinkCache := ⟨104,BottomForest.packed26000.rInput,BottomForest.packed26250.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 247. -/
theorem cachedLinkChecked247 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words247 BottomCase.words247 252928 cache0_247 cache1_247 cache2_247 cache3_247 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 247. -/
theorem linkChecked247 : ((List.range 1024).all fun j => linkCheck (252928+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked247 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words247 BottomCase.words247 252928 row
    cache0_247 cache1_247 cache2_247 cache3_247 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 247) (BottomCase.wordsAt 247) (1024*247) row = true := hc
  rw [linkChunkCheck_eq 247 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 248. -/
noncomputable def cache0_248 : LinkCache := ⟨201,BottomEmpty.beta0Words201,BottomEmpty.beta0Words202⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 248. -/
noncomputable def cache1_248 : LinkCache := ⟨19,BottomEmpty.beta1Words19,BottomEmpty.beta1Words20⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 248. -/
noncomputable def cache2_248 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 248. -/
noncomputable def cache3_248 : LinkCache := ⟨105,BottomForest.packed26250.rInput,BottomForest.packed26500.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 248. -/
theorem cachedLinkChecked248 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words248 BottomCase.words248 253952 cache0_248 cache1_248 cache2_248 cache3_248 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 248. -/
theorem linkChecked248 : ((List.range 1024).all fun j => linkCheck (253952+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked248 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words248 BottomCase.words248 253952 row
    cache0_248 cache1_248 cache2_248 cache3_248 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 248) (BottomCase.wordsAt 248) (1024*248) row = true := hc
  rw [linkChunkCheck_eq 248 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 249. -/
noncomputable def cache0_249 : LinkCache := ⟨202,BottomEmpty.beta0Words202,BottomEmpty.beta0Words203⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 249. -/
noncomputable def cache1_249 : LinkCache := ⟨19,BottomEmpty.beta1Words19,BottomEmpty.beta1Words20⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 249. -/
noncomputable def cache2_249 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 249. -/
noncomputable def cache3_249 : LinkCache := ⟨105,BottomForest.packed26250.rInput,BottomForest.packed26500.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 249. -/
theorem cachedLinkChecked249 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words249 BottomCase.words249 254976 cache0_249 cache1_249 cache2_249 cache3_249 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 249. -/
theorem linkChecked249 : ((List.range 1024).all fun j => linkCheck (254976+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked249 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words249 BottomCase.words249 254976 row
    cache0_249 cache1_249 cache2_249 cache3_249 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 249) (BottomCase.wordsAt 249) (1024*249) row = true := hc
  rw [linkChunkCheck_eq 249 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 250. -/
noncomputable def cache0_250 : LinkCache := ⟨203,BottomEmpty.beta0Words203,BottomEmpty.beta0Words204⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 250. -/
noncomputable def cache1_250 : LinkCache := ⟨19,BottomEmpty.beta1Words19,BottomEmpty.beta1Words20⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 250. -/
noncomputable def cache2_250 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 250. -/
noncomputable def cache3_250 : LinkCache := ⟨105,BottomForest.packed26250.rInput,BottomForest.packed26500.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 250. -/
theorem cachedLinkChecked250 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words250 BottomCase.words250 256000 cache0_250 cache1_250 cache2_250 cache3_250 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 250. -/
theorem linkChecked250 : ((List.range 1024).all fun j => linkCheck (256000+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked250 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words250 BottomCase.words250 256000 row
    cache0_250 cache1_250 cache2_250 cache3_250 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 250) (BottomCase.wordsAt 250) (1024*250) row = true := hc
  rw [linkChunkCheck_eq 250 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 251. -/
noncomputable def cache0_251 : LinkCache := ⟨204,BottomEmpty.beta0Words204,BottomEmpty.beta0Words205⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 251. -/
noncomputable def cache1_251 : LinkCache := ⟨19,BottomEmpty.beta1Words19,BottomEmpty.beta1Words20⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 251. -/
noncomputable def cache2_251 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 251. -/
noncomputable def cache3_251 : LinkCache := ⟨105,BottomForest.packed26250.rInput,BottomForest.packed26500.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 251. -/
theorem cachedLinkChecked251 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words251 BottomCase.words251 257024 cache0_251 cache1_251 cache2_251 cache3_251 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 251. -/
theorem linkChecked251 : ((List.range 1024).all fun j => linkCheck (257024+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked251 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words251 BottomCase.words251 257024 row
    cache0_251 cache1_251 cache2_251 cache3_251 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 251) (BottomCase.wordsAt 251) (1024*251) row = true := hc
  rw [linkChunkCheck_eq 251 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 252. -/
noncomputable def cache0_252 : LinkCache := ⟨205,BottomEmpty.beta0Words205,BottomEmpty.beta0Words206⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 252. -/
noncomputable def cache1_252 : LinkCache := ⟨19,BottomEmpty.beta1Words19,BottomEmpty.beta1Words20⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 252. -/
noncomputable def cache2_252 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 252. -/
noncomputable def cache3_252 : LinkCache := ⟨106,BottomForest.packed26500.rInput,BottomForest.packed26750.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 252. -/
theorem cachedLinkChecked252 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words252 BottomCase.words252 258048 cache0_252 cache1_252 cache2_252 cache3_252 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 252. -/
theorem linkChecked252 : ((List.range 1024).all fun j => linkCheck (258048+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked252 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words252 BottomCase.words252 258048 row
    cache0_252 cache1_252 cache2_252 cache3_252 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 252) (BottomCase.wordsAt 252) (1024*252) row = true := hc
  rw [linkChunkCheck_eq 252 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 253. -/
noncomputable def cache0_253 : LinkCache := ⟨206,BottomEmpty.beta0Words206,BottomEmpty.beta0Words207⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 253. -/
noncomputable def cache1_253 : LinkCache := ⟨19,BottomEmpty.beta1Words19,BottomEmpty.beta1Words20⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 253. -/
noncomputable def cache2_253 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 253. -/
noncomputable def cache3_253 : LinkCache := ⟨106,BottomForest.packed26500.rInput,BottomForest.packed26750.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 253. -/
theorem cachedLinkChecked253 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words253 BottomCase.words253 259072 cache0_253 cache1_253 cache2_253 cache3_253 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 253. -/
theorem linkChecked253 : ((List.range 1024).all fun j => linkCheck (259072+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked253 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words253 BottomCase.words253 259072 row
    cache0_253 cache1_253 cache2_253 cache3_253 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 253) (BottomCase.wordsAt 253) (1024*253) row = true := hc
  rw [linkChunkCheck_eq 253 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 254. -/
noncomputable def cache0_254 : LinkCache := ⟨207,BottomEmpty.beta0Words207,BottomEmpty.beta0Words208⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 254. -/
noncomputable def cache1_254 : LinkCache := ⟨19,BottomEmpty.beta1Words19,BottomEmpty.beta1Words20⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 254. -/
noncomputable def cache2_254 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 254. -/
noncomputable def cache3_254 : LinkCache := ⟨107,BottomForest.packed26750.rInput,BottomForest.packed27000.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 254. -/
theorem cachedLinkChecked254 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words254 BottomCase.words254 260096 cache0_254 cache1_254 cache2_254 cache3_254 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 254. -/
theorem linkChecked254 : ((List.range 1024).all fun j => linkCheck (260096+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked254 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words254 BottomCase.words254 260096 row
    cache0_254 cache1_254 cache2_254 cache3_254 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 254) (BottomCase.wordsAt 254) (1024*254) row = true := hc
  rw [linkChunkCheck_eq 254 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 255. -/
noncomputable def cache0_255 : LinkCache := ⟨208,BottomEmpty.beta0Words208,BottomEmpty.beta0Words209⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 255. -/
noncomputable def cache1_255 : LinkCache := ⟨19,BottomEmpty.beta1Words19,BottomEmpty.beta1Words20⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 255. -/
noncomputable def cache2_255 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 255. -/
noncomputable def cache3_255 : LinkCache := ⟨107,BottomForest.packed26750.rInput,BottomForest.packed27000.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 255. -/
theorem cachedLinkChecked255 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words255 BottomCase.words255 261120 cache0_255 cache1_255 cache2_255 cache3_255 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 255. -/
theorem linkChecked255 : ((List.range 1024).all fun j => linkCheck (261120+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked255 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words255 BottomCase.words255 261120 row
    cache0_255 cache1_255 cache2_255 cache3_255 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 255) (BottomCase.wordsAt 255) (1024*255) row = true := hc
  rw [linkChunkCheck_eq 255 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
#print axioms linkChecked224
end Quantum.Stabilizer.Homological.BB.Bravyi360.BottomShallow
