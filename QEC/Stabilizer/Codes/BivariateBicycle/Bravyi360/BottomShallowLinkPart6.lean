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
/-- Adjacent family 0 data blocks for census chunk 192. -/
noncomputable def cache0_192 : LinkCache := ⟨153,BottomEmpty.beta0Words153,BottomEmpty.beta0Words154⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 192. -/
noncomputable def cache1_192 : LinkCache := ⟨16,BottomEmpty.beta1Words16,BottomEmpty.beta1Words17⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 192. -/
noncomputable def cache2_192 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 192. -/
noncomputable def cache3_192 : LinkCache := ⟨84,BottomForest.packed21000.rInput,BottomForest.packed21250.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 192. -/
theorem cachedLinkChecked192 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words192 BottomCase.words192 196608 cache0_192 cache1_192 cache2_192 cache3_192 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 192. -/
theorem linkChecked192 : ((List.range 1024).all fun j => linkCheck (196608+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked192 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words192 BottomCase.words192 196608 row
    cache0_192 cache1_192 cache2_192 cache3_192 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 192) (BottomCase.wordsAt 192) (1024*192) row = true := hc
  rw [linkChunkCheck_eq 192 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 193. -/
noncomputable def cache0_193 : LinkCache := ⟨154,BottomEmpty.beta0Words154,BottomEmpty.beta0Words155⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 193. -/
noncomputable def cache1_193 : LinkCache := ⟨16,BottomEmpty.beta1Words16,BottomEmpty.beta1Words17⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 193. -/
noncomputable def cache2_193 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 193. -/
noncomputable def cache3_193 : LinkCache := ⟨85,BottomForest.packed21250.rInput,BottomForest.packed21500.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 193. -/
theorem cachedLinkChecked193 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words193 BottomCase.words193 197632 cache0_193 cache1_193 cache2_193 cache3_193 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 193. -/
theorem linkChecked193 : ((List.range 1024).all fun j => linkCheck (197632+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked193 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words193 BottomCase.words193 197632 row
    cache0_193 cache1_193 cache2_193 cache3_193 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 193) (BottomCase.wordsAt 193) (1024*193) row = true := hc
  rw [linkChunkCheck_eq 193 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 194. -/
noncomputable def cache0_194 : LinkCache := ⟨155,BottomEmpty.beta0Words155,BottomEmpty.beta0Words156⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 194. -/
noncomputable def cache1_194 : LinkCache := ⟨16,BottomEmpty.beta1Words16,BottomEmpty.beta1Words17⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 194. -/
noncomputable def cache2_194 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 194. -/
noncomputable def cache3_194 : LinkCache := ⟨85,BottomForest.packed21250.rInput,BottomForest.packed21500.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 194. -/
theorem cachedLinkChecked194 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words194 BottomCase.words194 198656 cache0_194 cache1_194 cache2_194 cache3_194 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 194. -/
theorem linkChecked194 : ((List.range 1024).all fun j => linkCheck (198656+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked194 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words194 BottomCase.words194 198656 row
    cache0_194 cache1_194 cache2_194 cache3_194 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 194) (BottomCase.wordsAt 194) (1024*194) row = true := hc
  rw [linkChunkCheck_eq 194 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 195. -/
noncomputable def cache0_195 : LinkCache := ⟨156,BottomEmpty.beta0Words156,BottomEmpty.beta0Words157⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 195. -/
noncomputable def cache1_195 : LinkCache := ⟨16,BottomEmpty.beta1Words16,BottomEmpty.beta1Words17⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 195. -/
noncomputable def cache2_195 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 195. -/
noncomputable def cache3_195 : LinkCache := ⟨85,BottomForest.packed21250.rInput,BottomForest.packed21500.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 195. -/
theorem cachedLinkChecked195 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words195 BottomCase.words195 199680 cache0_195 cache1_195 cache2_195 cache3_195 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 195. -/
theorem linkChecked195 : ((List.range 1024).all fun j => linkCheck (199680+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked195 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words195 BottomCase.words195 199680 row
    cache0_195 cache1_195 cache2_195 cache3_195 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 195) (BottomCase.wordsAt 195) (1024*195) row = true := hc
  rw [linkChunkCheck_eq 195 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 196. -/
noncomputable def cache0_196 : LinkCache := ⟨157,BottomEmpty.beta0Words157,BottomEmpty.beta0Words158⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 196. -/
noncomputable def cache1_196 : LinkCache := ⟨16,BottomEmpty.beta1Words16,BottomEmpty.beta1Words17⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 196. -/
noncomputable def cache2_196 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 196. -/
noncomputable def cache3_196 : LinkCache := ⟨86,BottomForest.packed21500.rInput,BottomForest.packed21750.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 196. -/
theorem cachedLinkChecked196 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words196 BottomCase.words196 200704 cache0_196 cache1_196 cache2_196 cache3_196 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 196. -/
theorem linkChecked196 : ((List.range 1024).all fun j => linkCheck (200704+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked196 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words196 BottomCase.words196 200704 row
    cache0_196 cache1_196 cache2_196 cache3_196 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 196) (BottomCase.wordsAt 196) (1024*196) row = true := hc
  rw [linkChunkCheck_eq 196 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 197. -/
noncomputable def cache0_197 : LinkCache := ⟨158,BottomEmpty.beta0Words158,BottomEmpty.beta0Words159⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 197. -/
noncomputable def cache1_197 : LinkCache := ⟨16,BottomEmpty.beta1Words16,BottomEmpty.beta1Words17⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 197. -/
noncomputable def cache2_197 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 197. -/
noncomputable def cache3_197 : LinkCache := ⟨86,BottomForest.packed21500.rInput,BottomForest.packed21750.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 197. -/
theorem cachedLinkChecked197 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words197 BottomCase.words197 201728 cache0_197 cache1_197 cache2_197 cache3_197 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 197. -/
theorem linkChecked197 : ((List.range 1024).all fun j => linkCheck (201728+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked197 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words197 BottomCase.words197 201728 row
    cache0_197 cache1_197 cache2_197 cache3_197 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 197) (BottomCase.wordsAt 197) (1024*197) row = true := hc
  rw [linkChunkCheck_eq 197 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 198. -/
noncomputable def cache0_198 : LinkCache := ⟨159,BottomEmpty.beta0Words159,BottomEmpty.beta0Words160⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 198. -/
noncomputable def cache1_198 : LinkCache := ⟨17,BottomEmpty.beta1Words17,BottomEmpty.beta1Words18⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 198. -/
noncomputable def cache2_198 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 198. -/
noncomputable def cache3_198 : LinkCache := ⟨86,BottomForest.packed21500.rInput,BottomForest.packed21750.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 198. -/
theorem cachedLinkChecked198 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words198 BottomCase.words198 202752 cache0_198 cache1_198 cache2_198 cache3_198 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 198. -/
theorem linkChecked198 : ((List.range 1024).all fun j => linkCheck (202752+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked198 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words198 BottomCase.words198 202752 row
    cache0_198 cache1_198 cache2_198 cache3_198 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 198) (BottomCase.wordsAt 198) (1024*198) row = true := hc
  rw [linkChunkCheck_eq 198 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 199. -/
noncomputable def cache0_199 : LinkCache := ⟨159,BottomEmpty.beta0Words159,BottomEmpty.beta0Words160⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 199. -/
noncomputable def cache1_199 : LinkCache := ⟨17,BottomEmpty.beta1Words17,BottomEmpty.beta1Words18⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 199. -/
noncomputable def cache2_199 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 199. -/
noncomputable def cache3_199 : LinkCache := ⟨87,BottomForest.packed21750.rInput,BottomForest.packed22000.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 199. -/
theorem cachedLinkChecked199 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words199 BottomCase.words199 203776 cache0_199 cache1_199 cache2_199 cache3_199 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 199. -/
theorem linkChecked199 : ((List.range 1024).all fun j => linkCheck (203776+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked199 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words199 BottomCase.words199 203776 row
    cache0_199 cache1_199 cache2_199 cache3_199 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 199) (BottomCase.wordsAt 199) (1024*199) row = true := hc
  rw [linkChunkCheck_eq 199 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 200. -/
noncomputable def cache0_200 : LinkCache := ⟨160,BottomEmpty.beta0Words160,BottomEmpty.beta0Words161⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 200. -/
noncomputable def cache1_200 : LinkCache := ⟨17,BottomEmpty.beta1Words17,BottomEmpty.beta1Words18⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 200. -/
noncomputable def cache2_200 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 200. -/
noncomputable def cache3_200 : LinkCache := ⟨87,BottomForest.packed21750.rInput,BottomForest.packed22000.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 200. -/
theorem cachedLinkChecked200 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words200 BottomCase.words200 204800 cache0_200 cache1_200 cache2_200 cache3_200 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 200. -/
theorem linkChecked200 : ((List.range 1024).all fun j => linkCheck (204800+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked200 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words200 BottomCase.words200 204800 row
    cache0_200 cache1_200 cache2_200 cache3_200 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 200) (BottomCase.wordsAt 200) (1024*200) row = true := hc
  rw [linkChunkCheck_eq 200 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 201. -/
noncomputable def cache0_201 : LinkCache := ⟨161,BottomEmpty.beta0Words161,BottomEmpty.beta0Words162⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 201. -/
noncomputable def cache1_201 : LinkCache := ⟨17,BottomEmpty.beta1Words17,BottomEmpty.beta1Words18⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 201. -/
noncomputable def cache2_201 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 201. -/
noncomputable def cache3_201 : LinkCache := ⟨87,BottomForest.packed21750.rInput,BottomForest.packed22000.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 201. -/
theorem cachedLinkChecked201 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words201 BottomCase.words201 205824 cache0_201 cache1_201 cache2_201 cache3_201 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 201. -/
theorem linkChecked201 : ((List.range 1024).all fun j => linkCheck (205824+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked201 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words201 BottomCase.words201 205824 row
    cache0_201 cache1_201 cache2_201 cache3_201 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 201) (BottomCase.wordsAt 201) (1024*201) row = true := hc
  rw [linkChunkCheck_eq 201 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 202. -/
noncomputable def cache0_202 : LinkCache := ⟨162,BottomEmpty.beta0Words162,BottomEmpty.beta0Words163⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 202. -/
noncomputable def cache1_202 : LinkCache := ⟨17,BottomEmpty.beta1Words17,BottomEmpty.beta1Words18⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 202. -/
noncomputable def cache2_202 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 202. -/
noncomputable def cache3_202 : LinkCache := ⟨88,BottomForest.packed22000.rInput,BottomForest.packed22250.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 202. -/
theorem cachedLinkChecked202 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words202 BottomCase.words202 206848 cache0_202 cache1_202 cache2_202 cache3_202 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 202. -/
theorem linkChecked202 : ((List.range 1024).all fun j => linkCheck (206848+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked202 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words202 BottomCase.words202 206848 row
    cache0_202 cache1_202 cache2_202 cache3_202 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 202) (BottomCase.wordsAt 202) (1024*202) row = true := hc
  rw [linkChunkCheck_eq 202 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 203. -/
noncomputable def cache0_203 : LinkCache := ⟨163,BottomEmpty.beta0Words163,BottomEmpty.beta0Words164⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 203. -/
noncomputable def cache1_203 : LinkCache := ⟨17,BottomEmpty.beta1Words17,BottomEmpty.beta1Words18⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 203. -/
noncomputable def cache2_203 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 203. -/
noncomputable def cache3_203 : LinkCache := ⟨88,BottomForest.packed22000.rInput,BottomForest.packed22250.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 203. -/
theorem cachedLinkChecked203 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words203 BottomCase.words203 207872 cache0_203 cache1_203 cache2_203 cache3_203 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 203. -/
theorem linkChecked203 : ((List.range 1024).all fun j => linkCheck (207872+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked203 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words203 BottomCase.words203 207872 row
    cache0_203 cache1_203 cache2_203 cache3_203 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 203) (BottomCase.wordsAt 203) (1024*203) row = true := hc
  rw [linkChunkCheck_eq 203 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 204. -/
noncomputable def cache0_204 : LinkCache := ⟨164,BottomEmpty.beta0Words164,BottomEmpty.beta0Words165⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 204. -/
noncomputable def cache1_204 : LinkCache := ⟨17,BottomEmpty.beta1Words17,BottomEmpty.beta1Words18⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 204. -/
noncomputable def cache2_204 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 204. -/
noncomputable def cache3_204 : LinkCache := ⟨89,BottomForest.packed22250.rInput,BottomForest.packed22500.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 204. -/
theorem cachedLinkChecked204 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words204 BottomCase.words204 208896 cache0_204 cache1_204 cache2_204 cache3_204 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 204. -/
theorem linkChecked204 : ((List.range 1024).all fun j => linkCheck (208896+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked204 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words204 BottomCase.words204 208896 row
    cache0_204 cache1_204 cache2_204 cache3_204 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 204) (BottomCase.wordsAt 204) (1024*204) row = true := hc
  rw [linkChunkCheck_eq 204 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 205. -/
noncomputable def cache0_205 : LinkCache := ⟨164,BottomEmpty.beta0Words164,BottomEmpty.beta0Words165⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 205. -/
noncomputable def cache1_205 : LinkCache := ⟨17,BottomEmpty.beta1Words17,BottomEmpty.beta1Words18⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 205. -/
noncomputable def cache2_205 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 205. -/
noncomputable def cache3_205 : LinkCache := ⟨89,BottomForest.packed22250.rInput,BottomForest.packed22500.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 205. -/
theorem cachedLinkChecked205 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words205 BottomCase.words205 209920 cache0_205 cache1_205 cache2_205 cache3_205 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 205. -/
theorem linkChecked205 : ((List.range 1024).all fun j => linkCheck (209920+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked205 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words205 BottomCase.words205 209920 row
    cache0_205 cache1_205 cache2_205 cache3_205 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 205) (BottomCase.wordsAt 205) (1024*205) row = true := hc
  rw [linkChunkCheck_eq 205 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 206. -/
noncomputable def cache0_206 : LinkCache := ⟨165,BottomEmpty.beta0Words165,BottomEmpty.beta0Words166⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 206. -/
noncomputable def cache1_206 : LinkCache := ⟨17,BottomEmpty.beta1Words17,BottomEmpty.beta1Words18⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 206. -/
noncomputable def cache2_206 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 206. -/
noncomputable def cache3_206 : LinkCache := ⟨89,BottomForest.packed22250.rInput,BottomForest.packed22500.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 206. -/
theorem cachedLinkChecked206 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words206 BottomCase.words206 210944 cache0_206 cache1_206 cache2_206 cache3_206 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 206. -/
theorem linkChecked206 : ((List.range 1024).all fun j => linkCheck (210944+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked206 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words206 BottomCase.words206 210944 row
    cache0_206 cache1_206 cache2_206 cache3_206 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 206) (BottomCase.wordsAt 206) (1024*206) row = true := hc
  rw [linkChunkCheck_eq 206 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 207. -/
noncomputable def cache0_207 : LinkCache := ⟨166,BottomEmpty.beta0Words166,BottomEmpty.beta0Words167⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 207. -/
noncomputable def cache1_207 : LinkCache := ⟨17,BottomEmpty.beta1Words17,BottomEmpty.beta1Words18⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 207. -/
noncomputable def cache2_207 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 207. -/
noncomputable def cache3_207 : LinkCache := ⟨90,BottomForest.packed22500.rInput,BottomForest.packed22750.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 207. -/
theorem cachedLinkChecked207 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words207 BottomCase.words207 211968 cache0_207 cache1_207 cache2_207 cache3_207 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 207. -/
theorem linkChecked207 : ((List.range 1024).all fun j => linkCheck (211968+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked207 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words207 BottomCase.words207 211968 row
    cache0_207 cache1_207 cache2_207 cache3_207 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 207) (BottomCase.wordsAt 207) (1024*207) row = true := hc
  rw [linkChunkCheck_eq 207 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 208. -/
noncomputable def cache0_208 : LinkCache := ⟨167,BottomEmpty.beta0Words167,BottomEmpty.beta0Words168⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 208. -/
noncomputable def cache1_208 : LinkCache := ⟨17,BottomEmpty.beta1Words17,BottomEmpty.beta1Words18⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 208. -/
noncomputable def cache2_208 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 208. -/
noncomputable def cache3_208 : LinkCache := ⟨90,BottomForest.packed22500.rInput,BottomForest.packed22750.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 208. -/
theorem cachedLinkChecked208 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words208 BottomCase.words208 212992 cache0_208 cache1_208 cache2_208 cache3_208 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 208. -/
theorem linkChecked208 : ((List.range 1024).all fun j => linkCheck (212992+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked208 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words208 BottomCase.words208 212992 row
    cache0_208 cache1_208 cache2_208 cache3_208 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 208) (BottomCase.wordsAt 208) (1024*208) row = true := hc
  rw [linkChunkCheck_eq 208 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 209. -/
noncomputable def cache0_209 : LinkCache := ⟨168,BottomEmpty.beta0Words168,BottomEmpty.beta0Words169⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 209. -/
noncomputable def cache1_209 : LinkCache := ⟨17,BottomEmpty.beta1Words17,BottomEmpty.beta1Words18⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 209. -/
noncomputable def cache2_209 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 209. -/
noncomputable def cache3_209 : LinkCache := ⟨90,BottomForest.packed22500.rInput,BottomForest.packed22750.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 209. -/
theorem cachedLinkChecked209 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words209 BottomCase.words209 214016 cache0_209 cache1_209 cache2_209 cache3_209 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 209. -/
theorem linkChecked209 : ((List.range 1024).all fun j => linkCheck (214016+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked209 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words209 BottomCase.words209 214016 row
    cache0_209 cache1_209 cache2_209 cache3_209 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 209) (BottomCase.wordsAt 209) (1024*209) row = true := hc
  rw [linkChunkCheck_eq 209 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 210. -/
noncomputable def cache0_210 : LinkCache := ⟨169,BottomEmpty.beta0Words169,BottomEmpty.beta0Words170⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 210. -/
noncomputable def cache1_210 : LinkCache := ⟨17,BottomEmpty.beta1Words17,BottomEmpty.beta1Words18⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 210. -/
noncomputable def cache2_210 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 210. -/
noncomputable def cache3_210 : LinkCache := ⟨91,BottomForest.packed22750.rInput,BottomForest.packed23000.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 210. -/
theorem cachedLinkChecked210 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words210 BottomCase.words210 215040 cache0_210 cache1_210 cache2_210 cache3_210 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 210. -/
theorem linkChecked210 : ((List.range 1024).all fun j => linkCheck (215040+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked210 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words210 BottomCase.words210 215040 row
    cache0_210 cache1_210 cache2_210 cache3_210 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 210) (BottomCase.wordsAt 210) (1024*210) row = true := hc
  rw [linkChunkCheck_eq 210 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 211. -/
noncomputable def cache0_211 : LinkCache := ⟨170,BottomEmpty.beta0Words170,BottomEmpty.beta0Words171⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 211. -/
noncomputable def cache1_211 : LinkCache := ⟨17,BottomEmpty.beta1Words17,BottomEmpty.beta1Words18⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 211. -/
noncomputable def cache2_211 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 211. -/
noncomputable def cache3_211 : LinkCache := ⟨91,BottomForest.packed22750.rInput,BottomForest.packed23000.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 211. -/
theorem cachedLinkChecked211 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words211 BottomCase.words211 216064 cache0_211 cache1_211 cache2_211 cache3_211 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 211. -/
theorem linkChecked211 : ((List.range 1024).all fun j => linkCheck (216064+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked211 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words211 BottomCase.words211 216064 row
    cache0_211 cache1_211 cache2_211 cache3_211 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 211) (BottomCase.wordsAt 211) (1024*211) row = true := hc
  rw [linkChunkCheck_eq 211 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 212. -/
noncomputable def cache0_212 : LinkCache := ⟨170,BottomEmpty.beta0Words170,BottomEmpty.beta0Words171⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 212. -/
noncomputable def cache1_212 : LinkCache := ⟨17,BottomEmpty.beta1Words17,BottomEmpty.beta1Words18⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 212. -/
noncomputable def cache2_212 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 212. -/
noncomputable def cache3_212 : LinkCache := ⟨92,BottomForest.packed23000.rInput,BottomForest.packed23250.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 212. -/
theorem cachedLinkChecked212 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words212 BottomCase.words212 217088 cache0_212 cache1_212 cache2_212 cache3_212 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 212. -/
theorem linkChecked212 : ((List.range 1024).all fun j => linkCheck (217088+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked212 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words212 BottomCase.words212 217088 row
    cache0_212 cache1_212 cache2_212 cache3_212 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 212) (BottomCase.wordsAt 212) (1024*212) row = true := hc
  rw [linkChunkCheck_eq 212 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 213. -/
noncomputable def cache0_213 : LinkCache := ⟨171,BottomEmpty.beta0Words171,BottomEmpty.beta0Words172⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 213. -/
noncomputable def cache1_213 : LinkCache := ⟨17,BottomEmpty.beta1Words17,BottomEmpty.beta1Words18⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 213. -/
noncomputable def cache2_213 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 213. -/
noncomputable def cache3_213 : LinkCache := ⟨92,BottomForest.packed23000.rInput,BottomForest.packed23250.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 213. -/
theorem cachedLinkChecked213 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words213 BottomCase.words213 218112 cache0_213 cache1_213 cache2_213 cache3_213 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 213. -/
theorem linkChecked213 : ((List.range 1024).all fun j => linkCheck (218112+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked213 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words213 BottomCase.words213 218112 row
    cache0_213 cache1_213 cache2_213 cache3_213 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 213) (BottomCase.wordsAt 213) (1024*213) row = true := hc
  rw [linkChunkCheck_eq 213 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 214. -/
noncomputable def cache0_214 : LinkCache := ⟨172,BottomEmpty.beta0Words172,BottomEmpty.beta0Words173⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 214. -/
noncomputable def cache1_214 : LinkCache := ⟨17,BottomEmpty.beta1Words17,BottomEmpty.beta1Words18⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 214. -/
noncomputable def cache2_214 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 214. -/
noncomputable def cache3_214 : LinkCache := ⟨93,BottomForest.packed23250.rInput,BottomForest.packed23500.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 214. -/
theorem cachedLinkChecked214 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words214 BottomCase.words214 219136 cache0_214 cache1_214 cache2_214 cache3_214 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 214. -/
theorem linkChecked214 : ((List.range 1024).all fun j => linkCheck (219136+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked214 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words214 BottomCase.words214 219136 row
    cache0_214 cache1_214 cache2_214 cache3_214 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 214) (BottomCase.wordsAt 214) (1024*214) row = true := hc
  rw [linkChunkCheck_eq 214 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 215. -/
noncomputable def cache0_215 : LinkCache := ⟨173,BottomEmpty.beta0Words173,BottomEmpty.beta0Words174⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 215. -/
noncomputable def cache1_215 : LinkCache := ⟨17,BottomEmpty.beta1Words17,BottomEmpty.beta1Words18⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 215. -/
noncomputable def cache2_215 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 215. -/
noncomputable def cache3_215 : LinkCache := ⟨93,BottomForest.packed23250.rInput,BottomForest.packed23500.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 215. -/
theorem cachedLinkChecked215 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words215 BottomCase.words215 220160 cache0_215 cache1_215 cache2_215 cache3_215 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 215. -/
theorem linkChecked215 : ((List.range 1024).all fun j => linkCheck (220160+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked215 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words215 BottomCase.words215 220160 row
    cache0_215 cache1_215 cache2_215 cache3_215 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 215) (BottomCase.wordsAt 215) (1024*215) row = true := hc
  rw [linkChunkCheck_eq 215 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 216. -/
noncomputable def cache0_216 : LinkCache := ⟨174,BottomEmpty.beta0Words174,BottomEmpty.beta0Words175⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 216. -/
noncomputable def cache1_216 : LinkCache := ⟨18,BottomEmpty.beta1Words18,BottomEmpty.beta1Words19⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 216. -/
noncomputable def cache2_216 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 216. -/
noncomputable def cache3_216 : LinkCache := ⟨93,BottomForest.packed23250.rInput,BottomForest.packed23500.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 216. -/
theorem cachedLinkChecked216 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words216 BottomCase.words216 221184 cache0_216 cache1_216 cache2_216 cache3_216 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 216. -/
theorem linkChecked216 : ((List.range 1024).all fun j => linkCheck (221184+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked216 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words216 BottomCase.words216 221184 row
    cache0_216 cache1_216 cache2_216 cache3_216 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 216) (BottomCase.wordsAt 216) (1024*216) row = true := hc
  rw [linkChunkCheck_eq 216 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 217. -/
noncomputable def cache0_217 : LinkCache := ⟨175,BottomEmpty.beta0Words175,BottomEmpty.beta0Words176⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 217. -/
noncomputable def cache1_217 : LinkCache := ⟨18,BottomEmpty.beta1Words18,BottomEmpty.beta1Words19⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 217. -/
noncomputable def cache2_217 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 217. -/
noncomputable def cache3_217 : LinkCache := ⟨94,BottomForest.packed23500.rInput,BottomForest.packed23750.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 217. -/
theorem cachedLinkChecked217 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words217 BottomCase.words217 222208 cache0_217 cache1_217 cache2_217 cache3_217 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 217. -/
theorem linkChecked217 : ((List.range 1024).all fun j => linkCheck (222208+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked217 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words217 BottomCase.words217 222208 row
    cache0_217 cache1_217 cache2_217 cache3_217 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 217) (BottomCase.wordsAt 217) (1024*217) row = true := hc
  rw [linkChunkCheck_eq 217 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 218. -/
noncomputable def cache0_218 : LinkCache := ⟨175,BottomEmpty.beta0Words175,BottomEmpty.beta0Words176⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 218. -/
noncomputable def cache1_218 : LinkCache := ⟨18,BottomEmpty.beta1Words18,BottomEmpty.beta1Words19⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 218. -/
noncomputable def cache2_218 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 218. -/
noncomputable def cache3_218 : LinkCache := ⟨94,BottomForest.packed23500.rInput,BottomForest.packed23750.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 218. -/
theorem cachedLinkChecked218 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words218 BottomCase.words218 223232 cache0_218 cache1_218 cache2_218 cache3_218 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 218. -/
theorem linkChecked218 : ((List.range 1024).all fun j => linkCheck (223232+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked218 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words218 BottomCase.words218 223232 row
    cache0_218 cache1_218 cache2_218 cache3_218 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 218) (BottomCase.wordsAt 218) (1024*218) row = true := hc
  rw [linkChunkCheck_eq 218 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 219. -/
noncomputable def cache0_219 : LinkCache := ⟨176,BottomEmpty.beta0Words176,BottomEmpty.beta0Words177⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 219. -/
noncomputable def cache1_219 : LinkCache := ⟨18,BottomEmpty.beta1Words18,BottomEmpty.beta1Words19⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 219. -/
noncomputable def cache2_219 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 219. -/
noncomputable def cache3_219 : LinkCache := ⟨94,BottomForest.packed23500.rInput,BottomForest.packed23750.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 219. -/
theorem cachedLinkChecked219 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words219 BottomCase.words219 224256 cache0_219 cache1_219 cache2_219 cache3_219 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 219. -/
theorem linkChecked219 : ((List.range 1024).all fun j => linkCheck (224256+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked219 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words219 BottomCase.words219 224256 row
    cache0_219 cache1_219 cache2_219 cache3_219 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 219) (BottomCase.wordsAt 219) (1024*219) row = true := hc
  rw [linkChunkCheck_eq 219 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 220. -/
noncomputable def cache0_220 : LinkCache := ⟨177,BottomEmpty.beta0Words177,BottomEmpty.beta0Words178⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 220. -/
noncomputable def cache1_220 : LinkCache := ⟨18,BottomEmpty.beta1Words18,BottomEmpty.beta1Words19⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 220. -/
noncomputable def cache2_220 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 220. -/
noncomputable def cache3_220 : LinkCache := ⟨95,BottomForest.packed23750.rInput,BottomForest.packed24000.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 220. -/
theorem cachedLinkChecked220 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words220 BottomCase.words220 225280 cache0_220 cache1_220 cache2_220 cache3_220 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 220. -/
theorem linkChecked220 : ((List.range 1024).all fun j => linkCheck (225280+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked220 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words220 BottomCase.words220 225280 row
    cache0_220 cache1_220 cache2_220 cache3_220 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 220) (BottomCase.wordsAt 220) (1024*220) row = true := hc
  rw [linkChunkCheck_eq 220 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 221. -/
noncomputable def cache0_221 : LinkCache := ⟨178,BottomEmpty.beta0Words178,BottomEmpty.beta0Words179⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 221. -/
noncomputable def cache1_221 : LinkCache := ⟨18,BottomEmpty.beta1Words18,BottomEmpty.beta1Words19⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 221. -/
noncomputable def cache2_221 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 221. -/
noncomputable def cache3_221 : LinkCache := ⟨95,BottomForest.packed23750.rInput,BottomForest.packed24000.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 221. -/
theorem cachedLinkChecked221 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words221 BottomCase.words221 226304 cache0_221 cache1_221 cache2_221 cache3_221 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 221. -/
theorem linkChecked221 : ((List.range 1024).all fun j => linkCheck (226304+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked221 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words221 BottomCase.words221 226304 row
    cache0_221 cache1_221 cache2_221 cache3_221 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 221) (BottomCase.wordsAt 221) (1024*221) row = true := hc
  rw [linkChunkCheck_eq 221 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 222. -/
noncomputable def cache0_222 : LinkCache := ⟨179,BottomEmpty.beta0Words179,BottomEmpty.beta0Words180⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 222. -/
noncomputable def cache1_222 : LinkCache := ⟨18,BottomEmpty.beta1Words18,BottomEmpty.beta1Words19⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 222. -/
noncomputable def cache2_222 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 222. -/
noncomputable def cache3_222 : LinkCache := ⟨96,BottomForest.packed24000.rInput,BottomForest.packed24250.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 222. -/
theorem cachedLinkChecked222 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words222 BottomCase.words222 227328 cache0_222 cache1_222 cache2_222 cache3_222 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 222. -/
theorem linkChecked222 : ((List.range 1024).all fun j => linkCheck (227328+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked222 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words222 BottomCase.words222 227328 row
    cache0_222 cache1_222 cache2_222 cache3_222 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 222) (BottomCase.wordsAt 222) (1024*222) row = true := hc
  rw [linkChunkCheck_eq 222 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 0 data blocks for census chunk 223. -/
noncomputable def cache0_223 : LinkCache := ⟨180,BottomEmpty.beta0Words180,BottomEmpty.beta0Words181⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 1 data blocks for census chunk 223. -/
noncomputable def cache1_223 : LinkCache := ⟨18,BottomEmpty.beta1Words18,BottomEmpty.beta1Words19⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 2 data blocks for census chunk 223. -/
noncomputable def cache2_223 : LinkCache := ⟨0,BottomEmpty.beta2Words0,BottomEmpty.beta2Words0⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent family 3 data blocks for census chunk 223. -/
noncomputable def cache3_223 : LinkCache := ⟨96,BottomForest.packed24000.rInput,BottomForest.packed24250.rInput⟩
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Checked exact family associations using fixed data blocks for chunk 223. -/
theorem cachedLinkChecked223 : ((List.range 1024).all fun j => linkCachedCheck OrbitBatchData.words223 BottomCase.words223 228352 cache0_223 cache1_223 cache2_223 cache3_223 j) = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact certificate-family associations for census chunk 223. -/
theorem linkChecked223 : ((List.range 1024).all fun j => linkCheck (228352+j)) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  have h := List.all_eq_true.mp cachedLinkChecked223 row hrow
  have hc := linkCachedCheck_sound OrbitBatchData.words223 BottomCase.words223 228352 row
    cache0_223 cache1_223 cache2_223 cache3_223 (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) h
  have hcFixed : linkChunkCheck (OrbitBatchData.wordsAt 223) (BottomCase.wordsAt 223) (1024*223) row = true := hc
  rw [linkChunkCheck_eq 223 row (by have := List.mem_range.mp hrow; omega)] at hcFixed
  exact hcFixed
#print axioms linkChecked192
end Quantum.Stabilizer.Homological.BB.Bravyi360.BottomShallow
