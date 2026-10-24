import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.BottomShallowChunkCheck

noncomputable section
namespace Quantum.Stabilizer.Homological.BB.Bravyi360.BottomShallow
open F2Mask PackedDigits
set_option maxRecDepth 100000
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Two adjacent packed blocks provide the relevant local certificate values. -/
structure LinkCache where
  block : Nat
  low : Nat
  high : Nat
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- A guarded lookup into either of two adjacent blocks. -/
noncomputable def cacheCheck (size : Nat) (c : LinkCache) (index beta : Nat) : Bool :=
  (Nat.beq (index / size) c.block &&
    Nat.beq beta (lane 256 (index % size) c.low)) ||
  (Nat.beq (index / size) (c.block + 1) &&
    Nat.beq beta (lane 256 (index % size) c.high))
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- A guarded local lookup agrees with the global block table. -/
theorem cacheCheck_sound (size : Nat) (c : LinkCache) (words : Nat → Nat)
    (hl : c.low = words c.block) (hh : c.high = words (c.block+1))
    (index beta : Nat) (h : cacheCheck size c index beta = true) :
    beta = lane 256 (index % size) (words (index / size)) := by
  simp only [cacheCheck,Bool.or_eq_true,Bool.and_eq_true,Nat.beq_eq] at h
  rcases h with ⟨he,hb⟩ | ⟨he,hb⟩
  · simpa only [he,hl] using hb
  · simpa only [he,hh] using hb
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Check one census row with fixed orbit, classification, and family-data blocks. -/
noncomputable def linkCachedCheck (orbitWords caseWords base : Nat)
    (c0 c1 c2 c3 : LinkCache) (row : Nat) : Bool :=
  let beta := lane 128 row orbitWords
  let entry := lane 24 row caseWords
  let index := entry / 8
  let family := if entry % 8 = 5 then
      if index < 28 ∧ base + row = BottomCase.deepOrbitIndex index then 5 else 4
    else min (entry % 8) 4
  match family with
  | 0 => Nat.blt index 224352 && cacheCheck 1024 c0 index beta
  | 1 => Nat.blt index 20904 && cacheCheck 1024 c1 index beta
  | 2 => Nat.blt index 859 && cacheCheck 1024 c2 index beta
  | 3 => Nat.blt index 27867 && cacheCheck 250 c3 index beta
  | 4 => Nat.beq beta 0
  | 5 => true
  | _ => false
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Fixed block checks imply the original exact certificate-family association. -/
theorem linkCachedCheck_sound (orbitWords caseWords base row : Nat)
    (c0 c1 c2 c3 : LinkCache)
    (h0l : c0.low = BottomEmpty.beta0Words c0.block)
    (h0h : c0.high = BottomEmpty.beta0Words (c0.block+1))
    (h1l : c1.low = BottomEmpty.beta1Words c1.block)
    (h1h : c1.high = BottomEmpty.beta1Words (c1.block+1))
    (h2l : c2.low = BottomEmpty.beta2Words c2.block)
    (h2h : c2.high = BottomEmpty.beta2Words (c2.block+1))
    (h3l : c3.low = (BottomForest.packedAt c3.block).rInput)
    (h3h : c3.high = (BottomForest.packedAt (c3.block+1)).rInput)
    (h : linkCachedCheck orbitWords caseWords base c0 c1 c2 c3 row = true) :
    linkChunkCheck orbitWords caseWords base row = true := by
  unfold linkCachedCheck at h
  unfold linkChunkCheck
  dsimp only at h ⊢
  split at h <;> rename_i he
  · simp only [he,Bool.and_eq_true,Nat.blt_eq] at h ⊢
    refine ⟨h.1,?_⟩
    exact Nat.beq_eq.mpr (cacheCheck_sound 1024 c0 _ h0l h0h _ _ h.2)
  · simp only [he,Bool.and_eq_true,Nat.blt_eq] at h ⊢
    refine ⟨h.1,?_⟩
    exact Nat.beq_eq.mpr (cacheCheck_sound 1024 c1 _ h1l h1h _ _ h.2)
  · simp only [he,Bool.and_eq_true,Nat.blt_eq] at h ⊢
    refine ⟨h.1,?_⟩
    exact Nat.beq_eq.mpr (cacheCheck_sound 1024 c2 _ h2l h2h _ _ h.2)
  · simp only [Bool.and_eq_true,Nat.blt_eq] at h
    simp only [he,forestLinkCheck,Bool.and_eq_true,Nat.blt_eq,Nat.beq_eq]
    exact ⟨h.1,cacheCheck_sound 250 c3 (fun b => (BottomForest.packedAt b).rInput) h3l h3h _ _ h.2⟩
  · simpa only [he] using h
  · simp only [he]
  · simp only [Bool.false_eq_true] at h
#print axioms linkCachedCheck_sound
end Quantum.Stabilizer.Homological.BB.Bravyi360.BottomShallow
