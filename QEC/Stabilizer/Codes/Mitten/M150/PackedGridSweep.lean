import QEC.Stabilizer.Codes.Mitten.M150.PackedClassification
import QEC.Stabilizer.Framework.Homological.Certificate.PackedGrid

namespace Quantum.Stabilizer.Homological.LP.M150
open PackedDigits F2Mask

/-- Unit markers separated by a whole row of inner masks. -/
def gridRowMarkers (xs ys : List Nat) : Nat :=
  packList (32 * ys.length) (xs.map fun _ => 1)

/-- One unit marker for every pair in a rectangular block. -/
def gridRep (xs ys : List Nat) : Nat := gridRowMarkers xs ys * packedOnes ys

/-- Unit row markers have the functional packing specification. -/
theorem gridRowMarkers_eq (xs ys : List Nat) :
    gridRowMarkers xs ys = packF (32 * ys.length) xs.length (fun _ => 1) := by
  unfold gridRowMarkers
  rw [packList_eq_ofDigits]
  unfold packF
  congr 1
  simp

/-- Rectangular markers cover exactly the row-major pair indices. -/
theorem gridRep_eq (xs ys : List Nat) :
    gridRep xs ys = packF 32 (xs.length * ys.length) (fun _ => 1) := by
  rw [gridRep, gridRowMarkers_eq, packedOnes_eq, packF_broadcast_rows]

/-- Reconstruct all outer images with enough spacing for one entire row. -/
def gridLeftImages (xs ys : List Nat) (columns : List (Nat × Nat)) : Nat :=
  forceNat (gridRowMarkers xs ys) fun rep =>
  forceNat (packList (32 * ys.length) xs) fun input =>
    batchRecon rep input columns

/-- The row-spaced reconstruction agrees with the outer split map. -/
theorem gridLeftImages_eq (T : SweepTables) (mode : Nat) (xs ys : List Nat)
    (columns : List (Nat × Nat)) (hy : 0 < ys.length)
    (hx : ∀ x ∈ xs, x < 2 ^ 30)
    (hc : ∀ p ∈ columns, p.1 < 32 ∧ p.2 < 2 ^ 32)
    (hf : ∀ x < 2 ^ 30, reconX columns x = sweepLeft T mode x) :
    gridLeftImages xs ys columns = packF (32 * ys.length) xs.length
      (fun i => sweepLeft T mode (xs.getD i 0)) := by
  have hw : 32 ≤ 32 * ys.length := by omega
  have hpow : 2 ^ 32 ≤ 2 ^ (32 * ys.length) :=
    Nat.pow_le_pow_right (by decide) hw
  unfold gridLeftImages
  simp only [forceNat_eq]
  rw [gridRowMarkers_eq, packList_eq_packF, batchRecon_packF]
  · apply packF_congr
    intro i hi
    apply hf
    rw [List.getD_eq_getElem _ _ hi]
    exact hx _ (List.getElem_mem hi)
  · omega
  · intro i hi
    rw [List.getD_eq_getElem _ _ hi]
    exact lt_of_lt_of_le (hx _ (List.getElem_mem hi))
      (le_trans (by decide : 2 ^ 30 ≤ 2 ^ 32) hpow)
  · intro p hp
    exact ⟨lt_of_lt_of_le (hc p hp).1 hw, lt_of_lt_of_le (hc p hp).2 hpow⟩

/-- Broadcast both linear images across a rectangular block, then XOR them. -/
def gridWords (xs ys : List Nat) (leftColumns rightColumns : List (Nat × Nat)) : Nat :=
  gridLeftImages xs ys leftColumns * packedOnes ys ^^^
    gridRowMarkers xs ys * packedImages ys rightColumns

/-- Every packed grid lane is the two-mask reconstruction for its pair. -/
theorem gridWords_eq (T : SweepTables) (mode : Nat) (xs ys : List Nat)
    (leftColumns rightColumns : List (Nat × Nat))
    (hy : 0 < ys.length)
    (hx : ∀ x ∈ xs, x < 2 ^ 30) (hyb : ∀ y ∈ ys, y < 2 ^ 30)
    (hlc : ∀ p ∈ leftColumns, p.1 < 32 ∧ p.2 < 2 ^ 32)
    (hrc : ∀ p ∈ rightColumns, p.1 < 32 ∧ p.2 < 2 ^ 32)
    (hlf : ∀ x < 2 ^ 30, reconX leftColumns x = sweepLeft T mode x)
    (hrf : ∀ y < 2 ^ 30, reconX rightColumns y = sweepRight T mode y)
    (hl : ∀ x ∈ xs, sweepLeft T mode x < 2 ^ 30)
    (hr : ∀ y ∈ ys, sweepRight T mode y < 2 ^ 30) :
    gridWords xs ys leftColumns rightColumns =
      packF 32 (xs.length * ys.length) (fun i =>
        sweepLeft T mode (xs.getD (i / ys.length) 0) ^^^
          sweepRight T mode (ys.getD (i % ys.length) 0)) := by
  rw [gridWords, gridLeftImages_eq T mode xs ys leftColumns hy hx hlc hlf,
    packedOnes_eq, gridRowMarkers_eq,
    packedImages_eq ys rightColumns (sweepRight T mode) hyb hrc hrf,
    packF_broadcast_rows, packF_broadcast_cols]
  apply packF_xor
  · decide
  · intro i hi
    have hi' : i / ys.length < xs.length := (Nat.div_lt_iff_lt_mul hy).mpr hi
    rw [List.getD_eq_getElem _ _ hi']
    exact lt_of_lt_of_le (hl _ (List.getElem_mem hi')) (by decide : 2 ^ 30 ≤ 2 ^ 32)
  · intro i _
    have hi' := Nat.mod_lt i hy
    rw [List.getD_eq_getElem _ _ hi']
    exact lt_of_lt_of_le (hr _ (List.getElem_mem hi')) (by decide : 2 ^ 30 ≤ 2 ^ 32)

/-- Validate exceptional pairs using packed input and census lookups. -/
def checkGridExceptions (T : SweepTables) (census : PackedCensus)
    (mode ann : Nat) (xs ys : List Nat) (certs : List (Nat × Nat)) : Bool :=
  match certs with
  | [] => true
  | _ :: _ =>
      forceNat census.data fun data =>
      forceNat (packList 32 xs) fun packedXs =>
      forceNat (packList 32 ys) fun packedYs =>
      forceNat ys.length fun width =>
        certs.all (fun p => sweepAcceptAt T { census with data := data } mode
          (lane 32 (p.1 / width) packedXs) (lane 32 (p.1 % width) packedYs) ann p.2)

/-- Packed input lookups preserve list lookup, including its out-of-range
zero default. -/
theorem checkGridExceptions_eq (T : SweepTables) (census : PackedCensus)
    (mode ann : Nat) (xs ys : List Nat) (certs : List (Nat × Nat))
    (hxMasks : ∀ v ∈ xs, v < 2 ^ 30) (hyMasks : ∀ v ∈ ys, v < 2 ^ 30) :
    checkGridExceptions T census mode ann xs ys certs =
      certs.all (fun p => sweepAcceptAt T census mode
        (xs.getD (p.1 / ys.length) 0) (ys.getD (p.1 % ys.length) 0) ann p.2) := by
  have hxLane (i : Nat) : lane 32 i (packList 32 xs) = xs.getD i 0 := by
    rw [packList_eq_ofDigits]
    exact lane_ofDigits 32 i xs fun v hv =>
      lt_of_lt_of_le (hxMasks v hv) (by decide : 2 ^ 30 ≤ 2 ^ 32)
  have hyLane (i : Nat) : lane 32 i (packList 32 ys) = ys.getD i 0 := by
    rw [packList_eq_ofDigits]
    exact lane_ofDigits 32 i ys fun v hv =>
      lt_of_lt_of_le (hyMasks v hv) (by decide : 2 ^ 30 ≤ 2 ^ 32)
  cases certs with
  | nil => rfl
  | cons p ps => simp only [checkGridExceptions, forceNat_eq, hxLane, hyLane]

/-- Check all weights in a grid and validate only its sparse exceptional pairs. -/
def checkGrid (T : SweepTables) (census : PackedCensus)
    (mode ann target : Nat) (xs ys : List Nat)
    (words : Nat) (certs : List (Nat × Nat)) : Bool :=
  Nat.beq (forceNat (gridRep xs ys) fun rep =>
      weightFlags rep (words ^^^ rep * ann) target)
    (indexFlags (certs.map Prod.fst)) &&
  checkGridExceptions T census mode ann xs ys certs

/-- A checked grid covers every pair of its outer and inner masks. -/
theorem checkGrid_sound (T : SweepTables) (census : PackedCensus)
    (mode ann target : Nat) (xs ys : List Nat)
    (words : Nat) (certs : List (Nat × Nat))
    (hcensus : PackedCensus.Valid T.cls census)
    (hy : 0 < ys.length) (ha : ann < 2 ^ 30) (ht : target < 32)
    (hxMasks : ∀ v ∈ xs, v < 2 ^ 30) (hyMasks : ∀ v ∈ ys, v < 2 ^ 30)
    (hl : ∀ x ∈ xs, sweepLeft T mode x < 2 ^ 30)
    (hr : ∀ y ∈ ys, sweepRight T mode y < 2 ^ 30)
    (hwords : words = packF 32 (xs.length * ys.length) (fun i =>
      sweepLeft T mode (xs.getD (i / ys.length) 0) ^^^
        sweepRight T mode (ys.getD (i % ys.length) 0)))
    (hcheck : checkGrid T census mode ann target xs ys words certs = true) :
    ∀ x ∈ xs, ∀ y ∈ ys, popCntGo 30 (sweepOutput T mode x y ann) = target →
      sweepAccept T mode x y ann = true := by
  intro x hx y hy' hweight
  obtain ⟨ix, hix, hex⟩ := List.getElem_of_mem hx
  obtain ⟨iy, hiy, hey⟩ := List.getElem_of_mem hy'
  let i := ix * ys.length + iy
  have hi : i < xs.length * ys.length := by
    have h := Nat.mul_le_mul_right ys.length (Nat.succ_le_of_lt hix)
    simp only [Nat.succ_mul] at h
    omega
  have hid : i / ys.length = ix := by
    dsimp only [i]
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hy, Nat.div_eq_of_lt hiy, Nat.zero_add]
  have him : i % ys.length = iy := by simp [i, Nat.mod_eq_of_lt hiy]
  have hxget : xs.getD (i / ys.length) 0 = x := by
    rw [hid, List.getD_eq_getElem _ _ hix, hex]
  have hyget : ys.getD (i % ys.length) 0 = y := by
    rw [him, List.getD_eq_getElem _ _ hiy, hey]
  let f := fun j => sweepLeft T mode (xs.getD (j / ys.length) 0) ^^^
    sweepRight T mode (ys.getD (j % ys.length) 0)
  have hf : ∀ j < xs.length * ys.length, f j < 2 ^ 30 := by
    intro j hj
    have hjx : j / ys.length < xs.length := (Nat.div_lt_iff_lt_mul hy).mpr hj
    have hjy := Nat.mod_lt j hy
    dsimp only [f]
    rw [List.getD_eq_getElem _ _ hjx, List.getD_eq_getElem _ _ hjy]
    exact Nat.xor_lt_two_pow (hl _ (List.getElem_mem hjx))
      (hr _ (List.getElem_mem hjy))
  have hpacked : words ^^^ gridRep xs ys * ann =
      packF 32 (xs.length * ys.length) (fun j => f j ^^^ ann) := by
    rw [hwords, gridRep_eq, repeat_mul_eq_packF]
    apply packF_xor
    · decide
    · exact fun j hj => lt_of_lt_of_le (hf j hj) (by decide : 2 ^ 30 ≤ 2 ^ 32)
    · exact fun _ _ => lt_of_lt_of_le ha (by decide : 2 ^ 30 ≤ 2 ^ 32)
  simp only [checkGrid, checkGridExceptions_eq T census mode ann xs ys certs hxMasks hyMasks,
    forceNat_eq, Bool.and_eq_true, Nat.beq_eq, gridRep_eq] at hcheck
  have hm : i ∈ certs.map Prod.fst := weightFlags_sound (xs.length * ys.length)
    target (words ^^^ gridRep xs ys * ann) (fun j => f j ^^^ ann)
    (fun j hj => Nat.xor_lt_two_pow (hf j hj) ha) ht hpacked _
    (by simpa only [gridRep_eq] using hcheck.1) i hi (by
      rw [← popCntGo_eq_bitCount]
      simpa only [f, hxget, hyget, sweepOutput] using hweight)
  obtain ⟨p, hp, he⟩ := List.mem_map.mp hm
  have hv := sweepAcceptAt_sound T census mode _ _ ann p.2 hcensus
    (List.all_eq_true.mp hcheck.2 p hp)
  simpa only [he, hxget, hyget] using hv

end Quantum.Stabilizer.Homological.LP.M150

#print axioms Quantum.Stabilizer.Homological.LP.M150.checkGrid_sound
#print axioms Quantum.Stabilizer.Homological.LP.M150.checkGridExceptions_eq
