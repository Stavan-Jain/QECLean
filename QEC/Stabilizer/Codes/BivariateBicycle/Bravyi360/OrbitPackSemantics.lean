import QEC.Stabilizer.Framework.Homological.Certificate.OrbitPackedExtra

noncomputable section

namespace Quantum.Stabilizer.Homological.GBOrbit
open PackedDigits

/-- Sparse scalar multiplier copying a word into15 separated positions. -/
noncomputable def copyPattern : Nat := 0x400000000000000000000000000000020000000000000000000000000000001000000000000000000000000000000080000000000000000000000000000004000000000000000000000000000000200000000000000000000000000000010000000000000000000000000000000800000000000000000000000000000040000000000000000000000000000002000000000000000000000000000000100000000000000000000000000000008000000000000000000000000000000400000000000000000000000000000020000000000000000000000000000001

/-- The literal `copyPattern` has the stated finite-table interpretation. -/
theorem copyPattern_eq : copyPattern = packF 125 15 (fun _ => 1) := by decide +kernel

/-- Mask selecting45-bit windows in15 separated lanes. -/
noncomputable def blockMaskPattern : Nat := 0x1fffffffffff000000000000000000001fffffffffff000000000000000000001fffffffffff000000000000000000001fffffffffff000000000000000000001fffffffffff000000000000000000001fffffffffff000000000000000000001fffffffffff000000000000000000001fffffffffff000000000000000000001fffffffffff000000000000000000001fffffffffff000000000000000000001fffffffffff000000000000000000001fffffffffff000000000000000000001fffffffffff000000000000000000001fffffffffff000000000000000000001fffffffffff

/-- The literal `blockMaskPattern` has the stated finite-table interpretation. -/
theorem blockMaskPattern_eq : blockMaskPattern = packF 128 15 (fun _ => 2 ^ 45 - 1) := by decide +kernel

/-- One low bit in each of45 lanes. -/
noncomputable def repeatPattern : Nat := 0x10000000000000000000000000000000100000000000000000000000000000001000000000000000000000000000000010000000000000000000000000000000100000000000000000000000000000001000000000000000000000000000000010000000000000000000000000000000100000000000000000000000000000001000000000000000000000000000000010000000000000000000000000000000100000000000000000000000000000001000000000000000000000000000000010000000000000000000000000000000100000000000000000000000000000001000000000000000000000000000000010000000000000000000000000000000100000000000000000000000000000001000000000000000000000000000000010000000000000000000000000000000100000000000000000000000000000001000000000000000000000000000000010000000000000000000000000000000100000000000000000000000000000001000000000000000000000000000000010000000000000000000000000000000100000000000000000000000000000001000000000000000000000000000000010000000000000000000000000000000100000000000000000000000000000001000000000000000000000000000000010000000000000000000000000000000100000000000000000000000000000001000000000000000000000000000000010000000000000000000000000000000100000000000000000000000000000001000000000000000000000000000000010000000000000000000000000000000100000000000000000000000000000001000000000000000000000000000000010000000000000000000000000000000100000000000000000000000000000001000000000000000000000000000000010000000000000000000000000000000100000000000000000000000000000001

/-- The literal `repeatPattern` has the stated finite-table interpretation. -/
theorem repeatPattern_eq : repeatPattern = packF 128 45 (fun _ => 1) := by decide +kernel

/-- The comparison sentinel in each of45 lanes. -/
noncomputable def sentinelPattern : Nat := 0x400000000000000000000000000000004000000000000000000000000000000040000000000000000000000000000000400000000000000000000000000000004000000000000000000000000000000040000000000000000000000000000000400000000000000000000000000000004000000000000000000000000000000040000000000000000000000000000000400000000000000000000000000000004000000000000000000000000000000040000000000000000000000000000000400000000000000000000000000000004000000000000000000000000000000040000000000000000000000000000000400000000000000000000000000000004000000000000000000000000000000040000000000000000000000000000000400000000000000000000000000000004000000000000000000000000000000040000000000000000000000000000000400000000000000000000000000000004000000000000000000000000000000040000000000000000000000000000000400000000000000000000000000000004000000000000000000000000000000040000000000000000000000000000000400000000000000000000000000000004000000000000000000000000000000040000000000000000000000000000000400000000000000000000000000000004000000000000000000000000000000040000000000000000000000000000000400000000000000000000000000000004000000000000000000000000000000040000000000000000000000000000000400000000000000000000000000000004000000000000000000000000000000040000000000000000000000000000000400000000000000000000000000000004000000000000000000000000000000040000000000000000000000000000000400000000000000000000000000000004000000000000000000000000000000040000000000000000000000

/-- The literal `sentinelPattern` has the stated finite-table interpretation. -/
theorem sentinelPattern_eq : sentinelPattern = packF 128 45 (fun _ => 2 ^ 90) := by decide +kernel

/-- The90-bit payload mask in each of45 lanes. -/
noncomputable def payloadPattern : Nat := 0x3ffffffffffffffffffffff0000000003ffffffffffffffffffffff0000000003ffffffffffffffffffffff0000000003ffffffffffffffffffffff0000000003ffffffffffffffffffffff0000000003ffffffffffffffffffffff0000000003ffffffffffffffffffffff0000000003ffffffffffffffffffffff0000000003ffffffffffffffffffffff0000000003ffffffffffffffffffffff0000000003ffffffffffffffffffffff0000000003ffffffffffffffffffffff0000000003ffffffffffffffffffffff0000000003ffffffffffffffffffffff0000000003ffffffffffffffffffffff0000000003ffffffffffffffffffffff0000000003ffffffffffffffffffffff0000000003ffffffffffffffffffffff0000000003ffffffffffffffffffffff0000000003ffffffffffffffffffffff0000000003ffffffffffffffffffffff0000000003ffffffffffffffffffffff0000000003ffffffffffffffffffffff0000000003ffffffffffffffffffffff0000000003ffffffffffffffffffffff0000000003ffffffffffffffffffffff0000000003ffffffffffffffffffffff0000000003ffffffffffffffffffffff0000000003ffffffffffffffffffffff0000000003ffffffffffffffffffffff0000000003ffffffffffffffffffffff0000000003ffffffffffffffffffffff0000000003ffffffffffffffffffffff0000000003ffffffffffffffffffffff0000000003ffffffffffffffffffffff0000000003ffffffffffffffffffffff0000000003ffffffffffffffffffffff0000000003ffffffffffffffffffffff0000000003ffffffffffffffffffffff0000000003ffffffffffffffffffffff0000000003ffffffffffffffffffffff0000000003ffffffffffffffffffffff0000000003ffffffffffffffffffffff0000000003ffffffffffffffffffffff0000000003ffffffffffffffffffffff

/-- The literal `payloadPattern` has the stated finite-table interpretation. -/
theorem payloadPattern_eq : payloadPattern = packF 128 45 (fun _ => 2 ^ 90 - 1) := by decide +kernel

/-- A duplicated45-bit word exposes every cyclic x translation as a window. -/
noncomputable def doubled (w : Nat) : Nat := w ||| (w <<< 45)

/-- The15 cyclic x translations, computed by one sparse multiplication and mask. -/
noncomputable def packX (w : Nat) : Nat :=
  (doubled w * copyPattern) &&& blockMaskPattern

/-- An x translation reads a45-bit window starting at a multiple of3. -/
noncomputable def translateX (w i : Nat) : Nat := (doubled w >>> (3 * i)) &&& (2 ^ 45 - 1)

/-- Duplicating a45-bit word produces a90-bit word. -/
theorem doubled_lt {w : Nat} (hw : w < 2 ^ 45) : doubled w < 2 ^ 90 := by
  apply Nat.or_lt_two_pow
  · exact lt_trans hw (by norm_num)
  · rw [Nat.shiftLeft_eq]
    have h := Nat.mul_lt_mul_of_pos_right hw (Nat.two_pow_pos 45)
    norm_num at h ⊢
    exact h

/-- Each x translation fits in45bits. -/
theorem translateX_lt (w i : Nat) : translateX w i < 2 ^ 45 := by
  exact lt_of_le_of_lt Nat.and_le_right (by norm_num)

/-- Sparse multiplication packs the15 cyclic x translations in128-bit lanes. -/
theorem packX_eq_packF {w : Nat} (hw : w < 2 ^ 45) :
    packX w = packF 128 15 (translateX w) := by
  have hd : doubled w < 2 ^ 125 := lt_trans (doubled_lt hw) (by norm_num)
  have hm : ∀ i < 15, 2 ^ 45 - 1 < 2 ^ 128 := fun _ _ => by norm_num
  have ht : ∀ i < 15, translateX w i < 2 ^ 128 := fun i _ =>
    lt_trans (translateX_lt w i) (by norm_num)
  rw [packX, copyPattern_eq, blockMaskPattern_eq, packF_mul]
  simp only [Nat.mul_one]
  apply eq_of_lane_eq (by decide : 0 < 128)
  intro i
  rw [lane_and, lane_packF _ _ _ _ hm, lane_packF _ _ _ _ ht]
  by_cases hi : i < 15
  · simp only [if_pos hi]
    apply Nat.eq_of_testBit_eq
    intro j
    rw [Nat.testBit_and, testBit_lane, Nat.testBit_two_pow_sub_one]
    by_cases hj : j < 45
    · have hj' : 3 * i + j < 125 := by omega
      have he : 128 * i + j = 125 * i + (3 * i + j) := by omega
      rw [he, testBit_packF_at 125 15 i (3 * i + j) _ (fun _ _ => hd) hj']
      simp only [if_pos hi, hj, show j < 128 by omega, translateX,
        Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one,
        decide_true, Bool.and_true]
    · simp only [hj, translateX, Nat.testBit_and, Nat.testBit_two_pow_sub_one,
        decide_false, Bool.and_false]
  · simp [hi]

/-- A bit in a cyclic x translation is read from the corresponding cyclic position. -/
theorem testBit_translateX {w i j : Nat} (hw : w < 2 ^ 45) (hi : i < 15) (hj : j < 45) :
    (translateX w i).testBit j = w.testBit ((3 * i + j) % 45) := by
  have hk : 3 * i + j < 90 := by omega
  simp only [translateX, Nat.testBit_and, Nat.testBit_shiftRight,
    Nat.testBit_two_pow_sub_one, decide_eq_true_eq, hj, Bool.and_true,
    doubled, Nat.testBit_or, Nat.testBit_shiftLeft]
  by_cases hlow : 3 * i + j < 45
  · have hge : ¬ 45 ≤ 3 * i + j := by omega
    simp [hlow, hge, Nat.mod_eq_of_lt hlow]
  · have hge : 45 ≤ 3 * i + j := by omega
    have hz : w.testBit (3 * i + j) = false := Nat.testBit_eq_false_of_lt
      (lt_of_lt_of_le hw (Nat.pow_le_pow_right (by decide) hge))
    have hmod : (3 * i + j) % 45 = 3 * i + j - 45 := by omega
    simp [hz, hge, hmod]


/-- Rotate the y coordinate in every three-bit cell of a45-bit block. -/
noncomputable def translateY (w : Nat) : Nat :=
  ((w &&& 0xdb6db6db6db) <<< 1) ||| ((w &&& 0x124924924924) >>> 2)

/-- A y translation always fits in45bits. -/
theorem translateY_lt (w : Nat) : translateY w < 2 ^ 45 := by
  apply Nat.or_lt_two_pow
  · have h : w &&& 0xdb6db6db6db ≤ 0xdb6db6db6db := Nat.and_le_right
    change (w &&& 0xdb6db6db6db) <<< 1 < 2 ^ 45
    rw [Nat.shiftLeft_eq]
    norm_num at h ⊢
    omega
  · have h : w &&& 0x124924924924 ≤ 0x124924924924 := Nat.and_le_right
    change (w &&& 0x124924924924) >>> 2 < 2 ^ 45
    rw [Nat.shiftRight_eq_div_pow]
    norm_num at h ⊢
    omega

/-- The low-cell mask selects the first two bits in each y cell. -/
theorem lowCell_bit (j : Fin 47) :
    (0xdb6db6db6db : Nat).testBit j.val = decide (j.val < 45 ∧ j.val % 3 < 2) := by
  revert j
  decide +kernel

/-- The high-cell mask selects the third bit in each y cell. -/
theorem highCell_bit (j : Fin 47) :
    (0x124924924924 : Nat).testBit j.val = decide (j.val < 45 ∧ j.val % 3 = 2) := by
  revert j
  decide +kernel

/-- The y translation reads the preceding y coordinate in each cell. -/
theorem testBit_translateY (w j : Nat) (hj : j < 45) :
    (translateY w).testBit j = w.testBit (3 * (j / 3) + (j % 3 + 2) % 3) := by
  have hl := lowCell_bit ⟨j - 1, by omega⟩
  have hh := highCell_bit ⟨2 + j, by omega⟩
  simp only [Fin.val_mk] at hl hh
  simp only [translateY, Nat.testBit_or, Nat.testBit_shiftLeft,
    Nat.testBit_shiftRight, Nat.testBit_and]
  rw [hl, hh]
  interval_cases j <;> norm_num

/-- Join two45-bit blocks into a90-bit chain. -/
noncomputable def join (a b : Nat) : Nat := a ||| (b <<< 45)

/-- Two bounded45-bit blocks form a bounded90-bit chain. -/
theorem join_lt {a b : Nat} (ha : a < 2 ^ 45) (hb : b < 2 ^ 45) : join a b < 2 ^ 90 := by
  apply Nat.or_lt_two_pow (lt_trans ha (by norm_num))
  exact Nat.shiftLeft_lt hb

/-- Translate both qubit blocks together in x. -/
noncomputable def translatePair (a b i : Nat) : Nat := join (translateX a i) (translateX b i)

/-- Packed translations of both blocks agree with the corresponding finite table. -/
theorem packPair_eq {a b : Nat} (ha : a < 2 ^ 45) (hb : b < 2 ^ 45) :
    packX a ||| (packX b <<< 45) = packF 128 15 (translatePair a b) := by
  have hat : ∀ i < 15, translateX a i < 2 ^ 128 := fun i _ =>
    lt_trans (translateX_lt a i) (by norm_num)
  have hbt : ∀ i < 15, translateX b i <<< 45 < 2 ^ 128 := by
    intro i hi
    exact lt_trans (Nat.shiftLeft_lt (translateX_lt b i)) (by norm_num)
  rw [packX_eq_packF ha, packX_eq_packF hb]
  have hs : (packF 128 15 (translateX b) <<< 45) =
      packF 128 15 (fun i => translateX b i <<< 45) := packF_shiftLeft 128 15 45 _
  rw [hs, packF_or _ _ _ _ (by decide) hat hbt]
  rfl

/-- The three y translations of a pair of qubit blocks. -/
noncomputable def entry (a b i : Nat) : Nat :=
  if i < 15 then translatePair a b i
  else if i - 15 < 15 then translatePair (translateY a) (translateY b) (i - 15)
  else translatePair (translateY (translateY a)) (translateY (translateY b)) (i - 30)

/-- Every translated entry is a90-bit chain. -/
theorem entry_lt (a b i : Nat) : entry a b i < 2 ^ 90 := by
  unfold entry translatePair
  split
  · exact join_lt (translateX_lt _ _) (translateX_lt _ _)
  · split <;> exact join_lt (translateX_lt _ _) (translateX_lt _ _)

/-- The multiplication-based packed orbit contains all45 translations. -/
noncomputable def packOrbit (a b : Nat) : Nat :=
  let p0 := packX a ||| (packX b <<< 45)
  let p1 := packX (translateY a) ||| (packX (translateY b) <<< 45)
  let p2 := packX (translateY (translateY a)) ||| (packX (translateY (translateY b)) <<< 45)
  p0 ||| ((p1 ||| (p2 <<< 1920)) <<< 1920)

/-- The packed-orbit implementation is the mathematical translation table. -/
theorem packOrbit_eq {a b : Nat} (ha : a < 2 ^ 45) (hb : b < 2 ^ 45) :
    packOrbit a b = packF 128 45 (entry a b) := by
  have hp : ∀ a b i, translatePair a b i < 2 ^ 128 := fun a b i =>
    lt_trans (join_lt (translateX_lt a i) (translateX_lt b i)) (by norm_num)
  unfold packOrbit
  rw [packPair_eq ha hb,
    packPair_eq (translateY_lt a) (translateY_lt b),
    packPair_eq (translateY_lt (translateY a)) (translateY_lt (translateY b))]
  dsimp only
  rw [show 1920 = 128 * 15 from rfl,
    packF_append 128 15 15 _ _ (by decide) (fun i _ => hp _ _ i) (fun i _ => hp _ _ i)]
  rw [packF_append 128 15 30 _ _ (by decide) (fun i _ => hp _ _ i)]
  · apply packF_congr
    intro i hi
    simp only [entry]
    split
    · rfl
    · split <;> simp_all only [Nat.sub_sub]
  · intro i hi
    split <;> exact hp _ _ _


/-- Read a bit in the first block of a joined chain. -/
theorem testBit_join_low (a b j : Nat) (hj : j < 45) :
    (join a b).testBit j = a.testBit j := by
  simp [join, Nat.testBit_or, Nat.testBit_shiftLeft, show ¬45 ≤ j by omega]

/-- Read a bit in the second block of a joined chain. -/
theorem testBit_join_high {a b j : Nat} (ha : a < 2 ^ 45) (hj : 45 ≤ j) :
    (join a b).testBit j = b.testBit (j - 45) := by
  have hz : a.testBit j = false := Nat.testBit_eq_false_of_lt
    (lt_of_lt_of_le ha (Nat.pow_le_pow_right (by decide) hj))
  simp [join, Nat.testBit_or, Nat.testBit_shiftLeft, hz, hj]

/-- Translate one45-bit block in both coordinates. -/
noncomputable def translateBlock (w x y : Nat) : Nat :=
  translateX (if y = 0 then w else if y = 1 then translateY w else translateY (translateY w)) x

/-- Coordinate formula for a translation of one45-bit block. -/
theorem testBit_translateBlock {w x y j : Nat} (hw : w < 2 ^ 45)
    (hx : x < 15) (hy : y < 3) (hj : j < 45) :
    (translateBlock w x y).testBit j =
      w.testBit (3 * ((j / 3 + x) % 15) + (j % 3 + 3 - y) % 3) := by
  have ht : (3 * x + j) % 45 < 45 := Nat.mod_lt _ (by decide)
  interval_cases y
  · simp only [translateBlock, ite_true, ite_false, Nat.reduceEqDiff]
    rw [testBit_translateX hw hx hj]
    congr 1
    omega
  · simp only [translateBlock, ite_true, ite_false, Nat.reduceEqDiff]
    rw [testBit_translateX (translateY_lt w) hx hj, testBit_translateY _ _ ht]
    congr 1
    omega
  · simp only [translateBlock, show ¬(2 : Nat) = 0 by decide,
      show ¬(2 : Nat) = 1 by decide, if_false]
    rw [testBit_translateX (translateY_lt (translateY w)) hx hj,
      testBit_translateY _ _ ht]
    have hu : 3 * (((3 * x + j) % 45) / 3) + (((3 * x + j) % 45) % 3 + 2) % 3 < 45 := by omega
    rw [testBit_translateY _ _ hu]
    congr 1
    omega

/-- An orbit-table entry is the simultaneous coordinate translation of both blocks. -/
theorem entry_eq_translateBlock (a b x y : Nat) (hx : x < 15) (hy : y < 3) :
    entry a b (15 * y + x) = join (translateBlock a x y) (translateBlock b x y) := by
  interval_cases y
  · simp [entry, translateBlock, translatePair, hx]
  · simp [entry, translateBlock, translatePair, hx]
  · simp [entry, translateBlock, translatePair, hx,
      show ¬30 + x < 15 by omega, show ¬30 + x - 15 < 15 by omega]

/-- Packed canonicality test: every translated90-bit entry is at least the original. -/
noncomputable def canonicalCheck (w : Nat) : Bool :=
  Nat.beq (((packOrbit (w % 2 ^ 45) (w / 2 ^ 45) +
    sentinelPattern) - w * repeatPattern) &&& sentinelPattern) sentinelPattern

/-- The packed canonicality check proves comparison with every translation. -/
theorem canonicalCheck_sound {w : Nat} (hw : w < 2 ^ 90) (hcheck : canonicalCheck w = true) :
    ∀ i < 45, w ≤ entry (w % 2 ^ 45) (w / 2 ^ 45) i := by
  have ha : w % 2 ^ 45 < 2 ^ 45 := Nat.mod_lt _ (Nat.two_pow_pos _)
  have hb : w / 2 ^ 45 < 2 ^ 45 := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)]
    norm_num at hw ⊢
    exact hw
  unfold canonicalCheck at hcheck
  rw [sentinelPattern_eq, repeatPattern_eq] at hcheck

  rw [Nat.beq_eq, packOrbit_eq ha hb, packF_mul] at hcheck
  simp only [Nat.mul_one] at hcheck
  exact packed_guarded_sub_sound 128 45 90 w _ (by decide) (fun j _ => entry_lt _ _ j) hw hcheck

end Quantum.Stabilizer.Homological.GBOrbit
