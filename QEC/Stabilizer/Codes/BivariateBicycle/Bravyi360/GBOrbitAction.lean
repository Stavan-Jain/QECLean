import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.OrbitPackSemantics
import QEC.Stabilizer.Framework.Homological.Certificate.OrbitCensus
import QEC.Stabilizer.Framework.Homological.BBChainComplex
import Mathlib.Logic.Equiv.Fin.Basic

noncomputable section

namespace Quantum.Stabilizer.Homological.GBOrbit
open PackedDigits

/-- Translation group of the90-qubit bottom code. -/
abbrev TranslationGroup := ZMod 15 × ZMod 3

/-- Qubit coordinates for the90-qubit bottom code. -/
abbrev Qubit := TranslationGroup × Fin 2

/-- Pack the block index first, followed by x and y with y varying fastest. -/
noncomputable def qubitEnum : Qubit ≃ Fin 90 :=
  (Equiv.prodComm _ _).trans
    ((Equiv.prodCongr (Equiv.refl (Fin 2)) finProdFinEquiv).trans finProdFinEquiv)

/-- The numerical index of a bottom-code qubit. -/
theorem qubitEnum_val (q : Qubit) :
    (qubitEnum q).val = q.1.2.val + 3 * q.1.1.val + 45 * q.2.val := rfl

/-- A chain encoded in the mask convention of the finite certificates. -/
noncomputable def chainMask (v : Qubit → ZMod 2) : Nat := F2Mask.maskOf qubitEnum v

/-- Translation acts on chains through the existing BB translation operator. -/
noncomputable instance chainTranslationAction : MulAction (Multiplicative TranslationGroup) (Qubit → ZMod 2) where
  smul g v := BB.translate1 g.toAdd v
  one_smul v := by
    funext q
    change v (q.1 + 0, q.2) = v q
    rw [add_zero]
  mul_smul g h v := by
    funext q
    change v (q.1 + (g.toAdd + h.toAdd), q.2) =
      v ((q.1 + g.toAdd) + h.toAdd, q.2)
    rw [add_assoc]

/-- The mask order makes chain canonicality a comparison of natural-number masks. -/
noncomputable instance chainMaskOrder : LinearOrder (Qubit → ZMod 2) :=
  LinearOrder.lift' chainMask (F2Mask.maskOf_injective qubitEnum)

/-- The low block is a45-bit word. -/
theorem lowBlock_lt (w : Nat) : w % 2 ^ 45 < 2 ^ 45 := Nat.mod_lt _ (Nat.two_pow_pos _)

/-- The high block of a90-bit word is a45-bit word. -/
theorem highBlock_lt {w : Nat} (hw : w < 2 ^ 90) : w / 2 ^ 45 < 2 ^ 45 := by
  rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)]
  norm_num at hw ⊢
  exact hw

/-- Translation in y is subtraction modulo3 in the packed orbit's index order. -/
theorem y_sub_val (a b : ZMod 3) : (a - b).val = (a.val + 3 - b.val) % 3 := by
  revert a b
  decide +kernel

/-- Read a low-block bit directly from its full mask. -/
theorem lowBlock_testBit (w j : Nat) (hj : j < 45) :
    (w % 2 ^ 45).testBit j = w.testBit j := by
  simp only [Nat.testBit_mod_two_pow, hj, decide_true, Bool.true_and]

/-- Read a high-block bit directly from its full mask. -/
theorem highBlock_testBit (w j : Nat) :
    (w / 2 ^ 45).testBit j = w.testBit (j + 45) := by
  exact Nat.testBit_div_two_pow w j

/-- The natural index of the translated qubit agrees with the blockwise formula. -/
theorem translated_index (q : Qubit) (x : ZMod 15) (y : ZMod 3) :
    (qubitEnum (q.1 + (x, -y), q.2)).val =
      3 * ((q.1.1.val + x.val) % 15) + (q.1.2.val + 3 - y.val) % 3 + 45 * q.2.val := by
  rw [qubitEnum_val]
  simp only [Prod.fst_add, Prod.snd_add]
  rw [ZMod.val_add q.1.1 x, ← sub_eq_add_neg q.1.2 y, y_sub_val]
  omega


/-- Numerical coordinate permutation for one of the45 translations. -/
noncomputable def translateIndex (x y j : Nat) : Nat :=
  45 * (j / 45) + 3 * (((j % 45) / 3 + x) % 15) + ((j % 45) % 3 + 3 - y) % 3

/-- Every table entry acts on the full mask by the stated coordinate permutation. -/
theorem entry_testBit {w x y j : Nat} (hw : w < 2 ^ 90)
    (hx : x < 15) (hy : y < 3) (hj : j < 90) :
    (entry (w % 2 ^ 45) (w / 2 ^ 45) (15 * y + x)).testBit j =
      w.testBit (translateIndex x y j) := by
  rw [entry_eq_translateBlock _ _ _ _ hx hy]
  by_cases hl : j < 45
  · rw [testBit_join_low _ _ _ hl,
      testBit_translateBlock (lowBlock_lt w) hx hy hl]
    have hs : 3 * ((j / 3 + x) % 15) + (j % 3 + 3 - y) % 3 < 45 := by omega
    rw [lowBlock_testBit _ _ hs]
    congr 1
    simp [translateIndex, Nat.div_eq_of_lt hl, Nat.mod_eq_of_lt hl]
  · have hg : 45 ≤ j := by omega
    have hlow : translateBlock (w % 2 ^ 45) x y < 2 ^ 45 := translateX_lt _ _
    rw [testBit_join_high hlow hg,
      testBit_translateBlock (highBlock_lt hw) hx hy (by omega), highBlock_testBit]
    congr 1
    unfold translateIndex
    omega

/-- The coordinate permutation agrees with addition in the BB translation group. -/
theorem translateIndex_enum (q : Qubit) (x : ZMod 15) (y : ZMod 3) :
    translateIndex x.val y.val (qubitEnum q).val =
      (qubitEnum (q.1 + (x, -y), q.2)).val := by
  rw [translated_index, qubitEnum_val]
  unfold translateIndex
  have hx := ZMod.val_lt q.1.1
  have hy := ZMod.val_lt q.1.2
  have hb := q.2.isLt
  omega

/-- Each packed orbit entry is the mask of the corresponding BB-translated chain. -/
theorem entry_chainMask (v : Qubit → ZMod 2) (x : ZMod 15) (y : ZMod 3) :
    entry (chainMask v % 2 ^ 45) (chainMask v / 2 ^ 45) (15 * y.val + x.val) =
      chainMask (BB.translate1 (x, -y) v) := by
  have hw : chainMask v < 2 ^ 90 := F2Mask.maskOf_lt qubitEnum v
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < 90
  · rw [entry_testBit hw (ZMod.val_lt x) (ZMod.val_lt y) hj]
    let q := qubitEnum.symm ⟨j, hj⟩
    have hq : (qubitEnum q).val = j := by simp [q]
    rw [← hq, translateIndex_enum]
    simp only [chainMask, F2Mask.testBit_maskOf_apply, BB.translate1]
    rfl
  · have hbound : 2 ^ 90 ≤ 2 ^ j := Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (entry_lt _ _ _) hbound)]
    change false = (F2Mask.maskOf qubitEnum (BB.translate1 (x, -y) v)).testBit j
    rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (F2Mask.maskOf_lt qubitEnum _) hbound)]

/-- Passing the packed canonicality check makes a chain a canonical orbit representative. -/
theorem canonicalCheck_chain_sound (v : Qubit → ZMod 2)
    (h : canonicalCheck (chainMask v) = true) :
    OrbitCensus.IsCanonical (G := Multiplicative TranslationGroup) v := by
  intro g
  let x := g.toAdd.1
  let y := -g.toAdd.2
  have hi : 15 * y.val + x.val < 45 := by have := ZMod.val_lt y; have := ZMod.val_lt x; omega
  have hc := canonicalCheck_sound (F2Mask.maskOf_lt qubitEnum v) h
    (15 * y.val + x.val) hi
  change chainMask v ≤ entry (chainMask v % 2 ^ 45) (chainMask v / 2 ^ 45) (15 * y.val + x.val) at hc
  rw [entry_chainMask] at hc
  change chainMask v ≤ chainMask (BB.translate1 g.toAdd v)
  simpa [x, y] using hc


/-- Packed mask whose sentinel bits identify the translations fixing a word. -/
noncomputable def fixedMask (w : Nat) : Nat :=
  sentinelPattern ^^^
    (((packOrbit (w % 2 ^ 45) (w / 2 ^ 45) ^^^ w * repeatPattern) +
      payloadPattern) &&& sentinelPattern)

/-- A sentinel bit of the fixed mask means exactly that its translation fixes the chain. -/
theorem fixedMask_bit (v : Qubit → ZMod 2) (x : ZMod 15) (y : ZMod 3) :
    (fixedMask (chainMask v)).testBit (128 * (15 * y.val + x.val) + 90) =
      decide (BB.translate1 (x, -y) v = v) := by
  have hw : chainMask v < 2 ^ 90 := F2Mask.maskOf_lt qubitEnum v
  have hi : 15 * y.val + x.val < 45 := by have := ZMod.val_lt y; have := ZMod.val_lt x; omega
  have h := packed_equal_mask_bit 128 45 90 (chainMask v) (15 * y.val + x.val)
    (entry (chainMask v % 2 ^ 45) (chainMask v / 2 ^ 45))
    (by decide) (fun i _ => entry_lt _ _ i) hw hi
  rw [entry_chainMask] at h
  have heq : (chainMask (BB.translate1 (x, -y) v) = chainMask v) ↔
      BB.translate1 (x, -y) v = v := (F2Mask.maskOf_injective qubitEnum).eq_iff
  simp only [heq] at h
  unfold fixedMask
  rw [sentinelPattern_eq, repeatPattern_eq, payloadPattern_eq]
  change (packF 128 45 (fun _ => 2 ^ 90) ^^^ (((packOrbit (chainMask v % 2 ^ 45) (chainMask v / 2 ^ 45) ^^^ chainMask v * packF 128 45 (fun _ => 1)) + packF 128 45 (fun _ => 2 ^ 90 - 1)) &&& packF 128 45 (fun _ => 2 ^ 90))).testBit (128 * (15 * y.val + x.val) + 90) = _
  rw [packOrbit_eq (lowBlock_lt _) (highBlock_lt hw), packF_mul]
  simp only [Nat.mul_one]
  simpa only [testBit_lane, show 90 < 128 from by decide, decide_true, Bool.and_true] using h

/-- Enumerate group elements in the x-fast, negated-y order used by the packed orbit. -/
noncomputable def orbitEnum : Multiplicative TranslationGroup ≃ Fin 45 :=
  (Multiplicative.toAdd).trans
    ((Equiv.prodCongr (Equiv.refl (ZMod 15)) (Equiv.neg (ZMod 3))).trans
      ((Equiv.prodComm _ _).trans finProdFinEquiv))

/-- The table position of a translation group element. -/
theorem orbitEnum_val (g : Multiplicative TranslationGroup) :
    (orbitEnum g).val = g.toAdd.1.val + 15 * (-g.toAdd.2).val := rfl

/-- Count fixed translations by inspecting the45 sentinel positions. -/
noncomputable def fixedCount (m : Nat) : Nat :=
  ((Finset.range 45).filter (fun i => m.testBit (128 * i + 90) = true)).card

/-- The packed fixed-point count is the stabilizer cardinality used in orbit-stabilizer. -/
theorem fixedCount_eq (v : Qubit → ZMod 2) :
    fixedCount (fixedMask (chainMask v)) =
      (OrbitCensus.fixed (G := Multiplicative TranslationGroup) v).card := by
  classical
  unfold fixedCount
  symm
  apply Finset.card_bij (fun g _ => (orbitEnum g).val)
  · intro g hg
    simp only [OrbitCensus.fixed, Finset.mem_filter, Finset.mem_univ, true_and] at hg
    simp only [Finset.mem_filter, Finset.mem_range]
    refine ⟨(orbitEnum g).isLt, ?_⟩
    rw [orbitEnum_val, Nat.add_comm _ (15 * _), fixedMask_bit]
    simpa using hg
  · intro g _ h _ he
    exact orbitEnum.injective (Fin.ext he)
  · intro i hi
    obtain ⟨hir, hib⟩ := Finset.mem_filter.mp hi
    let g := orbitEnum.symm ⟨i, Finset.mem_range.mp hir⟩
    have hg : (orbitEnum g).val = i := by simp [g]
    refine ⟨g, ?_, hg⟩
    simp only [OrbitCensus.fixed, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [← hg, orbitEnum_val, Nat.add_comm _ (15 * _), fixedMask_bit] at hib
    simpa using hib

/-- A checked fixed mask gives the exact orbit size of its chain. -/
theorem orbit_card_from_fixedMask (v : Qubit → ZMod 2) :
    (OrbitCensus.orbit (G := Multiplicative TranslationGroup) v).card =
      45 / fixedCount (fixedMask (chainMask v)) := by
  rw [OrbitCensus.orbit_card_eq_div, fixedCount_eq]
  have hc : Fintype.card (Multiplicative TranslationGroup) = 45 := by
    simpa using Fintype.card_congr orbitEnum
  rw [hc]

end Quantum.Stabilizer.Homological.GBOrbit



#print axioms Quantum.Stabilizer.Homological.GBOrbit.canonicalCheck_chain_sound
#print axioms Quantum.Stabilizer.Homological.GBOrbit.orbit_card_from_fixedMask
