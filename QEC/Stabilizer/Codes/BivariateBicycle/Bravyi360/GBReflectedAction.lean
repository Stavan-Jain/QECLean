import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.GBOrbitAction
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.Defs

noncomputable section

namespace Quantum.Stabilizer.Homological.BB.Bravyi360
open GBOrbit F2Mask

/-- Compare physical bottom chains by their reflected certificate masks. -/
@[reducible] noncomputable def reflectedChainOrder : LinearOrder (BaseGroup × Fin 2 → ZMod 2) :=
  LinearOrder.lift' (maskOf baseQubitEnum) (maskOf_injective baseQubitEnum)

attribute [local instance] reflectedChainOrder

/-- Reflect the group coordinate to convert certificate masks to the earlier orbit convention. -/
noncomputable def reflectBaseChain (v : BaseGroup × Fin 2 → ZMod 2) : BaseGroup × Fin 2 → ZMod 2 :=
  fun q => v (-q.1,q.2)

/-- Reflection of group coordinates is involutive. -/
theorem reflectBaseChain_involutive (v : BaseGroup × Fin 2 → ZMod 2) :
    reflectBaseChain (reflectBaseChain v) = v := by
  ext q
  simp [reflectBaseChain]

/-- The reflected enumeration is the ordinary enumeration after coordinate reflection. -/
theorem baseQubitEnum_reflection (q : BaseGroup × Fin 2) :
    baseQubitEnum q = GBOrbit.qubitEnum (-q.1,q.2) := rfl

/-- Reflected certificate masks are ordinary masks of reflected chains. -/
theorem reflected_mask_eq (v : BaseGroup × Fin 2 → ZMod 2) :
    maskOf baseQubitEnum v = GBOrbit.chainMask (reflectBaseChain v) := by
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < 90
  · let q := baseQubitEnum.symm ⟨j,hj⟩
    have hq : (baseQubitEnum q).val = j := by simp [q]
    rw [← hq, testBit_maskOf_apply, baseQubitEnum_reflection]
    change decide (v q ≠ 0) = (maskOf GBOrbit.qubitEnum (reflectBaseChain v)).testBit _
    rw [testBit_maskOf_apply]
    simp [reflectBaseChain]
  · have hpow : 2^90 ≤ 2^j := Nat.pow_le_pow_right (by decide) (by omega)
    change (maskOf baseQubitEnum v).testBit j = (maskOf GBOrbit.qubitEnum (reflectBaseChain v)).testBit j
    rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (maskOf_lt baseQubitEnum v) hpow),
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le
        (maskOf_lt GBOrbit.qubitEnum (reflectBaseChain v)) hpow)]

/-- Reflection conjugates a translation to its inverse. -/
theorem reflectBaseChain_translate (g : BaseGroup) (v : BaseGroup × Fin 2 → ZMod 2) :
    reflectBaseChain (translate1 g v) = translate1 (-g) (reflectBaseChain v) := by
  ext q
  simp only [reflectBaseChain, translate1, neg_add_rev, neg_neg]
  congr 2
  abel

/-- Each orbit entry has the stated translation meaning in reflected certificate coordinates. -/
theorem entry_reflected_mask (v : BaseGroup × Fin 2 → ZMod 2) (x : ZMod 15) (y : ZMod 3) :
    GBOrbit.entry (maskOf baseQubitEnum v % 2^45) (maskOf baseQubitEnum v / 2^45)
      (15*y.val+x.val) = maskOf baseQubitEnum (translate1 (-x,y) v) := by
  rw [reflected_mask_eq, GBOrbit.entry_chainMask, reflected_mask_eq, reflectBaseChain_translate]
  simp only [Prod.neg_mk, neg_neg]

/-- Passing the numerical canonicality check minimizes the reflected mask over all translations. -/
theorem canonicalCheck_reflected_sound (v : BaseGroup × Fin 2 → ZMod 2)
    (h : GBOrbit.canonicalCheck (maskOf baseQubitEnum v) = true) :
    ∀ g : BaseGroup, maskOf baseQubitEnum v ≤ maskOf baseQubitEnum (translate1 g v) := by
  intro g
  have hb := GBOrbit.canonicalCheck_sound (maskOf_lt baseQubitEnum v) h
    (15*g.2.val+(-g.1).val) (by have := ZMod.val_lt g.2; have := ZMod.val_lt (-g.1); omega)
  rw [entry_reflected_mask] at hb
  simpa using hb

/-- Passing the canonicality check gives canonicality in the reflected mask order. -/
theorem canonicalCheck_reflected_isCanonical (v : BaseGroup × Fin 2 → ZMod 2)
    (h : GBOrbit.canonicalCheck (maskOf baseQubitEnum v) = true) :
    OrbitCensus.IsCanonical (G := Multiplicative BaseGroup) v := by
  intro g
  exact canonicalCheck_reflected_sound v h g.toAdd

/-- Entrywise numerical comparisons suffice for canonicality in reflected mask order. -/
theorem entries_reflected_isCanonical (v : BaseGroup × Fin 2 → ZMod 2)
    (h : ∀ i < 45, maskOf baseQubitEnum v ≤
      GBOrbit.entry (maskOf baseQubitEnum v % 2^45) (maskOf baseQubitEnum v / 2^45) i) :
    OrbitCensus.IsCanonical (G := Multiplicative BaseGroup) v := by
  intro g
  have hb := h (15*g.toAdd.2.val+(-g.toAdd.1).val)
    (by have := ZMod.val_lt g.toAdd.2; have := ZMod.val_lt (-g.toAdd.1); omega)
  rw [entry_reflected_mask] at hb
  simpa using hb

/-- Reflection is an injective reindexing of chains. -/
theorem reflectBaseChain_injective : Function.Injective reflectBaseChain := by
  intro a b h
  have h' := congrArg reflectBaseChain h
  simpa only [reflectBaseChain_involutive] using h'

/-- A fixed-mask bit detects the corresponding physical translation in reflected coordinates. -/
theorem fixedMask_reflected_bit (v : BaseGroup × Fin 2 → ZMod 2)
    (x : ZMod 15) (y : ZMod 3) :
    (GBOrbit.fixedMask (maskOf baseQubitEnum v)).testBit (128*(15*y.val+x.val)+90) =
      decide (translate1 (-x,y) v = v) := by
  rw [reflected_mask_eq, GBOrbit.fixedMask_bit]
  have he : translate1 (x,-y) (reflectBaseChain v) = reflectBaseChain v ↔
      translate1 (-x,y) v = v := by
    rw [← reflectBaseChain_injective.eq_iff]
    rw [reflectBaseChain_translate]
    simp only [Prod.neg_mk, neg_neg, reflectBaseChain_involutive]
  simp only [he]

/-- Enumeration of physical translations in the order of reflected orbit entries. -/
noncomputable def reflectedOrbitEnum : Multiplicative BaseGroup ≃ Fin 45 :=
  Multiplicative.toAdd.trans
    ((Equiv.prodCongr (Equiv.neg (ZMod 15)) (Equiv.refl (ZMod 3))).trans
      ((Equiv.prodComm _ _).trans finProdFinEquiv))

/-- The position of a physical translation in the reflected orbit table. -/
theorem reflectedOrbitEnum_val (g : Multiplicative BaseGroup) :
    (reflectedOrbitEnum g).val = (-g.toAdd.1).val + 15*g.toAdd.2.val := rfl

/-- Fixed-mask cardinality is the number of physical translations fixing the chain. -/
theorem fixedCount_reflected_eq (v : BaseGroup × Fin 2 → ZMod 2) :
    GBOrbit.fixedCount (GBOrbit.fixedMask (maskOf baseQubitEnum v)) =
      (OrbitCensus.fixed (G := Multiplicative BaseGroup) v).card := by
  classical
  unfold GBOrbit.fixedCount
  symm
  apply Finset.card_bij (fun g _ => (reflectedOrbitEnum g).val)
  · intro g hg
    simp only [OrbitCensus.fixed, Finset.mem_filter, Finset.mem_univ, true_and] at hg
    simp only [Finset.mem_filter, Finset.mem_range]
    refine ⟨(reflectedOrbitEnum g).isLt, ?_⟩
    rw [reflectedOrbitEnum_val, Nat.add_comm _ (15*_ ), fixedMask_reflected_bit]
    simpa using hg
  · intro g _ h _ he
    exact reflectedOrbitEnum.injective (Fin.ext he)
  · intro i hi
    obtain ⟨hir,hib⟩ := Finset.mem_filter.mp hi
    let g := reflectedOrbitEnum.symm ⟨i,Finset.mem_range.mp hir⟩
    have hg : (reflectedOrbitEnum g).val = i := by simp [g]
    refine ⟨g, ?_, hg⟩
    simp only [OrbitCensus.fixed, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [← hg, reflectedOrbitEnum_val, Nat.add_comm _ (15*_ ), fixedMask_reflected_bit] at hib
    simpa using hib

/-- The packed fixed count determines the orbit size in reflected certificate coordinates. -/
theorem orbit_card_reflected (v : BaseGroup × Fin 2 → ZMod 2) :
    (OrbitCensus.orbit (G := Multiplicative BaseGroup) v).card =
      45 / GBOrbit.fixedCount (GBOrbit.fixedMask (maskOf baseQubitEnum v)) := by
  rw [OrbitCensus.orbit_card_eq_div, fixedCount_reflected_eq]
  have hc : Fintype.card (Multiplicative BaseGroup) = 45 := by
    simpa using Fintype.card_congr reflectedOrbitEnum
  rw [hc]

end Quantum.Stabilizer.Homological.BB.Bravyi360

#print axioms Quantum.Stabilizer.Homological.BB.Bravyi360.canonicalCheck_reflected_isCanonical
#print axioms Quantum.Stabilizer.Homological.BB.Bravyi360.orbit_card_reflected
