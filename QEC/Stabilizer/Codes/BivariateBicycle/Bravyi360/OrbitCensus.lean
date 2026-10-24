import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.OrbitGlobalProperties
import QEC.Stabilizer.Framework.Homological.Certificate.OrbitIndexedCensus
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.ReachableCensusBound
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.ReachableTranslation
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.Membership
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.TranslationNormalization

noncomputable section

namespace Quantum.Stabilizer.Homological.BB.Bravyi360
open F2Mask
attribute [local instance] reflectedChainOrder

/-- The finite target population counted by the four affine trellises. -/
noncomputable def reachableLightMasks : Finset Nat := by
  classical
  exact (Finset.range (2^90)).filter fun word =>
    XorSpan (ReachabilityData.reachableGenerators.map Prod.snd) word ∧ bitCount 90 word ≤ 22

/-- The corresponding physical bottom-chain population. -/
noncomputable def reachableLightChains : Finset (BaseGroup × Fin 2 → ZMod 2) :=
  reachableLightMasks.image (chainOfMask baseQubitEnum)

/--
Physical-chain membership is exactly reachability together with the light-
weight bound.
-/
theorem mem_reachableLightChains (v : BaseGroup × Fin 2 → ZMod 2) :
    v ∈ reachableLightChains ↔
      XorSpan (ReachabilityData.reachableGenerators.map Prod.snd) (maskOf baseQubitEnum v) ∧
        bitCount 90 (maskOf baseQubitEnum v) ≤ 22 := by
  classical
  constructor
  · intro h
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp h
    obtain ⟨hwfit,hwspan,hwlight⟩ := Finset.mem_filter.mp hw
    rw [maskOf_chainOfMask baseQubitEnum (Finset.mem_range.mp hwfit)]
    exact ⟨hwspan,hwlight⟩
  · intro h
    apply Finset.mem_image.mpr
    refine ⟨maskOf baseQubitEnum v,?_,chainOfMask_maskOf baseQubitEnum v⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (maskOf_lt baseQubitEnum v),h⟩

/--
The independent trellis census bounds the physical reachable target
population.
-/
theorem reachableLightChains_card_le : reachableLightChains.card ≤ 12329961 := by
  classical
  apply (Finset.card_image_le).trans
  apply reachable_light_card_le reachableLightMasks
  · intro w hw
    exact (Finset.mem_filter.mp hw).2.1
  · intro w hw
    exact (Finset.mem_filter.mp hw).2.2

/-- Translating a physical bottom chain preserves the inspected mask weight. -/
theorem base_translate_mask_weight (g : BaseGroup) (v : BaseGroup × Fin 2 → ZMod 2) :
    bitCount 90 (maskOf baseQubitEnum (translate1 g v)) = bitCount 90 (maskOf baseQubitEnum v) := by
  rw [← card_support_eq_bitCount, ← card_support_eq_bitCount]
  exact SmallCycle.card_support_translate1 g v

/-- The target population is invariant under every bottom translation. -/
theorem reachableLightChains_closed (g : Multiplicative BaseGroup)
    (v : BaseGroup × Fin 2 → ZMod 2) (hv : v ∈ reachableLightChains) :
    g • v ∈ reachableLightChains := by
  obtain ⟨hs,hw⟩ := (mem_reachableLightChains v).mp hv
  apply (mem_reachableLightChains _).mpr
  change XorSpan _ (maskOf baseQubitEnum (translate1 g.toAdd v)) ∧
    bitCount 90 (maskOf baseQubitEnum (translate1 g.toAdd v)) ≤ 22
  exact ⟨reachable_chain_translate v hs g.toAdd,by rw [base_translate_mask_weight]; exact hw⟩

/-- Decode a canonical representative to a physical bottom chain. -/
noncomputable def orbitRepresentative (i : Fin 274011) : BaseGroup × Fin 2 → ZMod 2 :=
  chainOfMask baseQubitEnum (OrbitBatchData.repAt i.val)

/-- Decoding a representative preserves its checked mask. -/
theorem mask_orbitRepresentative (i : Fin 274011) :
    maskOf baseQubitEnum (orbitRepresentative i) = OrbitBatchData.repAt i.val :=
  maskOf_chainOfMask baseQubitEnum (OrbitBatchData.repAt_bounded i)

/-- Distinct stored indices represent distinct physical chains. -/
theorem orbitRepresentative_injective : Function.Injective orbitRepresentative := by
  intro a b h
  apply OrbitBatchData.repAt_strictMono.injective
  have hm := congrArg (maskOf baseQubitEnum) h
  simpa only [mask_orbitRepresentative] using hm

/--
Every decoded representative is the minimum of its complete translation orbit.
-/
theorem orbitRepresentative_canonical (i : Fin 274011) :
    OrbitCensus.IsCanonical (G := Multiplicative BaseGroup) (orbitRepresentative i) := by
  apply entries_reflected_isCanonical
  rw [mask_orbitRepresentative]
  exact OrbitBatchData.repAt_canonical i

/--
Every decoded representative lies in the independently counted target
population.
-/
theorem orbitRepresentative_inside (i : Fin 274011) : orbitRepresentative i ∈ reachableLightChains := by
  apply (mem_reachableLightChains _).mpr
  rw [mask_orbitRepresentative]
  exact ⟨Membership.repAt_mem i,OrbitBatchData.repAt_weight i⟩

/--
The disjoint representative orbits reach the independent target-count upper
bound.
-/
theorem orbitRepresentative_card_sum :
    (∑ i : Fin 274011, (OrbitCensus.orbit (G := Multiplicative BaseGroup) (orbitRepresentative i)).card) =
      12329961 := by
  have he : ∀ i : Fin 274011,
      (OrbitCensus.orbit (G := Multiplicative BaseGroup) (orbitRepresentative i)).card =
        45/OrbitBatchData.fixedAt i.val := by
    intro i
    rw [orbit_card_reflected,mask_orbitRepresentative,OrbitBatchData.repAt_fixed]
  simp_rw [he]
  exact OrbitBatchData.orbit_size_sum

/--
Every reachable mask of weight at most 22 translates to a certified canonical
representative.
-/
theorem reachable_light_normalize (v : BaseGroup × Fin 2 → ZMod 2)
    (hspan : XorSpan (ReachabilityData.reachableGenerators.map Prod.snd) (maskOf baseQubitEnum v))
    (hweight : bitCount 90 (maskOf baseQubitEnum v) ≤ 22) :
    ∃ (i : Fin 274011) (g : BaseGroup),
      maskOf baseQubitEnum (translate1 g v) = OrbitBatchData.repAt i.val := by
  obtain ⟨i,g,hg⟩ := OrbitCensus.indexed_normalize (G := Multiplicative BaseGroup)
    orbitRepresentative reachableLightChains orbitRepresentative_injective
    orbitRepresentative_canonical orbitRepresentative_inside reachableLightChains_closed
    (by rw [orbitRepresentative_card_sum]; exact reachableLightChains_card_le)
    ((mem_reachableLightChains v).mpr ⟨hspan,hweight⟩)
  refine ⟨i,g.toAdd,?_⟩
  have hm := congrArg (maskOf baseQubitEnum) hg
  simpa only [mask_orbitRepresentative] using hm

/--
Every light reachable physical chain normalizes to the complete canonical
census.
-/
theorem reachable_light_normalize_weight (v : BaseGroup × Fin 2 → ZMod 2)
    (hspan : XorSpan (ReachabilityData.reachableGenerators.map Prod.snd) (maskOf baseQubitEnum v))
    (hweight : baseComplex.chainWeight v ≤ 22) :
    ∃ (i : Fin 274011) (g : BaseGroup),
      maskOf baseQubitEnum (translate1 g v) = OrbitBatchData.repAt i.val := by
  apply reachable_light_normalize v hspan
  rw [← card_support_eq_bitCount baseQubitEnum]
  exact hweight

/-- The first canonical representative is the zero chain. -/
theorem orbit_repAt_zero : OrbitBatchData.repAt 0 = 0 := by decide +kernel

/--
Every light reachable chain is zero or normalizes to the nonzero certified
census.
-/
theorem reachable_light_normalize_nonzero (v : BaseGroup × Fin 2 → ZMod 2)
    (hspan : XorSpan (ReachabilityData.reachableGenerators.map Prod.snd) (maskOf baseQubitEnum v))
    (hweight : bitCount 90 (maskOf baseQubitEnum v) ≤ 22) :
    v = 0 ∨ ∃ (i : Fin 274010) (g : BaseGroup),
      maskOf baseQubitEnum (translate1 g v) = OrbitBatchData.repAt (i.val+1) := by
  obtain ⟨i,g,hg⟩ := reachable_light_normalize v hspan hweight
  by_cases hi : i.val = 0
  · left
    rw [hi,orbit_repAt_zero] at hg
    have hzero : translate1 g v = 0 := by
      apply maskOf_injective baseQubitEnum
      simpa only [maskOf_zero] using hg
    have hh := congrArg (translate1 (-g)) hzero
    simpa only [translate1_neg_cancel,translate1,Pi.zero_apply] using hh
  · right
    refine ⟨⟨i.val-1,by have := i.isLt; omega⟩,g,?_⟩
    simpa only [show i.val-1+1=i.val by omega] using hg

end Quantum.Stabilizer.Homological.BB.Bravyi360

#print axioms Quantum.Stabilizer.Homological.BB.Bravyi360.reachable_light_normalize_weight
