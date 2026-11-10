import QEC.Stabilizer.Framework.Homological.Covering
import QEC.Stabilizer.Framework.Homological.LogicalCorrespondence

/-!
# X/Z duality of the bivariate bicycle chain complex

For the bivariate bicycle complex `bbChainComplex A B` over a finite abelian
group `G`, with `∂₂ f = (A ⋆ f | B ⋆ f)` and `∂₁ c = B ⋆ c_L + A ⋆ c_R`, the
transposes of the boundary maps are again convolutions, by the reflected
elements `reflect a = a ∘ (-·)`:

* `bb_dualBoundary_eq`: `dualBoundary c = reflect A ⋆ c_L + reflect B ⋆ c_R`;
* `bb_cutMap_eq`: `cutMap s = (reflect B ⋆ s | reflect A ⋆ s)`.

So the dual of the complex of `(A, B)` is the complex of
`(reflect B, reflect A)`, and the map `bbDualFn c = c ∘ blockSwapNeg`, which
negates the group coordinate and swaps the two blocks of qubits, is a
weight-preserving involution exchanging the two:

* `bbDual_mem_dualCycles_iff`: `bbDualFn c` is a dual cycle iff `c` is a cycle;
* `bbDual_mem_dualBoundaries_iff`: `bbDualFn c` is a dual boundary iff `c` is a
  boundary;
* `bbDual_chainWeight`: `bbDualFn` preserves `chainWeight`.

Consequently (`bb_cycle_bound_iff_dual_bound`) a lower bound on the weight of
the cycles that are not boundaries holds iff the same bound holds for the dual
cycles that are not dual boundaries: the X- and Z-distances of a bivariate
bicycle code agree at the level of chains.
-/

namespace Quantum
namespace Stabilizer
namespace Homological
namespace BB

open scoped BigOperators

/-! ## Reflection of chains -/

section Reflect

variable {G : Type} [AddCommGroup G]

/-- Reflection of a chain through the group inverse: `reflect a g = a (-g)`.
This is the antipode of the group algebra `𝔽₂[G]`; convolution by `reflect a`
is the transpose of convolution by `a` (`reflect_conv_apply`). -/
def reflect (a : G → ZMod 2) : G → ZMod 2 := fun g => a (-g)

@[simp] lemma reflect_apply (a : G → ZMod 2) (g : G) :
    reflect a g = a (-g) := rfl

/-- Reflection is an involution. -/
@[simp] lemma reflect_reflect (a : G → ZMod 2) : reflect (reflect a) = a :=
  funext fun g => congrArg a (neg_neg g)

/-- Reflection is injective, being an involution. -/
lemma reflect_injective : Function.Injective (reflect (G := G)) :=
  Function.LeftInverse.injective reflect_reflect

/-- A chain vanishes iff its reflection does. -/
lemma reflect_eq_zero_iff (a : G → ZMod 2) : reflect a = 0 ↔ a = 0 :=
  reflect_injective.eq_iff' rfl

/-- Reflection is multiplicative: `reflect (a ⋆ b) = reflect a ⋆ reflect b`. -/
lemma reflect_conv [Fintype G] (a b : G → ZMod 2) :
    reflect (a ⋆ b) = reflect a ⋆ reflect b := by
  funext g
  simp only [reflect_apply, conv_apply]
  rw [← Equiv.sum_comp (Equiv.neg G) (fun h => a h * b (-g - h))]
  refine Finset.sum_congr rfl fun h _ => ?_
  simp only [Equiv.neg_apply]
  congr 1
  abel_nf

/-- Convolution by `reflect q` is the transpose of convolution by `q`:
`(reflect q ⋆ s) g = ∑ v, s v * q (v - g)`. -/
lemma reflect_conv_apply [Fintype G] (q s : G → ZMod 2) (g : G) :
    (reflect q ⋆ s) g = ∑ v, s v * q (v - g) := by
  rw [conv_comm, conv_apply]
  simp only [reflect_apply, neg_sub]

/-! ## The duality map on 1-chains -/

/-- The duality equivalence on the qubits of a bivariate bicycle code: negate
the group coordinate and swap the two blocks. -/
def blockSwapNeg : (G × Fin 2) ≃ (G × Fin 2) :=
  (Equiv.neg G).prodCongr (Equiv.swap 0 1)

@[simp] lemma blockSwapNeg_apply_zero (g : G) :
    blockSwapNeg (g, (0 : Fin 2)) = (-g, 1) := rfl

@[simp] lemma blockSwapNeg_apply_one (g : G) :
    blockSwapNeg (g, (1 : Fin 2)) = (-g, 0) := rfl

/-- `blockSwapNeg` is an involution. -/
lemma blockSwapNeg_involutive (p : G × Fin 2) :
    blockSwapNeg (blockSwapNeg p) = p :=
  Prod.ext (neg_neg p.1) (Equiv.swap_apply_self 0 1 p.2)

/-- The duality map on 1-chains: `bbDualFn c = c ∘ blockSwapNeg`. -/
def bbDualFn (c : G × Fin 2 → ZMod 2) : G × Fin 2 → ZMod 2 :=
  c ∘ blockSwapNeg

/-- The duality map is an involution. -/
@[simp] lemma bbDualFn_bbDualFn (c : G × Fin 2 → ZMod 2) :
    bbDualFn (bbDualFn c) = c :=
  funext fun p => congrArg c (blockSwapNeg_involutive p)

/-- The duality map is injective, being an involution. -/
lemma bbDualFn_injective :
    Function.Injective (bbDualFn (G := G)) :=
  Function.LeftInverse.injective bbDualFn_bbDualFn

/-- The left half of `bbDualFn c` is the reflected right half of `c`. -/
lemma leftHalf_bbDualFn (c : G × Fin 2 → ZMod 2) :
    leftHalf (bbDualFn c) = reflect (rightHalf c) := rfl

/-- The right half of `bbDualFn c` is the reflected left half of `c`. -/
lemma rightHalf_bbDualFn (c : G × Fin 2 → ZMod 2) :
    rightHalf (bbDualFn c) = reflect (leftHalf c) := rfl

end Reflect

/-! ## The transposes of the boundary maps -/

variable {G : Type} [Fintype G] [AddCommGroup G] [DecidableEq G]
variable (A B : G → ZMod 2)

/-- `∂₂` of a point mass: `∂₂ δ_f` is `A (h - f)` at `(h, 0)` and `B (h - f)`
at `(h, 1)`. -/
lemma bbBoundary2Fn_single (f : G) (h : G) (j : Fin 2) :
    bbBoundary2Fn A B (Pi.single f 1) (h, j)
      = if j = 0 then A (h - f) else B (h - f) := by
  simp only [bbBoundary2Fn, conv_single_right_apply]

/-- The transpose of `∂₂` for the bivariate bicycle complex:
`dualBoundary c = reflect A ⋆ c_L + reflect B ⋆ c_R`. -/
theorem bb_dualBoundary_eq (c : G × Fin 2 → ZMod 2) :
    (bbChainComplex A B).dualBoundary c
      = fun f => (reflect A ⋆ leftHalf c) f
          + (reflect B ⋆ rightHalf c) f := by
  funext f
  change ∑ p : G × Fin 2, c p * bbBoundary2Fn A B (Pi.single f 1) p = _
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two, bbBoundary2Fn_single,
    reflect_conv_apply, Finset.sum_add_distrib]
  rfl

/-- `∂₁` of a point mass in the left block: `(∂₁ δ_(g,0)) v = B (v - g)`. -/
lemma bbBoundary1Fn_single_left (g v : G) :
    bbBoundary1Fn A B (Pi.single ((g, 0) : G × Fin 2) 1) v = B (v - g) := by
  have hL : leftHalf (Pi.single ((g, 0) : G × Fin 2) (1 : ZMod 2)) = Pi.single g 1 := by
    funext h
    simp [leftHalf, Pi.single_apply]
  have hR : rightHalf (Pi.single ((g, 0) : G × Fin 2) (1 : ZMod 2)) = 0 := by
    funext h
    simp [rightHalf]
  rw [bbBoundary1Fn_eq, hL, hR, conv_zero_right, add_zero, conv_single_right_apply]

/-- `∂₁` of a point mass in the right block: `(∂₁ δ_(g,1)) v = A (v - g)`. -/
lemma bbBoundary1Fn_single_right (g v : G) :
    bbBoundary1Fn A B (Pi.single ((g, 1) : G × Fin 2) 1) v = A (v - g) := by
  have hL : leftHalf (Pi.single ((g, 1) : G × Fin 2) (1 : ZMod 2)) = 0 := by
    funext h
    simp [leftHalf]
  have hR : rightHalf (Pi.single ((g, 1) : G × Fin 2) (1 : ZMod 2)) = Pi.single g 1 := by
    funext h
    simp [rightHalf, Pi.single_apply]
  rw [bbBoundary1Fn_eq, hL, hR, conv_zero_right, zero_add, conv_single_right_apply]

/-- The transpose of `∂₁` for the bivariate bicycle complex:
`cutMap s = (reflect B ⋆ s | reflect A ⋆ s)`. -/
theorem bb_cutMap_eq (s : G → ZMod 2) :
    (bbChainComplex A B).cutMap s
      = fun p : G × Fin 2 =>
          if p.2 = 0 then (reflect B ⋆ s) p.1 else (reflect A ⋆ s) p.1 := by
  funext ⟨g, j⟩
  change ∑ v : G, s v * bbBoundary1Fn A B (Pi.single (g, j) 1) v = _
  obtain rfl | rfl : j = 0 ∨ j = 1 := by omega
  · simp only [bbBoundary1Fn_single_left, reflect_conv_apply]
    rfl
  · simp only [bbBoundary1Fn_single_right, reflect_conv_apply]
    rfl

/-! ## The duality map exchanges the complex with its dual -/

/-- The dual boundary of `bbDualFn c` is the reflected boundary of `c`. -/
theorem dualBoundary_bbDualFn (c : G × Fin 2 → ZMod 2) :
    (bbChainComplex A B).dualBoundary (bbDualFn c)
      = reflect (bbBoundary1Fn A B c) := by
  rw [bb_dualBoundary_eq, leftHalf_bbDualFn, rightHalf_bbDualFn, ← reflect_conv,
    ← reflect_conv]
  exact funext fun f => add_comm _ _

/-- `bbDualFn` carries `∂₂ f` to the cut of the reflected chain. -/
theorem bbDualFn_bbBoundary2Fn (f2 : G → ZMod 2) :
    bbDualFn (bbBoundary2Fn A B f2)
      = (bbChainComplex A B).cutMap (reflect (G := G) f2) := by
  rw [bb_cutMap_eq, halves_ext_iff, leftHalf_bbDualFn, rightHalf_bbDualFn,
    leftHalf_bbBoundary2Fn, rightHalf_bbBoundary2Fn, reflect_conv, reflect_conv]
  exact ⟨rfl, rfl⟩

/-- `bbDualFn c` is a dual cycle iff `c` is a cycle. -/
theorem bbDual_mem_dualCycles_iff (c : G × Fin 2 → ZMod 2) :
    bbDualFn c ∈ (bbChainComplex A B).dualCycles
      ↔ c ∈ (bbChainComplex A B).cycles := by
  change (bbChainComplex A B).dualBoundary (bbDualFn c) = 0 ↔ bbBoundary1Fn A B c = 0
  rw [dualBoundary_bbDualFn]
  exact reflect_eq_zero_iff _

/-- `bbDualFn c` is a dual boundary iff `c` is a boundary. -/
theorem bbDual_mem_dualBoundaries_iff (c : G × Fin 2 → ZMod 2) :
    bbDualFn c ∈ (bbChainComplex A B).dualBoundaries
      ↔ c ∈ (bbChainComplex A B).boundaries := by
  constructor
  · rintro ⟨s, hs⟩
    exact ⟨reflect (G := G) s, bbDualFn_injective <|
      (bbDualFn_bbBoundary2Fn A B (reflect (G := G) s)).trans (by rw [reflect_reflect]; exact hs)⟩
  · rintro ⟨f2, rfl⟩
    exact ⟨reflect (G := G) f2, (bbDualFn_bbBoundary2Fn A B f2).symm⟩

/-! ## The duality map preserves weight -/

/-- Composing a predicate with an equivalence does not change how many points
satisfy it. -/
lemma card_filter_comp_equiv {α β : Type} [Fintype α] [Fintype β]
    (e : α ≃ β) (p : β → Prop) [DecidablePred p] :
    (Finset.univ.filter fun a => p (e a)).card
      = (Finset.univ.filter p).card :=
  Finset.card_equiv e (by simp)

/-- `bbDualFn` preserves chain weight. -/
theorem bbDual_chainWeight (c : G × Fin 2 → ZMod 2) :
    (bbChainComplex A B).chainWeight (bbDualFn c)
      = (bbChainComplex A B).chainWeight c :=
  card_filter_comp_equiv blockSwapNeg (fun p => c p ≠ 0)

/-! ## Equality of the chain-level X- and Z-distances -/

/-- A lower bound on the weight of the cycles that are not boundaries holds iff
the same bound holds on the dual cycles that are not dual boundaries, since
`bbDualFn` is a weight-preserving bijection between the two. -/
theorem bb_cycle_bound_iff_dual_bound (K : ℕ) :
    (∀ c ∈ (bbChainComplex A B).cycles,
        c ∉ (bbChainComplex A B).boundaries →
        K ≤ (bbChainComplex A B).chainWeight c)
      ↔ (∀ c ∈ (bbChainComplex A B).dualCycles,
        c ∉ (bbChainComplex A B).dualBoundaries →
        K ≤ (bbChainComplex A B).chainWeight c) := by
  constructor
  · intro hX c hc hnb
    rw [← bbDual_chainWeight]
    refine hX (bbDualFn c) ((bbDual_mem_dualCycles_iff A B _).mp (by rwa [bbDualFn_bbDualFn]))
      fun h => hnb ?_
    simpa using (bbDual_mem_dualBoundaries_iff A B _).mpr h
  · intro hZ c hc hnb
    rw [← bbDual_chainWeight]
    exact hZ (bbDualFn c) ((bbDual_mem_dualCycles_iff A B c).mpr hc)
      fun h => hnb ((bbDual_mem_dualBoundaries_iff A B c).mp h)

end BB
end Homological
end Stabilizer
end Quantum
