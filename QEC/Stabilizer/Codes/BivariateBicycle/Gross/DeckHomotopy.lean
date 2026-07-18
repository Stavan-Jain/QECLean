/-
# The deck homotopy (R) for the gross code

The headline (`deck_add_mem_boundaries`): for every 1-cycle `v` of the gross
complex, `v + σv` is a boundary — i.e. the deck translation `σ` acts trivially
on homology.  The explicit homotopy chain is

  `z := (1 + x²) ⋆ B ⋆ v_R`

and the computation `∂₂ z = v + σv` rests on two machine-certified polynomial
identities, `B⋆B = 1 + x² + x⁴` and `(1 + x²)(1 + x² + x⁴) = 1 + x⁶`, plus the
cycle condition.

## Convention bridge (lab notes → repo)

Repo convention: `∂₂ f = (A⋆f | B⋆f)`, `∂₁ c = B⋆c_L + A⋆c_R`; cycle
condition `B⋆v_L = A⋆v_R`.  **Repo-left = lab-right** — hence the homotopy
chain is built from `rightHalf v`, and

  `A⋆z = (1+x²)⋆B⋆(A⋆v_R) = (1+x²)⋆B⋆(B⋆v_L) = (1+x⁶)⋆v_L`,
  `B⋆z = (1+x²)⋆(B⋆B)⋆v_R = (1+x⁶)⋆v_R`,

so `∂₂ z = (1+x⁶)⋆v = v + σv` blockwise.
-/

import QEC.Stabilizer.Codes.BivariateBicycle.Gross.CoverTransfer

namespace Quantum
namespace Stabilizer
namespace Homological
namespace BB

/-! ## Machine-certified polynomial identities -/

theorem gross_conv_B_B : conv grossB grossB = bSquaredPoly := by
  native_decide

theorem gross_conv_onePlusX2_Bsq :
    conv onePlusX2 bSquaredPoly = onePlusX6 := by
  native_decide

/-! ## `1 + x⁶` acts as `1 + deck shift` -/

theorem onePlusX6_eq :
    onePlusX6 = Pi.single (0 : GrossGroup) 1 + Pi.single deckS 1 := by
  native_decide

theorem conv_onePlusX6 (v : GrossGroup → ZMod 2) :
    conv onePlusX6 v = v + deckShift0 v := by
  rw [onePlusX6_eq, conv_add_left, conv_single_left, conv_single_left]
  funext g
  simp only [Pi.add_apply, sub_zero, deckShift0_apply]
  rw [sub_eq_add_neg, neg_deckS]

/-! ## The homotopy chain -/

/-- The homotopy chain `z := (1 + x²) ⋆ B ⋆ v_R`. -/
def homotopyChain (v : GrossGroup × Fin 2 → ZMod 2) : GrossGroup → ZMod 2 :=
  conv onePlusX2 (conv grossB (rightHalf v))

/-- Cycle condition in convolution form: `A⋆v_R = B⋆v_L`. -/
lemma cycle_conv_eq {v : GrossGroup × Fin 2 → ZMod 2}
    (hv : v ∈ grossComplex.cycles) :
    conv grossA (rightHalf v) = conv grossB (leftHalf v) := by
  have h0 : bbBoundary1Fn grossA grossB v = 0 :=
    (HomologicalCode.mem_cycles_iff grossComplex v).mp hv
  funext g
  have hg : conv grossB (leftHalf v) g + conv grossA (rightHalf v) g = 0 :=
    congrFun h0 g
  have := (CharTwo.add_eq_zero (a := conv grossB (leftHalf v) g)
    (b := conv grossA (rightHalf v) g)).mp hg
  exact this.symm

/-- `A ⋆ z = v_L + σ v_L`. -/
lemma conv_grossA_homotopyChain {v : GrossGroup × Fin 2 → ZMod 2}
    (hv : v ∈ grossComplex.cycles) :
    conv grossA (homotopyChain v) = leftHalf v + deckShift0 (leftHalf v) := by
  unfold homotopyChain
  calc conv grossA (conv onePlusX2 (conv grossB (rightHalf v)))
      = conv (conv grossA onePlusX2) (conv grossB (rightHalf v)) :=
        (conv_assoc _ _ _).symm
    _ = conv (conv onePlusX2 grossA) (conv grossB (rightHalf v)) := by
        rw [conv_comm grossA]
    _ = conv onePlusX2 (conv grossA (conv grossB (rightHalf v))) :=
        conv_assoc _ _ _
    _ = conv onePlusX2 (conv (conv grossA grossB) (rightHalf v)) := by
        rw [conv_assoc]
    _ = conv onePlusX2 (conv (conv grossB grossA) (rightHalf v)) := by
        rw [conv_comm grossA grossB]
    _ = conv onePlusX2 (conv grossB (conv grossA (rightHalf v))) := by
        rw [conv_assoc]
    _ = conv onePlusX2 (conv grossB (conv grossB (leftHalf v))) := by
        rw [cycle_conv_eq hv]
    _ = conv onePlusX2 (conv (conv grossB grossB) (leftHalf v)) := by
        rw [conv_assoc]
    _ = conv onePlusX2 (conv bSquaredPoly (leftHalf v)) := by
        rw [gross_conv_B_B]
    _ = conv (conv onePlusX2 bSquaredPoly) (leftHalf v) :=
        (conv_assoc _ _ _).symm
    _ = conv onePlusX6 (leftHalf v) := by
        rw [gross_conv_onePlusX2_Bsq]
    _ = leftHalf v + deckShift0 (leftHalf v) := conv_onePlusX6 _

/-- `B ⋆ z = v_R + σ v_R`. -/
lemma conv_grossB_homotopyChain (v : GrossGroup × Fin 2 → ZMod 2) :
    conv grossB (homotopyChain v) = rightHalf v + deckShift0 (rightHalf v) := by
  unfold homotopyChain
  calc conv grossB (conv onePlusX2 (conv grossB (rightHalf v)))
      = conv (conv grossB onePlusX2) (conv grossB (rightHalf v)) :=
        (conv_assoc _ _ _).symm
    _ = conv (conv onePlusX2 grossB) (conv grossB (rightHalf v)) := by
        rw [conv_comm grossB]
    _ = conv onePlusX2 (conv grossB (conv grossB (rightHalf v))) :=
        conv_assoc _ _ _
    _ = conv onePlusX2 (conv (conv grossB grossB) (rightHalf v)) := by
        rw [conv_assoc]
    _ = conv onePlusX2 (conv bSquaredPoly (rightHalf v)) := by
        rw [gross_conv_B_B]
    _ = conv (conv onePlusX2 bSquaredPoly) (rightHalf v) :=
        (conv_assoc _ _ _).symm
    _ = conv onePlusX6 (rightHalf v) := by
        rw [gross_conv_onePlusX2_Bsq]
    _ = rightHalf v + deckShift0 (rightHalf v) := conv_onePlusX6 _

/-- `∂₂ z = v + σv` for any cycle `v`. -/
theorem bbBoundary2Fn_homotopyChain {v : GrossGroup × Fin 2 → ZMod 2}
    (hv : v ∈ grossComplex.cycles) :
    bbBoundary2Fn grossA grossB (homotopyChain v) = v + deckShift1 v := by
  funext p
  obtain ⟨h, j⟩ := p
  fin_cases j
  · change conv grossA (homotopyChain v) h = (v + deckShift1 v) (h, 0)
    rw [conv_grossA_homotopyChain hv]
    rfl
  · change conv grossB (homotopyChain v) h = (v + deckShift1 v) (h, 1)
    rw [conv_grossB_homotopyChain v]
    rfl

/-- **The deck homotopy (R)**: for every gross 1-cycle `v`, the deck
translate differs from `v` by a boundary; i.e. `σ` acts trivially on `H₁`. -/
theorem deck_add_mem_boundaries {v : GrossGroup × Fin 2 → ZMod 2}
    (hv : v ∈ grossComplex.cycles) :
    v + deckShift1 v ∈ grossComplex.boundaries := by
  refine ⟨homotopyChain v, ?_⟩
  change bbBoundary2Fn grossA grossB (homotopyChain v) = v + deckShift1 v
  exact bbBoundary2Fn_homotopyChain hv

end BB
end Homological
end Stabilizer
end Quantum
