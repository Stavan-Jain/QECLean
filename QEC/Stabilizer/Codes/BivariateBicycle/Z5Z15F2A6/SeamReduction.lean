/-
# A23 seam floor, layer 3: `SeamCosetFloor 16` from the core inequality

The quantifier collapse of the seam-coset floor (A23 §6):

1. a base 2-cycle `ζ` lies in `ker(A⋆) = ker ∂₂`, so `kerA_classify`
   pins it to one of the 16 span elements `kerElt e₁ e₂ e₃ e₄`;
2. the **dictionary** (`seam_dict`, one finite check): for every nonzero
   kernel pattern, `seamC (kerElt e) = (translate ge e₀ | 0) + ∂₂ fe`
   with tabulated `ge`, `fe` — so every seam-coset element is
   `(translate ge e₀ + A⋆g | B⋆g)`;
3. for the zero pattern the coset is the boundary space itself,
   contradicting non-boundaryness;
4. the `G`-orbit collapse: translating by `-ge` moves the offset to `e₀`
   itself and preserves weights, landing in the **core inequality**
   `core_ineq : 16 ≤ |e₀ + A⋆g| + |B⋆g|` (`SeamSweep.lean`).

Result: `seamCosetFloor_16 : coverData.SeamCosetFloor 16` — the S4
CryptoMiniSat XOR-native `UNSAT@14` certificate behind the `[[300,8,16]]`
distance theorem is replaced by kernel/`native_decide`-checked analytic
certificates.
-/

import QEC.Stabilizer.Codes.BivariateBicycle.Z5Z15F2A6.SeamSweep
import QEC.Stabilizer.Codes.BivariateBicycle.Z5Z15F2A6.BaseFloorKernel

namespace Quantum
namespace Stabilizer
namespace Homological
namespace BB
namespace Z5Z15F2A6

open scoped BigOperators

set_option maxRecDepth 4096

/-! ## The seam dictionary -/

/-- Dictionary shift of a kernel pattern (`t = e₁ + 2e₂ + 4e₃ + 8e₄`). -/
def dictGe (t : ℕ) : G150 :=
  (((dictGx.getD t 0 : ℕ) : ZMod 5), ((dictGy.getD t 0 : ℕ) : ZMod 15))

/-- Dictionary 2-chain of a kernel pattern. -/
def dictF (t : ℕ) : G150 → ZMod 2 := maskFun (dictFe.getD t 0)

/-- **The seam dictionary**: for every nonzero kernel pattern `e`, the
seam-crossing chain of `kerElt e` is the graph-form chain
`(translate ge e₀ + A⋆fe | B⋆fe)` with tabulated `ge`, `fe`. -/
lemma seam_dict : ∀ e1 e2 e3 e4 : ZMod 2,
    ¬(e1 = 0 ∧ e2 = 0 ∧ e3 = 0 ∧ e4 = 0) →
    ∀ p : G150 × Fin 2,
      coverData.seamC (kerElt e1 e2 e3 e4) p
        = if p.2 = 0 then
            e0f (p.1 + dictGe (e1.val + 2 * e2.val + 4 * e3.val + 8 * e4.val))
              + conv a150
                  (dictF (e1.val + 2 * e2.val + 4 * e3.val + 8 * e4.val)) p.1
          else
            conv b150
              (dictF (e1.val + 2 * e2.val + 4 * e3.val + 8 * e4.val)) p.1 := by
  native_decide

/-! ## The per-class floor from a dictionary entry -/

/-- Any seam-coset chain of a class with a dictionary entry has weight
at least 16: translate the offset to `e₀` and apply the core
inequality. -/
lemma floor_of_dict (ζ : G150 → ZMod 2) (ge : G150) (fe : G150 → ZMod 2)
    (hdict : ∀ p : G150 × Fin 2,
      coverData.seamC ζ p
        = if p.2 = 0 then e0f (p.1 + ge) + conv a150 fe p.1
          else conv b150 fe p.1)
    (f : G150 → ZMod 2) :
    16 ≤ coverData.baseComplex.chainWeight
      (coverData.seamC ζ + bbBoundary2Fn a150 b150 f) := by
  -- the coset chain in two-block graph form
  have hchain : (coverData.seamC ζ + bbBoundary2Fn a150 b150 f)
      = fun p : G150 × Fin 2 =>
          if p.2 = 0 then translate ge e0f p.1 + conv a150 (fe + f) p.1
          else conv b150 (fe + f) p.1 := by
    funext p
    obtain ⟨h, j⟩ := p
    rw [Pi.add_apply, hdict (h, j)]
    by_cases hj : j = 0
    · subst hj
      show (if (0 : Fin 2) = 0 then e0f (h + ge) + conv a150 fe h
          else conv b150 fe h) + bbBoundary2Fn a150 b150 f (h, 0)
        = if (0 : Fin 2) = 0 then translate ge e0f h + conv a150 (fe + f) h
          else conv b150 (fe + f) h
      rw [if_pos rfl, if_pos rfl,
        show bbBoundary2Fn a150 b150 f (h, 0) = conv a150 f h from rfl,
        conv_add_right]
      show e0f (h + ge) + conv a150 fe h + conv a150 f h
        = e0f (h + ge) + (conv a150 fe h + conv a150 f h)
      ring
    · have hj1 : j = 1 := by omega
      subst hj1
      show (if (1 : Fin 2) = 0 then e0f (h + ge) + conv a150 fe h
          else conv b150 fe h) + bbBoundary2Fn a150 b150 f (h, 1)
        = if (1 : Fin 2) = 0 then translate ge e0f h + conv a150 (fe + f) h
          else conv b150 (fe + f) h
      rw [if_neg (by decide), if_neg (by decide),
        show bbBoundary2Fn a150 b150 f (h, 1) = conv b150 f h from rfl,
        conv_add_right]
      rfl
  -- weight split by blocks
  have hcards : (Finset.univ.filter fun p : G150 × Fin 2 =>
        (coverData.seamC ζ + bbBoundary2Fn a150 b150 f) p ≠ 0).card
      = wt150 (fun h => translate ge e0f h + conv a150 (fe + f) h)
        + wt150 (conv b150 (fe + f)) := by
    rw [show (coverData.seamC ζ + bbBoundary2Fn a150 b150 f)
        = fun p : G150 × Fin 2 =>
            if p.2 = 0 then translate ge e0f p.1 + conv a150 (fe + f) p.1
            else conv b150 (fe + f) p.1 from hchain]
    exact card_two_blocks
      (fun h => translate ge e0f h + conv a150 (fe + f) h)
      (conv b150 (fe + f))
  -- translation collapse of the offset to `e₀`
  have ha : conv a150 (fe + f)
      = translate ge (conv a150 (translate (-ge) (fe + f))) := by
    rw [conv_translate, translate_comp, add_neg_cancel, translate_zero']
  have hb : conv b150 (fe + f)
      = translate ge (conv b150 (translate (-ge) (fe + f))) := by
    rw [conv_translate, translate_comp, add_neg_cancel, translate_zero']
  have hLB : (fun h => translate ge e0f h + conv a150 (fe + f) h)
      = translate ge (e0f + conv a150 (translate (-ge) (fe + f))) := by
    rw [ha]
    rfl
  rw [coverData.baseComplex_chainWeight_eq, hcards, hLB, hb,
    wt150_translate, wt150_translate]
  exact core_ineq (translate (-ge) (fe + f))

/-! ## The target Prop -/

/-- The all-zero kernel pattern is the zero chain. -/
lemma kerElt_zero_pattern : kerElt 0 0 0 0 = 0 := by
  funext g
  show (0 : ZMod 2) * zf1 g + 0 * zf2 g + 0 * zf3 g + 0 * zf4 g = 0
  ring

/-- **The seam-coset floor at 16** — the (M-im) input of the
`[[150,8,8]] → [[300,8,16]]` doubling instance, proved analytically:
kernel classification + the seam dictionary + the `G`-orbit collapse +
the core two-trinomial inequality. -/
theorem seamCosetFloor_16 : coverData.SeamCosetFloor 16 := by
  intro ζ hζ f hnb
  -- `ζ` is annihilated by `conv a150`
  have hkerA : conv a150 ζ = 0 := by
    funext h
    exact congrFun hζ (h, 0)
  have hζcls := kerA_classify ζ hkerA
  by_cases hzero : ζ fc1 = 0 ∧ ζ fc2 = 0 ∧ ζ fc3 = 0 ∧ ζ fc4 = 0
  · -- zero class: the coset is the boundary space — contradiction
    exfalso
    apply hnb
    obtain ⟨z1, z2, z3, z4⟩ := hzero
    rw [z1, z2, z3, z4, kerElt_zero_pattern] at hζcls
    rw [hζcls, coverData.seamC_zero, zero_add]
    exact ⟨show G150 → ZMod 2 from f, rfl⟩
  · -- nonzero class: apply the dictionary
    have hdict := seam_dict (ζ fc1) (ζ fc2) (ζ fc3) (ζ fc4) hzero
    rw [← hζcls] at hdict
    exact floor_of_dict ζ _ _ hdict f

end Z5Z15F2A6
end BB
end Homological
end Stabilizer
end Quantum
