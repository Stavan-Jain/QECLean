/-
# Tabulated seam-crossing terms for the three Smith classes

`coverData.seamC (kcombo c₀ c₁)` is a closed constant with 72 values, but
inside a `2¹⁸` sweep the compiler re-derives it at every (mask, cell)
pair — `sheet1 ∘ liftStab ∘ liftC2` with a 36-term cover convolution and
`AddMonoidHom` coercion towers per application, ~10¹¹ operations spent
recomputing a 72-entry table.  This file tabulates the three class seams
as literal chains and certifies each table with one (sub-second) kernel
identity; the `SweepSafe*.lean` leaves sweep against the literals.

Tables emitted by `qec-lab:experiments/bb_lab/scripts/gen_pair72_z6z6_data.py`
(§5b); each has weight 12.
-/

import QEC.Stabilizer.Codes.BivariateBicycle.Z3Z6.MaskDefs

namespace Quantum
namespace Stabilizer
namespace Homological
namespace BB
namespace Z3Z6

/-- `seamC (kcombo 1 0)`, tabulated. -/
def seam10 : G36 × Fin 2 → ZMod 2 := fun p =>
  if p.2 = 0 then
    (if p.1 = (0, 1) ∨ p.1 = (0, 2) ∨ p.1 = (0, 4) ∨ p.1 = (0, 5) ∨
        p.1 = (1, 0) ∨ p.1 = (1, 1) ∨ p.1 = (1, 3) ∨ p.1 = (1, 4)
     then 1 else 0)
  else
    (if p.1 = (0, 0) ∨ p.1 = (0, 1) ∨ p.1 = (0, 3) ∨ p.1 = (0, 4)
     then 1 else 0)

/-- `seamC (kcombo 0 1)`, tabulated. -/
def seam01 : G36 × Fin 2 → ZMod 2 := fun p =>
  if p.2 = 0 then
    (if p.1 = (0, 0) ∨ p.1 = (0, 1) ∨ p.1 = (0, 3) ∨ p.1 = (0, 4) ∨
        p.1 = (1, 0) ∨ p.1 = (1, 2) ∨ p.1 = (1, 3) ∨ p.1 = (1, 5)
     then 1 else 0)
  else
    (if p.1 = (0, 0) ∨ p.1 = (0, 2) ∨ p.1 = (0, 3) ∨ p.1 = (0, 5)
     then 1 else 0)

/-- `seamC (kcombo 1 1)`, tabulated. -/
def seam11 : G36 × Fin 2 → ZMod 2 := fun p =>
  if p.2 = 0 then
    (if p.1 = (0, 0) ∨ p.1 = (0, 2) ∨ p.1 = (0, 3) ∨ p.1 = (0, 5) ∨
        p.1 = (1, 1) ∨ p.1 = (1, 2) ∨ p.1 = (1, 4) ∨ p.1 = (1, 5)
     then 1 else 0)
  else
    (if p.1 = (0, 1) ∨ p.1 = (0, 2) ∨ p.1 = (0, 4) ∨ p.1 = (0, 5)
     then 1 else 0)

theorem seamC_eq_seam10 : coverData.seamC (kcombo 1 0) = seam10 := by
  native_decide

theorem seamC_eq_seam01 : coverData.seamC (kcombo 0 1) = seam01 := by
  native_decide

theorem seamC_eq_seam11 : coverData.seamC (kcombo 1 1) = seam11 := by
  native_decide

/-! ## Seam mask literals (for the bitmask sweeps) -/

def seam01Mask : Nat := 11799387
def seam10Mask : Nat := 7079670
def seam11Mask : Nat := 14159277

theorem seam01Mask_eq : c1MaskOf seam01 = seam01Mask := by native_decide
theorem seam10Mask_eq : c1MaskOf seam10 = seam10Mask := by native_decide
theorem seam11Mask_eq : c1MaskOf seam11 = seam11Mask := by native_decide

end Z3Z6
end BB
end Homological
end Stabilizer
end Quantum
