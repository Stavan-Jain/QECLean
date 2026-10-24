import QEC.Stabilizer.Framework.Homological.BBCover
import QEC.Stabilizer.Framework.Homological.BBDuality
import QEC.Stabilizer.Framework.Homological.BBDeficitWall
import Mathlib.Logic.Equiv.Fin.Basic

noncomputable section

/-! The 360-qubit bivariate bicycle code and its two successive double quotients.
Certificate coordinates reflect both group coordinates, matching the matrices
used by qec-lab. The chosen sections use the same reflected convention. -/

namespace Quantum.Stabilizer.Homological.BB.Bravyi360

/-- Translation group of the 360-qubit code. -/
abbrev Group := ZMod 30 × ZMod 6
/-- Translation group after quotienting the order-two y translation. -/
abbrev MiddleGroup := ZMod 30 × ZMod 3
/-- Translation group after subsequently quotienting the order-two x translation. -/
abbrev BaseGroup := ZMod 15 × ZMod 3

/-- The first defining polynomial of the 360-qubit code. -/
noncomputable def A : Group → ZMod 2 := poly[x^9 + y + y^2]
/-- The second defining polynomial of the 360-qubit code. -/
noncomputable def B : Group → ZMod 2 := poly[y^3 + x^25 + x^26]
/-- The first polynomial in the 180-qubit quotient. -/
noncomputable def middleA : MiddleGroup → ZMod 2 := poly[x^9 + y + y^2]
/-- The second polynomial in the 180-qubit quotient. -/
noncomputable def middleB : MiddleGroup → ZMod 2 := poly[1 + x^25 + x^26]
/-- The first polynomial in the 90-qubit quotient. -/
noncomputable def baseA : BaseGroup → ZMod 2 := poly[x^9 + y + y^2]
/-- The second polynomial in the 90-qubit quotient. -/
noncomputable def baseB : BaseGroup → ZMod 2 := poly[1 + x^10 + x^11]

/-- The 360-qubit chain complex. -/
noncomputable def complex : HomologicalCode := bbChainComplex A B
/-- The 180-qubit quotient chain complex. -/
noncomputable def middleComplex : HomologicalCode := bbChainComplex middleA middleB
/-- The 90-qubit quotient chain complex. -/
noncomputable def baseComplex : HomologicalCode := bbChainComplex baseA baseB

/-- The top projection reduces y modulo three. -/
noncomputable def topProjection : Group →+ MiddleGroup :=
  AddMonoidHom.prodMap (AddMonoidHom.id (ZMod 30))
    (ZMod.castHom (by norm_num : (3 : Nat) ∣ 6) (ZMod 3)).toAddMonoidHom
/-- The lower projection reduces x modulo fifteen. -/
noncomputable def baseProjection : MiddleGroup →+ BaseGroup :=
  AddMonoidHom.prodMap
    (ZMod.castHom (by norm_num : (15 : Nat) ∣ 30) (ZMod 15)).toAddMonoidHom
    (AddMonoidHom.id (ZMod 3))
/-- The top section uses the lower y sheet in certificate coordinates. -/
noncomputable def topSection (p : MiddleGroup) : Group := (p.1, -((-p.2).val : ZMod 6))
/-- The lower section uses the lower x sheet in certificate coordinates. -/
noncomputable def baseSection (p : BaseGroup) : MiddleGroup := (-((-p.1).val : ZMod 30), p.2)

/-- Reflected group coordinates identify 180 checks with their certificate indices. -/
noncomputable def faceEnum : Group ≃ Fin 180 :=
  (Equiv.prodCongr (Equiv.neg (ZMod 30)) (Equiv.neg (ZMod 6))).trans finProdFinEquiv
/-- Reflected coordinates for the 90 middle checks. -/
noncomputable def middleFaceEnum : MiddleGroup ≃ Fin 90 :=
  (Equiv.prodCongr (Equiv.neg (ZMod 30)) (Equiv.neg (ZMod 3))).trans finProdFinEquiv
/-- Reflected coordinates for the 45 bottom checks. -/
noncomputable def baseFaceEnum : BaseGroup ≃ Fin 45 :=
  (Equiv.prodCongr (Equiv.neg (ZMod 15)) (Equiv.neg (ZMod 3))).trans finProdFinEquiv

/-- Certificate qubit indices place the block first, then the reflected group index. -/
noncomputable def qubitEnum : (Group × Fin 2) ≃ Fin 360 :=
  (Equiv.prodComm _ _).trans
    ((Equiv.prodCongr (Equiv.refl (Fin 2)) faceEnum).trans finProdFinEquiv)
/-- Reflected certificate coordinates for the 180 middle qubits. -/
noncomputable def middleQubitEnum : (MiddleGroup × Fin 2) ≃ Fin 180 :=
  (Equiv.prodComm _ _).trans
    ((Equiv.prodCongr (Equiv.refl (Fin 2)) middleFaceEnum).trans finProdFinEquiv)
/-- Reflected certificate coordinates for the 90 bottom qubits. -/
noncomputable def baseQubitEnum : (BaseGroup × Fin 2) ≃ Fin 90 :=
  (Equiv.prodComm _ _).trans
    ((Equiv.prodCongr (Equiv.refl (Fin 2)) baseFaceEnum).trans finProdFinEquiv)

set_option maxRecDepth 4096

/-- The y projection has exactly the two expected sheets. -/
theorem topProjection_fiber : ∀ g g' : Group,
    topProjection g' = topProjection g ↔ g' = g ∨ g' = g + (0, 3) := by decide +kernel
/-- The x projection has exactly the two expected sheets. -/
theorem baseProjection_fiber : ∀ g g' : MiddleGroup,
    baseProjection g' = baseProjection g ↔ g' = g ∨ g' = g + (15, 0) := by decide +kernel
/-- The reflected top section is a right inverse. -/
theorem topProjection_section : ∀ p, topProjection (topSection p) = p := by decide +kernel
/-- The reflected bottom section is a right inverse. -/
theorem baseProjection_section : ∀ p, baseProjection (baseSection p) = p := by decide +kernel
/-- The first top polynomial descends to the middle code. -/
theorem top_push_A : fiberSumFn topProjection A = middleA := by decide +kernel
/-- The second top polynomial descends to the middle code. -/
theorem top_push_B : fiberSumFn topProjection B = middleB := by decide +kernel
/-- The first middle polynomial descends to the bottom code. -/
theorem base_push_A : fiberSumFn baseProjection middleA = baseA := by decide +kernel
/-- The second middle polynomial descends to the bottom code. -/
theorem base_push_B : fiberSumFn baseProjection middleB = baseB := by decide +kernel

/-- The first double cover, from 360 to 180 qubits. -/
noncomputable def topCover : XDoubleCoverData Group MiddleGroup where
  proj := topProjection
  deckS := (0, 3)
  sec := topSection
  Ac := A
  Bc := B
  Ab := middleA
  Bb := middleB
  deckS_ne_zero := by decide
  proj_fiber := topProjection_fiber
  proj_sec := topProjection_section
  push_A := top_push_A
  push_B := top_push_B

/-- The second double cover, from 180 to 90 qubits. -/
noncomputable def baseCover : XDoubleCoverData MiddleGroup BaseGroup where
  proj := baseProjection
  deckS := (15, 0)
  sec := baseSection
  Ac := middleA
  Bc := middleB
  Ab := baseA
  Bb := baseB
  deckS_ne_zero := by decide
  proj_fiber := baseProjection_fiber
  proj_sec := baseProjection_section
  push_A := base_push_A
  push_B := base_push_B

/-- The code has 360 physical qubits. -/
theorem numQubits : complex.numQubits = 360 := by
  change bbNumQubits Group = 360
  unfold bbNumQubits
  rw [Fintype.card_prod, ZMod.card, ZMod.card]

/-- Every bottom-code cycle has even weight. -/
theorem base_cycle_even {v : BaseGroup × Fin 2 → ZMod 2}
    (hv : v ∈ baseComplex.cycles) : Even (baseComplex.chainWeight v) :=
  baseCover.base_cycle_weight_even (by decide +kernel) (by decide +kernel) hv

/-- Every middle-code cycle has even weight. -/
theorem middle_cycle_even {v : MiddleGroup × Fin 2 → ZMod 2}
    (hv : v ∈ middleComplex.cycles) : Even (middleComplex.chainWeight v) :=
  baseCover.cover_cycle_weight_even (by decide +kernel) (by decide +kernel) hv

/-- Every 360-qubit cycle has even weight. -/
theorem cycle_even {v : Group × Fin 2 → ZMod 2}
    (hv : v ∈ complex.cycles) : Even (complex.chainWeight v) :=
  topCover.cover_cycle_weight_even (by decide +kernel) (by decide +kernel) hv

end Quantum.Stabilizer.Homological.BB.Bravyi360
