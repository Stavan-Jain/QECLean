import QEC.Stabilizer.Framework.Homological.Distance
import QEC.Stabilizer.Framework.Homological.ToCode
import QEC.Stabilizer.Codes.RotatedSurface.BoundaryMaps

/-!
# The rotated surface code as a `HomologicalCode`

`rotatedSurfaceHomologicalCode L` packages the boundary maps `rscBoundary1` and
`rscBoundary2` of the rotated surface code of odd size `L ≥ 3` as a
`HomologicalCode`, with the qubit `(x, y)` numbered `y * L + x`
(`rscQubitEquiv`). The theorems on homological CSS codes then apply to it.

The cycles, boundaries and first homology of the complex are also available
under their own names `rscCycles` (`Z₁ L`), `rscBoundaries` (`B₁ L`) and
`rscH1` (`H₁ L`), which do not depend on the `HomologicalCode` structure. Those
of `rotatedSurfaceHomologicalCode L` are these by definition
(`rotatedSurfaceHomologicalCode_cycles_eq`,
`rotatedSurfaceHomologicalCode_boundaries_eq`,
`rotatedSurfaceHomologicalCode_H1_eq`), its cut map is `rscZCutMap`
(`rotatedSurfaceHomologicalCode_cutMap_eq`), and its dual boundary map sums a
chain over the support of each X-check
(`rotatedSurfaceHomologicalCode_dualBoundary_apply`).
-/

namespace Quantum
namespace Stabilizer
namespace Lattice
namespace RotatedSurface

open scoped RotatedSurfaceChain
open Homological

/-! ## Cycles, boundaries and homology -/

variable (L : ℕ)

/-- 1-cycles: the kernel of `∂₁`. -/
def rscCycles : Submodule (ZMod 2) (VtxIdx L → ZMod 2) :=
  LinearMap.ker (∂₁ L)

/-- 1-boundaries: the range of `∂₂`. -/
def rscBoundaries : Submodule (ZMod 2) (VtxIdx L → ZMod 2) :=
  LinearMap.range (∂₂ L)

/-- `Z₁ L` is the rotated-surface 1-cycle submodule `rscCycles L` (`L` explicit,
as for `∂₁`). Scoped: `open scoped RotatedSurfaceChain`. The `ToricChain` scope
binds the same tokens `Z₁`/`B₁`/`H₁` to the toric submodules, so open one of the
two scopes per file. -/
scoped[RotatedSurfaceChain] notation "Z₁" => Quantum.Stabilizer.Lattice.RotatedSurface.rscCycles

/-- `B₁ L` is the rotated-surface 1-boundary submodule `rscBoundaries L`.
Scoped: `open scoped RotatedSurfaceChain`. -/
scoped[RotatedSurfaceChain] notation "B₁" =>
  Quantum.Stabilizer.Lattice.RotatedSurface.rscBoundaries

/-- Every boundary is a cycle. -/
theorem rscBoundaries_le_rscCycles [Fact (Odd L)] : B₁ L ≤ Z₁ L := by
  rintro _ ⟨f, rfl⟩
  exact rscBoundary_comp_zero_apply L f

/-- First homology `H₁ = Z₁ / B₁` of the rotated surface code. -/
abbrev rscH1 : Type :=
  Z₁ L ⧸ Submodule.comap (Z₁ L).subtype (B₁ L)

/-- `H₁ L` is the rotated-surface first homology `rscH1 L = Z₁ L ⧸ B₁ L`.
Scoped: `open scoped RotatedSurfaceChain`. -/
scoped[RotatedSurfaceChain] notation "H₁" => Quantum.Stabilizer.Lattice.RotatedSurface.rscH1

/-! ## Numbering of the qubits -/

/-- The row-major numbering of the qubits: `(x, y)` is qubit `y * L + x`. -/
def rscQubitEquiv : VtxIdx L ≃ Fin (L * L) :=
  (Equiv.prodComm (Fin L) (Fin L)).trans finProdFinEquiv

lemma rscQubitEquiv_apply_val (v : VtxIdx L) :
    (rscQubitEquiv L v).val = v.2.val * L + v.1.val := by
  simp [rscQubitEquiv, Nat.add_comm, Nat.mul_comm]

/-! ## The `HomologicalCode` -/

/-- The chain complex of the rotated surface code as a `HomologicalCode`: the
0-cells are the Z-checks, the 1-cells the qubits and the 2-cells the
X-checks. -/
noncomputable def rotatedSurfaceHomologicalCode [Fact (Odd L)] [Fact (3 ≤ L)] :
    HomologicalCode where
  C0 := ZFaceIdx L
  C1 := VtxIdx L
  C2 := XFaceIdx L
  decEq0 := inferInstance
  decEq1 := inferInstance
  decEq2 := inferInstance
  fin0 := inferInstance
  fin1 := inferInstance
  fin2 := inferInstance
  boundary1 := ∂₁ L
  boundary2 := ∂₂ L
  boundary_comp := rscBoundary_comp_zero L
  numQubits := L * L
  numQubits_eq := by simp
  edgeEquiv := rscQubitEquiv L

variable [Fact (Odd L)] [Fact (3 ≤ L)]

/-! ## Definitional identifications -/

theorem rotatedSurfaceHomologicalCode_cycles_eq :
    (rotatedSurfaceHomologicalCode L).cycles = Z₁ L := rfl

theorem rotatedSurfaceHomologicalCode_boundaries_eq :
    (rotatedSurfaceHomologicalCode L).boundaries = B₁ L := rfl

theorem rotatedSurfaceHomologicalCode_H1_eq :
    (rotatedSurfaceHomologicalCode L).H1 = H₁ L := rfl

/-! ## The cut map and the dual boundary map -/

/-- The cut map of `rotatedSurfaceHomologicalCode L`, defined as the transpose
of `∂₁`, is `δ⁰`: both send a combination of Z-checks to the sum of their
supports. -/
theorem rotatedSurfaceHomologicalCode_cutMap_eq :
    (rotatedSurfaceHomologicalCode L).cutMap = δ⁰ L :=
  LinearMap.ext fun s => funext fun v =>
    Finset.sum_congr rfl fun zf _ => congrArg (s zf * ·) (rscBoundary1_single L v zf)

/-- The dual boundary map of `rotatedSurfaceHomologicalCode L`, defined as the
transpose of `∂₂`, sends a chain to its sum over the support of each
X-check. -/
theorem rotatedSurfaceHomologicalCode_dualBoundary_apply (c : VtxIdx L → ZMod 2)
    (xf : XFaceIdx L) :
    (rotatedSurfaceHomologicalCode L).dualBoundary c xf = ∑ v ∈ xFaceSupport xf, c v :=
  (Finset.sum_congr rfl fun v _ =>
    (congrArg (c v * ·) (rscBoundary2_single L xf v)).trans (mul_boole _ _)).trans
    (Fintype.sum_ite_mem _ _)

end RotatedSurface
end Lattice
end Stabilizer
end Quantum
