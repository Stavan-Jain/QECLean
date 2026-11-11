import QEC.Stabilizer.Codes.Toric.BoundaryMaps

/-!
# Homology of the toric chain complex

The 1-cycles `toricCycles L = ker ∂₁`, the 1-boundaries
`toricBoundaries L = im ∂₂`, and the first homology `toricH1 L`, the quotient of
the cycles by the boundaries. Boundaries are cycles
(`toricBoundaries_le_toricCycles`).

The scoped notations `Z₁ L`, `B₁ L` and `H₁ L` (scope `ToricChain`) stand for
these three objects. The scope `RotatedSurfaceChain` binds the same tokens to
the rotated-surface complex, so a file opens only one of the two scopes.
-/

namespace Quantum
namespace Stabilizer
namespace Lattice

open scoped ToricChain

variable (L : ℕ) [Fact (0 < L)]

/-- The 1-cycles: the kernel of `∂₁`. -/
def toricCycles : Submodule (ZMod 2) (C1 L) :=
  LinearMap.ker (∂₁ L)

/-- The 1-boundaries: the range of `∂₂`. -/
def toricBoundaries : Submodule (ZMod 2) (C1 L) :=
  LinearMap.range (∂₂ L)

/-- `Z₁ L` is the toric 1-cycle submodule `toricCycles L`. Scoped:
`open scoped ToricChain`. -/
scoped[ToricChain] notation "Z₁" => Quantum.Stabilizer.Lattice.toricCycles

/-- `B₁ L` is the toric 1-boundary submodule `toricBoundaries L`. Scoped:
`open scoped ToricChain`. -/
scoped[ToricChain] notation "B₁" => Quantum.Stabilizer.Lattice.toricBoundaries

/-- Every boundary is a cycle: `im ∂₂ ≤ ker ∂₁`. -/
theorem toricBoundaries_le_toricCycles : B₁ L ≤ Z₁ L := by
  rintro _ ⟨f, rfl⟩
  exact toricBoundary_comp_zero_apply L f

/-- The first homology `H₁ = Z₁ / B₁` of the toric chain complex. -/
abbrev toricH1 : Type :=
  Z₁ L ⧸ Submodule.comap (Z₁ L).subtype (B₁ L)

/-- `H₁ L` is the toric first homology `toricH1 L = Z₁ L ⧸ B₁ L`. Scoped:
`open scoped ToricChain`. -/
scoped[ToricChain] notation "H₁" => Quantum.Stabilizer.Lattice.toricH1

end Lattice
end Stabilizer
end Quantum
