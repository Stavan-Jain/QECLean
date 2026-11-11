import Mathlib.Tactic
import QEC.Stabilizer.Geometry.FinPeriodic

/-!
# Cells of the periodic square lattice

Index types for the vertices, edges and faces of an `L × L` periodic square
lattice (`VtxIdx`, `EdgeIdx`, `FaceIdx`), their cardinalities, and the chain
groups `C0`, `C1`, `C2` of `ZMod 2`-valued functions on them.
-/

namespace Quantum
namespace Stabilizer
namespace Lattice

open scoped BigOperators

/-- Vertices of the `L × L` periodic square lattice. -/
abbrev VtxIdx (L : ℕ) : Type := Fin L × Fin L

/-- Faces of the `L × L` periodic square lattice. -/
abbrev FaceIdx (L : ℕ) : Type := Fin L × Fin L

/-- Edges of the `L × L` periodic square lattice: a horizontal edge `h x y` and a
vertical edge `v x y` at each site. -/
inductive EdgeIdx (L : ℕ) where
  | h : Fin L → Fin L → EdgeIdx L
  | v : Fin L → Fin L → EdgeIdx L
deriving DecidableEq, Fintype

/-- 0-chains: `ZMod 2`-valued functions on vertices. -/
abbrev C0 (L : ℕ) : Type := VtxIdx L → ZMod 2

/-- 1-chains: `ZMod 2`-valued functions on edges. -/
abbrev C1 (L : ℕ) : Type := EdgeIdx L → ZMod 2

/-- 2-chains: `ZMod 2`-valued functions on faces. -/
abbrev C2 (L : ℕ) : Type := FaceIdx L → ZMod 2

/-- The horizontal edge at site `(x, y)`. -/
abbrev hEdgeIdx (L : ℕ) (x y : Fin L) : EdgeIdx L := EdgeIdx.h x y

/-- The vertical edge at site `(x, y)`. -/
abbrev vEdgeIdx (L : ℕ) (x y : Fin L) : EdgeIdx L := EdgeIdx.v x y

@[simp] lemma card_vtxIdx (L : ℕ) : Fintype.card (VtxIdx L) = L * L := by
  simp [VtxIdx]

@[simp] lemma card_faceIdx (L : ℕ) : Fintype.card (FaceIdx L) = L * L := by
  simp [FaceIdx]

/-- Edges are two copies of the sites: one for horizontal edges and one for
vertical edges. -/
def edgeIdxEquivSum (L : ℕ) : EdgeIdx L ≃ (VtxIdx L ⊕ VtxIdx L) where
  toFun
    | EdgeIdx.h x y => Sum.inl (x, y)
    | EdgeIdx.v x y => Sum.inr (x, y)
  invFun
    | Sum.inl p => EdgeIdx.h p.1 p.2
    | Sum.inr p => EdgeIdx.v p.1 p.2
  left_inv := by intro e; cases e <;> rfl
  right_inv := by intro s; cases s <;> rfl

@[simp] lemma card_edgeIdx (L : ℕ) : Fintype.card (EdgeIdx L) = 2 * L * L := by
  rw [Fintype.card_congr (edgeIdxEquivSum L), Fintype.card_sum, card_vtxIdx]
  ring

end Lattice
end Stabilizer
end Quantum

