import Mathlib.Tactic

/-!
# Grid indexing

Lattice codes number the cells of a grid by encoding coordinates as a single
natural number. This file proves that the row-major encoding is injective
(`rowMajor_injective`) and that indices on either side of an offset differ
(`fin_ne_of_val_lt_offset_le`).
-/

namespace Quantum
namespace Stabilizer
namespace Lattice

/-- The row-major encoding `(x, y) ↦ y * L + x` is injective on
`Fin L × Fin L`. -/
lemma rowMajor_injective (L : ℕ) [Fact (0 < L)] :
    Function.Injective (fun p : Fin L × Fin L => p.2.val * L + p.1.val) := by
  rintro ⟨x₁, y₁⟩ ⟨x₂, y₂⟩ hpq
  have hL : 0 < L := Fact.out
  simp only at hpq
  have hx : x₁.val = x₂.val := by
    simpa [Nat.add_mod, Nat.mod_eq_of_lt x₁.isLt, Nat.mod_eq_of_lt x₂.isLt] using
      congrArg (· % L) hpq
  rw [hx] at hpq
  exact Prod.ext (Fin.ext hx)
    (Fin.ext (Nat.eq_of_mul_eq_mul_right hL (Nat.add_right_cancel hpq)))

/-- A number below an offset differs from a number at or above it. -/
lemma ne_of_lt_offset_le {a b offset : ℕ} (ha : a < offset) (hb : offset ≤ b) : a ≠ b := by
  omega

/-- Two indices in `Fin n` differ if one is below an offset and the other is at
or above it. -/
lemma fin_ne_of_val_lt_offset_le {n offset : ℕ} {i j : Fin n}
    (hi : i.val < offset) (hj : offset ≤ j.val) : i ≠ j :=
  fun hij => ne_of_lt_offset_le hi hj (congrArg Fin.val hij)

end Lattice
end Stabilizer
end Quantum
