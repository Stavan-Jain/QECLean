import QEC.Stabilizer.Framework.Homological.Certificate.PackedPopcount

/-!
# Packed rectangular tables

Packing a table row by row equals packing its flattened entries
(`packF_grid`). Multiplication by a packed table of ones broadcasts row values
(`packF_broadcast_rows`) and column values (`packF_broadcast_cols`) across the
rectangle, so one packed operation can process many rows together.
-/

namespace PackedDigits

/-- Packing rows of a rectangular table equals packing all entries in row
order. -/
theorem packF_grid (width rows cols : Nat) (f : Nat → Nat) :
    packF (width * cols) rows (fun i => packF width cols (fun j => f (i * cols + j))) =
      packF width (rows * cols) f := by
  induction rows with
  | zero => simp [packF]
  | succ rows ih =>
    rw [packF_succ, ih, Nat.succ_mul, packF_split,
      show width * cols * rows = width * (rows * cols) by ring]

/-- A repetition word broadcasts each outer-table entry across its row. -/
theorem packF_broadcast_rows (width rows cols : Nat) (a : Nat → Nat) :
    packF (width * cols) rows a * packF width cols (fun _ => 1) =
      packF width (rows * cols) (fun i => a (i / cols)) := by
  rcases Nat.eq_zero_or_pos cols with rfl | hcpos
  · simp [packF]
  rw [Nat.mul_comm, packF_mul, ← packF_grid]
  refine packF_congr _ _ _ _ fun i _ => ?_
  rw [repeat_mul_eq_packF]
  refine packF_congr _ _ _ _ fun j hj => ?_
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ hcpos, Nat.div_eq_of_lt hj, Nat.zero_add]

/-- Repeating an inner-table pattern broadcasts it across every row. -/
theorem packF_broadcast_cols (width rows cols : Nat) (b : Nat → Nat) :
    packF (width * cols) rows (fun _ => 1) * packF width cols b =
      packF width (rows * cols) (fun i => b (i % cols)) := by
  rw [repeat_mul_eq_packF, ← packF_grid]
  refine packF_congr _ _ _ _ fun i _ => packF_congr _ _ _ _ fun j hj => ?_
  simp only [Nat.add_mod, Nat.mul_mod_left, Nat.zero_add, Nat.mod_eq_of_lt hj]

end PackedDigits
