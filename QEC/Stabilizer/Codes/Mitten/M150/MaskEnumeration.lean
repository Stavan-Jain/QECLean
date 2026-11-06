import QEC.Stabilizer.Codes.Mitten.M150.FloorCore

/-!
# Chunked certificates for fixed-weight mask enumeration

Each leaf certifies a small part of the recursive mask enumeration. Splits
combine those parts symbolically, so coverage does not require reducing one
large equality between complete lists.
-/

namespace Quantum.Stabilizer.Homological.LP.M150

/-- A tree of certified chunks for fixed-weight masks with a common prefix. -/
inductive MaskCover : (n k prefixMask : Nat) → Type
  | leaf {n k prefixMask : Nat} (values : List Nat)
      (h : values = (masksOfWt n k).map (fun m => m ||| prefixMask)) :
      MaskCover n k prefixMask
  | split {n k prefixMask : Nat}
      (left : MaskCover n (k + 1) prefixMask)
      (right : MaskCover n k (prefixMask ||| (1 <<< n))) :
      MaskCover (n + 1) (k + 1) prefixMask

namespace MaskCover

/-- The certified chunks in their original enumeration order. -/
def chunks {n k prefixMask : Nat} : MaskCover n k prefixMask → List (List Nat)
  | .leaf values _ => [values]
  | .split left right => left.chunks ++ right.chunks

/-- Flattening the chunks recovers the prefixed fixed-weight enumeration. -/
theorem cover {n k prefixMask : Nat} (c : MaskCover n k prefixMask) :
    c.chunks.flatten = (masksOfWt n k).map (fun m => m ||| prefixMask) := by
  induction c with
  | leaf values h => simpa only [chunks, List.flatten_cons, List.flatten_nil,
      List.append_nil] using h
  | split left right ihLeft ihRight =>
    simp only [chunks, List.flatten_append, ihLeft, ihRight, masksOfWt,
      List.map_append, List.map_map, Function.comp_def, Nat.or_assoc]
    rw [Nat.or_comm _ (1 <<< _)]

/-- With a zero prefix, the chunks cover the original mask enumeration. -/
theorem cover_zero {n k : Nat} (c : MaskCover n k 0) :
    c.chunks.flatten = masksOfWt n k := by
  simpa only [Nat.or_zero, List.map_id'] using c.cover

end MaskCover
end Quantum.Stabilizer.Homological.LP.M150

#print axioms Quantum.Stabilizer.Homological.LP.M150.MaskCover.cover
#print axioms Quantum.Stabilizer.Homological.LP.M150.MaskCover.cover_zero
