import QEC.Stabilizer.Framework.Homological.Certificate.PackedLaneShifts
import QEC.Stabilizer.Framework.Homological.Certificate.MaskLinear

/-!
# Window reconstruction on a packed table of masks

`batchRecon rep coeff rows` applies the window reconstruction `F2Mask.reconX`
to every lane of the packed table `coeff` at once: for each `(pivot, row)` pair
of the window it selects the pivot bit of every lane, multiplies the resulting
table of zeros and ones by the row, and XORs the products.

* `batchRecon_packF`: on a packed table, `batchRecon` is `reconX` in each lane.
* `batchRecon_mem_span`: every lane of a batch reconstruction lies in the
  `F2Mask.XorSpan` of the window's rows.
-/

namespace PackedDigits
open Quantum.Stabilizer.Homological.F2Mask

/-- Perform a binary reconstruction simultaneously in all packed lanes; `rep`
is the packed table with `1` in every lane. -/
def batchRecon (rep coeff : Nat) : List (Nat × Nat) → Nat
  | [] => 0
  | (bit, row) :: rest =>
      ((coeff >>> bit) &&& rep) * row ^^^ batchRecon rep coeff rest

/-- Packed reconstruction is the window reconstruction `reconX` in each
lane. -/
theorem batchRecon_packF (width size : Nat) (f : Nat → Nat)
    (hw : 0 < width) (hf : ∀ i < size, f i < 2 ^ width)
    (w : List (Nat × Nat)) (hrows : ∀ p ∈ w, p.1 < width ∧ p.2 < 2 ^ width) :
    batchRecon (packF width size (fun _ => 1)) (packF width size f) w =
      packF width size (fun i => reconX w (f i)) := by
  induction w with
  | nil => simp [batchRecon, reconX, packF]
  | cons p ps ih =>
    have hp := hrows p List.mem_cons_self
    have hps : ∀ q ∈ ps, q.1 < width ∧ q.2 < 2 ^ width :=
      fun q hq => hrows q (List.mem_cons_of_mem p hq)
    have hs : ∀ i < size, p.2 * (if (f i).testBit p.1 then 1 else 0) < 2 ^ width := by
      intro i hi
      split <;> simp_all
    rw [batchRecon, packF_selectBit _ _ _ _ hw hp.1 hf, Nat.mul_comm, packF_mul, ih hps,
      packF_xor _ _ _ _ hw hs fun i _ => reconX_lt ps (f i) width fun q hq => (hps q hq).2]
    refine packF_congr _ _ _ _ fun i _ => ?_
    rw [reconX_cons]
    cases (f i).testBit p.1 <;> simp

/-- A certified packed reconstruction places each output lane in the
generator span. -/
theorem batchRecon_mem_span (width size coeff output : Nat) (hw : 0 < width)
    (hcoeff : coeff < 2 ^ (width * size)) (rows : List (Nat × Nat))
    (hrows : ∀ p ∈ rows, p.1 < width ∧ p.2 < 2 ^ width)
    (hcheck : batchRecon (packF width size (fun _ => 1)) coeff rows = output) :
    ∀ i < size, XorSpan (rows.map Prod.snd) (lane width i output) := by
  rw [← packF_lanes width size coeff hw hcoeff,
    batchRecon_packF width size (fun i => lane width i coeff) hw
      (fun _ _ => lane_lt _ _ _) rows hrows] at hcheck
  intro i hi
  rw [← hcheck, lane_packF _ _ _ _
    (fun j _ => reconX_lt rows (lane width j coeff) width (fun p hp => (hrows p hp).2)), if_pos hi]
  exact reconX_mem_span rows (lane width i coeff)

end PackedDigits
