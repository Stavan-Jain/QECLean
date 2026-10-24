import QEC.Stabilizer.Framework.Homological.Certificate.BatchDualRaw

namespace PackedDigits
open Quantum.Stabilizer.Homological.F2Mask

/-- The binary parity digit fits in a single bit. -/
theorem parityFold_lt_two (k x : Nat) : parityFold k x < 2 := by
  rw [parityFold_eq]
  exact Nat.mod_lt _ (by decide)

/-- The complement of a parity digit is also a single bit. -/
theorem one_xor_parityFold_lt_two (k x : Nat) : (1 ^^^ parityFold k x) < 2 := by
  exact Nat.xor_lt_two_pow (by decide : 1 < 2^1) (parityFold_lt_two _ _)

/-- Off-support singleton positions compatible with one dual equation. -/
def scalarCompatible (bits k beta z : Nat) : Nat :=
  (z &&& (2^bits-1)) ^^^ ((1 ^^^ parityFold k ((z >>> bits) &&& beta)) * (2^bits-1))

/-- Parallel right-hand-side parity flags for one table of duals. -/
def batchRHS (bits k rep beta coeff : Nat) (rows : List (Nat × Nat)) : Nat :=
  rawParityFold k ((batchRecon rep coeff rows >>> bits) &&& beta) &&& rep

/-- Parallel compatible-singleton masks for one table of duals. -/
def batchCompatible (bits k rep beta coeff : Nat) (rows : List (Nat × Nat)) : Nat :=
  (batchRecon rep coeff rows &&& (rep*(2^bits-1))) ^^^
    ((rep ^^^ batchRHS bits k rep beta coeff rows) * (2^bits-1))

/-- Multiplying packed one-bit selectors fills their selected lanes with a short mask. -/
theorem packF_fill (width size value : Nat) :
    packF width size (fun _ => 1) * value = packF width size (fun _ => value) := by
  rw [Nat.mul_comm,packF_mul]
  simp

/-- One packed right-hand-side table gives each lane's own parity digit. -/
theorem batchRHS_packF (width size bits k : Nat) (beta coeff : Nat → Nat)
    (hw : 0 < width) (hfit : bits+bits ≤ width) (hk : 2^k ≤ width)
    (hb : ∀ i < size, beta i < 2^bits) (hc : ∀ i < size, coeff i < 2^width)
    (rows : List (Nat × Nat)) (hr : ∀ p ∈ rows,p.1 < width ∧ p.2 < 2^width) :
    batchRHS bits k (packF width size (fun _ => 1)) (packF width size beta)
      (packF width size coeff) rows =
        packF width size (fun i => parityFold k ((reconX rows (coeff i) >>> bits) &&& beta i)) := by
  unfold batchRHS
  rw [batchRecon_packF _ _ _ hw hc rows hr,
    packF_shiftRight_and _ _ _ _ _ _ hw hfit
      (fun i _ => reconX_lt rows (coeff i) width (fun p hp => (hr p hp).2)) hb]
  apply rawParityFold_packF _ _ _ _ hw hk
  exact fun i hi => lt_of_le_of_lt Nat.and_le_right
    ((hb i hi).trans_le (Nat.pow_le_pow_right (by decide) (by omega)))

/-- Compatible-singleton bitsets computed in parallel have their exact lane semantics. -/
theorem batchCompatible_packF (width size bits k : Nat) (beta coeff : Nat → Nat)
    (hw : 0 < width) (hfit : bits+bits ≤ width) (hk : 2^k ≤ width)
    (hb : ∀ i < size, beta i < 2^bits) (hc : ∀ i < size, coeff i < 2^width)
    (rows : List (Nat × Nat)) (hr : ∀ p ∈ rows,p.1 < width ∧ p.2 < 2^width) :
    batchCompatible bits k (packF width size (fun _ => 1)) (packF width size beta)
      (packF width size coeff) rows =
        packF width size (fun i => scalarCompatible bits k (beta i) (reconX rows (coeff i))) := by
  have hm : 2^bits-1 < 2^width := lt_of_lt_of_le
    (Nat.sub_lt (Nat.two_pow_pos _) (by decide))
    (Nat.pow_le_pow_right (by decide) (by omega))
  have hone : (1 : Nat) < 2^width := Nat.one_lt_two_pow hw.ne'
  have hp : ∀ i < size, parityFold k ((reconX rows (coeff i) >>> bits) &&& beta i) < 2^width := by
    intro i hi
    have h := parityFold_lt_two k ((reconX rows (coeff i) >>> bits) &&& beta i)
    omega
  unfold batchCompatible
  rw [batchRHS_packF _ _ _ _ _ _ hw hfit hk hb hc rows hr,
    batchRecon_packF _ _ _ hw hc rows hr,packF_fill,
    packF_and _ _ _ _ hw (fun i _ => reconX_lt rows (coeff i) width (fun p hp => (hr p hp).2)) (fun _ _ => hm),
    packF_xor _ _ _ _ hw (fun _ _ => hone) hp,Nat.mul_comm,packF_mul]
  rw [packF_xor]
  · apply packF_congr
    intro i hi
    simp only [scalarCompatible,Nat.mul_comm]
  · exact hw
  · exact fun i hi => lt_of_le_of_lt Nat.and_le_right hm
  · intro i hi
    have h := one_xor_parityFold_lt_two k ((reconX rows (coeff i) >>> bits) &&& beta i)
    exact lt_of_le_of_lt (Nat.mul_le_mul_left (2^bits-1) (by omega : (1 ^^^ parityFold k ((reconX rows (coeff i) >>> bits) &&& beta i)) ≤ 1)) (by simpa using hm)

#print axioms batchCompatible_packF
end PackedDigits

namespace PackedDigits
open Quantum.Stabilizer.Homological.F2Mask

/-- A compatible-singleton mask occupies only its original coordinate block. -/
theorem scalarCompatible_lt (bits k beta z : Nat) : scalarCompatible bits k beta z < 2^bits := by
  unfold scalarCompatible
  apply Nat.xor_lt_two_pow
  · exact lt_of_le_of_lt Nat.and_le_right (Nat.sub_lt (Nat.two_pow_pos _) (by decide))
  · have h := one_xor_parityFold_lt_two k ((z >>> bits) &&& beta)
    exact lt_of_le_of_lt (Nat.mul_le_mul_right (2^bits-1) (by omega : (1 ^^^ parityFold k ((z >>> bits) &&& beta)) ≤ 1)) (by simpa using Nat.sub_lt (Nat.two_pow_pos bits) Nat.zero_lt_one)

/-- Intersect all compatible-singleton masks, initially excluding the shadow. -/
def scalarAllowed1 (bits k beta : Nat) : List Nat → Nat
  | [] => (2^bits-1) ^^^ beta
  | z::zs => scalarCompatible bits k beta z &&& scalarAllowed1 bits k beta zs

/-- The zero outside support is compatible precisely when every dual has even right-hand side. -/
def scalarZero1 (bits k beta : Nat) : List Nat → Nat
  | [] => 1
  | z::zs => (1 ^^^ parityFold k ((z >>> bits) &&& beta)) &&& scalarZero1 bits k beta zs

/-- Parallel intersection of all dual-compatible singleton masks. -/
def batchAllowed1 (bits k rep beta : Nat) (rows : List (Nat × Nat)) : List Nat → Nat
  | [] => (rep*(2^bits-1)) ^^^ beta
  | c::cs => batchCompatible bits k rep beta c rows &&& batchAllowed1 bits k rep beta rows cs

/-- Parallel flags for an admissible empty outside support. -/
def batchZero1 (bits k rep beta : Nat) (rows : List (Nat × Nat)) : List Nat → Nat
  | [] => rep
  | c::cs => (rep ^^^ batchRHS bits k rep beta c rows) &&& batchZero1 bits k rep beta rows cs

/-- Compatible-singleton intersections remain bounded. -/
theorem scalarAllowed1_lt (bits k beta : Nat) (zs : List Nat) (hb : beta < 2^bits) :
    scalarAllowed1 bits k beta zs < 2^bits := by
  cases zs with
  | nil => exact Nat.xor_lt_two_pow (Nat.sub_lt (Nat.two_pow_pos _) (by decide)) hb
  | cons z zs => exact lt_of_le_of_lt Nat.and_le_left (scalarCompatible_lt _ _ _ _)

/-- Empty-support flags remain binary. -/
theorem scalarZero1_lt (bits k beta : Nat) (zs : List Nat) : scalarZero1 bits k beta zs < 2 := by
  cases zs with
  | nil => exact (by decide : 1 < 2)
  | cons z zs => exact lt_of_le_of_lt Nat.and_le_left (one_xor_parityFold_lt_two _ _)

/-- Parallel intersection has exactly the scalar compatible-singleton semantics in every lane. -/
theorem batchAllowed1_packF (width size bits k : Nat) (beta : Nat → Nat)
    (coeffs : List (Nat → Nat)) (hw : 0 < width) (hfit : bits+bits ≤ width) (hk : 2^k ≤ width)
    (hb : ∀ i < size, beta i < 2^bits)
    (hc : ∀ f ∈ coeffs, ∀ i < size, f i < 2^width)
    (rows : List (Nat × Nat)) (hr : ∀ p ∈ rows,p.1 < width ∧ p.2 < 2^width) :
    batchAllowed1 bits k (packF width size (fun _ => 1)) (packF width size beta) rows
      (coeffs.map fun f => packF width size f) =
    packF width size (fun i => scalarAllowed1 bits k (beta i) (coeffs.map fun f => reconX rows (f i))) := by
  have hbw : bits ≤ width := by omega
  have hbound : ∀ x, x < 2^bits → x < 2^width := fun x hx =>
    hx.trans_le (Nat.pow_le_pow_right (by decide) hbw)
  induction coeffs with
  | nil =>
    simp only [List.map_nil,batchAllowed1,scalarAllowed1]
    rw [packF_fill,packF_xor _ _ _ _ hw
      (fun _ _ => hbound _ (Nat.sub_lt (Nat.two_pow_pos _) (by decide))) (fun i hi => hbound _ (hb i hi))]
  | cons f fs ih =>
    have hcf := hc f (by simp)
    have hcfs : ∀ g ∈ fs, ∀ i < size, g i < 2^width := fun g hg => hc g (by simp [hg])
    simp only [List.map_cons,batchAllowed1,scalarAllowed1]
    rw [batchCompatible_packF _ _ _ _ _ _ hw hfit hk hb hcf rows hr,ih hcfs]
    exact packF_and _ _ _ _ hw (fun i hi => hbound _ (scalarCompatible_lt _ _ _ _))
      (fun i hi => hbound _ (scalarAllowed1_lt _ _ _ _ (hb i hi)))

/-- Parallel empty-support flags have exactly their scalar semantics in every lane. -/
theorem batchZero1_packF (width size bits k : Nat) (beta : Nat → Nat)
    (coeffs : List (Nat → Nat)) (hw : 0 < width) (hfit : bits+bits ≤ width) (hk : 2^k ≤ width)
    (hb : ∀ i < size, beta i < 2^bits)
    (hc : ∀ f ∈ coeffs, ∀ i < size, f i < 2^width)
    (rows : List (Nat × Nat)) (hr : ∀ p ∈ rows,p.1 < width ∧ p.2 < 2^width) :
    batchZero1 bits k (packF width size (fun _ => 1)) (packF width size beta) rows
      (coeffs.map fun f => packF width size f) =
    packF width size (fun i => scalarZero1 bits k (beta i) (coeffs.map fun f => reconX rows (f i))) := by
  have hbound : ∀ x, x < 2 → x < 2^width := by
    intro x hx
    exact hx.trans_le (Nat.pow_le_pow_right (show 1 ≤ (2 : Nat) by decide) hw)
  induction coeffs with
  | nil => rfl
  | cons f fs ih =>
    have hcf := hc f (by simp)
    have hcfs : ∀ g ∈ fs, ∀ i < size, g i < 2^width := fun g hg => hc g (by simp [hg])
    simp only [List.map_cons,batchZero1,scalarZero1]
    rw [batchRHS_packF _ _ _ _ _ _ hw hfit hk hb hcf rows hr,ih hcfs,
      packF_xor _ _ _ _ hw (fun _ _ => hbound 1 (by decide)) (fun i _ => hbound _ (parityFold_lt_two _ _))]
    exact packF_and _ _ _ _ hw (fun i _ => hbound _ (one_xor_parityFold_lt_two _ _))
      (fun i _ => hbound _ (scalarZero1_lt _ _ _ _))

#print axioms batchAllowed1_packF
#print axioms batchZero1_packF
end PackedDigits
