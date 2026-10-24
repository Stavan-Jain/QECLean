import QEC.Stabilizer.Framework.Homological.Trellis
import QEC.Stabilizer.Framework.Homological.Certificate.PackedDigits
import Mathlib.Data.ZMod.Basic

namespace Quantum.Stabilizer.Homological.F2Mask.Trellis

open PackedDigits

/-- The finite residue ring storing a truncated weight polynomial. -/
abbrev WeightRing (slot degree : Nat) := ZMod (2 ^ (slot * (degree + 1)))

/-- A packed evaluator together with its polynomial bounds and trellis semantics. -/
structure PackedProgram (slot degree initialWidth finalWidth : Nat) where
  /-- The certified affine encoder and its abstract path-counting network. -/
  certificate : CertifiedProgram (WeightRing slot degree) (2 ^ slot) initialWidth finalWidth
  /-- The efficient whole-table evaluator. -/
  numeric : Nat → Nat
  /-- The number of pairwise summations, bounding each coefficient's growth. -/
  merges : Nat
  /-- Packed evaluation agrees with the abstract network without carries between lanes. -/
  sound : ∀ (bound : Nat) (f : Nat → Nat), 0 < slot →
    bound * 2 ^ merges < 2 ^ slot →
    (∀ i < 2 ^ initialWidth, BoundedPolynomial slot degree bound (f i)) →
    ∃ g : Nat → Nat,
      (∀ i < 2 ^ finalWidth, BoundedPolynomial slot degree (bound * 2 ^ merges) (g i)) ∧
      numeric (packF (slot * (degree + 1)) (2 ^ initialWidth) f) =
        packF (slot * (degree + 1)) (2 ^ finalWidth) g ∧
      ∀ i < 2 ^ finalWidth, (g i : WeightRing slot degree) =
        certificate.network.forward (fun j => (f j : WeightRing slot degree)) i

/-- A permutation of state indices with an efficient, verified packed implementation. -/
structure PackedPermutation (lane width : Nat) where
  /-- The scalar source state for each destination state. -/
  source : Nat → Nat
  /-- The corresponding whole-table transformation. -/
  numeric : Nat → Nat
  /-- Every active state remains within the finite table. -/
  range : ∀ i < 2 ^ width, source i < 2 ^ width
  /-- The permutation is its own inverse. -/
  involution : ∀ i < 2 ^ width, source (source i) = i
  /-- Packed and scalar permutations agree on every bounded table. -/
  sound : ∀ (f : Nat → Nat), 0 < lane →
    (∀ i < 2 ^ width, f i < 2 ^ lane) →
    numeric (packF lane (2 ^ width) f) = packF lane (2 ^ width) (fun i => f (source i))

namespace PackedProgram

variable {slot degree : Nat}

/-- Every intermediate coefficient bound is at most its final doubled bound. -/
lemma le_doubled_bound (bound count : Nat) : bound ≤ bound * 2 ^ count := by
  have : 1 ≤ 2 ^ count := Nat.one_le_two_pow
  nlinarith

/-- The empty packed program preserves its input table. -/
def done (width : Nat) : PackedProgram slot degree width width where
  certificate := .done width
  numeric := id
  merges := 0
  sound bound f hs hb hf := by
    refine ⟨f, ?_, rfl, ?_⟩
    · simpa using hf
    · intro i hi
      rfl

/-- Introducing a coefficient duplicates the packed table into its upper half. -/
def read {width finalWidth : Nat} (tail : PackedProgram slot degree (width + 1) finalWidth) :
    PackedProgram slot degree width finalWidth where
  certificate := .read tail.certificate
  numeric table := tail.numeric (table ||| (table <<< ((slot * (degree + 1)) * 2 ^ width)))
  merges := tail.merges
  sound bound f hs hb hf := by
    let g : Nat → Nat := fun i => f (i % 2 ^ width)
    have hbase : bound < 2 ^ slot := lt_of_le_of_lt (le_doubled_bound bound tail.merges) hb
    have hlane : 0 < slot * (degree + 1) := Nat.mul_pos hs (by omega)
    have hfit : ∀ i < 2 ^ width, f i < 2 ^ (slot * (degree + 1)) :=
      fun i hi => (hf i hi).lt hs hbase
    have hdup : packF (slot * (degree + 1)) (2 ^ width) f |||
        (packF (slot * (degree + 1)) (2 ^ width) f <<< ((slot * (degree + 1)) * 2 ^ width)) =
        packF (slot * (degree + 1)) (2 ^ (width + 1)) g := by
      rw [packF_duplicate _ _ _ hlane hfit, pow_succ, Nat.mul_two]
      apply packF_congr
      intro i hi
      dsimp [g]
      by_cases hlow : i < 2 ^ width
      · simp [hlow, Nat.mod_eq_of_lt hlow]
      · have hsub : i - 2 ^ width < 2 ^ width := by omega
        rw [if_neg hlow, Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt hsub]
    obtain ⟨out, hout, hnum, hsem⟩ := tail.sound bound g hs hb
      (fun i hi => hf _ (Nat.mod_lt _ (Nat.two_pow_pos _)))
    refine ⟨out, hout, ?_, ?_⟩
    · rw [hdup]
      exact hnum
    · intro i hi
      exact hsem i hi

/-- Efficient whole-lane mask for one affine output parity. -/
def outputMask (lane width : Nat) (positions : List Nat) (offset : Bool) : Nat :=
  positions.foldr (fun p acc => bitZeroMask lane width p ^^^ acc)
    (if offset then 2 ^ (lane * 2 ^ width) - 1 else 0)

/-- The output mask selects exactly the states whose emitted bit is one. -/
theorem outputMask_eq_packF (lane width : Nat) (positions : List Nat) (offset : Bool)
    (hlane : 0 < lane) (hpositions : ∀ p ∈ positions, p < width) :
    outputMask lane width positions offset =
      packF lane (2 ^ width) (fun i => if outputBit positions offset i then 2 ^ lane - 1 else 0) := by
  induction positions with
  | nil =>
    cases offset with
    | false => simp [outputMask, outputBit, packF]
    | true => exact lowMask_eq_packF _ _ hlane
  | cons p ps ih =>
    rw [outputMask, List.foldr_cons]
    change bitZeroMask lane width p ^^^ outputMask lane width ps offset = _
    rw [bitZeroMask_eq_packF _ _ _ hlane (hpositions p (by simp)),
      ih (fun p hp => hpositions p (by simp [hp])), packF_mask_xor _ _ _ _ hlane]
    rfl

/-- Emitting one coordinate multiplies selected polynomial lanes by the weight variable. -/
def emit {width finalWidth : Nat} (positions : List Nat) (offset : Bool)
    (hpositions : ∀ p ∈ positions, p < width)
    (tail : PackedProgram slot degree width finalWidth) :
    PackedProgram slot degree width finalWidth where
  certificate := .emit positions offset tail.certificate
  numeric table :=
    let lane := slot * (degree + 1)
    let mask := outputMask lane width positions offset
    let full := 2 ^ (lane * 2 ^ width) - 1
    let clip := repeatBlock (2 ^ (slot * degree) - 1) lane width
    tail.numeric ((table &&& (full ^^^ mask)) ||| (((table &&& mask) &&& clip) <<< slot))
  merges := tail.merges
  sound bound f hs hb hf := by
    let lane := slot * (degree + 1)
    let g : Nat → Nat := fun i => if outputBit positions offset i then
      (f i * 2 ^ slot) % 2 ^ lane else f i
    have hbase : bound < 2 ^ slot := lt_of_le_of_lt (le_doubled_bound bound tail.merges) hb
    have hlane : 0 < lane := Nat.mul_pos hs (by omega)
    have hfit : ∀ i < 2 ^ width, f i < 2 ^ lane := fun i hi => (hf i hi).lt hs hbase
    have hkeep : slot * degree + slot = lane := by dsimp [lane]; ring
    have hclip : 2 ^ (slot * degree) - 1 < 2 ^ lane := by
      apply lt_of_lt_of_le (Nat.sub_lt (Nat.two_pow_pos _) (by omega))
      exact Nat.pow_le_pow_right (by omega) (by omega)
    have hstep :
        (packF lane (2 ^ width) f &&& ((2 ^ (lane * 2 ^ width) - 1) ^^^
          outputMask lane width positions offset)) |||
          (((packF lane (2 ^ width) f &&& outputMask lane width positions offset) &&&
            repeatBlock (2 ^ (slot * degree) - 1) lane width) <<< slot) =
          packF lane (2 ^ width) g := by
      rw [outputMask_eq_packF _ _ _ _ hlane hpositions,
        lowMask_eq_packF _ _ hlane, packF_complement_mask _ _ _ hlane,
        repeatBlock_eq_packF _ _ _ hlane hclip]
      apply (packF_weight_step lane (2 ^ width) (slot * degree) slot f
        (fun i => outputBit positions offset i) hlane hkeep hfit).trans
      apply packF_congr
      intro i hi
      simp only [g, clip_shift_eq_mod, hkeep]
    have hg : ∀ i < 2 ^ width, BoundedPolynomial slot degree bound (g i) := by
      intro i hi
      dsimp [g]
      split
      · exact (hf i hi).shift hbase
      · exact hf i hi
    obtain ⟨out, hout, hnum, hsem⟩ := tail.sound bound g hs hb hg
    refine ⟨out, hout, ?_, ?_⟩
    · change tail.numeric _ = _
      rw [hstep]
      exact hnum
    · intro i hi
      rw [hsem i hi]
      change tail.certificate.network.forward (fun j => (g j : WeightRing slot degree)) i =
        tail.certificate.network.forward
          (fun j => (f j : WeightRing slot degree) *
            (if outputBit positions offset j then (2 ^ slot : WeightRing slot degree) else 1)) i
      apply Network.forward_congr _ _ _ _ i hi
      intro j hj
      dsimp [g]
      split_ifs <;> simp [WeightRing, lane, ZMod.natCast_mod]

/-- Forgetting one coefficient permutes its bit to the top and sums the two table halves. -/
def forget {width finalWidth : Nat} (position : Nat)
    (permutation : PackedPermutation (slot * (degree + 1)) (width + 1))
    (hforget : ∀ i < 2 ^ (width + 1),
      forgetBit position (width + 1) i = permutation.source i % 2 ^ width)
    (tail : PackedProgram slot degree width finalWidth) :
    PackedProgram slot degree (width + 1) finalWidth where
  certificate := .forget position permutation.source permutation.range permutation.involution
    hforget tail.certificate
  numeric table :=
    let table := permutation.numeric table
    let half := (slot * (degree + 1)) * 2 ^ width
    tail.numeric ((table &&& (2 ^ half - 1)) + (table >>> half))
  merges := tail.merges + 1
  sound bound f hs hb hf := by
    let lane := slot * (degree + 1)
    let g : Nat → Nat := fun i => f (permutation.source i) +
      f (permutation.source (i + 2 ^ width))
    have hbase : bound < 2 ^ slot :=
      lt_of_le_of_lt (le_doubled_bound bound (tail.merges + 1)) hb
    have hlane : 0 < lane := Nat.mul_pos hs (by omega)
    have hfit : ∀ i < 2 ^ (width + 1), f i < 2 ^ lane :=
      fun i hi => (hf i hi).lt hs hbase
    have hlow : ∀ i < 2 ^ width, i < 2 ^ (width + 1) := by
      intro i hi
      rw [pow_succ, Nat.mul_two]
      omega
    have hhigh : ∀ i < 2 ^ width, i + 2 ^ width < 2 ^ (width + 1) := by
      intro i hi
      rw [pow_succ, Nat.mul_two]
      omega
    have hstep :
        (permutation.numeric (packF lane (2 ^ (width + 1)) f) &&&
          (2 ^ (lane * 2 ^ width) - 1)) +
        (permutation.numeric (packF lane (2 ^ (width + 1)) f) >>> (lane * 2 ^ width)) =
        packF lane (2 ^ width) g := by
      rw [permutation.sound f hlane hfit, pow_succ, Nat.mul_two,
        packF_merge _ _ _ hlane (fun i hi => hfit _ (permutation.range i (hlow i hi)))]
      apply packF_congr
      intro i hi
      simp only [g, Nat.add_comm]
    have hg : ∀ i < 2 ^ width, BoundedPolynomial slot degree (bound + bound) (g i) := by
      intro i hi
      exact (hf _ (permutation.range i (hlow i hi))).add
        (hf _ (permutation.range _ (hhigh i hi)))
    have hfactor : (bound + bound) * 2 ^ tail.merges = bound * 2 ^ (tail.merges + 1) := by
      rw [pow_succ]
      ring
    obtain ⟨out, hout, hnum, hsem⟩ := tail.sound (bound + bound) g hs (by rwa [hfactor]) hg
    refine ⟨out, ?_, ?_, ?_⟩
    · simpa only [hfactor] using hout
    · change tail.numeric _ = _
      rw [hstep]
      exact hnum
    · intro i hi
      rw [hsem i hi]
      change tail.certificate.network.forward (fun j => (g j : WeightRing slot degree)) i =
        tail.certificate.network.forward
          (fun j => (f (permutation.source j) : WeightRing slot degree) +
            (f (permutation.source (j + 2 ^ width)) : WeightRing slot degree)) i
      apply Network.forward_congr _ _ _ _ i hi
      intro j hj
      simp only [g, Nat.cast_add]

/-- The scalar result of a closed packed program is its certified weighted input count. -/
theorem closed_eq_sum (C : PackedProgram slot degree 0 0) (hs : 0 < slot)
    (hbudget : 2 ^ C.merges < 2 ^ slot) :
    (C.numeric 1 : WeightRing slot degree) =
      ∑ input ∈ Finset.range (2 ^ reads C.certificate.program),
        (2 ^ slot : WeightRing slot degree) ^
          bitCount (outputs C.certificate.program) (runWord C.certificate.program input 0) := by
  obtain ⟨g, hg, hnum, hsem⟩ := C.sound 1 (fun _ => 1) hs (by simpa using hbudget)
    (fun i hi => BoundedPolynomial.one slot degree)
  have hpack (f : Nat → Nat) : packF (slot * (degree + 1)) (2 ^ 0) f = f 0 := by
    simp [packF]
  rw [hpack, hpack] at hnum
  rw [hnum, hsem 0 (by decide)]
  simpa only [Nat.cast_one] using C.certificate.forward_eq_sum

end PackedProgram

end Quantum.Stabilizer.Homological.F2Mask.Trellis
