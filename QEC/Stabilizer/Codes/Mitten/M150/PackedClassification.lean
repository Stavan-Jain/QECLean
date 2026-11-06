import QEC.Stabilizer.Codes.Mitten.M150.PackedSweep
import QEC.Stabilizer.Codes.Mitten.M150.SweepAdapters

namespace Quantum.Stabilizer.Homological.LP.M150
open PackedDigits F2Mask

/-- A checked reconstruction table agrees with the right split map everywhere. -/
theorem sweepRight_eq_recon (T : SweepTables) (mode : Nat) (columns : List (Nat × Nat))
    (hbit : ∀ i < 30, reconX columns (1 <<< i) = sweepRight T mode (1 <<< i)) :
    ∀ x < 2 ^ 30, reconX columns x = sweepRight T mode x :=
  linear_ext 30 (reconX_zero columns) (sweepRight_zero T mode)
    (reconX_xor columns) (sweepRight_xor T mode) hbit

/-- A checked reconstruction table agrees with the left split map everywhere. -/
theorem sweepLeft_eq_recon (T : SweepTables) (mode : Nat) (columns : List (Nat × Nat))
    (hbit : ∀ i < 30, reconX columns (1 <<< i) = sweepLeft T mode (1 <<< i)) :
    ∀ x < 2 ^ 30, reconX columns x = sweepLeft T mode x :=
  linear_ext 30 (reconX_zero columns) (sweepLeft_zero T mode)
    (reconX_xor columns) (sweepLeft_xor T mode) hbit

/-- A census stored as ninety-bit entries in one packed natural number. -/
structure PackedCensus where
  /-- The number of entries available for indexed lookup. -/
  count : Nat
  /-- The census entries packed in their original list order. -/
  data : Nat

/-- The packed census faithfully represents the original classification list. -/
def PackedCensus.Valid (cls : List Nat) (c : PackedCensus) : Prop :=
  c.count = cls.length ∧ c.data = packList 90 cls ∧ ∀ v ∈ cls, v < 2 ^ 90

/-- Validity of an explicit packed census is decidable by its finite data. -/
instance PackedCensus.instDecidableValid (cls : List Nat) (c : PackedCensus) :
    Decidable (PackedCensus.Valid cls c) := by
  unfold PackedCensus.Valid
  infer_instance

/-- A census lookup certificate identifies a triple by its packed lane index. -/
def okTripleAt (census : PackedCensus) (u w t index : Nat) : Bool :=
  (u ||| w ||| t) == 0 ||
    (decide (index < census.count) && lane 90 index census.data == packTriple u w t)

/-- An indexed census witness implies the original membership test. -/
theorem okTripleAt_sound (cls : List Nat) (census : PackedCensus) (u w t index : Nat)
    (hcensus : PackedCensus.Valid cls census)
    (h : okTripleAt census u w t index = true) : okTriple cls u w t = true := by
  simp only [okTripleAt, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq,
    beq_iff_eq] at h
  apply Bool.or_eq_true_iff.mpr
  rcases h with hz | ⟨hi, he⟩
  · exact Or.inl (beq_iff_eq.mpr hz)
  · apply Or.inr
    apply List.contains_iff_mem.mpr
    have hi' : index < cls.length := by simpa only [hcensus.1] using hi
    have hlane : lane 90 index census.data = cls.getD index 0 := by
      rw [hcensus.2.1, packList_eq_ofDigits]
      exact lane_ofDigits 90 index cls hcensus.2.2
    rw [hlane, List.getD_eq_getElem _ _ hi'] at he
    rw [← he]
    exact List.getElem_mem hi'

/-- Acceptance with a direct census index for each exceptional pair. -/
def sweepAcceptAt (T : SweepTables) (census : PackedCensus)
    (mode x y a index : Nat) : Bool :=
  let out := sweepOutput T mode x y a
  match mode with
  | 0 => okTripleAt census x out y index
  | 1 => okTripleAt census x y out index
  | 2 =>
      let c := xorFold T.tWC x ^^^ xorFold T.tTC y
      parity (T.ln0 &&& c) || parity (T.ln1 &&& c) || okTripleAt census out x y index
  | _ =>
      let c := xorFold T.tUC x ^^^ xorFold T.tWC2 y
      parity (T.lnT0 &&& c) || parity (T.lnT1 &&& c) || okTripleAt census x y out index

/-- Indexed exceptional-pair validation implies the original acceptance test. -/
theorem sweepAcceptAt_sound (T : SweepTables) (census : PackedCensus)
    (mode x y a index : Nat) (hcensus : PackedCensus.Valid T.cls census)
    (h : sweepAcceptAt T census mode x y a index = true) :
    sweepAccept T mode x y a = true := by
  rcases mode with _ | _ | _ | mode
  · exact okTripleAt_sound _ _ _ _ _ _ hcensus h
  · exact okTripleAt_sound _ _ _ _ _ _ hcensus h
  · simp only [sweepAcceptAt, Bool.or_eq_true] at h
    simp only [sweepAccept, Bool.or_eq_true]
    exact h.elim Or.inl (fun ht => Or.inr (okTripleAt_sound _ _ _ _ _ _ hcensus ht))
  · simp only [sweepAcceptAt, Bool.or_eq_true] at h
    simp only [sweepAccept, Bool.or_eq_true]
    exact h.elim Or.inl (fun ht => Or.inr (okTripleAt_sound _ _ _ _ _ _ hcensus ht))

end Quantum.Stabilizer.Homological.LP.M150

#print axioms Quantum.Stabilizer.Homological.LP.M150.okTripleAt_sound
#print axioms Quantum.Stabilizer.Homological.LP.M150.sweepAcceptAt_sound
