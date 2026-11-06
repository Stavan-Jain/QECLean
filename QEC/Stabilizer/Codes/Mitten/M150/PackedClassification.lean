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

/-- A census lookup certificate identifies a triple by its list index. -/
def okTripleAt (cls : List Nat) (u w t index : Nat) : Bool :=
  (u ||| w ||| t) == 0 ||
    (cls[index]? == some (packTriple u w t))

/-- An indexed census witness implies the original membership test. -/
theorem okTripleAt_sound (cls : List Nat) (u w t index : Nat)
    (h : okTripleAt cls u w t index = true) : okTriple cls u w t = true := by
  simp only [okTripleAt, Bool.or_eq_true, beq_iff_eq] at h
  apply Bool.or_eq_true_iff.mpr
  rcases h with hz | he
  · exact Or.inl (beq_iff_eq.mpr hz)
  · apply Or.inr
    apply List.contains_iff_mem.mpr
    obtain ⟨hi, he⟩ := List.getElem?_eq_some_iff.mp he
    rw [← he]
    exact List.getElem_mem hi

/-- Acceptance with a direct census index for each exceptional pair. -/
def sweepAcceptAt (T : SweepTables) (mode x y a index : Nat) : Bool :=
  let out := sweepOutput T mode x y a
  match mode with
  | 0 => okTripleAt T.cls x out y index
  | 1 => okTripleAt T.cls x y out index
  | 2 =>
      let c := xorFold T.tWC x ^^^ xorFold T.tTC y
      parity (T.ln0 &&& c) || parity (T.ln1 &&& c) || okTripleAt T.cls out x y index
  | _ =>
      let c := xorFold T.tUC x ^^^ xorFold T.tWC2 y
      parity (T.lnT0 &&& c) || parity (T.lnT1 &&& c) || okTripleAt T.cls x y out index

/-- Indexed exceptional-pair validation implies the original acceptance test. -/
theorem sweepAcceptAt_sound (T : SweepTables) (mode x y a index : Nat)
    (h : sweepAcceptAt T mode x y a index = true) : sweepAccept T mode x y a = true := by
  rcases mode with _ | _ | _ | mode
  · exact okTripleAt_sound _ _ _ _ _ h
  · exact okTripleAt_sound _ _ _ _ _ h
  · simp only [sweepAcceptAt, Bool.or_eq_true] at h
    simp only [sweepAccept, Bool.or_eq_true]
    exact h.elim Or.inl (fun ht => Or.inr (okTripleAt_sound _ _ _ _ _ ht))
  · simp only [sweepAcceptAt, Bool.or_eq_true] at h
    simp only [sweepAccept, Bool.or_eq_true]
    exact h.elim Or.inl (fun ht => Or.inr (okTripleAt_sound _ _ _ _ _ ht))

end Quantum.Stabilizer.Homological.LP.M150
