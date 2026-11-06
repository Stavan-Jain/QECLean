import QEC.Stabilizer.Codes.Mitten.M150.Sparse
import QEC.Stabilizer.Framework.Homological.Presentation
import QEC.Stabilizer.Foundations.BinarySymplectic.RankCertificate

/-!
# The mitten code as a `StabilizerCode 150 30`

Kernel-checked inverse certificates establish injectivity of both check
maps. The generic homological presentation then supplies the canonical
stabilizer generator list and the `[[150,30]]` code.
-/

namespace Quantum.Stabilizer.Homological.LP.M150
open scoped BigOperators
open NQubitPauliGroupElement

/-! ## §3  Decoder identities and the kernel-trivial cores

`wX`/`wZ` pack `(H[:,piv])⁻¹` row-wise; reading `H[:,piv]·W = I` column-wise
gives `Σ_j W[j,p']·H[p, piv_j] = [p = p']`, which inverts `∂₂` (resp.
`cutMap`) on check chains: `f p' = Σ_j W[j,p']·(∂₂ f)(piv_j)`.  Both check
matrices have full rank 60, so there is no kernel-correction term and the
cores conclude `f = 0` outright. -/

/-- Bit `p'` of packed decoder row `j` (`wX`). -/
def wbitX (j p' : Fin 60) : ZMod 2 :=
  if (wX.getD j.val 0).testBit p'.val then 1 else 0

/-- Bit `p'` of packed decoder row `j` (`wZ`). -/
def wbitZ (j p' : Fin 60) : ZMod 2 :=
  if (wZ.getD j.val 0).testBit p'.val then 1 else 0

/-- The `j`-th pivot qubit cell for `H_X`. -/
def pivXcell (j : Fin 60) : Fin 5 × M150G := qubitOf (pivX.getD j.val 0)

/-- The `j`-th pivot qubit cell for `H_Z`. -/
def pivZcell (j : Fin 60) : Fin 5 × M150G := qubitOf (pivZ.getD j.val 0)

/-- The sixty entries of a binary row, packed into a natural number. -/
def pivotRowMask (M : Fin 60 → Fin 60 → ZMod 2) (p : Fin 60) : Nat :=
  RankCertificate.ofBitsFrom
    (fun j => if h : j < 60 then decide (M p ⟨j, h⟩ = 1) else false) 0 60

/-- Packed rows of the square pivot matrix. -/
def pivotRows (M : Fin 60 → Fin 60 → ZMod 2) : List Nat :=
  List.ofFn (pivotRowMask M)

/-- Transpose the existing packed inverse rows into certificate columns. -/
def decoderColumns (w : List Nat) : List Nat :=
  List.ofFn fun p : Fin 60 =>
    RankCertificate.ofBitsFrom (fun j => (w.getD j 0).testBit p.val) 0 60

/-- A binary coefficient is its zero-one indicator. -/
private lemma zmod_indicator (x : ZMod 2) :
    (if x = 1 then (1 : ZMod 2) else 0) = x := by
  fin_cases x <;> decide

/-- A packed pivot row has the corresponding matrix coefficients as bits. -/
lemma pivotRows_entry (M : Fin 60 → Fin 60 → ZMod 2) (p j : Fin 60) :
    M p j = if ((pivotRows M).getD p.val 0).testBit j.val then 1 else 0 := by
  rw [List.getD_eq_getElem _ _ (by simp [pivotRows])]
  simp only [pivotRows, List.getElem_ofFn, pivotRowMask,
    RankCertificate.testBit_ofBitsFrom, j.isLt, decide_true, Bool.true_and, zero_add,
    dite_true, decide_eq_true_eq]
  exact (zmod_indicator (M p j)).symm

/-- The certificate matrix reads the bits of the supplied inverse rows. -/
lemma decoderColumns_entry (w : List Nat) (j p : Fin 60) :
    RankCertificate.certMatrix 60 60 (decoderColumns w) j p =
      if (w.getD j.val 0).testBit p.val then 1 else 0 := by
  unfold RankCertificate.certMatrix
  rw [List.getD_eq_getElem _ _ (by simp [decoderColumns])]
  simp only [decoderColumns, List.getElem_ofFn, RankCertificate.testBit_ofBitsFrom,
    j.isLt, decide_true, Bool.true_and, zero_add]

/-- A passing packed inverse check establishes the old sum-shaped decoder identity. -/
lemma decoder_identity_of_check (M : Fin 60 → Fin 60 → ZMod 2) (w : List Nat)
    (h : RankCertificate.check 60 (pivotRows M) (decoderColumns w) = true)
    (p p' : Fin 60) :
    (∑ j : Fin 60, (if (w.getD j.val 0).testBit p'.val then (1 : ZMod 2) else 0)
      * M p j) = (if p = p' then 1 else 0) := by
  have hm := RankCertificate.mul_certMatrix_eq_one M (pivotRows M) (decoderColumns w)
    (by simp [pivotRows]) (pivotRows_entry M) h
  have he := congrFun (congrFun hm p) p'
  simp only [Matrix.mul_apply, decoderColumns_entry, Matrix.one_apply] at he
  simpa only [mul_comm] using he

/-- The packed face inverse certificate is accepted by the kernel. -/
lemma decoder_check_X : RankCertificate.check 60
    (pivotRows fun p j => d2term (checkOfF p) (pivXcell j)) (decoderColumns wX) = true := by
  decide +kernel

/-- The packed vertex inverse certificate is accepted by the kernel. -/
lemma decoder_check_Z : RankCertificate.check 60
    (pivotRows fun p j => cmTerm (checkOfF p) (pivZcell j)) (decoderColumns wZ) = true := by
  decide +kernel

/-- The packed inverse decodes every face coefficient. -/
theorem decoder_identity_X : ∀ p p' : Fin 60,
    (∑ j : Fin 60, wbitX j p' * d2term (checkOfF p) (pivXcell j))
      = (if p = p' then 1 else 0) :=
  decoder_identity_of_check _ wX decoder_check_X

/-- The packed inverse decodes every vertex coefficient. -/
theorem decoder_identity_Z : ∀ p p' : Fin 60,
    (∑ j : Fin 60, wbitZ j p' * cmTerm (checkOfF p) (pivZcell j))
      = (if p = p' then 1 else 0) :=
  decoder_identity_of_check _ wZ decoder_check_Z

/-- Decoder collapse, generic over the side (`γ` instantiates at
`m150Complex.C2` and `.C0`): if the packed decoder rows invert the sparse
matrix `M` on the pivot columns (`hid`) and every pivot column annihilates
`f` (`hz`), then `f = 0`. -/
private lemma kernel_trivial_core {γ : Type} [Fintype γ]
    (f : γ → ZMod 2) (M : γ → (Fin 5 × M150G) → ZMod 2)
    (w : Fin 60 → Fin 60 → ZMod 2) (piv : Fin 60 → Fin 5 × M150G)
    (idx : Fin 60 → γ) (hbij : Function.Bijective idx)
    (hid : ∀ p p' : Fin 60,
      (∑ j : Fin 60, w j p' * M (idx p) (piv j)) = (if p = p' then 1 else 0))
    (hz : ∀ j : Fin 60, (∑ c : γ, f c * M c (piv j)) = 0) :
    f = 0 := by
  funext c'
  obtain ⟨p', rfl⟩ := hbij.surjective c'
  change f (idx p') = 0
  have hexp : f (idx p')
      = ∑ p : Fin 60, f (idx p) * (if p = p' then 1 else 0) := by
    rw [Finset.sum_eq_single p']
    · simp
    · intro b _ hb
      rw [if_neg hb, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ p') h
  have hswap : (∑ p : Fin 60, f (idx p) * (if p = p' then 1 else 0))
      = ∑ j : Fin 60, w j p' * (∑ p : Fin 60, f (idx p) * M (idx p) (piv j)) := by
    have hpt : ∀ p : Fin 60, f (idx p) * (if p = p' then 1 else 0)
        = ∑ j : Fin 60, w j p' * (f (idx p) * M (idx p) (piv j)) := by
      intro p
      rw [← hid p p', Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    simp_rw [hpt]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
  have hcell : ∀ j : Fin 60,
      (∑ p : Fin 60, f (idx p) * M (idx p) (piv j))
        = ∑ c : γ, f c * M c (piv j) :=
    fun j => hbij.sum_comp (fun c => f c * M c (piv j))
  rw [hexp, hswap]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [hcell j, hz j, mul_zero]

/-- **Face block independence core**: a `∂₂`-cycle is `0` (full rank —
no drop set needed, unlike the gross case). -/
lemma face_kernel_trivial {f : m150Complex.C2 → ZMod 2}
    (hf : m150Complex.boundary2 f = 0) : f = 0 := by
  refine kernel_trivial_core f d2term wbitX pivXcell checkOfF checkOfF_bijective
    decoder_identity_X fun j => ?_
  rw [← boundary2_apply_eq_sum_d2term f (pivXcell j), hf]
  rfl

/-- **Vertex block independence core**: a `cutMap`-kernel chain is `0`. -/
lemma vtx_kernel_trivial {s : m150Complex.C0 → ZMod 2}
    (hs : m150Complex.cutMap s = 0) : s = 0 := by
  refine kernel_trivial_core s cmTerm wbitZ pivZcell checkOfF checkOfF_bijective
    decoder_identity_Z fun j => ?_
  rw [← cutMap_apply_eq_sum_cmTerm s (pivZcell j), hs]
  rfl

/-- The face map is injective, certified by its decoder. -/
lemma boundary2_injective : Function.Injective m150Complex.boundary2 := by
  intro f g h
  apply sub_eq_zero.mp
  apply face_kernel_trivial
  rw [map_sub, h, sub_self]

/-- The cut map is injective, certified by its decoder. -/
lemma cutMap_injective : Function.Injective m150Complex.cutMap := by
  intro f g h
  apply sub_eq_zero.mp
  apply vtx_kernel_trivial
  rw [map_sub, h, sub_self]

/-- The canonical presentation retains all sixty checks of each kind. -/
noncomputable def m150Presentation :
    Quantum.StabilizerGroup.StabilizerCode.Presentation m150Complex.numQubits 30 :=
  m150Complex.presentation 30 (by rw [m150_numQubits]; omega)
    (by change 60 + 60 = 150 - 30; decide) cutMap_injective boundary2_injective

/-- The canonical mitten stabilizer code has thirty logical qubits. -/
noncomputable def m150StabilizerCode :
    Quantum.StabilizerGroup.StabilizerCode m150Complex.numQubits 30 :=
  m150Presentation.toCode

/-- The presentation generates the homological stabilizer subgroup. -/
theorem m150StabilizerCode_toSubgroup_eq :
    m150StabilizerCode.toStabilizerGroup.toSubgroup =
      m150Complex.homologicalStabilizerGroup.toSubgroup :=
  m150Complex.presentation_toCode_subgroup 30 _ _ cutMap_injective boundary2_injective


end Quantum.Stabilizer.Homological.LP.M150

#print axioms Quantum.Stabilizer.Homological.LP.M150.m150StabilizerCode
