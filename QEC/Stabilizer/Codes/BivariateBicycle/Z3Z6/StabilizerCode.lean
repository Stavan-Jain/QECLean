/-
# The `[[72,4,8]]` doubling cover as a `StabilizerCode`, with distance 8

S3.9 packaging: bundle `pair72Complex` (the `bbChainComplex a72 b72` of
`Defs.lean`) as a genuine `StabilizerCode 72 4`, transport the Pauli-level
distance theorem `pair72_pauli_distance_eq_8` onto `HasCodeDistance`, and
expose `pair72StabilizerCodeWithDistance : StabilizerCodeWithDistance 72 4 8`.
Mirrors the gross Phase-5 packaging
(`QEC/Stabilizer/Codes/BivariateBicycle/StabilizerCode.lean`) at pair72 scale.

This file embeds offline-validated `𝔽₂` linear-algebra data
(`experiments/bb_lab/scripts/gen_pair72_packaging_data.py`, ALL-PASS gate):
* `dropSet` — 2 faces / 2 vertices dropped to trim 72 generators to 68;
* `redP2` / `redCM` — reduced bases of `ker ∂₂` / `ker cutMap` (2 each),
  satisfying `redP2 j (dropSet i) = [i=j]`, giving both the closure relations
  and the independence kernel-collapse;
* `phiX` / `phiZ` — left-inverse "syndrome decoder" certificates proving the
  trimmed rows are independent (no rank theorem; see `decoder_identity_*`);
* `logX` / `logZ` — a symplectic basis of 4 X-cycles + 4 Z-dual-cycles
  with identity `4×4` intersection matrix (the 4 logical qubits).

Status: complete — all four packaging obligations (closure equality,
generator independence via the decoder identities, the 4 logical qubits,
assembly) plus the distance transport and the bundled
`pair72StabilizerCodeWithDistance`.
-/

import QEC.Stabilizer.Codes.BivariateBicycle.Z3Z6.Distance
import QEC.Stabilizer.Codes.BivariateBicycle.Z3Z6.StabilizerCodeData
import QEC.Stabilizer.Framework.Homological.LogicalCorrespondence
import QEC.Stabilizer.Framework.Core.Logical.CodeDistance
import Mathlib.Data.List.GetD

namespace Quantum.Stabilizer.Homological.BB.Z3Z6

open scoped BigOperators
open Quantum.Stabilizer.Homological NQubitPauliGroupElement

/-! ## §2  Sparse boundary terms and the decoder identities

`∂₂(δ_f)` and `cutMap(δ_v)` are sparse point-mass images; evaluating them
through these few-term forms (rather than `conv`) keeps the kernel sweeps
cheap. -/

/-- `∂₂(δ_f)` evaluated at qubit `(h, j)`:  `A(h-f)` on the left block,
`B(h-f)` on the right. -/
def d2term (f h : G72) (j : Fin 2) : ZMod 2 :=
  if j = 0 then a72 (h - f) else b72 (h - f)

/-- `cutMap(δ_v)` evaluated at qubit `(h, j)`:  `B(v-h)` on the left block,
`A(v-h)` on the right. -/
def cmTerm (v h : G72) (j : Fin 2) : ZMod 2 :=
  if j = 0 then b72 (v - h) else a72 (v - h)

/-- Apply the `phiX` decoder to `∂₂(δ_p)`, read at output face `p'`. -/
def decodeXAt (p p' : G72) : ZMod 2 :=
  (phiX.filter (fun pr => pr.1 = p')).foldl
    (fun acc pr => acc + d2term p pr.2.1 pr.2.2) 0

/-- Apply the `phiZ` decoder to `cutMap(δ_p)`, read at output vertex `p'`. -/
def decodeZAt (p p' : G72) : ZMod 2 :=
  (phiZ.filter (fun pr => pr.1 = p')).foldl
    (fun acc pr => acc + cmTerm p pr.2.1 pr.2.2) 0

/-- Kernel-basis correction term `Σ_j [p = dropSet j] · (red j)(p')`. -/
def kerCorrection (red : List (List G72)) (p p' : G72) : ZMod 2 :=
  ((List.range 2).filter (fun j => dropSet.getD j 0 = p)).foldl
    (fun acc j => acc + (if (red.getD j []).contains p' then 1 else 0)) 0

/-- **Face decoder identity**: the `phiX` decoder inverts `∂₂` on the trimmed
face subspace, modulo the `redP2` kernel basis, over all `36×36` basis pairs.
This is the independence hard-core for the X block — it yields
`∂₂ f = 0 ∧ f|_dropSet = 0 → f = 0` by linearity. -/
theorem decoder_identity_X :
    ∀ p p' : G72,
      decodeXAt p p' + kerCorrection redP2 p p' = (if p' = p then 1 else 0) := by
  native_decide

/-- **Vertex decoder identity**: mirror of `decoder_identity_X` for the Z
block (`cutMap`, `phiZ`, `redCM`). -/
theorem decoder_identity_Z :
    ∀ p p' : G72,
      decodeZAt p p' + kerCorrection redCM p p' = (if p' = p then 1 else 0) := by
  native_decide


/-! ## §3  Lift the decoder identities to all chains (the independence core)

`decoder_identity_X` is a per-basis-vector fact; here we lift it by linearity
to `face_kernel_trivial : ∂₂ f = 0 ∧ f|_dropSet = 0 → f = 0` (and the mirror
`vtx_kernel_trivial`). These feed the block-split `rowsLinearIndependent`. -/

/-- A `ZMod 2`-valued left fold with `+` from `0` is the sum of the mapped list. -/
private lemma foldl_add_eq_sum {α : Type*} (l : List α) (g : α → ZMod 2) :
    l.foldl (fun acc x => acc + g x) 0 = (l.map g).sum := by
  have gen : ∀ (a : ZMod 2), l.foldl (fun acc x => acc + g x) a = a + (l.map g).sum := by
    induction l with
    | nil => intro a; simp
    | cons x xs ih => intro a; simp [ih (a + g x), add_assoc]
  simpa using gen 0

/-- **(L1, X)** Basis expansion of `∂₂` in the sparse `d2term` form. -/
lemma boundary2_apply_eq_sum_d2term (f : G72 → ZMod 2) (h : G72) (j : Fin 2) :
    pair72Complex.boundary2 f (h, j) = ∑ p : G72, f p * d2term p h j := by
  have hgr : pair72Complex.boundary2 f = bbBoundary2Fn a72 b72 f := rfl
  rw [hgr]
  by_cases hj : j = 0
  · subst hj
    change conv a72 f h = ∑ p : G72, f p * d2term p h 0
    rw [conv_apply]
    refine (Equiv.sum_comp (Equiv.subLeft h) (fun x => a72 x * f (h - x))).symm.trans ?_
    refine Finset.sum_congr rfl fun p _ => ?_
    have hp : h - (h - p) = p := by abel
    simp [d2term, Equiv.subLeft_apply, hp, mul_comm]
  · have hj1 : j = 1 := by omega
    subst hj1
    change conv b72 f h = ∑ p : G72, f p * d2term p h 1
    rw [conv_apply]
    refine (Equiv.sum_comp (Equiv.subLeft h) (fun x => b72 x * f (h - x))).symm.trans ?_
    refine Finset.sum_congr rfl fun p _ => ?_
    have hp : h - (h - p) = p := by abel
    simp [d2term, Equiv.subLeft_apply, hp, mul_comm]

/-- **(L1, Z)** `cutMap(δ_v)` per qubit, in the sparse `cmTerm` form. -/
lemma cmTerm_eq (v h : G72) (j : Fin 2) :
    pair72Complex.boundary1 (Pi.single (h, j) 1) v = cmTerm v h j := by
  have hgr : pair72Complex.boundary1 (Pi.single (h, j) (1:ZMod 2))
      = bbBoundary1Fn a72 b72 (Pi.single (h, j) 1) := rfl
  rw [hgr, bbBoundary1Fn]
  by_cases hj : j = 0
  · subst hj
    have hL : leftHalf (Pi.single ((h, (0:Fin 2))) (1:ZMod 2)) = Pi.single h 1 := by
      funext g; simp [leftHalf, Pi.single_apply, Prod.ext_iff]
    have hR : rightHalf (Pi.single ((h, (0:Fin 2))) (1:ZMod 2)) = 0 := by
      funext g; simp [rightHalf, Prod.ext_iff]
    rw [hL, hR, conv_comm b72 (Pi.single h 1), conv_single_left_apply]
    simp [cmTerm, conv_apply]
  · have hj1 : j = 1 := by omega
    subst hj1
    have hL : leftHalf (Pi.single ((h, (1:Fin 2))) (1:ZMod 2)) = 0 := by
      funext g; simp [leftHalf, Prod.ext_iff]
    have hR : rightHalf (Pi.single ((h, (1:Fin 2))) (1:ZMod 2)) = Pi.single h 1 := by
      funext g; simp [rightHalf, Pi.single_apply, Prod.ext_iff]
    rw [hL, hR, conv_comm a72 (Pi.single h 1), conv_single_left_apply]
    simp [cmTerm, conv_apply]

lemma cutMap_apply_eq_sum_cmTerm (s : G72 → ZMod 2) (h : G72) (j : Fin 2) :
    pair72Complex.cutMap s (h, j) = ∑ v : G72, s v * cmTerm v h j := by
  rw [HomologicalCode.cutMap_apply]
  exact Finset.sum_congr rfl fun v _ => by rw [cmTerm_eq]

/-- Interchange a `Fintype` sum with a `List` sum (over `ZMod 2`). -/
private lemma finset_sum_list_sum_comm {ι α : Type*} [Fintype ι] (l : List α)
    (k : ι → α → ZMod 2) :
    ∑ p : ι, (l.map (k p)).sum = (l.map (fun x => ∑ p : ι, k p x)).sum := by
  induction l with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons, List.sum_cons, Finset.sum_add_distrib, ih]

/-- `kerCorrection` vanishes off the drop-set. -/
private lemma kerCorrection_eq_zero_of_not_mem (red : List (List G72)) {p : G72}
    (hp : p ∉ dropSet) (p' : G72) : kerCorrection red p p' = 0 := by
  have hempty : (List.range 2).filter (fun j => dropSet.getD j 0 = p) = [] := by
    rw [List.filter_eq_nil_iff]
    intro j hj hcond
    rw [List.mem_range] at hj
    have hlen : dropSet.length = 2 := by decide
    have hmem : dropSet.getD j 0 ∈ dropSet := by
      rw [List.getD_eq_getElem dropSet 0 (by omega)]; exact List.getElem_mem _
    have : dropSet.getD j 0 = p := by simpa using hcond
    exact hp (this ▸ hmem)
  rw [kerCorrection, hempty]; rfl

/-- **(A, X)** A `∂₂`-cycle makes the `phiX`-decoder sum vanish. -/
lemma sum_decodeXAt_eq_zero_of_boundary {f : G72 → ZMod 2}
    (hf : pair72Complex.boundary2 f = 0) (p' : G72) :
    ∑ p : G72, f p * decodeXAt p p' = 0 := by
  have hstep : ∀ p : G72, f p * decodeXAt p p'
      = ((phiX.filter (fun pr => pr.1 = p')).map
          (fun pr => f p * d2term p pr.2.1 pr.2.2)).sum := fun p => by
    rw [decodeXAt, foldl_add_eq_sum, List.sum_map_mul_left]
  simp_rw [hstep]
  rw [finset_sum_list_sum_comm]
  have hz : ∀ pr : G72 × (G72 × Fin 2),
      (∑ p : G72, f p * d2term p pr.2.1 pr.2.2) = 0 := fun pr => by
    rw [← boundary2_apply_eq_sum_d2term, hf]; rfl
  simp [hz]

/-- **(A, Z)** A `cutMap`-kernel chain makes the `phiZ`-decoder sum vanish. -/
lemma sum_decodeZAt_eq_zero_of_cutMap {s : G72 → ZMod 2}
    (hs : pair72Complex.cutMap s = 0) (p' : G72) :
    ∑ v : G72, s v * decodeZAt v p' = 0 := by
  have hstep : ∀ v : G72, s v * decodeZAt v p'
      = ((phiZ.filter (fun pr => pr.1 = p')).map
          (fun pr => s v * cmTerm v pr.2.1 pr.2.2)).sum := fun v => by
    rw [decodeZAt, foldl_add_eq_sum, List.sum_map_mul_left]
  simp_rw [hstep]
  rw [finset_sum_list_sum_comm]
  have hz : ∀ pr : G72 × (G72 × Fin 2),
      (∑ v : G72, s v * cmTerm v pr.2.1 pr.2.2) = 0 := fun pr => by
    rw [← cutMap_apply_eq_sum_cmTerm, hs]; rfl
  simp [hz]

/-- **Face block independence core**: a `∂₂`-cycle vanishing on `dropSet` is `0`. -/
lemma face_kernel_trivial {f : G72 → ZMod 2}
    (hf : pair72Complex.boundary2 f = 0) (hd : ∀ d ∈ dropSet, f d = 0) : f = 0 := by
  funext p'
  have hId : ∀ p, decodeXAt p p' = (if p' = p then 1 else 0) + kerCorrection redP2 p p' :=
    fun p => by rw [← decoder_identity_X p p', add_assoc, CharTwo.add_self_eq_zero, add_zero]
  have hA := sum_decodeXAt_eq_zero_of_boundary hf p'
  simp_rw [hId, mul_add, Finset.sum_add_distrib] at hA
  have hfirst : (∑ p : G72, f p * (if p' = p then (1:ZMod 2) else 0)) = f p' := by
    rw [Finset.sum_eq_single p']
    · simp
    · intro b _ hb; rw [if_neg (Ne.symm hb)]; ring
    · intro h; exact absurd (Finset.mem_univ p') h
  have hsecond : (∑ p : G72, f p * kerCorrection redP2 p p') = 0 := by
    refine Finset.sum_eq_zero fun p _ => ?_
    by_cases hpd : p ∈ dropSet
    · rw [hd p hpd]; ring
    · rw [kerCorrection_eq_zero_of_not_mem redP2 hpd]; ring
  rw [hfirst, hsecond, add_zero] at hA
  exact hA

/-- **Vertex block independence core**: a `cutMap`-kernel chain vanishing on
`dropSet` is `0`. -/
lemma vtx_kernel_trivial {s : G72 → ZMod 2}
    (hs : pair72Complex.cutMap s = 0) (hd : ∀ d ∈ dropSet, s d = 0) : s = 0 := by
  funext p'
  have hId : ∀ v, decodeZAt v p' = (if p' = v then 1 else 0) + kerCorrection redCM v p' :=
    fun v => by rw [← decoder_identity_Z v p', add_assoc, CharTwo.add_self_eq_zero, add_zero]
  have hA := sum_decodeZAt_eq_zero_of_cutMap hs p'
  simp_rw [hId, mul_add, Finset.sum_add_distrib] at hA
  have hfirst : (∑ v : G72, s v * (if p' = v then (1:ZMod 2) else 0)) = s p' := by
    rw [Finset.sum_eq_single p']
    · simp
    · intro b _ hb; rw [if_neg (Ne.symm hb)]; ring
    · intro h; exact absurd (Finset.mem_univ p') h
  have hsecond : (∑ v : G72, s v * kerCorrection redCM v p') = 0 := by
    refine Finset.sum_eq_zero fun v _ => ?_
    by_cases hvd : v ∈ dropSet
    · rw [hd v hvd]; ring
    · rw [kerCorrection_eq_zero_of_not_mem redCM hvd]; ring
  rw [hfirst, hsecond, add_zero] at hA
  exact hA

/-! ## §4  Closure equality (obligation 1)

The trimmed 68-generator list (34 kept vertex stabs ++ 34 kept face stabs)
generates the same subgroup as the full homological generator set. The dropped
generators re-enter via the reduced kernel relations `redP2` / `redCM`. -/

-- NB: list-mapped generators must be typed `List pair72Complex.C2` / `.C0`, not
-- `List G72`: the projection `C2`/`C0` is defeq but not syntactically
-- `G72`, which silently breaks `rw`/`simp` list-lemma matching.

/-- Product of face stabs over a list = `chainXOperator (∂₂ (Σ indicators))`. -/
lemma faceStabOf_listProd (L : List pair72Complex.C2) :
    (L.map pair72Complex.faceStabOf).prod
      = pair72Complex.chainXOperator
          (pair72Complex.boundary2 ((L.map (fun f => pair72Complex.singleFace f)).sum)) := by
  induction L with
  | nil =>
    simp only [List.map_nil, List.prod_nil, List.sum_nil, map_zero,
      HomologicalCode.chainXOperator_zero]
  | cons f L ih =>
    rw [List.map_cons, List.prod_cons, List.map_cons, List.sum_cons, map_add,
      HomologicalCode.chainXOperator_add, HomologicalCode.chainXOperator_boundary2_singleFace, ih]

/-- Product of vertex stabs over a list = `chainZOperator (cutMap (Σ indicators))`. -/
lemma vertexStabOf_listProd (L : List pair72Complex.C0) :
    (L.map pair72Complex.vertexStabOf).prod
      = pair72Complex.chainZOperator
          (pair72Complex.cutMap ((L.map (fun v => pair72Complex.singleVtx v)).sum)) := by
  induction L with
  | nil =>
    simp only [List.map_nil, List.prod_nil, List.sum_nil, map_zero,
      HomologicalCode.chainZOperator_zero]
  | cons v L ih =>
    rw [List.map_cons, List.prod_cons, List.map_cons, List.sum_cons, map_add,
      HomologicalCode.chainZOperator_add, HomologicalCode.chainZOperator_cutMap_singleVtx, ih]

/-! ## §4b  Boundary-column bridges and the per-drop closure relations -/

lemma boundary2_singleFace_apply (d : G72) (h : G72) (j : Fin 2) :
    pair72Complex.boundary2 (pair72Complex.singleFace d) (h, j) = d2term d h j := by
  rw [boundary2_apply_eq_sum_d2term]
  have hpt : ∀ p : G72, pair72Complex.singleFace d p = (if p = d then 1 else 0) :=
    fun p => by rw [HomologicalCode.singleFace]; exact Pi.single_apply d 1 p
  simp [hpt, Finset.sum_ite_eq']

lemma boundary2_listSum_singleFace_apply (L : List pair72Complex.C2) (h : G72) (j : Fin 2) :
    pair72Complex.boundary2 ((L.map (fun f => pair72Complex.singleFace f)).sum) (h, j)
      = (L.map (fun f : pair72Complex.C2 => d2term f h j)).sum := by
  induction L with
  | nil => simp only [List.map_nil, List.sum_nil, map_zero]; rfl
  | cons f L ih =>
    rw [List.map_cons, List.sum_cons, map_add, Pi.add_apply, boundary2_singleFace_apply, ih,
        List.map_cons, List.sum_cons]


/-- Generic drop relation: if `df`'s boundary column equals the sum of `kp`'s
columns (a kernel relation) and each `kp` face stab is in `S`, then
`faceStabOf df ∈ closure S`. -/
lemma faceStab_drop_mem_closure {S : Set (NQubitPauliGroupElement pair72Complex.numQubits)}
    (df : G72) (kp : List pair72Complex.C2)
    (hrel : ∀ (h : G72) (j : Fin 2),
       d2term df h j = (kp.map (fun f : pair72Complex.C2 => d2term f h j)).sum)
    (hkept : ∀ f ∈ kp, pair72Complex.faceStabOf f ∈ S) :
    pair72Complex.faceStabOf df ∈ Subgroup.closure S := by
  have hbd : pair72Complex.boundary2 (pair72Complex.singleFace df)
      = pair72Complex.boundary2 ((kp.map (fun f => pair72Complex.singleFace f)).sum) := by
    funext q; obtain ⟨h, j⟩ := q
    rw [boundary2_singleFace_apply, boundary2_listSum_singleFace_apply]
    exact hrel h j
  have heq : pair72Complex.faceStabOf df = (kp.map pair72Complex.faceStabOf).prod := by
    rw [faceStabOf_listProd, ← HomologicalCode.chainXOperator_boundary2_singleFace, hbd]
  rw [heq]
  exact Subgroup.list_prod_mem _ (fun g hg => by
    obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hg
    exact Subgroup.subset_closure (hkept f hf))

lemma cutMap_singleVtx_apply (v : G72) (h : G72) (j : Fin 2) :
    pair72Complex.cutMap (pair72Complex.singleVtx v) (h, j) = cmTerm v h j := by
  rw [cutMap_apply_eq_sum_cmTerm]
  have hpt : ∀ w : G72, pair72Complex.singleVtx v w = (if w = v then 1 else 0) :=
    fun w => by rw [HomologicalCode.singleVtx]; exact Pi.single_apply v 1 w
  simp [hpt, Finset.sum_ite_eq']

lemma cutMap_listSum_singleVtx_apply (L : List pair72Complex.C0) (h : G72) (j : Fin 2) :
    pair72Complex.cutMap ((L.map (fun v => pair72Complex.singleVtx v)).sum) (h, j)
      = (L.map (fun v : pair72Complex.C0 => cmTerm v h j)).sum := by
  induction L with
  | nil => simp only [List.map_nil, List.sum_nil, map_zero]; rfl
  | cons v L ih =>
    rw [List.map_cons, List.sum_cons, map_add, Pi.add_apply, cutMap_singleVtx_apply, ih,
        List.map_cons, List.sum_cons]

lemma vertexStab_drop_mem_closure {S : Set (NQubitPauliGroupElement pair72Complex.numQubits)}
    (dv : G72) (kp : List pair72Complex.C0)
    (hrel : ∀ (h : G72) (j : Fin 2),
       cmTerm dv h j = (kp.map (fun v : pair72Complex.C0 => cmTerm v h j)).sum)
    (hkept : ∀ v ∈ kp, pair72Complex.vertexStabOf v ∈ S) :
    pair72Complex.vertexStabOf dv ∈ Subgroup.closure S := by
  have hbd : pair72Complex.cutMap (pair72Complex.singleVtx dv)
      = pair72Complex.cutMap ((kp.map (fun v => pair72Complex.singleVtx v)).sum) := by
    funext q; obtain ⟨h, j⟩ := q
    rw [cutMap_singleVtx_apply, cutMap_listSum_singleVtx_apply]
    exact hrel h j
  have heq : pair72Complex.vertexStabOf dv = (kp.map pair72Complex.vertexStabOf).prod := by
    rw [vertexStabOf_listProd, ← HomologicalCode.chainZOperator_cutMap_singleVtx, hbd]
  rw [heq]
  exact Subgroup.list_prod_mem _ (fun g hg => by
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hg
    exact Subgroup.subset_closure (hkept v hv))

/-! ## §4c  Trimmed generator lists and closure equality -/

noncomputable def genListX : List (NQubitPauliGroupElement pair72Complex.numQubits) :=
  keptCoords.map pair72Complex.faceStabOf

noncomputable def genListZ : List (NQubitPauliGroupElement pair72Complex.numQubits) :=
  keptCoords.map pair72Complex.vertexStabOf

noncomputable def genListPackaged : List (NQubitPauliGroupElement pair72Complex.numQubits) :=
  genListZ ++ genListX

lemma cover : ∀ f : G72, f ∈ keptCoords ∨ f ∈ dropSet := by native_decide

lemma faceStab_kept_mem {f : G72} (hk : f ∈ keptCoords) :
    pair72Complex.faceStabOf f ∈ listToSet genListPackaged :=
  List.mem_append_right _ (List.mem_map.mpr ⟨f, hk, rfl⟩)

lemma vtxStab_kept_mem {v : G72} (hk : v ∈ keptCoords) :
    pair72Complex.vertexStabOf v ∈ listToSet genListPackaged :=
  List.mem_append_left _ (List.mem_map.mpr ⟨v, hk, rfl⟩)

lemma faceStabOf_mem_closure (f : G72) :
    pair72Complex.faceStabOf f ∈ Subgroup.closure (listToSet genListPackaged) := by
  rcases cover f with hk | hd
  · exact Subgroup.subset_closure (faceStab_kept_mem hk)
  · simp only [dropSet, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl
    · exact faceStab_drop_mem_closure _ (keptPartX.getD 0 []) (by native_decide)
        (fun f' hf' => faceStab_kept_mem
          ((by native_decide : ∀ x ∈ keptPartX.getD 0 [], x ∈ keptCoords) f' hf'))
    · exact faceStab_drop_mem_closure _ (keptPartX.getD 1 []) (by native_decide)
        (fun f' hf' => faceStab_kept_mem
          ((by native_decide : ∀ x ∈ keptPartX.getD 1 [], x ∈ keptCoords) f' hf'))

lemma vertexStabOf_mem_closure (v : G72) :
    pair72Complex.vertexStabOf v ∈ Subgroup.closure (listToSet genListPackaged) := by
  rcases cover v with hk | hd
  · exact Subgroup.subset_closure (vtxStab_kept_mem hk)
  · simp only [dropSet, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl
    · exact vertexStab_drop_mem_closure _ (keptPartZ.getD 0 []) (by native_decide)
        (fun v' hv' => vtxStab_kept_mem
          ((by native_decide : ∀ x ∈ keptPartZ.getD 0 [], x ∈ keptCoords) v' hv'))
    · exact vertexStab_drop_mem_closure _ (keptPartZ.getD 1 []) (by native_decide)
        (fun v' hv' => vtxStab_kept_mem
          ((by native_decide : ∀ x ∈ keptPartZ.getD 1 [], x ∈ keptCoords) v' hv'))

/-- **Closure equality**: the trimmed 68-generator list generates exactly the
gross homological stabilizer subgroup. -/
lemma closure_packaged_eq :
    Subgroup.closure (listToSet genListPackaged)
      = pair72Complex.homologicalStabilizerGroup.toSubgroup := by
  rw [HomologicalCode.homologicalStabilizerGroup_toSubgroup]
  apply le_antisymm
  · refine Subgroup.closure_mono ?_
    intro g hg
    have hgl : g ∈ genListPackaged := hg
    rw [genListPackaged, List.mem_append] at hgl
    rcases hgl with hz | hx
    · obtain ⟨v, _, rfl⟩ := List.mem_map.mp hz
      exact Or.inl ⟨v, rfl⟩
    · obtain ⟨f, _, rfl⟩ := List.mem_map.mp hx
      exact Or.inr ⟨f, rfl⟩
  · refine (Subgroup.closure_le _).mpr ?_
    rintro g (hz | hx)
    · obtain ⟨v, rfl⟩ := hz; exact vertexStabOf_mem_closure v
    · obtain ⟨f, rfl⟩ := hx; exact faceStabOf_mem_closure f

/-! ## §5a  Symplectic-row bridges (for `rowsLinearIndependent`) -/

private lemma zmod2_dich (a : ZMod 2) : a = 0 ∨ a = 1 := by
  rcases Fin.exists_fin_two.mp ⟨a, rfl⟩ with h | h
  · exact Or.inl h
  · exact Or.inr h

/-- Z-half symplectic entry of a vertex stab = the cutMap chain value at that edge. -/
lemma vertexStabOf_sympl_Z (v : pair72Complex.C0) (i : Fin pair72Complex.numQubits) :
    NQubitPauliOperator.toSymplectic (pair72Complex.vertexStabOf v).operators
        (Fin.natAdd pair72Complex.numQubits i)
      = pair72Complex.cutMap (pair72Complex.singleVtx v) (pair72Complex.edgeEquiv.symm i) := by
  rw [NQubitPauliOperator.toSymplectic_Z_part]
  change ((pair72Complex.chainZOperator
    (pair72Complex.cutMap (pair72Complex.singleVtx v))).operators i).toSymplecticSingle.2 = _
  rw [HomologicalCode.chainZOperator_op_at]
  set c := pair72Complex.cutMap (pair72Complex.singleVtx v) with hc
  by_cases h : ∃ e, pair72Complex.edgeEquiv e = i ∧ c e = 1
  · obtain ⟨e, he, hce⟩ := h
    rw [if_pos ⟨e, he, hce⟩]
    have : pair72Complex.edgeEquiv.symm i = e := by rw [← he, Equiv.symm_apply_apply]
    rw [this, hce]; rfl
  · rw [if_neg h]
    have hz : c (pair72Complex.edgeEquiv.symm i) = 0 := by
      rcases zmod2_dich (c (pair72Complex.edgeEquiv.symm i)) with h0 | h1
      · exact h0
      · exact absurd ⟨pair72Complex.edgeEquiv.symm i, Equiv.apply_symm_apply _ _, h1⟩ h
    rw [hz]; rfl

/-- X-half symplectic entry of a face stab = the boundary2 chain value at that edge. -/
lemma faceStabOf_sympl_X (f : pair72Complex.C2) (i : Fin pair72Complex.numQubits) :
    NQubitPauliOperator.toSymplectic (pair72Complex.faceStabOf f).operators
        (Fin.castAdd pair72Complex.numQubits i)
      = pair72Complex.boundary2 (pair72Complex.singleFace f) (pair72Complex.edgeEquiv.symm i) := by
  rw [NQubitPauliOperator.toSymplectic_X_part]
  change ((pair72Complex.chainXOperator
      (pair72Complex.boundary2 (pair72Complex.singleFace f))).operators i).toSymplecticSingle.1 = _
  rw [HomologicalCode.chainXOperator_op_at]
  set c := pair72Complex.boundary2 (pair72Complex.singleFace f) with hc
  by_cases h : ∃ e, pair72Complex.edgeEquiv e = i ∧ c e = 1
  · obtain ⟨e, he, hce⟩ := h
    rw [if_pos ⟨e, he, hce⟩]
    have : pair72Complex.edgeEquiv.symm i = e := by rw [← he, Equiv.symm_apply_apply]
    rw [this, hce]; rfl
  · rw [if_neg h]
    have hz : c (pair72Complex.edgeEquiv.symm i) = 0 := by
      rcases zmod2_dich (c (pair72Complex.edgeEquiv.symm i)) with h0 | h1
      · exact h0
      · exact absurd ⟨pair72Complex.edgeEquiv.symm i, Equiv.apply_symm_apply _ _, h1⟩ h
    rw [hz]; rfl

/-- A vertex stab (Z-type) has zero X-half symplectic entries. -/
lemma vertexStabOf_sympl_X_zero (v : pair72Complex.C0) (i : Fin pair72Complex.numQubits) :
    NQubitPauliOperator.toSymplectic (pair72Complex.vertexStabOf v).operators
        (Fin.castAdd pair72Complex.numQubits i) = 0 := by
  rw [NQubitPauliOperator.toSymplectic_X_part]
  rcases (HomologicalCode.vertexStabOf_isZType v).2 i with hI | hZ
  · rw [hI]; rfl
  · rw [hZ]; rfl

/-- A face stab (X-type) has zero Z-half symplectic entries. -/
lemma faceStabOf_sympl_Z_zero (f : pair72Complex.C2) (i : Fin pair72Complex.numQubits) :
    NQubitPauliOperator.toSymplectic (pair72Complex.faceStabOf f).operators
        (Fin.natAdd pair72Complex.numQubits i) = 0 := by
  rw [NQubitPauliOperator.toSymplectic_Z_part]
  rcases (HomologicalCode.faceStabOf_isXType f).2 i with hI | hX
  · rw [hI]; rfl
  · rw [hX]; rfl

/-! ## §5b  Coefficient-collapse helpers (consume the kernel-trivial cores) -/

lemma keptCoords_nodup : keptCoords.Nodup := by native_decide

private lemma singleVtx_apply' (a b : G72) :
    pair72Complex.singleVtx a b = if b = a then (1 : ZMod 2) else 0 := by
  rw [HomologicalCode.singleVtx]; exact Pi.single_apply a 1 b

private lemma singleFace_apply' (a b : G72) :
    pair72Complex.singleFace a b = if b = a then (1 : ZMod 2) else 0 := by
  rw [HomologicalCode.singleFace]; exact Pi.single_apply a 1 b

private lemma keptCoords_get_not_dropSet (i : Fin keptCoords.length) :
    (keptCoords.get i : G72) ∉ dropSet := by
  have hmem : (keptCoords.get i) ∈ keptCoords := List.get_mem _ _
  have hsub : ∀ x ∈ keptCoords, x ∉ dropSet := by native_decide
  exact hsub _ hmem

lemma combo_singleVtx_kernel_zero (c : Fin keptCoords.length → ZMod 2)
    (hker : pair72Complex.cutMap
      (∑ i, c i • pair72Complex.singleVtx (keptCoords.get i)) = 0) :
    ∀ i, c i = 0 := by
  set s := ∑ i, c i • pair72Complex.singleVtx (keptCoords.get i) with hs
  have hd : ∀ d ∈ dropSet, s d = 0 := by
    intro d hdmem
    rw [hs, Finset.sum_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    have hne : d ≠ keptCoords.get i := fun h => keptCoords_get_not_dropSet i (h ▸ hdmem)
    simp only [Pi.smul_apply, singleVtx_apply', smul_eq_mul, if_neg hne, mul_zero]
  have hs0 : s = 0 := vtx_kernel_trivial hker hd
  intro j
  have hsj := congr_fun hs0 (keptCoords.get j)
  rw [hs, Finset.sum_apply, Finset.sum_eq_single j] at hsj
  · simpa [singleVtx_apply'] using hsj
  · intro i _ hij
    have hne : keptCoords.get j ≠ keptCoords.get i :=
      fun h => hij (List.nodup_iff_injective_get.mp keptCoords_nodup h.symm)
    simp only [Pi.smul_apply, singleVtx_apply', smul_eq_mul, if_neg hne, mul_zero]
  · intro hc; exact absurd (Finset.mem_univ j) hc

lemma combo_singleFace_kernel_zero (c : Fin keptCoords.length → ZMod 2)
    (hker : pair72Complex.boundary2
      (∑ i, c i • pair72Complex.singleFace (keptCoords.get i)) = 0) :
    ∀ i, c i = 0 := by
  set s := ∑ i, c i • pair72Complex.singleFace (keptCoords.get i) with hs
  have hd : ∀ d ∈ dropSet, s d = 0 := by
    intro d hdmem
    rw [hs, Finset.sum_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    have hne : d ≠ keptCoords.get i := fun h => keptCoords_get_not_dropSet i (h ▸ hdmem)
    simp only [Pi.smul_apply, singleFace_apply', smul_eq_mul, if_neg hne, mul_zero]
  have hs0 : s = 0 := face_kernel_trivial hker hd
  intro j
  have hsj := congr_fun hs0 (keptCoords.get j)
  rw [hs, Finset.sum_apply, Finset.sum_eq_single j] at hsj
  · simpa [singleFace_apply'] using hsj
  · intro i _ hij
    have hne : keptCoords.get j ≠ keptCoords.get i :=
      fun h => hij (List.nodup_iff_injective_get.mp keptCoords_nodup h.symm)
    simp only [Pi.smul_apply, singleFace_apply', smul_eq_mul, if_neg hne, mul_zero]
  · intro hc; exact absurd (Finset.mem_univ j) hc

/-! ## §5c  Packaged-list indexing -/

lemma genListPackaged_length :
    genListPackaged.length = keptCoords.length + keptCoords.length := by
  have h : genListPackaged.length = (keptCoords.map pair72Complex.vertexStabOf).length
    + (keptCoords.map pair72Complex.faceStabOf).length := rfl
  simpa [List.length_map] using h

lemma get_packaged_Z (i : Fin keptCoords.length)
    (hi : i.val < genListPackaged.length) :
    genListPackaged.get ⟨i.val, hi⟩ = pair72Complex.vertexStabOf (keptCoords.get i) := by
  have hlt : i.val < (keptCoords.map pair72Complex.vertexStabOf).length := by
    rw [List.length_map]; exact i.isLt
  change (keptCoords.map pair72Complex.vertexStabOf
    ++ keptCoords.map pair72Complex.faceStabOf).get ⟨i.val, hi⟩ = _
  rw [List.get_eq_getElem, List.getElem_append_left hlt, List.getElem_map]
  rfl

set_option maxRecDepth 4096 in
lemma get_packaged_X (i : Fin keptCoords.length)
    (hi : keptCoords.length + i.val < genListPackaged.length) :
    genListPackaged.get ⟨keptCoords.length + i.val, hi⟩
      = pair72Complex.faceStabOf (keptCoords.get i) := by
  have hZlen : (keptCoords.map pair72Complex.vertexStabOf).length = keptCoords.length :=
    List.length_map _
  have hge : (keptCoords.map pair72Complex.vertexStabOf).length ≤ keptCoords.length + i.val := by
    rw [hZlen]; omega
  have hidx : keptCoords.length + i.val - (keptCoords.map pair72Complex.vertexStabOf).length
      = i.val := by rw [hZlen]; omega
  change (keptCoords.map pair72Complex.vertexStabOf
    ++ keptCoords.map pair72Complex.faceStabOf).get ⟨keptCoords.length + i.val, hi⟩ = _
  rw [List.get_eq_getElem, List.getElem_append_right hge, List.getElem_map]
  simp only [hidx]
  rfl

/-! ## §5d  rowsLinearIndependent (block-split) and generators_independent -/

private lemma zidx_lt (i : Fin keptCoords.length) : i.val < genListPackaged.length := by
  have := genListPackaged_length; have := i.isLt; omega

private lemma xidx_lt (i : Fin keptCoords.length) :
    keptCoords.length + i.val < genListPackaged.length := by
  have := genListPackaged_length; have := i.isLt; omega

set_option maxRecDepth 4096 in
private lemma sum_split_Z {M : Type*} [AddCommMonoid M]
    (F : Fin genListPackaged.length → M)
    (hX : ∀ i : Fin keptCoords.length, F ⟨keptCoords.length + i.val, xidx_lt i⟩ = 0) :
    ∑ k, F k = ∑ i : Fin keptCoords.length, F ⟨i.val, zidx_lt i⟩ := by
  have hlen := genListPackaged_length
  rw [← Equiv.sum_comp (finCongr hlen.symm) F, Fin.sum_univ_add]
  have hXsum : (∑ i : Fin keptCoords.length,
      F (finCongr hlen.symm (Fin.natAdd keptCoords.length i))) = 0 := by
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [← hX i]; congr 1
  rw [hXsum, add_zero]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1

set_option maxRecDepth 4096 in
private lemma sum_split_X {M : Type*} [AddCommMonoid M]
    (F : Fin genListPackaged.length → M)
    (hZ : ∀ i : Fin keptCoords.length, F ⟨i.val, zidx_lt i⟩ = 0) :
    ∑ k, F k = ∑ i : Fin keptCoords.length, F ⟨keptCoords.length + i.val, xidx_lt i⟩ := by
  have hlen := genListPackaged_length
  rw [← Equiv.sum_comp (finCongr hlen.symm) F, Fin.sum_univ_add]
  have hZsum : (∑ i : Fin keptCoords.length,
      F (finCongr hlen.symm (Fin.castAdd keptCoords.length i))) = 0 := by
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [← hZ i]; congr 1
  rw [hZsum, zero_add]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
-- the block-split reduction unifies 68 check-matrix rows against the chain maps,
-- which exceeds the default heartbeat budget.
/-- The trimmed 68-generator list has linearly independent check-matrix rows. -/
theorem rowsLinearIndependent_packaged :
    NQubitPauliGroupElement.rowsLinearIndependent genListPackaged := by
  rw [NQubitPauliGroupElement.rowsLinearIndependent, Fintype.linearIndependent_iff]
  intro g hsum
  set n := pair72Complex.numQubits with hn
  have hZchain : pair72Complex.cutMap (∑ i : Fin keptCoords.length,
      g ⟨i.val, zidx_lt i⟩ • pair72Complex.singleVtx (keptCoords.get i)) = 0 := by
    funext e
    rw [map_sum]
    simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    have hcol := congr_fun hsum (Fin.natAdd n (pair72Complex.edgeEquiv e))
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hcol
    rw [← hcol, sum_split_Z (fun k => g k *
      NQubitPauliGroupElement.checkMatrix genListPackaged k
        (Fin.natAdd n (pair72Complex.edgeEquiv e)))]
    · refine Finset.sum_congr rfl fun i _ => ?_
      have hterm : NQubitPauliGroupElement.checkMatrix genListPackaged ⟨i.val, zidx_lt i⟩
          (Fin.natAdd n (pair72Complex.edgeEquiv e))
          = pair72Complex.cutMap (pair72Complex.singleVtx (keptCoords.get i)) e := by
        unfold NQubitPauliGroupElement.checkMatrix
        rw [get_packaged_Z i, vertexStabOf_sympl_Z, Equiv.symm_apply_apply]
      rw [hterm]
    · intro i
      have hterm : NQubitPauliGroupElement.checkMatrix genListPackaged
          ⟨keptCoords.length + i.val, xidx_lt i⟩
          (Fin.natAdd n (pair72Complex.edgeEquiv e)) = 0 := by
        unfold NQubitPauliGroupElement.checkMatrix
        rw [get_packaged_X i, faceStabOf_sympl_Z_zero]
      rw [hterm, mul_zero]
  have hZ0 := combo_singleVtx_kernel_zero _ hZchain
  have hXchain : pair72Complex.boundary2 (∑ i : Fin keptCoords.length,
      g ⟨keptCoords.length + i.val, xidx_lt i⟩ • pair72Complex.singleFace (keptCoords.get i))
        = 0 := by
    funext e
    rw [map_sum]
    simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    have hcol := congr_fun hsum (Fin.castAdd n (pair72Complex.edgeEquiv e))
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hcol
    rw [← hcol, sum_split_X (fun k => g k *
      NQubitPauliGroupElement.checkMatrix genListPackaged k
        (Fin.castAdd n (pair72Complex.edgeEquiv e)))]
    · refine Finset.sum_congr rfl fun i _ => ?_
      have hterm : NQubitPauliGroupElement.checkMatrix genListPackaged
          ⟨keptCoords.length + i.val, xidx_lt i⟩ (Fin.castAdd n (pair72Complex.edgeEquiv e))
          = pair72Complex.boundary2 (pair72Complex.singleFace (keptCoords.get i)) e := by
        unfold NQubitPauliGroupElement.checkMatrix
        rw [get_packaged_X i, faceStabOf_sympl_X, Equiv.symm_apply_apply]
      rw [hterm]
    · intro i
      have hterm : NQubitPauliGroupElement.checkMatrix genListPackaged ⟨i.val, zidx_lt i⟩
          (Fin.castAdd n (pair72Complex.edgeEquiv e)) = 0 := by
        unfold NQubitPauliGroupElement.checkMatrix
        rw [get_packaged_Z i, vertexStabOf_sympl_X_zero]
      rw [hterm, mul_zero]
  have hX0 := combo_singleFace_kernel_zero _ hXchain
  intro k
  by_cases hk : k.val < keptCoords.length
  · have hz := hZ0 ⟨k.val, hk⟩
    rwa [Fin.eta] at hz
  · push Not at hk
    have hlen := genListPackaged_length
    have hkl := k.isLt
    have hsub : k.val - keptCoords.length < keptCoords.length := by omega
    have hx := hX0 ⟨k.val - keptCoords.length, hsub⟩
    have hidx : (⟨keptCoords.length + (k.val - keptCoords.length), by omega⟩ :
        Fin genListPackaged.length) = k := by
      apply Fin.ext; change keptCoords.length + (k.val - keptCoords.length) = k.val; omega
    rwa [hidx] at hx

/-- The trimmed generator list is an independent generating set. -/
theorem generators_independent_packaged :
    Quantum.StabilizerGroup.GeneratorsIndependent pair72Complex.numQubits genListPackaged :=
  Quantum.StabilizerGroup.GeneratorsIndependent_of_rowsLinearIndependent
    pair72Complex.numQubits genListPackaged rowsLinearIndependent_packaged

/-! ## §6  Packaged stabilizer group, logical operators, the `StabilizerCode` + `HasCodeDistance`

The 4 logical-qubit operators are the `pair72Complex.chainXOperator`/`chainZOperator`
of the offline-validated symplectic basis `logX`/`logZ` (identity `4×4`
intersection matrix). The performance trap — kernel `whnf` exploding through the
noncomputable `pair72Complex` and the 68-element literal generator list when a
`centralizer`-transport `rw` or `commute_or_anticommute` runs against a *concrete*
chain operator — is dodged by proving every centralizer / (anti)commutation fact
in a helper lemma with the **chain held abstract** (a stuck variable that blocks
`chainXOperator c` from reducing and keeps `packagedSG` behind the precompiled
`packagedSG_toSubgroup_eq`). `logicalQubit` then only *applies* those helpers by
substitution, paying the heavy defeq once, generically. -/

open Quantum.StabilizerGroup

/-- The 68 trimmed generators all lie in the full homological generator set. -/
lemma listToSet_packaged_subset_homGens :
    listToSet genListPackaged ⊆ pair72Complex.homologicalGenerators := by
  intro g hg
  have hg' : g ∈ genListZ ++ genListX := hg
  rcases List.mem_append.mp hg' with hz | hx
  · obtain ⟨v, _, rfl⟩ := List.mem_map.mp hz
    exact HomologicalCode.ZGenerators_subset_homologicalGenerators ⟨v, rfl⟩
  · obtain ⟨f, _, rfl⟩ := List.mem_map.mp hx
    exact HomologicalCode.XGenerators_subset_homologicalGenerators ⟨f, rfl⟩

/-- The trimmed generators pairwise commute. -/
lemma gens_commute_packaged :
    ∀ g ∈ listToSet genListPackaged, ∀ h ∈ listToSet genListPackaged, g * h = h * g := by
  intro g hg h hh
  exact HomologicalCode.homologicalGenerators_commute g (listToSet_packaged_subset_homGens hg)
    h (listToSet_packaged_subset_homGens hh)

/-- `-I` is not in the closure of the trimmed generators. -/
lemma gens_no_neg_packaged :
    negIdentity pair72Complex.numQubits ∉ Subgroup.closure (listToSet genListPackaged) := by
  rw [closure_packaged_eq]
  exact pair72Complex.homologicalStabilizerGroup.no_neg_identity

/-- The packaged stabilizer group (closure of the trimmed 68-generator list). -/
noncomputable def packagedSG : StabilizerGroup pair72Complex.numQubits :=
  mkStabilizerFromGenerators pair72Complex.numQubits genListPackaged
    gens_commute_packaged gens_no_neg_packaged

/-- The packaged stabilizer subgroup equals the gross homological stabilizer
subgroup — the bridge transporting the chain-level distance theorems. -/
lemma packagedSG_toSubgroup_eq :
    packagedSG.toSubgroup = pair72Complex.homologicalStabilizerGroup.toSubgroup := by
  change Subgroup.closure (listToSet genListPackaged) = _
  exact closure_packaged_eq

/-- Centralizer membership for an X-chain operator, **chain abstract**: the stuck
`c` blocks `pair72Complex.chainXOperator` from reducing and `packagedSG` stays behind
`packagedSG_toSubgroup_eq`, so the `centralizer`-transport defeq is paid once here. -/
lemma chainXOperator_mem_centralizer_packagedSG (c : pair72Complex.C1 → ZMod 2)
    (hc : pair72Complex.boundary1 c = 0) :
    pair72Complex.chainXOperator c ∈ centralizer packagedSG := by
  rw [centralizer_eq_of_toSubgroup_eq packagedSG pair72Complex.homologicalStabilizerGroup
    packagedSG_toSubgroup_eq]
  exact (HomologicalCode.chainXOperator_mem_centralizer_iff_mem_cycles c).mpr
    ((pair72Complex.mem_cycles_iff c).mpr hc)

/-- Centralizer membership for a Z-chain operator (chain abstract; mirror of the X case). -/
lemma chainZOperator_mem_centralizer_packagedSG (c : pair72Complex.C1 → ZMod 2)
    (hc : pair72Complex.dualBoundary c = 0) :
    pair72Complex.chainZOperator c ∈ centralizer packagedSG := by
  rw [centralizer_eq_of_toSubgroup_eq packagedSG pair72Complex.homologicalStabilizerGroup
    packagedSG_toSubgroup_eq]
  refine (HomologicalCode.chainZOperator_mem_centralizer_iff_mem_dualCycles c).mpr ?_
  change c ∈ LinearMap.ker pair72Complex.dualBoundary
  rw [LinearMap.mem_ker]
  exact hc

/-- An X-chain and a Z-chain operator anticommute when their inner product is `1`
(chains abstract — `commute_or_anticommute` never reduces the concrete operators). -/
lemma chainXOperator_anticommute_chainZOperator (c c' : pair72Complex.C1 → ZMod 2)
    (h : pair72Complex.chainInnerProduct c c' = 1) :
    NQubitPauliGroupElement.Anticommute
      (pair72Complex.chainXOperator c) (pair72Complex.chainZOperator c') := by
  rcases NQubitPauliGroupElement.commute_or_anticommute
    (pair72Complex.chainXOperator c) (pair72Complex.chainZOperator c') with hcomm | ha
  · exfalso
    have hzero := (HomologicalCode.chainXOperator_commutes_chainZOperator_iff c c').mp hcomm
    rw [h] at hzero
    exact one_ne_zero hzero
  · exact ha

/-- An X-chain and a Z-chain operator commute when their inner product is `0`
(chains abstract). -/
lemma chainXOperator_commute_chainZOperator (c c' : pair72Complex.C1 → ZMod 2)
    (h : pair72Complex.chainInnerProduct c c' = 0) :
    pair72Complex.chainXOperator c * pair72Complex.chainZOperator c'
      = pair72Complex.chainZOperator c' * pair72Complex.chainXOperator c :=
  (HomologicalCode.chainXOperator_commutes_chainZOperator_iff c c').mpr h

/-- Indicator chain of the `i`-th X-logical support. -/
def logXchain (i : Fin 4) : G72 × Fin 2 → ZMod 2 :=
  fun e => if e ∈ logX.getD i.val [] then 1 else 0

/-- Indicator chain of the `i`-th Z-logical support. -/
def logZchain (i : Fin 4) : G72 × Fin 2 → ZMod 2 :=
  fun e => if e ∈ logZ.getD i.val [] then 1 else 0

/-- Computable form of `dualBoundary` on a 1-chain: the transpose of `∂₂`. -/
def dualBfn (c : G72 × Fin 2 → ZMod 2) (f : G72) : ZMod 2 :=
  ∑ h : G72, (c (h, 0) * d2term f h 0 + c (h, 1) * d2term f h 1)

lemma dualBoundary_eq_dualBfn (c : G72 × Fin 2 → ZMod 2) (f : G72) :
    pair72Complex.dualBoundary c f = dualBfn c f := by
  rw [HomologicalCode.dualBoundary_apply]
  change (∑ e : G72 × Fin 2,
    c e * pair72Complex.boundary2 (pair72Complex.singleFace f) e) = dualBfn c f
  unfold dualBfn
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [Fin.sum_univ_two, boundary2_singleFace_apply, boundary2_singleFace_apply]

/-- All 4 X-logicals are cycles (`∂₁ = 0`). -/
lemma logXchain_cycle (i : Fin 4) : pair72Complex.boundary1 (logXchain i) = 0 := by
  have h : ∀ k : Fin 4, bbBoundary1Fn a72 b72 (logXchain k) = 0 := by native_decide
  exact h i

/-- All 4 Z-logicals are dual cycles (`dualBoundary = 0`). -/
lemma logZchain_dualCycle (i : Fin 4) : pair72Complex.dualBoundary (logZchain i) = 0 := by
  have h : ∀ k : Fin 4, ∀ f : G72, dualBfn (logZchain k) f = 0 := by native_decide
  funext f
  rw [dualBoundary_eq_dualBfn]
  exact h i f

/-- The `4×4` intersection matrix is the identity. -/
lemma logChain_inner (i j : Fin 4) :
    pair72Complex.chainInnerProduct (logXchain i) (logZchain j) = (if i = j then 1 else 0) := by
  have h : ∀ a b : Fin 4,
      (∑ e : G72 × Fin 2, logXchain a e * logZchain b e) = (if a = b then 1 else 0) := by
    native_decide
  exact h i j

set_option maxRecDepth 4096 in
/-- The `i`-th logical qubit operator pair: the abstract helpers above are simply
*applied* to the concrete chains, so no heavy defeq is re-run here. -/
noncomputable def logicalQubit (i : Fin 4) :
    LogicalQubitOps pair72Complex.numQubits packagedSG where
  xOp := pair72Complex.chainXOperator (logXchain i)
  zOp := pair72Complex.chainZOperator (logZchain i)
  x_mem_centralizer := chainXOperator_mem_centralizer_packagedSG (logXchain i) (logXchain_cycle i)
  z_mem_centralizer :=
    chainZOperator_mem_centralizer_packagedSG (logZchain i) (logZchain_dualCycle i)
  anticommute := chainXOperator_anticommute_chainZOperator (logXchain i) (logZchain i)
    (by rw [logChain_inner i i, if_pos rfl])

set_option maxRecDepth 4096 in
/-- Logical operators for different logical qubits commute (the `4×4` matrix is
diagonal off the diagonal). -/
theorem logical_commute_cross : ∀ ℓ ℓ' : Fin 4, ℓ ≠ ℓ' →
    ((logicalQubit ℓ).xOp * (logicalQubit ℓ').xOp
        = (logicalQubit ℓ').xOp * (logicalQubit ℓ).xOp ∧
      (logicalQubit ℓ).xOp * (logicalQubit ℓ').zOp
        = (logicalQubit ℓ').zOp * (logicalQubit ℓ).xOp ∧
      (logicalQubit ℓ).zOp * (logicalQubit ℓ').xOp
        = (logicalQubit ℓ').xOp * (logicalQubit ℓ).zOp ∧
      (logicalQubit ℓ).zOp * (logicalQubit ℓ').zOp
        = (logicalQubit ℓ').zOp * (logicalQubit ℓ).zOp) := by
  intro ℓ ℓ' hne
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact Quantum.StabilizerGroup.CSSCommutationLemmas.XType_commutes
      (HomologicalCode.chainXOperator_isXType _) (HomologicalCode.chainXOperator_isXType _)
  · exact chainXOperator_commute_chainZOperator (logXchain ℓ) (logZchain ℓ')
      (by rw [logChain_inner ℓ ℓ', if_neg hne])
  · exact (chainXOperator_commute_chainZOperator (logXchain ℓ') (logZchain ℓ)
      (by rw [logChain_inner ℓ' ℓ, if_neg (Ne.symm hne)])).symm
  · exact Quantum.StabilizerGroup.CSSCommutationLemmas.ZType_commutes
      (HomologicalCode.chainZOperator_isZType _) (HomologicalCode.chainZOperator_isZType _)


set_option maxRecDepth 4096 in
/-- The `[[72, 4, 8]]` doubling-cover code as a `StabilizerCode`. -/
noncomputable def pair72StabilizerCode : StabilizerCode pair72Complex.numQubits 4 where
  hk := by rw [pair72Complex_numQubits]; omega
  generatorsList := genListPackaged
  generators_length := by
    have h34 : keptCoords.length = 34 := by decide
    have hn := pair72Complex_numQubits
    rw [genListPackaged_length]; omega
  generators_phaseZero := by
    intro g hg
    rcases List.mem_append.mp (show g ∈ genListZ ++ genListX from hg) with hz | hx
    · obtain ⟨v, _, rfl⟩ := List.mem_map.mp hz
      exact (HomologicalCode.vertexStabOf_isZType v).1
    · obtain ⟨f, _, rfl⟩ := List.mem_map.mp hx
      exact (HomologicalCode.faceStabOf_isXType f).1
  generators_independent := generators_independent_packaged
  generators_commute := gens_commute_packaged
  closure_no_neg_identity := gens_no_neg_packaged
  logicalOps := logicalQubit
  logical_commute_cross := logical_commute_cross

/-- The packaged code's stabilizer subgroup is the pair72 homological stabilizer
subgroup — the bridge that transports the Pauli-level distance theorem. -/
theorem pair72StabilizerCode_toSubgroup_eq :
    pair72StabilizerCode.toStabilizerGroup.toSubgroup
      = pair72Complex.homologicalStabilizerGroup.toSubgroup := by
  change Subgroup.closure (listToSet genListPackaged) = _
  exact closure_packaged_eq

/-- **`HasCodeDistance pair72StabilizerCode 8`** — unconditional.  Transports
the Pauli-level `pair72_pauli_distance_eq_8` (stated against
`pair72Complex.homologicalStabilizerGroup`) through the `toSubgroup` bridge.
Axiom bar: the standard three + `Lean.ofReduceBool`. -/
theorem pair72StabilizerCode_hasCodeDistance_8 :
    HasCodeDistance pair72StabilizerCode 8 := by
  -- ∃-restatement with the layer defs unfolded to the concrete complex
  -- (`coverData.coverComplex = pair72Complex` is `rfl`).
  have hleast : IsLeast {w : ℕ |
      ∃ g : NQubitPauliGroupElement pair72Complex.numQubits,
        IsNontrivialLogicalOperator g pair72Complex.homologicalStabilizerGroup ∧
        NQubitPauliGroupElement.weight g = w} 8 := pair72_pauli_distance_eq_8
  refine ⟨by norm_num, ?_, ?_⟩
  · intro g hg _
    exact hleast.2 ⟨g, (IsNontrivialLogicalOperator_of_toSubgroup_eq g
      pair72StabilizerCode_toSubgroup_eq).mp hg, rfl⟩
  · obtain ⟨g, hg, hw⟩ := hleast.1
    exact ⟨g, (IsNontrivialLogicalOperator_of_toSubgroup_eq g
      pair72StabilizerCode_toSubgroup_eq).mpr hg, hw⟩

/-- **The `[[72, 4, 8]]` doubling-cover code as a fully-parametrized object** —
the S3.9 deliverable.  Bundles the stabilizer code with its unconditional
distance proof into a single `StabilizerCodeWithDistance` carrying all three
`[[n, k, d]]` parameters in its type. -/
noncomputable def pair72StabilizerCodeWithDistance :
    Quantum.StabilizerGroup.StabilizerCodeWithDistance 72 4 8 where
  toStabilizerCode := pair72StabilizerCode
  hasDistance := pair72StabilizerCode_hasCodeDistance_8

end Quantum.Stabilizer.Homological.BB.Z3Z6
