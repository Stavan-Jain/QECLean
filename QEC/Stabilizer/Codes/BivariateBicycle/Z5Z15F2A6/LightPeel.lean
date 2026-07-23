/-
# A22: peel and span classification for the per-rep δ-data systems

The parametric row-combination kernel argument (the `BaseFloorKernel`
pattern transposed into αβ-space): per orbit rep `j`, the certificate is
a pivot list (position, 120-bit W-functional) with the transposed-
syndrome orthogonality check `xorFoldCols W = 0` and RREF triangularity,
plus δ-normalized span generators with `∂₂`-preimages certified through
the packed `rowFold` identity.

* `peel_delta` — a boundary's δ-data supported on the pivot positions of
  a valid certificate vanishes;
* `classify` — a boundary's δ-data supported on the rep's byte positions
  is `maskFun120 (xorGensE j e)` for the free-coordinate code `e < 2^n`.

All certificate conditions are one `Bool` per rep (`subCertOK`),
discharged for all 429 reps by a single `native_decide` in
`LightChecks.lean`.
-/

import QEC.Stabilizer.Codes.BivariateBicycle.Z5Z15F2A6.LightLinear
import QEC.Stabilizer.Codes.BivariateBicycle.Z5Z15F2A6.KernelCert

namespace Quantum
namespace Stabilizer
namespace Homological
namespace BB
namespace Z5Z15F2A6

open scoped BigOperators

set_option maxRecDepth 4096

/-! ## Per-rep data accessors -/

/-- Number of pivots of rep `j`. -/
def nPiv (j : ℕ) : ℕ := SUB_PIV_OFF.getD (j + 1) 0 - SUB_PIV_OFF.getD j 0

/-- Pivot position `k` of rep `j`. -/
def pivPos (j k : ℕ) : ℕ := pivPosGet (SUB_PIV_OFF.getD j 0 + k)

/-- Pivot functional `k` of rep `j`. -/
def pivW (j k : ℕ) : ℕ := pivWGet (SUB_PIV_OFF.getD j 0 + k)

/-- Number of span generators of rep `j`. -/
def nGen (j : ℕ) : ℕ := SUB_GEN_OFF.getD (j + 1) 0 - SUB_GEN_OFF.getD j 0

/-- Free position `i` of rep `j`. -/
def genFree (j i : ℕ) : ℕ := genFreeGet (SUB_GEN_OFF.getD j 0 + i)

/-- Span generator `i` of rep `j` (120-bit). -/
def genMask (j i : ℕ) : ℕ := genMaskGet (SUB_GEN_OFF.getD j 0 + i)

/-- Generator `∂₂`-preimage `i` of rep `j` (75-bit). -/
def genPre (j i : ℕ) : ℕ := genPreGet (SUB_GEN_OFF.getD j 0 + i)

/-- Survivor list of rep `j`. -/
def survList (j : ℕ) : List ℕ :=
  (List.range (SUB_SURV_OFF.getD (j + 1) 0 - SUB_SURV_OFF.getD j 0)).map
    fun k => survGet (SUB_SURV_OFF.getD j 0 + k)

/-- The pivot list of rep `j`. -/
def pivList (j : ℕ) : List (ℕ × ℕ) :=
  (List.range (nPiv j)).map fun k => (pivPos j k, pivW j k)

/-- Byte membership: position `p` lies over an active site of rep `j`. -/
def byteBit (j p : ℕ) : Bool := (REP7.getD j 0).testBit (p / 8)

/-! ## Certificate checks -/

/-- One pivot step: bounded position, vanishing column fold, own bit set,
later pivots' bits clear. -/
def pivStepOK (pos W : ℕ) (later : List ℕ) : Bool :=
  decide (pos < 120) && (xorFoldCols W == 0) && W.testBit pos
    && later.all fun p' => !(W.testBit p')

/-- The pivot-list check (peel order: head first). -/
def pivListOK : List (ℕ × ℕ) → Bool
  | [] => true
  | (pos, W) :: rest =>
      pivStepOK pos W (rest.map Prod.fst) && pivListOK rest

/-- Generator checks: bounded free positions, packed preimage identity,
support inside the rep's bytes, δ-normalization. -/
def genOK (j : ℕ) : Bool :=
  (List.range (nGen j)).all fun i =>
    decide (genFree j i < 120)
    && (rowFold (genPre j i) == genMask j i)
    && ((List.range 120).all fun p => !(genMask j i).testBit p || byteBit j p)
    && ((List.range (nGen j)).all fun i' =>
          (genMask j i).testBit (genFree j i') == (i == i'))

/-- Coverage: every byte position is a pivot or a free position. -/
def covOK (j : ℕ) : Bool :=
  (List.range 120).all fun p =>
    !(byteBit j p)
    || ((List.range (nPiv j)).any fun k => pivPos j k == p)
    || ((List.range (nGen j)).any fun i => genFree j i == p)

/-- The full per-rep certificate check. -/
def subCertOK (j : ℕ) : Bool := pivListOK (pivList j) && genOK j && covOK j

/-! ## The peel -/

/-- **Peel**: a boundary's δ-data supported on the pivot positions of a
valid certificate is zero. -/
theorem peel_delta (l : List (ℕ × ℕ)) (hl : pivListOK l = true)
    (f : G150 → ZMod 2)
    (hsupp : ∀ p : Fin 120,
      deltaData (bbBoundary2Fn a150 b150 f) p ≠ 0 →
        p.val ∈ l.map Prod.fst) :
    deltaData (bbBoundary2Fn a150 b150 f) = 0 := by
  induction l with
  | nil =>
    funext p
    show deltaData (bbBoundary2Fn a150 b150 f) p = 0
    by_contra hp
    exact List.not_mem_nil (hsupp p hp)
  | cons q rest ih =>
    obtain ⟨pos, W⟩ := q
    have hl' : (pivStepOK pos W (rest.map Prod.fst)
        && pivListOK rest) = true := hl
    rw [Bool.and_eq_true] at hl'
    obtain ⟨hstep, hrest⟩ := hl'
    simp only [pivStepOK, Bool.and_eq_true, List.all_eq_true,
      Bool.not_eq_true', beq_iff_eq, decide_eq_true_eq] at hstep
    obtain ⟨⟨⟨hpos120, hortho⟩, hbit⟩, hlater⟩ := hstep
    set y := deltaData (bbBoundary2Fn a150 b150 f) with hy
    have hpair : pairW W y = 0 := pairW_boundary W hortho f
    have hsingle : pairW W y = y ⟨pos, hpos120⟩ := by
      rw [pairW]
      rw [Finset.sum_eq_single (⟨pos, hpos120⟩ : Fin 120)]
      · rw [if_pos hbit]
      · intro p _ hne
        by_cases hyp : y p = 0
        · rw [hyp]
          split <;> rfl
        · have hmem := hsupp p hyp
          simp only [List.map_cons, List.mem_cons] at hmem
          rcases hmem with h | h
          · exact absurd (Fin.ext h : p = ⟨pos, hpos120⟩) hne
          · rw [hlater p.val h]
            simp
      · intro habs
        exact absurd (Finset.mem_univ _) habs
    have hy0 : y ⟨pos, hpos120⟩ = 0 := by
      rw [← hsingle]
      exact hpair
    refine ih hrest fun p hp => ?_
    have hmem := hsupp p hp
    simp only [List.map_cons, List.mem_cons] at hmem
    rcases hmem with h | h
    · have hpe : p = ⟨pos, hpos120⟩ := Fin.ext h
      rw [hpe] at hp
      exact absurd hy0 hp
    · exact h

/-! ## Free-coordinate encoding -/

/-- Total lookup of αβ-data at a possibly-unbounded position. -/
def yAt (y : Fin 120 → ZMod 2) (p : ℕ) : ZMod 2 :=
  if h : p < 120 then y ⟨p, h⟩ else 0

/-- The free-coordinate code of αβ-data at rep `j` (bit `i` = value at
free position `i`). -/
def encFree (j : ℕ) (y : Fin 120 → ZMod 2) : ℕ → ℕ
  | 0 => 0
  | i + 1 =>
      (if yAt y (genFree j i) = 1 then 1 <<< i else 0) ^^^ encFree j y i

lemma encFree_lt (j : ℕ) (y : Fin 120 → ZMod 2) :
    ∀ k, encFree j y k < 2 ^ k := by
  intro k
  induction k with
  | zero => simp [encFree]
  | succ k ih =>
    show ((if yAt y (genFree j k) = 1 then 1 <<< k else 0)
        ^^^ encFree j y k) < 2 ^ (k + 1)
    have h1 : (if yAt y (genFree j k) = 1 then 1 <<< k else 0) < 2 ^ (k + 1) := by
      split
      · rw [Nat.one_shiftLeft]
        exact Nat.pow_lt_pow_right (by norm_num) (by omega)
      · positivity
    have h2 : encFree j y k < 2 ^ (k + 1) :=
      lt_trans ih (Nat.pow_lt_pow_right (by norm_num) (by omega))
    exact xor_lt_two_pow h1 h2

lemma encFree_testBit (j : ℕ) (y : Fin 120 → ZMod 2) :
    ∀ k i : ℕ, (encFree j y k).testBit i
      = (decide (i < k) && decide (yAt y (genFree j i) = 1)) := by
  intro k
  induction k with
  | zero =>
    intro i
    simp [encFree]
  | succ k ih =>
    intro i
    show ((if yAt y (genFree j k) = 1 then 1 <<< k else 0)
        ^^^ encFree j y k).testBit i = _
    rw [Nat.testBit_xor, ih i]
    by_cases hik : i = k
    · subst hik
      have h2 : ¬ i < i := by omega
      have h3 : i < i + 1 := by omega
      simp only [h2, decide_false, Bool.false_and, Bool.xor_false, h3,
        decide_true, Bool.true_and]
      split
      · next hb => simp [Nat.one_shiftLeft, Nat.testBit_two_pow, hb]
      · next hb => simp [Nat.zero_testBit, hb]
    · have hbit0 : (if yAt y (genFree j k) = 1 then 1 <<< k
          else 0).testBit i = false := by
        split
        · simp [Nat.one_shiftLeft, Nat.testBit_two_pow, Ne.symm hik]
        · simp [Nat.zero_testBit]
      rw [hbit0, Bool.false_xor]
      congr 1
      simp only [decide_eq_decide]
      omega

/-! ## The span fold -/

/-- The packed span element of coefficient code `e` at rep `j`. -/
def xorGensE (j e : ℕ) : ℕ := xorSelTab e.testBit (genMask j) (nGen j)

/-- Unpacked span fold as a sum. -/
lemma maskFun120_xorSelTab (sel : ℕ → Bool) (tab : ℕ → ℕ) (n : ℕ) :
    maskFun120 (xorSelTab sel tab n)
      = ∑ i ∈ Finset.range n,
          (if sel i then maskFun120 (tab i) else 0) := by
  funext p
  rw [Finset.sum_apply]
  show (if (xorSelTab sel tab n).testBit p.val then (1 : ZMod 2) else 0) = _
  rw [xorSelTab_testBit sel tab p.val n]
  refine Finset.sum_congr rfl fun i _ => ?_
  split <;> rfl

/-! ## The classification -/

/-- **Span classification**: a boundary's δ-data supported on the byte
positions of a certified rep is the unpacked span element of its own
free-coordinate code. -/
theorem classify (j : ℕ) (hj : subCertOK j = true)
    (f : G150 → ZMod 2)
    (hsupp : ∀ p : Fin 120,
      deltaData (bbBoundary2Fn a150 b150 f) p ≠ 0 → byteBit j p.val = true) :
    deltaData (bbBoundary2Fn a150 b150 f)
      = maskFun120 (xorGensE j
          (encFree j (deltaData (bbBoundary2Fn a150 b150 f)) (nGen j)))
    ∧ encFree j (deltaData (bbBoundary2Fn a150 b150 f)) (nGen j)
        < 2 ^ nGen j := by
  have hcert := hj
  rw [subCertOK, Bool.and_eq_true, Bool.and_eq_true] at hcert
  obtain ⟨⟨hpivs, hgens⟩, hcov⟩ := hcert
  rw [genOK, List.all_eq_true] at hgens
  have hgen : ∀ i < nGen j,
      genFree j i < 120
      ∧ rowFold (genPre j i) = genMask j i
      ∧ (∀ p < 120, (genMask j i).testBit p = true → byteBit j p = true)
      ∧ (∀ i' < nGen j,
          (genMask j i).testBit (genFree j i') = (i == i')) := by
    intro i hi
    have hthis := hgens i (List.mem_range.mpr hi)
    rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at hthis
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hthis
    rw [decide_eq_true_eq] at h1
    rw [beq_iff_eq] at h2
    rw [List.all_eq_true] at h3 h4
    refine ⟨h1, h2, ?_, ?_⟩
    · intro p hp hbit
      have hor := h3 p (List.mem_range.mpr hp)
      rw [Bool.or_eq_true, Bool.not_eq_true'] at hor
      rcases hor with h | h
      · rw [hbit] at h
        exact absurd h (by simp)
      · exact h
    · intro i' hi'
      have hb4 := h4 i' (List.mem_range.mpr hi')
      rwa [beq_iff_eq] at hb4
  set y := deltaData (bbBoundary2Fn a150 b150 f) with hydef
  refine ⟨?_, encFree_lt j y (nGen j)⟩
  -- the correction chain and its preimage
  set FG : G150 → ZMod 2 :=
    ∑ i ∈ Finset.range (nGen j),
      (if yAt y (genFree j i) = 1 then maskFun75 (genPre j i) else 0)
    with hFG
  have hM0 : deltaData (bbBoundary2Fn a150 b150 (0 : G150 → ZMod 2)) = 0 := by
    rw [bbBoundary2Fn_zero, deltaData_zero]
  have hMadd : ∀ x z : G150 → ZMod 2,
      deltaData (bbBoundary2Fn a150 b150 (x + z))
        = deltaData (bbBoundary2Fn a150 b150 x)
          + deltaData (bbBoundary2Fn a150 b150 z) := by
    intro x z
    rw [bbBoundary2Fn_add, deltaData_add]
  set G : Fin 120 → ZMod 2 :=
    ∑ i ∈ Finset.range (nGen j),
      (if yAt y (genFree j i) = 1 then maskFun120 (genMask j i) else 0)
    with hG
  have hFGdelta : deltaData (bbBoundary2Fn a150 b150 FG) = G := by
    rw [hFG, addMap_sum (fun x => deltaData (bbBoundary2Fn a150 b150 x))
      hM0 hMadd, hG]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hgi := hgen i (List.mem_range.mp hi)
    by_cases hc : yAt y (genFree j i) = 1
    · rw [if_pos hc, if_pos hc, deltaData_boundary_mask, hgi.2.1]
    · rw [if_neg hc, if_neg hc]
      exact hM0
  -- y + G is a boundary's δ-data supported on the pivots
  have hyG : y + G = deltaData (bbBoundary2Fn a150 b150 (f + FG)) := by
    rw [hMadd, hFGdelta, hydef]
  -- support of y + G
  have hGapp : ∀ p : Fin 120, G p
      = ∑ i ∈ Finset.range (nGen j),
          (if yAt y (genFree j i) = 1 then maskFun120 (genMask j i) p
           else 0) := by
    intro p
    rw [hG, Finset.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    split <;> rfl
  have hsupp' : ∀ p : Fin 120, (y + G) p ≠ 0 →
      p.val ∈ (pivList j).map Prod.fst := by
    intro p hp
    by_cases hbyte : byteBit j p.val = true
    · -- inside the rep's bytes: free positions vanish, so p is a pivot
      by_cases hfree : ∃ i < nGen j, genFree j i = p.val
      · exfalso
        obtain ⟨i₀, hi₀, hfp⟩ := hfree
        have hcollapse : G p = (if yAt y (genFree j i₀) = 1 then 1 else 0) := by
          rw [hGapp p]
          rw [Finset.sum_eq_single_of_mem i₀ (List.mem_range.mpr hi₀)]
          · have hbit := (hgen i₀ hi₀).2.2.2 i₀ hi₀
            rw [beq_self_eq_true, hfp] at hbit
            simp only [maskFun120, hbit]
            norm_num
          · intro i hi hne
            have hbit := (hgen i (List.mem_range.mp hi)).2.2.2 i₀ hi₀
            have hne' : (i == i₀) = false := by
              rw [beq_eq_false_iff_ne]
              exact hne
            rw [hne', hfp] at hbit
            simp only [maskFun120, hbit]
            simp
        have hyp : yAt y (genFree j i₀) = y p := by
          rw [hfp, yAt, dif_pos p.isLt]
        have hz : ∀ a : ZMod 2, a + (if a = 1 then (1 : ZMod 2) else 0) = 0 := by
          decide
        apply hp
        show y p + G p = 0
        rw [hcollapse, hyp]
        exact hz (y p)
      · -- covered: p is a pivot position
        rw [covOK, List.all_eq_true] at hcov
        have := hcov p.val (List.mem_range.mpr p.isLt)
        simp only [Bool.or_eq_true, Bool.not_eq_true', List.any_eq_true,
          beq_iff_eq] at this
        rcases this with (h | h) | h
        · rw [hbyte] at h
          exact absurd h (by simp)
        · obtain ⟨k, hk, hpk⟩ := h
          rw [pivList, List.map_map]
          refine List.mem_map.mpr ⟨k, hk, ?_⟩
          exact hpk
        · obtain ⟨i, hi, hip⟩ := h
          exact absurd ⟨i, List.mem_range.mp hi, hip⟩ hfree
    · -- outside the bytes: both y and G vanish
      exfalso
      apply hp
      have hy0 : y p = 0 := by
        by_contra hy
        exact hbyte (hsupp p hy)
      have hG0 : G p = 0 := by
        rw [hGapp p]
        refine Finset.sum_eq_zero fun i hi => ?_
        have hgi := hgen i (List.mem_range.mp hi)
        have hgb : maskFun120 (genMask j i) p = 0 := by
          rw [maskFun120]
          rcases hb : (genMask j i).testBit p.val with _ | _
          · rfl
          · exact absurd (hgi.2.2.1 p.val p.isLt hb) hbyte
        rw [hgb]
        split <;> rfl
      show y p + G p = 0
      rw [hy0, hG0, add_zero]
  have hpeel := peel_delta (pivList j) hpivs (f + FG)
    (by rw [← hyG]; exact hsupp')
  rw [← hyG] at hpeel
  -- conclude y = G
  have hGG : G + G = 0 := by
    funext q
    exact CharTwo.add_self_eq_zero _
  have hyeqG : y = G := by
    have h1 : y + G + G = G := by
      rw [hpeel, zero_add]
    calc y = y + (G + G) := by rw [hGG, add_zero]
      _ = y + G + G := by ring
      _ = G := h1
  -- rewrite G as the packed span fold
  have hspan : maskFun120 (xorGensE j (encFree j y (nGen j))) = G := by
    rw [xorGensE, maskFun120_xorSelTab, hG]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hbitE := encFree_testBit j y (nGen j) i
    have hilt := List.mem_range.mp hi
    rw [hbitE]
    simp only [hilt, decide_true, Bool.true_and]
    rcases hcase : decide (yAt y (genFree j i) = 1) with _ | _
    · have hnc : ¬ yAt y (genFree j i) = 1 := by
        rwa [decide_eq_false_iff_not] at hcase
      rw [if_neg hnc]
      simp
    · have hyc : yAt y (genFree j i) = 1 := by
        rwa [decide_eq_true_eq] at hcase
      rw [if_pos hyc]
      simp
  rw [hspan]
  exact hyeqG

end Z5Z15F2A6
end BB
end Homological
end Stabilizer
end Quantum
