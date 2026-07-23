/-
# A23 seam floor, layer 2: the ≤7-active-site sweep and the core inequality

The δ-data vector `wOf f : WIdx → ZMod 2` of the pair `(e₀ + A⋆f, B⋆f)`
satisfies 64 tabulated affine relations (`rels_hold` — the relations cut
out the realizable affine subspace, rank-certified by the generator).
The **sweep theorem** (`sweep_bound`): every `w` satisfying the relations
has site-cost sum ≥ 16.  Proof: if ≥ 8 sites are active, each costs ≥ 2;
otherwise the active sitemask `m` has a tabulated certificate:

* **inconsistency** (16,084 masks): a row combination of the relations
  supported off the active sites with constant sum 1 — no such `w`
  exists (`consSound`/`inconsSound`);
* **classification** (300 masks): RREF pivot certificates prove every
  solution is `particular + span(extras)` (δ-normalized, `k ≤ 4`), and
  all `2^k` representatives have cost ≥ 16 (`c8`).

Combined with the per-site bound of `SeamFiber.lean` this yields the
**core inequality** `core_ineq : 16 ≤ |e₀ + A⋆f| + |B⋆f|` — the
final form of the seam-coset floor (A23 §6).  Certificate provenance:
`qec-lab:experiments/bb_lab/scripts/a23_gen_seam_sweep.py` (independent
verification pass mirroring `checkCertAt`).
-/

import QEC.Stabilizer.Codes.BivariateBicycle.Z5Z15F2A6.SeamFiber

namespace Quantum
namespace Stabilizer
namespace Homological
namespace BB
namespace Z5Z15F2A6

open scoped BigOperators

set_option maxRecDepth 4096

/-! ## Relation evaluation -/

/-- The `j`-th relation mask. -/
def relMaskAt (j : ℕ) : ℕ := RELM.getD j 0

/-- The `j`-th relation constant (packed in `RELCONSTS`). -/
def relConst (j : ℕ) : ZMod 2 := if RELCONSTS.testBit j then 1 else 0

/-- Pairing of a 120-bit mask against a δ-data vector. -/
def evalMaskF (x : ℕ) (w : WIdx → ZMod 2) : ZMod 2 :=
  ∑ p : WIdx, if x.testBit (widxNat p) then w p else 0

/-- XOR of the relation masks selected by `sel`. -/
def foldXorSel (sel : ℕ) : ℕ :=
  (List.range 64).foldl
    (fun acc j => if sel.testBit j then acc ^^^ relMaskAt j else acc) 0

/-- Sum of the relation constants selected by `sel`. -/
def selConstSum (sel : ℕ) : ZMod 2 :=
  ∑ j ∈ Finset.range 64, if sel.testBit j then relConst j else 0

/-- δ-data vector of a packed 120-bit mask. -/
def wFunOf (x : ℕ) : WIdx → ZMod 2 := fun p =>
  if x.testBit (widxNat p) then 1 else 0

/-! ## `evalMaskF` algebra -/

lemma evalMaskF_add (x : ℕ) (w₁ w₂ : WIdx → ZMod 2) :
    evalMaskF x (fun p => w₁ p + w₂ p) = evalMaskF x w₁ + evalMaskF x w₂ := by
  rw [evalMaskF, evalMaskF, evalMaskF, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  by_cases h : x.testBit (widxNat p)
  · rw [if_pos h, if_pos h, if_pos h]
  · rw [if_neg h, if_neg h, if_neg h, add_zero]

lemma evalMaskF_smul (x : ℕ) (c : ZMod 2) (w : WIdx → ZMod 2) :
    evalMaskF x (fun p => c * w p) = c * evalMaskF x w := by
  rw [evalMaskF, evalMaskF, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  by_cases h : x.testBit (widxNat p)
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h, mul_zero]

lemma evalMaskF_zero_w (x : ℕ) :
    evalMaskF x (fun _ => (0 : ZMod 2)) = 0 := by
  refine Finset.sum_eq_zero fun p _ => ?_
  split <;> rfl

lemma evalMaskF_mask_zero (w : WIdx → ZMod 2) : evalMaskF 0 w = 0 := by
  refine Finset.sum_eq_zero fun p _ => ?_
  rw [Nat.zero_testBit, if_neg Bool.false_ne_true]

lemma evalMaskF_xor (a b : ℕ) (w : WIdx → ZMod 2) :
    evalMaskF (a ^^^ b) w = evalMaskF a w + evalMaskF b w := by
  rw [evalMaskF, evalMaskF, evalMaskF, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Nat.testBit_xor]
  rcases ha : a.testBit (widxNat p) <;> rcases hb : b.testBit (widxNat p)
  · simp
  · simp
  · simp
  · simp [CharTwo.add_self_eq_zero]

/-- Expansion of a fold-XOR pairing as the sum of selected relation
pairings. -/
lemma foldXor_eval (sel : ℕ) (w : WIdx → ZMod 2) :
    evalMaskF (foldXorSel sel) w
      = ∑ j ∈ Finset.range 64,
          if sel.testBit j then evalMaskF (relMaskAt j) w else 0 := by
  have key : ∀ n : ℕ,
      evalMaskF ((List.range n).foldl
        (fun acc j => if sel.testBit j then acc ^^^ relMaskAt j else acc) 0) w
      = ∑ j ∈ Finset.range n,
          if sel.testBit j then evalMaskF (relMaskAt j) w else 0 := by
    intro n
    induction n with
    | zero => simpa using evalMaskF_mask_zero w
    | succ n ih =>
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
        Finset.sum_range_succ, ← ih]
      by_cases h : sel.testBit n
      · rw [if_pos h, if_pos h, evalMaskF_xor]
      · rw [if_neg h, if_neg h, add_zero]
  exact key 64

/-- Under the relation hypotheses, selected pairings sum to the selected
constants. -/
lemma sum_relEval_eq (sel : ℕ) (w : WIdx → ZMod 2)
    (hrels : ∀ j : Fin 64, evalMaskF (relMaskAt j.val) w = relConst j.val) :
    (∑ j ∈ Finset.range 64,
        if sel.testBit j then evalMaskF (relMaskAt j) w else 0)
      = selConstSum sel := by
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj64 : j < 64 := Finset.mem_range.mp hj
  by_cases h : sel.testBit j
  · rw [if_pos h, if_pos h]
    exact hrels ⟨j, hj64⟩
  · rw [if_neg h, if_neg h]

/-! ## The certificate checker -/

/-- Sitemask of an active-site set. -/
def maskNat (S : Finset Sites) : ℕ := ∑ s ∈ S, 2 ^ siteIdx s

/-- Inconsistency certificate check: the selected row combination is
supported off the active sites and its constants sum to 1. -/
def checkIncons (m : ℕ) : Bool :=
  decide (ROWSEL.getD m 0 ≠ 0) &&
  decide (∀ p : WIdx, (foldXorSel (ROWSEL.getD m 0)).testBit (widxNat p) →
    m.testBit (siteIdx p.1) = false) &&
  decide (selConstSum (ROWSEL.getD m 0) = 1)

/-- Kernel extra `c` of consistent certificate `i`. -/
def cexAt (i : ℕ) (c : Fin 4) : ℕ :=
  if c.val = 0 then CEX0.getD i 0
  else if c.val = 1 then CEX1.getD i 0
  else if c.val = 2 then CEX2.getD i 0
  else CEX3.getD i 0

/-- Free coordinate `c` of consistent certificate `i`. -/
def cfrAt (i : ℕ) (c : Fin 4) : ℕ :=
  if c.val = 0 then CFR0.getD i 0
  else if c.val = 1 then CFR1.getD i 0
  else if c.val = 2 then CFR2.getD i 0
  else CFR3.getD i 0

/-- The `τ`-repricing of consistent certificate `i`:
`particular + Σ τ_c · extra_c`. -/
def candFun (i : ℕ) (τ : Fin 4 → ZMod 2) : WIdx → ZMod 2 := fun p =>
  wFunOf (CPART.getD i 0) p + ∑ c : Fin 4, τ c * wFunOf (cexAt i c) p

/-- Site-cost sum of a δ-data vector. -/
def costSum (w : WIdx → ZMod 2) : ℕ :=
  ∑ s : Sites, siteCost (tU w s) (tV w s)

/-- Classification certificate check for sitemask `m`, cons index `i`. -/
def checkConsAt (m i : ℕ) : Bool :=
  -- (c1) particular supported on the active sites, satisfying the relations
  decide (∀ p : WIdx, (CPART.getD i 0).testBit (widxNat p) →
    m.testBit (siteIdx p.1) = true) &&
  decide (∀ j : Fin 64,
    evalMaskF (relMaskAt j.val) (wFunOf (CPART.getD i 0)) = relConst j.val) &&
  -- (c3) extras: on-site support, homogeneous, zero beyond `k`
  decide (∀ c : Fin 4, c.val < CK.getD i 0 →
    ∀ p : WIdx, (cexAt i c).testBit (widxNat p) →
      m.testBit (siteIdx p.1) = true) &&
  decide (∀ c : Fin 4, c.val < CK.getD i 0 →
    ∀ j : Fin 64, evalMaskF (relMaskAt j.val) (wFunOf (cexAt i c)) = 0) &&
  decide (∀ c : Fin 4, CK.getD i 0 ≤ c.val → cexAt i c = 0) &&
  -- (c4) frees: in range and on-site
  decide (∀ c : Fin 4, c.val < CK.getD i 0 → cfrAt i c < 120 ∧
    m.testBit (siteIdx (wIdxOf (cfrAt i c)).1) = true) &&
  -- (c5) δ-normalization of the extras on the frees
  decide (∀ c c' : Fin 4, c.val < CK.getD i 0 → c'.val < CK.getD i 0 →
    (cexAt i c).testBit (cfrAt i c') = decide (c = c')) &&
  -- (c6) coverage: every active coordinate is a pivot or a free
  decide (∀ p : WIdx, m.testBit (siteIdx p.1) = true →
    (∃ t ∈ List.range' (CPOFF.getD i 0) (CPOFF.getD (i + 1) 0 - CPOFF.getD i 0),
      CPIDX.getD t 0 = widxNat p) ∨
    (∃ c : Fin 4, c.val < CK.getD i 0 ∧ cfrAt i c = widxNat p)) &&
  -- (c7) pivot row-combination certificates
  decide (∀ t ∈ List.range' (CPOFF.getD i 0)
      (CPOFF.getD (i + 1) 0 - CPOFF.getD i 0),
    (foldXorSel (CPSEL.getD t 0)).testBit (CPIDX.getD t 0) = true ∧
    (∀ q : WIdx, (foldXorSel (CPSEL.getD t 0)).testBit (widxNat q) →
      m.testBit (siteIdx q.1) = false ∨ widxNat q = CPIDX.getD t 0 ∨
      ∃ c : Fin 4, c.val < CK.getD i 0 ∧ cfrAt i c = widxNat q) ∧
    (∀ c : Fin 4, c.val < CK.getD i 0 →
      (cexAt i c).testBit (CPIDX.getD t 0)
          = (foldXorSel (CPSEL.getD t 0)).testBit (cfrAt i c) ∧
        cfrAt i c ≠ CPIDX.getD t 0)) &&
  -- (c8) all 2^k representatives cost at least 16
  decide (∀ τ : Fin 4 → ZMod 2, 16 ≤ costSum (candFun i τ))

/-- Classification certificate check for sitemask `m`. -/
def checkCons (m : ℕ) : Bool :=
  decide (CIDX.getD m 0 ≠ 0) && checkConsAt m (CIDX.getD m 0 - 1)

/-- Full certificate check for sitemask `m`. -/
def checkCertAt (m : ℕ) : Bool := checkIncons m || checkCons m

/-! ## Soundness of the two certificate kinds -/

/-- An inconsistency certificate rules the mask out entirely. -/
lemma incons_sound (m : ℕ) (hchk : checkIncons m = true)
    (w : WIdx → ZMod 2)
    (hrels : ∀ j : Fin 64, evalMaskF (relMaskAt j.val) w = relConst j.val)
    (hvan : ∀ p : WIdx, m.testBit (siteIdx p.1) = false → w p = 0) :
    False := by
  rw [checkIncons, Bool.and_eq_true, Bool.and_eq_true] at hchk
  obtain ⟨⟨-, hsupp⟩, hconst⟩ := hchk
  rw [decide_eq_true_eq] at hsupp hconst
  have hzero : evalMaskF (foldXorSel (ROWSEL.getD m 0)) w = 0 := by
    refine Finset.sum_eq_zero fun p _ => ?_
    by_cases hb : (foldXorSel (ROWSEL.getD m 0)).testBit (widxNat p)
    · rw [if_pos hb, hvan p (hsupp p hb)]
    · rw [if_neg hb]
  rw [foldXor_eval, sum_relEval_eq _ w hrels, hconst] at hzero
  exact one_ne_zero hzero


/-! ## Soundness of the classification certificates

For a `w` vanishing off the certificate's sites, the *residual*
`v := (w + particular) + Σ_c tvec_c · extra_c` (with `tvec` the values of
`w + particular` at the free coordinates) vanishes identically: off-site
by support, at frees by δ-normalization, at pivots by the row-combination
certificates.  Hence `w` is the `tvec`-repricing, whose cost is checked. -/

/-- The homogeneous difference `w + particular`. -/
def deltaW (i : ℕ) (w : WIdx → ZMod 2) : WIdx → ZMod 2 := fun p =>
  w p + wFunOf (CPART.getD i 0) p

/-- Free-coordinate values of the homogeneous difference. -/
def tvecOf (i : ℕ) (w : WIdx → ZMod 2) : Fin 4 → ZMod 2 := fun c =>
  if _ : c.val < CK.getD i 0 then deltaW i w (wIdxOf (cfrAt i c)) else 0

/-- The residual vector. -/
def residual (i : ℕ) (w : WIdx → ZMod 2) : WIdx → ZMod 2 := fun p =>
  deltaW i w p + ∑ c : Fin 4, tvecOf i w c * wFunOf (cexAt i c) p

/-- `evalMaskF` distributes over a `Fin 4` sum of vectors. -/
lemma evalMaskF_sum4 (x : ℕ) (h : Fin 4 → WIdx → ZMod 2) :
    evalMaskF x (fun p => ∑ c : Fin 4, h c p)
      = ∑ c : Fin 4, evalMaskF x (h c) := by
  have step : ∀ p : WIdx,
      (if x.testBit (widxNat p) then ∑ c : Fin 4, h c p else 0)
        = ∑ c : Fin 4, if x.testBit (widxNat p) then h c p else 0 := by
    intro p
    by_cases hb : x.testBit (widxNat p)
    · rw [if_pos hb]
      exact Finset.sum_congr rfl fun c _ => (if_pos hb).symm
    · rw [if_neg hb]
      exact (Finset.sum_eq_zero fun c _ => if_neg hb).symm
  rw [evalMaskF, Finset.sum_congr rfl fun p _ => step p, Finset.sum_comm]
  rfl

section ConsSound

variable {m i : ℕ} {w : WIdx → ZMod 2}

/-- A classification certificate bounds the cost of every admissible `w`
vanishing off its sites: `w` must be one of the `2^k` tabulated
representatives, all of which were checked to cost ≥ 16. -/
lemma cons_sound (hchk : checkConsAt m i = true)
    (hrels : ∀ j : Fin 64, evalMaskF (relMaskAt j.val) w = relConst j.val)
    (hvan : ∀ p : WIdx, m.testBit (siteIdx p.1) = false → w p = 0) :
    16 ≤ costSum w := by
  rw [checkConsAt] at hchk
  repeat rw [Bool.and_eq_true] at hchk
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨c1, c2⟩, c3s⟩, c3r⟩, c3z⟩, c4⟩, c5⟩, c6⟩, c7⟩, c8⟩ := hchk
  rw [decide_eq_true_eq] at c1 c2 c3s c3r c3z c4 c5 c6 c7 c8
  -- the homogeneous difference satisfies the homogeneous relations
  have hdrels : ∀ j : Fin 64, evalMaskF (relMaskAt j.val) (deltaW i w) = 0 := by
    intro j
    have h := evalMaskF_add (relMaskAt j.val) w (wFunOf (CPART.getD i 0))
    rw [show evalMaskF (relMaskAt j.val) (deltaW i w)
        = evalMaskF (relMaskAt j.val)
            (fun p => w p + wFunOf (CPART.getD i 0) p) from rfl,
      h, hrels j, c2 j, CharTwo.add_self_eq_zero]
  -- ... and so does the residual
  have hvrels : ∀ j : Fin 64, evalMaskF (relMaskAt j.val) (residual i w) = 0 := by
    intro j
    have h := evalMaskF_add (relMaskAt j.val) (deltaW i w)
      (fun p => ∑ c : Fin 4, tvecOf i w c * wFunOf (cexAt i c) p)
    rw [show evalMaskF (relMaskAt j.val) (residual i w)
        = evalMaskF (relMaskAt j.val)
            (fun p => deltaW i w p
              + ∑ c : Fin 4, tvecOf i w c * wFunOf (cexAt i c) p) from rfl,
      h, hdrels j, zero_add,
      evalMaskF_sum4 (relMaskAt j.val)
        (fun c p => tvecOf i w c * wFunOf (cexAt i c) p)]
    refine Finset.sum_eq_zero fun c _ => ?_
    rw [evalMaskF_smul]
    by_cases hck : c.val < CK.getD i 0
    · rw [c3r c hck j, mul_zero]
    · rw [show tvecOf i w c = 0 from dif_neg hck, zero_mul]
  -- extras vanish off the active sites (and beyond `k`)
  have hex_off : ∀ (c : Fin 4) (p : WIdx), m.testBit (siteIdx p.1) = false →
      wFunOf (cexAt i c) p = 0 := by
    intro c p hp
    by_cases hck : c.val < CK.getD i 0
    · by_cases hb : (cexAt i c).testBit (widxNat p)
      · rw [c3s c hck p hb] at hp
        exact absurd hp (by simp)
      · exact if_neg hb
    · rw [c3z c (Nat.le_of_not_lt hck)]
      exact if_neg (by rw [Nat.zero_testBit]; exact Bool.false_ne_true)
  -- the residual vanishes off the active sites
  have hv_off : ∀ p : WIdx, m.testBit (siteIdx p.1) = false →
      residual i w p = 0 := by
    intro p hp
    have h1 : deltaW i w p = 0 := by
      have hw : w p = 0 := hvan p hp
      have hpart : wFunOf (CPART.getD i 0) p = 0 := by
        by_cases hb : (CPART.getD i 0).testBit (widxNat p)
        · rw [c1 p hb] at hp
          exact absurd hp (by simp)
        · exact if_neg hb
      rw [show deltaW i w p = w p + wFunOf (CPART.getD i 0) p from rfl,
        hw, hpart, add_zero]
    rw [show residual i w p = deltaW i w p
        + ∑ c : Fin 4, tvecOf i w c * wFunOf (cexAt i c) p from rfl,
      h1, zero_add]
    refine Finset.sum_eq_zero fun c _ => ?_
    rw [hex_off c p hp, mul_zero]
  -- the residual vanishes at the free coordinates
  have hv_free : ∀ c₀ : Fin 4, c₀.val < CK.getD i 0 →
      residual i w (wIdxOf (cfrAt i c₀)) = 0 := by
    intro c₀ hc₀
    have hfr120 : cfrAt i c₀ < 120 := (c4 c₀ hc₀).1
    have hwidx : widxNat (wIdxOf (cfrAt i c₀)) = cfrAt i c₀ :=
      widxNat_wIdxOf ⟨cfrAt i c₀, hfr120⟩
    have hsum : (∑ c : Fin 4,
        tvecOf i w c * wFunOf (cexAt i c) (wIdxOf (cfrAt i c₀)))
        = tvecOf i w c₀ := by
      rw [Finset.sum_eq_single c₀]
      · have hbit : (cexAt i c₀).testBit (cfrAt i c₀) = true := by
          rw [c5 c₀ c₀ hc₀ hc₀]
          simp
        rw [show wFunOf (cexAt i c₀) (wIdxOf (cfrAt i c₀))
            = if (cexAt i c₀).testBit (widxNat (wIdxOf (cfrAt i c₀))) then 1
              else 0 from rfl, hwidx, hbit, if_pos rfl, mul_one]
      · intro c _ hc
        by_cases hck : c.val < CK.getD i 0
        · have hbit : (cexAt i c).testBit (cfrAt i c₀) = false := by
            rw [c5 c c₀ hck hc₀]
            simp [hc]
          rw [show wFunOf (cexAt i c) (wIdxOf (cfrAt i c₀))
              = if (cexAt i c).testBit (widxNat (wIdxOf (cfrAt i c₀))) then 1
                else 0 from rfl, hwidx, hbit, if_neg Bool.false_ne_true,
            mul_zero]
        · rw [show tvecOf i w c = 0 from dif_neg hck, zero_mul]
      · intro habs
        exact absurd (Finset.mem_univ c₀) habs
    rw [show residual i w (wIdxOf (cfrAt i c₀))
        = deltaW i w (wIdxOf (cfrAt i c₀))
          + ∑ c : Fin 4, tvecOf i w c * wFunOf (cexAt i c) (wIdxOf (cfrAt i c₀))
        from rfl, hsum, show tvecOf i w c₀ = deltaW i w (wIdxOf (cfrAt i c₀))
        from dif_pos hc₀, CharTwo.add_self_eq_zero]
  -- the residual vanishes everywhere
  have hv_all : ∀ p : WIdx, residual i w p = 0 := by
    intro p
    by_cases hon : m.testBit (siteIdx p.1) = true
    · by_cases hfree : ∃ c : Fin 4, c.val < CK.getD i 0 ∧ cfrAt i c = widxNat p
      · obtain ⟨c₀, hck, hfc⟩ := hfree
        have hp : p = wIdxOf (cfrAt i c₀) := by
          rw [hfc, wIdxOf_widxNat]
        rw [hp]
        exact hv_free c₀ hck
      · rcases c6 p hon with hpiv | hf
        · obtain ⟨t, ht, hidx⟩ := hpiv
          obtain ⟨hbit, hsupp, -⟩ := c7 t ht
          have hz : evalMaskF (foldXorSel (CPSEL.getD t 0)) (residual i w) = 0 := by
            rw [foldXor_eval]
            refine Finset.sum_eq_zero fun j hj => ?_
            by_cases hb : (CPSEL.getD t 0).testBit j
            · rw [if_pos hb]
              exact hvrels ⟨j, Finset.mem_range.mp hj⟩
            · rw [if_neg hb]
          have hsingle : evalMaskF (foldXorSel (CPSEL.getD t 0)) (residual i w)
              = residual i w p := by
            rw [evalMaskF, Finset.sum_eq_single p]
            · rw [hidx] at hbit
              rw [if_pos hbit]
            · intro q _ hqp
              by_cases hbq : (foldXorSel (CPSEL.getD t 0)).testBit (widxNat q)
              · rw [if_pos hbq]
                rcases hsupp q hbq with hoff | hqidx | ⟨c, hck, hfc⟩
                · exact hv_off q hoff
                · exfalso
                  apply hqp
                  have : wIdxOf (widxNat q) = wIdxOf (widxNat p) := by
                    rw [hqidx, hidx]
                  rwa [wIdxOf_widxNat, wIdxOf_widxNat] at this
                · have hq : q = wIdxOf (cfrAt i c) := by
                    rw [hfc, wIdxOf_widxNat]
                  rw [hq]
                  exact hv_free c hck
              · rw [if_neg hbq]
            · intro habs
              exact absurd (Finset.mem_univ p) habs
          rw [hsingle] at hz
          exact hz
        · exact absurd hf hfree
    · exact hv_off p (by simpa using hon)
  -- hence `w` is the `tvec`-repricing, and its cost was checked
  have hw_cand : w = candFun i (tvecOf i w) := by
    funext p
    have h1 : deltaW i w p
        = ∑ c : Fin 4, tvecOf i w c * wFunOf (cexAt i c) p := by
      have hkey : ∀ a b : ZMod 2, a + b = 0 → a = b := by decide
      exact hkey _ _ (hv_all p)
    have h2 : w p = wFunOf (CPART.getD i 0) p + deltaW i w p := by
      have hkey : ∀ a b : ZMod 2, a = b + (a + b) := by decide
      exact hkey (w p) (wFunOf (CPART.getD i 0) p)
    rw [show candFun i (tvecOf i w) p = wFunOf (CPART.getD i 0) p
        + ∑ c : Fin 4, tvecOf i w c * wFunOf (cexAt i c) p from rfl,
      h2, h1]
  rw [hw_cand]
  exact c8 (tvecOf i w)

end ConsSound

/-- **Certificate soundness**: a verified certificate at sitemask `m`
bounds the cost of every relation-satisfying `w` vanishing off `m`. -/
theorem cert_sound (m : ℕ) (hchk : checkCertAt m = true)
    (w : WIdx → ZMod 2)
    (hrels : ∀ j : Fin 64, evalMaskF (relMaskAt j.val) w = relConst j.val)
    (hvan : ∀ p : WIdx, m.testBit (siteIdx p.1) = false → w p = 0) :
    16 ≤ costSum w := by
  rw [checkCertAt, Bool.or_eq_true] at hchk
  rcases hchk with hI | hC
  · exact absurd (incons_sound m hI w hrels hvan) not_false
  · rw [checkCons, Bool.and_eq_true] at hC
    exact cons_sound hC.2 hrels hvan

/-! ## The three global finite checks -/

/-- Sitemask bits decode membership (finite check over all 32,768
subsets). -/
lemma maskNat_testBit : ∀ (S : Finset Sites) (s : Sites),
    (maskNat S).testBit (siteIdx s) = decide (s ∈ S) := by
  native_decide

/-- **Table coverage**: every ≤7-site mask carries a verified
certificate. -/
lemma table_coverage : ∀ S : Finset Sites, S.card ≤ 7 →
    checkCertAt (maskNat S) = true := by
  native_decide

/-! ## The sweep theorem -/

/-- Zero δ-type on both sides means the site's 8 coordinates vanish. -/
lemma coords_zero_of_types_zero (w : WIdx → ZMod 2) (s : Sites)
    (hU : tU w s = 0) (hV : tV w s = 0) (r : Fin 8) : w (s, r) = 0 := by
  by_cases hr : r.val < 4
  · have h := dTypeOf_eq_zero _ hU ⟨r.val, hr⟩
    rwa [show ((s, ⟨r.val, by omega⟩) : WIdx) = (s, r) by
      exact Prod.ext rfl (Fin.ext rfl)] at h
  · have h4 : r.val - 4 < 4 := by omega
    have hval : r.val - 4 + 4 = r.val := by omega
    have h := dTypeOf_eq_zero _ hV ⟨r.val - 4, h4⟩
    rwa [show ((s, ⟨r.val - 4 + 4, by omega⟩) : WIdx) = (s, r) from
      Prod.ext rfl (Fin.ext hval)] at h

/-- **The sweep theorem**: every δ-data vector satisfying the 64
relations has site-cost sum at least 16. -/
theorem sweep_bound (w : WIdx → ZMod 2)
    (hrels : ∀ j : Fin 64, evalMaskF (relMaskAt j.val) w = relConst j.val) :
    16 ≤ costSum w := by
  by_cases hbig : 8 ≤ (Finset.univ.filter fun s : Sites =>
      ¬(tU w s = 0 ∧ tV w s = 0)).card
  · -- at least 8 active sites, each costing ≥ 2
    calc (16 : ℕ)
        ≤ 2 * (Finset.univ.filter fun s : Sites =>
            ¬(tU w s = 0 ∧ tV w s = 0)).card := by omega
      _ = ∑ _s ∈ Finset.univ.filter fun s : Sites =>
            ¬(tU w s = 0 ∧ tV w s = 0), 2 := by
          rw [Finset.sum_const, smul_eq_mul, mul_comm]
      _ ≤ ∑ s ∈ Finset.univ.filter fun s : Sites =>
            ¬(tU w s = 0 ∧ tV w s = 0), siteCost (tU w s) (tV w s) := by
          refine Finset.sum_le_sum fun s hs => ?_
          exact siteCost_active _ _ (Finset.mem_filter.mp hs).2
      _ ≤ costSum w :=
          Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
  · -- at most 7 active sites: dispatch to the tabulated certificate
    have hcard : (Finset.univ.filter fun s : Sites =>
        ¬(tU w s = 0 ∧ tV w s = 0)).card ≤ 7 := by omega
    refine cert_sound _ (table_coverage _ hcard) w hrels fun p hp => ?_
    have hmem := maskNat_testBit
      (Finset.univ.filter fun s : Sites => ¬(tU w s = 0 ∧ tV w s = 0)) p.1
    rw [hp] at hmem
    have hnotin : p.1 ∉ Finset.univ.filter fun s : Sites =>
        ¬(tU w s = 0 ∧ tV w s = 0) := by
      intro hin
      rw [decide_eq_true_eq.mpr hin] at hmem
      exact Bool.false_ne_true hmem
    have htypes : tU w p.1 = 0 ∧ tV w p.1 = 0 := by
      by_contra hcon
      exact hnotin (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcon⟩)
    have h := coords_zero_of_types_zero w p.1 htypes.1 htypes.2 p.2
    rwa [show ((p.1, p.2) : WIdx) = p from rfl] at h

/-! ## The relations hold on every realizable δ-data vector -/

/-- The linear part of the δ-data map. -/
def wLin (f : G150 → ZMod 2) : WIdx → ZMod 2 := fun p =>
  if h : p.2.val < 4 then dcoord (conv a150 f) p.1 ⟨p.2.val, h⟩
  else dcoord (conv b150 f) (p.1 + (1, 0)) ⟨p.2.val - 4, by omega⟩

/-- Closed form of `wLin` on a δ-basis chain (sparse polynomial
lookups — the shape the finite check evaluates). -/
def wLinPt (g : G150) : WIdx → ZMod 2 := fun p =>
  if h : p.2.val < 4 then
    a150 (fpt p.1 (⟨p.2.val, h⟩ : Fin 4).castSucc - g) + a150 (fpt p.1 4 - g)
  else
    b150 (fpt (p.1 + (1, 0)) (⟨p.2.val - 4, by omega⟩ : Fin 4).castSucc - g)
      + b150 (fpt (p.1 + (1, 0)) 4 - g)

lemma dcoord_add (u v : G150 → ZMod 2) (s : Sites) (i : Fin 4) :
    dcoord (u + v) s i = dcoord u s i + dcoord v s i := by
  rw [dcoord, dcoord, dcoord, Pi.add_apply, Pi.add_apply]
  ring

lemma dcoord_zero (s : Sites) (i : Fin 4) :
    dcoord (0 : G150 → ZMod 2) s i = 0 := by
  rw [dcoord]
  rfl

/-- Affine split of the δ-data map. -/
lemma wOf_split (f : G150 → ZMod 2) :
    wOf f = fun p => wOf 0 p + wLin f p := by
  funext p
  rw [wOf, wOf, wLin]
  by_cases h : p.2.val < 4
  · rw [dif_pos h, dif_pos h, dif_pos h, conv_zero_right, add_zero,
      dcoord_add]
  · rw [dif_neg h, dif_neg h, dif_neg h, conv_zero_right, dcoord_zero,
      zero_add]

lemma wLin_add (f₁ f₂ : G150 → ZMod 2) :
    wLin (f₁ + f₂) = fun p => wLin f₁ p + wLin f₂ p := by
  funext p
  rw [wLin, wLin, wLin]
  by_cases h : p.2.val < 4
  · rw [dif_pos h, dif_pos h, dif_pos h, conv_add_right, dcoord_add]
  · rw [dif_neg h, dif_neg h, dif_neg h, conv_add_right, dcoord_add]

lemma wLin_zero : wLin (0 : G150 → ZMod 2) = fun _ => 0 := by
  funext p
  rw [wLin]
  by_cases h : p.2.val < 4
  · rw [dif_pos h, conv_zero_right, dcoord_zero]
  · rw [dif_neg h, conv_zero_right, dcoord_zero]

/-- `conv` against a δ-basis chain is a lookup of the reflected
polynomial. -/
lemma conv_single_right (P : G150 → ZMod 2) (g x : G150) :
    conv P (Pi.single g 1) x = P (x - g) := by
  rw [conv_apply, Finset.sum_eq_single (x - g)]
  · rw [show x - (x - g) = g by abel, Pi.single_eq_same, mul_one]
  · intro h _ hne
    rw [Pi.single_eq_of_ne (fun hc : x - h = g => hne (by rw [← hc]; abel)),
      mul_zero]
  · intro habs
    exact absurd (Finset.mem_univ _) habs

/-- On δ-basis chains, `wLin` is the sparse closed form. -/
lemma wLin_single (g : G150) : wLin (Pi.single g 1) = wLinPt g := by
  funext p
  rw [wLin, wLinPt]
  by_cases h : p.2.val < 4
  · rw [dif_pos h, dif_pos h, dcoord, conv_single_right, conv_single_right]
  · rw [dif_neg h, dif_neg h, dcoord, conv_single_right, conv_single_right]

/-- The relations annihilate the linear part on the δ-basis
(finite check: 64 relations × 75 basis chains). -/
lemma rels_lin_basis : ∀ (j : Fin 64) (g : G150),
    evalMaskF (relMaskAt j.val) (wLinPt g) = 0 := by
  native_decide

/-- The relation constants are the pairings of the affine offset
(finite check). -/
lemma rels_base : ∀ j : Fin 64,
    evalMaskF (relMaskAt j.val) (wOf 0) = relConst j.val := by
  native_decide

/-- **The relations hold on every realizable δ-data vector.** -/
theorem rels_hold (f : G150 → ZMod 2) (j : Fin 64) :
    evalMaskF (relMaskAt j.val) (wOf f) = relConst j.val := by
  have hsplit : evalMaskF (relMaskAt j.val) (wOf f)
      = evalMaskF (relMaskAt j.val) (wOf 0)
        + evalMaskF (relMaskAt j.val) (wLin f) := by
    rw [show wOf f = fun p => wOf 0 p + wLin f p from wOf_split f]
    exact evalMaskF_add _ _ _
  have hlin : evalMaskF (relMaskAt j.val) (wLin f) = 0 := by
    have h := funLiftF2
      (M := fun f : G150 → ZMod 2 => evalMaskF (relMaskAt j.val) (wLin f))
      (N := fun _ : G150 → ZMod 2 => (0 : ZMod 2))
      (by
        show evalMaskF (relMaskAt j.val) (wLin 0) = 0
        rw [wLin_zero]
        exact evalMaskF_zero_w _)
      rfl
      (by
        intro a b
        show evalMaskF (relMaskAt j.val) (wLin (a + b))
          = evalMaskF (relMaskAt j.val) (wLin a)
            + evalMaskF (relMaskAt j.val) (wLin b)
        rw [wLin_add]
        exact evalMaskF_add _ _ _)
      (by
        intro a b
        show (0 : ZMod 2) = 0 + 0
        rw [add_zero])
      (by
        intro g
        show evalMaskF (relMaskAt j.val) (wLin (Pi.single g 1)) = 0
        rw [wLin_single]
        exact rels_lin_basis j g)
      f
    exact h
  rw [hsplit, rels_base j, hlin, add_zero]

/-! ## The core inequality -/

/-- **The A23 core inequality** (`SeamCosetFloor 16` final form, §6):
for every 2-chain `f`, `|e₀ + A⋆f| + |B⋆f| ≥ 16`. -/
theorem core_ineq (f : G150 → ZMod 2) :
    16 ≤ wt150 (e0f + conv a150 f) + wt150 (conv b150 f) :=
  le_trans (sweep_bound (wOf f) (rels_hold f)) (weight_ge_cost_sum f)

end Z5Z15F2A6
end BB
end Homological
end Stabilizer
end Quantum
