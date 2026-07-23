/-
# A22: `lightClassification` — the analytic light-boundary classification

The capstone: `LightClassification` (the 2⁷⁵-quantified certificate
hypothesis of the (M) kernel route, `Classification.lean`) is a
*theorem*.  Proof shape, per the A22 note
(`qec-lab:experiments/bb_lab/notes/A22_analytic_classification.md`):

1. a boundary of weight ≤ 14 has ≤ 7 δ-active sites (each active
   ε-paired site pair weighs ≥ 2 — `active_card_le`);
2. translate so the active set lands in a canonical size-7 orbit rep
   (`shift_all`; the translation `gOfTau` shifts sites without fiber
   rotation);
3. the δ-data, supported in the rep's bytes, is classified by the rep's
   row-combination pivot certificate into an explicit span element
   (`classify`), and the ε-data splits as an in-rep pattern plus at
   most one outside flip (`flip_card_le`, `expand_extract_or`);
4. the packed sweep (`checkA_all`/`checkB_all`) has verified that every
   such (span element, ε-completion) of table weight ≤ 14 reconstructs
   to a tabulated translate of one of the 113 class reps;
5. the σ-bijection reconstructs the boundary from its own codes
   (`recon_eq`), so the sweep's verdict transports back through the
   translation.
-/

import QEC.Stabilizer.Codes.BivariateBicycle.Z5Z15F2A6.LightBridge

namespace Quantum
namespace Stabilizer
namespace Homological
namespace BB
namespace Z5Z15F2A6

open scoped BigOperators

set_option maxRecDepth 4096

/-! ## Small helpers -/

lemma xorGensE_zero (j : ℕ) : xorGensE j 0 = 0 := by
  rw [xorGensE]
  have : ∀ k, xorSelTab (Nat.testBit 0) (genMask j) k = 0 := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      show (if (0 : ℕ).testBit k then genMask j k else 0)
          ^^^ xorSelTab (Nat.testBit 0) (genMask j) k = 0
      rw [Nat.zero_testBit, ih]
      simp
  exact this (nGen j)

lemma expandMask_zero : ∀ sites : List ℕ, expandMask sites 0 = 0 := by
  intro sites
  induction sites with
  | nil => rfl
  | cons s rest ih =>
    show (if (0 : ℕ) % 2 = 1 then 1 <<< s else 0) ||| expandMask rest (0 / 2) = 0
    norm_num
    exact ih

lemma reconFn_zero : reconFn (maskFun15 0) (maskFun120 0) = 0 := by
  funext p
  show reconAt (maskFun15 0) (maskFun120 0) (siteFibOf p)
    = (0 : G150 × Fin 2 → ZMod 2) p
  unfold reconAt σbit
  split <;> simp [maskFun15, maskFun120, Nat.zero_testBit]

lemma translate1_zero_chain (c : G150) :
    translate1 c (0 : G150 × Fin 2 → ZMod 2) = 0 := rfl

lemma translate1_id (v : G150 × Fin 2 → ZMod 2) : translate1 0 v = v := by
  funext p
  show v (p.1 + 0, p.2) = v p
  rw [add_zero]

/-- ε-bit of the packed ε-vector. -/
lemma packH_testBit_site (h : Fin 15 → ZMod 2) (s : Fin 15) :
    (packH h).testBit s.val = decide (h s = 1) := by
  rw [packH, packHUpTo_testBit]
  have hlt : s.val < 15 := s.isLt
  have hha : hAt h s.val = h s := by
    rw [hAt, dif_pos hlt]
  simp [hlt, hha]

/-! ## The per-rep core -/

set_option maxHeartbeats 2000000 in
/-- **Per-rep classification**: a nonzero weight-≤14 boundary whose
δ-active sites lie inside rep `j` is a tabulated translate. -/
theorem rep_classify (j : ℕ) (hj429 : j < 429) (f' : G150 → ZMod 2)
    (hne : bbBoundary2Fn a150 b150 f' ≠ 0)
    (h14 : (Finset.univ.filter fun p : G150 × Fin 2 =>
      bbBoundary2Fn a150 b150 f' p ≠ 0).card ≤ 14)
    (hact : ∀ s : Fin 15, siteActive (bbBoundary2Fn a150 b150 f') s →
      (REP7.getD j 0).testBit s.val = true) :
    ∃ i : Fin 113, ∃ c : G150,
      bbBoundary2Fn a150 b150 f' = translate1 c (repChain i) := by
  set b' := bbBoundary2Fn a150 b150 f' with hbdef
  have hEps' : ∀ s : Fin 15, hV b' s = hU b' s := fun s => hV_boundary_eq_hU f' s
  have hcert : subCertOK j = true := subCert_all ⟨j, hj429⟩
  -- δ-support inside the rep's bytes
  have hsupp : ∀ p : Fin 120, deltaData b' p ≠ 0 → byteBit j p.val = true := by
    intro p hp
    have hsact : siteActive b' ⟨p.val / 8, by omega⟩ := by
      simp only [deltaData] at hp
      split at hp
      · exact Or.inl ⟨⟨p.val % 4, by omega⟩, hp⟩
      · exact Or.inr ⟨⟨p.val % 4, by omega⟩, hp⟩
    exact hact _ hsact
  -- classify the δ-data
  obtain ⟨hydata, helt⟩ := classify j hcert f' hsupp
  rw [← hbdef] at hydata helt
  set e := encFree j (deltaData b') (nGen j) with hedef
  set M := xorGensE j e with hMdef
  -- pack the ε-vector
  set hm := packH (hU b') with hmdef
  have hhm : hU b' = maskFun15 hm := (maskFun15_packH _).symm
  -- packed weight
  have hwt : (Finset.univ.filter fun p : G150 × Fin 2 => b' p ≠ 0).card
      = wtOf M hm := weight_eq_wtOf b' hEps' M hm hydata hhm
  have hwt14 : wtOf M hm ≤ 14 := by
    rw [← hwt]
    exact h14
  -- checkA: e is a survivor (or zero)
  have hesurv : e = 0 ∨ e ∈ survList j := by
    by_cases h0 : e = 0
    · exact Or.inl h0
    · by_cases hc : e ∈ survList j
      · exact Or.inr hc
      · exfalso
        have hA := checkA_all ⟨j, hj429⟩
        rw [checkA, List.all_eq_true] at hA
        have hAe := hA e (List.mem_range.mpr helt)
        have hb0 : (e == 0) = false := by
          rw [beq_eq_false_iff_ne]
          exact h0
        have hbc : (survList j).contains e = false := by
          rcases hcc : (survList j).contains e with _ | _
          · rfl
          · exact absurd (by simpa using hcc : e ∈ survList j) hc
        rw [hb0, hbc, Bool.false_or, Bool.false_or, decide_eq_true_eq] at hAe
        rw [← hMdef] at hAe
        have hle := le_trans (minCost_le_wtOf M hm) hwt14
        omega
  -- ε-decomposition data
  have hlen7 : (siteList j).length = 7 := siteList_length ⟨j, hj429⟩
  set hS := extractS hm (siteList j) with hSdef
  have hS128 : hS < 128 := by
    have := extractS_lt hm (siteList j)
    rwa [hlen7] at this
  have hmbit : ∀ s : Fin 15, hm.testBit s.val = decide (hU b' s = 1) :=
    fun s => packH_testBit_site (hU b') s
  -- outside flip sites
  set F := Finset.univ.filter (fun s : Fin 15 =>
    ¬ (REP7.getD j 0).testBit s.val = true ∧ hm.testBit s.val = true)
    with hFdef
  have hFcard : F.card ≤ 1 := by
    refine le_trans (Finset.card_le_card ?_) (flip_card_le b' hEps' h14)
    intro s hs
    rw [hFdef, Finset.mem_filter] at hs
    rw [Finset.mem_filter]
    obtain ⟨-, hout, hbit⟩ := hs
    refine ⟨Finset.mem_univ _, fun hsa => hout (hact s hsa), ?_⟩
    rw [hmbit s, decide_eq_true_eq] at hbit
    rw [hbit]
    norm_num
  have hmlt : hm < 2 ^ 15 := packH_lt _
  -- byte-vanishing of the span element outside the rep
  have hMout : ∀ os : ℕ, os < 15 →
      (REP7.getD j 0).testBit os = false →
      ∀ n, n < 8 → M.testBit (8 * os + n) = false := by
    intro os hos15 hrep n hn
    rcases hMb : M.testBit (8 * os + n) with _ | _
    · rfl
    · exfalso
      have := xorGensE_support j hcert e (8 * os + n) (by omega) hMb
      rw [byteBit] at this
      have hdiv : (8 * os + n) / 8 = os := by omega
      rw [hdiv, hrep] at this
      exact absurd this (by simp)
  -- the site split of the ε-mask
  have hsplitS : ∀ t : Fin 15, hm.testBit t.val = true →
      ¬ (REP7.getD j 0).testBit t.val = true → t ∈ F := by
    intro t hbit hout
    rw [hFdef, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hout, hbit⟩
  have hsiteMem : ∀ t : ℕ, t < 15 → (REP7.getD j 0).testBit t = true →
      t ∈ siteList j := by
    intro t ht15 hrep
    rw [siteList, List.mem_filter]
    exact ⟨List.mem_range.mpr ht15, hrep⟩
  -- the reconstruction identity for b'
  have hrecon : b' = reconFn (maskFun15 hm) (maskFun120 M) := by
    rw [← hhm, ← hydata]
    exact recon_eq b' hEps'
  -- membership consumption (shared ending)
  have hfinish : memberTT (reconPack hm M) = true →
      ∃ i : Fin 113, ∃ c : G150, b' = translate1 c (repChain i) := by
    intro hmem
    obtain ⟨i, c, hic⟩ := memberTT_translate hmem
    refine ⟨i, c, ?_⟩
    rw [reconPack, ← hrecon, maskFun150_packChain] at hic
    exact hic
  -- e-membership in the checkB outer list
  have hemem : e ∈ (0 : ℕ) :: survList j := by
    rcases hesurv with h | h
    · rw [h]
      exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ h
  have hB := checkB_all ⟨j, hj429⟩
  rw [checkB, List.all_eq_true] at hB
  have hBe := hB e hemem
  simp only [List.all_eq_true, Bool.and_eq_true] at hBe
  have hBhS := hBe hS (List.mem_range.mpr hS128)
  -- split on the outside-flip cases
  rcases Finset.eq_empty_or_nonempty F with hFe | hFne
  · -- no outside flip: hm = expandMask (siteList j) hS
    have hexp : expandMask (siteList j) hS = hm := by
      have h0 := expand_extract_or hm (siteList j) 0 hmlt ?_ (Or.inl rfl)
      · rw [Nat.or_zero] at h0
        exact h0
      · intro t ht15 hbit
        by_cases hrep : (REP7.getD j 0).testBit t = true
        · exact Or.inl (hsiteMem t ht15 hrep)
        · exfalso
          have := hsplitS ⟨t, ht15⟩ hbit hrep
          rw [hFe] at this
          exact absurd this (Finset.notMem_empty _)
    have hw' : ¬ (14 < wtOf M (expandMask (siteList j) hS)) := by
      rw [hexp]
      omega
    have hpart1 := hBhS.1
    rw [if_neg hw'] at hpart1
    by_cases hz : (e == 0 && hS == 0) = true
    · exfalso
      rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at hz
      apply hne
      have hhm0 : hm = 0 := by
        rw [← hexp, hz.2, expandMask_zero]
      show b' = 0
      rw [hrecon, hMdef, hz.1, xorGensE_zero, hhm0]
      exact reconFn_zero
    · rw [if_neg (by simpa using hz)] at hpart1
      exact hfinish (by rwa [hexp] at hpart1)
  · -- one outside flip at `os`
    obtain ⟨os, hosF⟩ := hFne
    have hosdata := hosF
    rw [hFdef, Finset.mem_filter] at hosdata
    obtain ⟨-, hosOut, hosBit⟩ := hosdata
    have hFsingle : ∀ t : Fin 15, t ∈ F → t = os := by
      intro t ht
      by_contra hne'
      have h2 : ({t, os} : Finset (Fin 15)) ⊆ F := by
        intro x hx
        rcases Finset.mem_insert.mp hx with h | h
        · rwa [h]
        · rw [Finset.mem_singleton.mp h]
          exact hosF
      have hc2 : ({t, os} : Finset (Fin 15)).card = 2 := by
        rw [Finset.card_insert_of_notMem
          (by simp [Finset.mem_singleton, hne'] : t ∉ ({os} : Finset (Fin 15))),
          Finset.card_singleton]
      have hle := Finset.card_le_card h2
      rw [hc2] at hle
      omega
    have hosrep : (REP7.getD j 0).testBit os.val = false := by
      rcases hb : (REP7.getD j 0).testBit os.val with _ | _
      · rfl
      · exact absurd hb hosOut
    -- hm splits as in-rep pattern OR the outside bit
    have hexp : expandMask (siteList j) hS ||| 1 <<< os.val = hm := by
      refine expand_extract_or hm (siteList j) (1 <<< os.val) hmlt ?_
        (Or.inr ⟨os.val, os.isLt, rfl, hosBit, ?_⟩)
      · intro t ht15 hbit
        by_cases hrep : (REP7.getD j 0).testBit t = true
        · exact Or.inl (hsiteMem t ht15 hrep)
        · have hmem := hsplitS ⟨t, ht15⟩ hbit hrep
          have := hFsingle _ hmem
          refine Or.inr ⟨by rw [← this], ?_⟩
          have htos : t = os.val := by
            rw [← this]
          rw [htos]
          apply Nat.eq_of_testBit_eq
          intro i
          simp only [Nat.testBit_and, Nat.one_shiftLeft, Nat.testBit_two_pow]
          by_cases hi : os.val = i
          · subst hi
            simp [hosBit]
          · simp [hi]
      · intro hmem
        rw [siteList, List.mem_filter] at hmem
        rw [hosrep] at hmem
        exact absurd hmem.2 (by simp)
    -- expandMask has no bit at os
    have hexpos : (expandMask (siteList j) hS).testBit os.val = false := by
      rw [hSdef, expandMask_extractS_testBit]
      have : decide (os.val ∈ siteList j) = false := by
        rw [decide_eq_false_iff_not]
        intro hmem
        rw [siteList, List.mem_filter, hosrep] at hmem
        exact absurd hmem.2 (by simp)
      rw [this, Bool.and_false]
    -- the +10 weight split
    have hw10 : wtOf M hm = wtOf M (expandMask (siteList j) hS) + 10 := by
      rw [← hexp]
      exact wtOf_or_single M (expandMask (siteList j) hS) os.val os.isLt
        (fun n hn => hMout os.val os.isLt hosrep n hn) hexpos
    have hwIn : ¬ (4 < wtOf M (expandMask (siteList j) hS)) := by omega
    have hpart2 := hBe hS (List.mem_range.mpr hS128) |>.2
    rw [if_neg hwIn, List.all_eq_true] at hpart2
    have hosout : os.val ∈ outList j := by
      rw [outList, List.mem_filter]
      refine ⟨List.mem_range.mpr os.isLt, ?_⟩
      rw [hosrep]
      rfl
    have hmemb := hpart2 os.val hosout
    rw [hexp] at hmemb
    exact hfinish hmemb

/-! ## The main theorem -/

set_option maxHeartbeats 2000000 in
/-- **The light-boundary classification is a theorem**: every nonzero
boundary of the `[[150,8,8]]` base with weight ≤ 14 is a base translate
of one of the 113 tabulated class representatives. -/
theorem lightClassification : LightClassification := by
  intro f hne h14
  set b := bbBoundary2Fn a150 b150 f with hbdef
  have hEps : ∀ s : Fin 15, hV b s = hU b s := fun s => hV_boundary_eq_hU f s
  -- the active mask and its popcount
  set am := packH (fun s => if siteActive b s then 1 else 0) with hamdef
  have hamlt : am < 32768 := packH_lt _
  have hcount : countBits am 15 ≤ 7 := by
    rw [hamdef, countBits_packH_eq_card]
    exact active_card_le b hEps h14
  obtain ⟨hjlt, hshift⟩ := shift_all ⟨am, hamlt⟩ hcount
  set τ : Fin 15 := ⟨shiftAnsGet am % 15, Nat.mod_lt _ (by norm_num)⟩
    with hτdef
  set cτ := gOfTau τ with hcτdef
  set f' := translate cτ f with hf'def
  have hb' : bbBoundary2Fn a150 b150 f' = translate1 cτ b := by
    rw [hf'def, hbdef]
    exact bbBoundary2Fn_translate a150 b150 cτ f
  -- activity bits of the packed mask
  have hambit : ∀ s : Fin 15, am.testBit s.val = decide (siteActive b s) := by
    intro s
    rw [hamdef, packH_testBit_site]
    by_cases hP : siteActive b s
    · simp [hP]
    · simp [hP]
  -- transported hypotheses
  have hne' : bbBoundary2Fn a150 b150 f' ≠ 0 := by
    rw [hb']
    intro h0
    apply hne
    show b = 0
    have hback := congrArg (translate1 (-cτ)) h0
    rw [translate1_comp, add_neg_cancel, translate1_id,
      translate1_zero_chain] at hback
    exact hback
  have h14' : (Finset.univ.filter fun p : G150 × Fin 2 =>
      bbBoundary2Fn a150 b150 f' p ≠ 0).card ≤ 14 := by
    simp only [hb']
    rw [chainWeight_translate1]
    exact h14
  have hact' : ∀ s : Fin 15, siteActive (bbBoundary2Fn a150 b150 f') s →
      (REP7.getD (shiftAnsGet am / 15) 0).testBit s.val = true := by
    intro s hs
    rw [hb'] at hs
    have hsb : siteActive b (siteAdd s τ) := (siteActive_translate b τ s).mp hs
    have hbit : am.testBit (siteAdd s τ).val = true := by
      rw [hambit]
      rw [decide_eq_true_eq]
      exact hsb
    exact hshift s hbit
  obtain ⟨i, c, hic⟩ :=
    rep_classify (shiftAnsGet am / 15) hjlt f' hne' h14' hact'
  refine ⟨i, c + -cτ, ?_⟩
  show b = translate1 (c + -cτ) (repChain i)
  have hback : b = translate1 (-cτ) (bbBoundary2Fn a150 b150 f') := by
    rw [hb', translate1_comp, add_neg_cancel, translate1_id]
  rw [hback, hic, translate1_comp]
