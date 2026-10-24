import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.BottomForestSound
import QEC.Stabilizer.Framework.Homological.Certificate.BatchListBinary
import QEC.Stabilizer.Framework.Homological.Certificate.PackedPopcount

noncomputable section
namespace Quantum.Stabilizer.Homological.BB.Bravyi360.BottomForest
open F2Mask FiberData PackedDigits

/-- A checked forest record has the claimed full right-hand-side bound. -/
theorem fiberCheck_rhs (r : Fiber) (h : fiberCheck r = true) : r.rhs < 2^90 := by
  simp only [fiberCheck,Bool.and_eq_true,Nat.blt_eq,and_assoc] at h
  exact h.2.2.1

/-- A checked forest record has its claimed exact shadow weight. -/
theorem fiberCheck_weight (r : Fiber) (h : fiberCheck r = true) : bitCount 90 r.beta = r.weight := by
  have hb := fiberCheck_beta r h
  simp only [fiberCheck,Bool.and_eq_true,Nat.beq_eq,and_assoc] at h
  have hw := h.2.1
  rw [bitCountFast_eq] at hw
  have he := bitCount_extend 90 6 r.beta hb
  rw [he] at hw
  exact hw

/-- Every record in a checked chunk passes its own structural checker. -/
theorem groupCheck_member (rs : List Fiber) (h : groupCheck rs = true) :
    ∀ r ∈ rs, fiberCheck r = true := by
  simp only [groupCheck,Bool.and_eq_true,List.all_eq_true,and_assoc] at h
  exact h.1

/-- Both full base matrices fit in the parallel256-bit representation. -/
theorem full_columns_fit :
    (∀ p ∈ bottomEColumns, p.1 < 256 ∧ p.2 < 2^256) ∧
    (∀ p ∈ bottomRColumns, p.1 < 256 ∧ p.2 < 2^256) := by
  constructor
  · intro p hp
    exact ⟨lt_trans (bottomEAdjoint_bounds.1 p hp) (by decide),
      lt_trans (bottomEColumns_bounded p hp) (by norm_num)⟩
  · intro p hp
    exact ⟨lt_trans (bottomRAdjoint_bounds.1 p hp) (by decide),
      lt_trans (bottomRColumns_bounded p hp) (by norm_num)⟩

/-- Both bottom-sheet embeddings fit the parallel256-bit representation. -/
theorem join_columns_fit :
    (∀ p ∈ bottomLeft, p.1 < 256 ∧ p.2 < 2^256) ∧
    (∀ p ∈ bottomRight, p.1 < 256 ∧ p.2 < 2^256) := by decide +kernel

/-- All full-E map entries of a checked chunk are bounded. -/
theorem ePairs_bound (rs : List Fiber) (h : groupCheck rs = true) :
    ∀ p ∈ ePairs rs, p.1 < 2^256 ∧ p.2 < 2^256 := by
  have hd := groupCheck_member rs h
  intro p hp
  obtain ⟨r,hr,hp⟩ := List.mem_flatMap.mp hp
  have hc := hd r hr
  have lift : ∀ x, x < 2^90 → x < 2^256 := fun x hx => hx.trans (by norm_num)
  rcases List.mem_cons.mp hp with rfl | hp
  · exact ⟨lift _ (fiberCheck_beta r hc),by norm_num⟩
  · rcases List.mem_append.mp hp with hp | hp
    · obtain ⟨c,hcm,rfl⟩ := List.mem_map.mp hp
      have hcp := fiberCheck_components r hc c hcm
      have hb : c.word < 2^90 := by
        rw [← hcp.2.2.1]
        exact lt_of_le_of_lt Nat.and_le_right (fiberCheck_beta r hc)
      exact ⟨lift _ hb,lift _ hcp.2.1⟩
    · obtain ⟨s,hsm,rfl⟩ := List.mem_map.mp hp
      exact ⟨lift _ (fiberCheck_seed r hc s hsm).1,lift _ (fiberCheck_rhs r hc)⟩

/-- Every full-E map entry in a checked chunk has its stated image. -/
theorem ePairs_sound (rs : List Fiber) (h : groupCheck rs = true) :
    ∀ p ∈ ePairs rs, reconX bottomEColumns p.1 = p.2 := by
  have hm : mapCheck bottomEColumns (ePairs rs) = true := by
    have hh := h
    simp only [groupCheck,Bool.and_eq_true,and_assoc] at hh
    exact hh.2.1
  unfold mapCheck at hm
  exact reconstruction_list_sound 256 _ (by decide) (ePairs_bound rs h)
    bottomEColumns full_columns_fit.1 (Nat.beq_eq.mp hm)

/-- Every shadow in a checked chunk has its stated full-R image. -/
theorem rPairs_sound (rs : List Fiber) (h : groupCheck rs = true) :
    ∀ r ∈ rs, reconX bottomRColumns r.beta = r.rhs := by
  have hd := groupCheck_member rs h
  have hm : mapCheck bottomRColumns (rPairs rs) = true := by
    have hh := h
    simp only [groupCheck,Bool.and_eq_true,and_assoc] at hh
    exact hh.2.2.1
  have hb : ∀ p ∈ rPairs rs, p.1 < 2^256 ∧ p.2 < 2^256 := by
    intro p hp
    obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hp
    exact ⟨(fiberCheck_beta r (hd r hr)).trans (by norm_num),
      (fiberCheck_rhs r (hd r hr)).trans (by norm_num)⟩
  have he := reconstruction_list_sound 256 _ (by decide) hb bottomRColumns
    full_columns_fit.2 (Nat.beq_eq.mp hm)
  intro r hr
  exact he _ (List.mem_map.mpr ⟨r,hr,rfl⟩)

/-- The checked parallel joins connect every recorded target to the common top bank. -/
theorem joinTriples_sound (rs : List Fiber) (h : groupCheck rs = true) :
    ∀ t ∈ joinTriples rs, bottomJoin t.1 t.2.1 = t.2.2 := by
  have hd := groupCheck_member rs h
  have hm : joinsCheck (joinTriples rs) = true := by
    have hh := h
    simp only [groupCheck,Bool.and_eq_true,and_assoc] at hh
    exact hh.2.2.2
  have hb : ∀ t ∈ joinTriples rs, t.1 < 2^90 ∧ t.2.1 < 2^90 ∧ t.2.2 < 2^180 := by
    intro t ht
    obtain ⟨r,hr,ht⟩ := List.mem_flatMap.mp ht
    obtain ⟨s,hs,ht⟩ := List.mem_flatMap.mp ht
    obtain ⟨u,hu,rfl⟩ := List.mem_map.mp ht
    exact ⟨((fiberCheck_seed r (hd r hr) s hs).2.2.1 u hu).1,
      fiberCheck_beta r (hd r hr),topBankMask_lt u.2⟩
  apply binary_reconstruction_list_sound 256 (joinTriples rs) Prod.fst
    (fun t => t.1 ^^^ t.2.1) (fun t => t.2.2) (by decide)
    (fun t ht => (hb t ht).1.trans (by norm_num))
    (fun t ht => (Nat.xor_lt_two_pow (hb t ht).1 (hb t ht).2.1).trans (by norm_num))
    (fun t ht => (hb t ht).2.2.trans (by norm_num)) bottomLeft bottomRight
    join_columns_fit.1 join_columns_fit.2
  exact Nat.beq_eq.mp hm

/-- A checked forest chunk classifies every solution whose outside support is listed. -/
theorem group_solution_bank (rs : List Fiber) (h : groupCheck rs = true)
    (r : Fiber) (hr : r ∈ rs) (word : Nat)
    (he : reconX bottomEColumns word = reconX bottomRColumns r.beta)
    (hoff : outsideMask word r.beta ∈ r.seeds.map Seed.off) :
    ∃ j : Fin 58130, bottomJoin word r.beta = topBankMask j ∨
      bottomJoin (word ^^^ r.beta) r.beta = topBankMask j := by
  have hc := groupCheck_member rs h r hr
  have hE := ePairs_sound rs h
  have hR := rPairs_sound rs h r hr
  have hcm : ∀ c ∈ r.components, reconX bottomEColumns c.word = c.image := by
    intro c hcm
    apply hE (c.word,c.image)
    exact List.mem_flatMap.mpr ⟨r,hr,List.mem_cons.mpr (Or.inr (List.mem_append.mpr (Or.inl (List.mem_map.mpr ⟨c,hcm,rfl⟩))))⟩
  obtain ⟨s,hs,hso⟩ := List.mem_map.mp hoff
  have hseed : reconX bottomEColumns s.word = r.rhs := by
    apply hE (s.word,r.rhs)
    exact List.mem_flatMap.mpr ⟨r,hr,List.mem_cons.mpr (Or.inr (List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨s,hs,rfl⟩))))⟩
  have ht := solution_target r hc hcm s hs hseed word (he.trans hR) hso.symm
  obtain ⟨t,ht,htw⟩ := ht
  have hti := ((fiberCheck_seed r hc s hs).2.2.1 t ht).2
  have hj := joinTriples_sound rs h (t.1,r.beta,topBankMask t.2)
    (List.mem_flatMap.mpr ⟨r,hr,List.mem_flatMap.mpr ⟨s,hs,List.mem_map.mpr ⟨t,ht,rfl⟩⟩⟩)
  refine ⟨⟨t.2,hti⟩,?_⟩
  rcases htw with heq | heq
  · exact Or.inl (heq ▸ hj)
  · exact Or.inr (heq ▸ hj)

#print axioms group_solution_bank
end Quantum.Stabilizer.Homological.BB.Bravyi360.BottomForest
