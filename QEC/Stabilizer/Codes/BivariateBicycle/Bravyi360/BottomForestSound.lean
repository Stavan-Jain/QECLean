import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.BottomForestCheck
import QEC.Stabilizer.Framework.Homological.Certificate.MaskRowEval
import QEC.Stabilizer.Framework.Homological.Certificate.TaggedReconstruction
import QEC.Stabilizer.Framework.Homological.Certificate.SearchInitial

noncomputable section

namespace Quantum.Stabilizer.Homological.BB.Bravyi360.BottomForest
open F2Mask FiberData PackedDigits

/-- The selected-row mask contains every named peeling equation. -/
theorem selectedRows_bit (r : Fiber) (c : Component) (hc : c ∈ r.components)
    (q : Nat) (hq : q ∈ c.steps) : (selectedRows r).testBit q = true := by
  have hmem : q ∈ r.components.flatMap (fun c => c.steps) :=
    List.mem_flatMap.mpr ⟨c,hc,hq⟩
  unfold selectedRows
  generalize r.components.flatMap (fun c => c.steps) = qs at *
  induction qs with
  | nil => simp at hmem
  | cons a qs ih =>
    change ((1 <<< a) ||| qs.foldr (fun q s => Nat.lor (Nat.shiftLeft 1 q) s) 0).testBit q = true
    rw [Nat.testBit_or,Nat.shiftLeft_eq,Nat.one_mul,Nat.testBit_two_pow]
    rcases List.mem_cons.mp hmem with he | he
    · subst a; simp
    · rw [ih he]; simp

/-- A forest checker certifies its shadow bound. -/
theorem fiberCheck_beta (r : Fiber) (h : fiberCheck r = true) : r.beta < 2^90 := by
  simp only [fiberCheck,Bool.and_eq_true,Nat.blt_eq,and_assoc] at h
  exact h.1

/-- A forest checker certifies all individual component conditions. -/
theorem fiberCheck_components (r : Fiber) (h : fiberCheck r = true)
    (c : Component) (hc : c ∈ r.components) :
    c.root < 90 ∧ c.image < 2^90 ∧ c.word &&& r.beta = c.word ∧
    c.word &&& rootMask r = 2^c.root ∧ c.image &&& selectedRows r = 0 ∧
    ∀ q ∈ c.steps, q < 90 := by
  simp only [fiberCheck,Bool.and_eq_true,Nat.blt_eq,Nat.beq_eq,List.all_eq_true,and_assoc] at h
  have ht := h.2.2.2.1 c hc
  rw [show Nat.shiftLeft 1 c.root = 2^c.root by
    change (1 <<< c.root) = _
    rw [Nat.shiftLeft_eq,Nat.one_mul]] at ht
  exact ht

/-- A forest checker certifies the complete peeling sequence. -/
theorem fiberCheck_peel (r : Fiber) (h : fiberCheck r = true) :
    peelForestOK (fun q => r.beta &&& bottomERow q) r.beta 0 (forest r) = true := by
  simp only [fiberCheck,Bool.and_eq_true,and_assoc] at h
  exact h.2.2.2.2.1

/-- A forest checker certifies the seed support and its full free-component walk. -/
theorem fiberCheck_seed (r : Fiber) (h : fiberCheck r = true)
    (s : Seed) (hs : s ∈ r.seeds) :
    s.word < 2^90 ∧ outsideMask s.word r.beta = s.off ∧
    (∀ t ∈ s.targets, t.1 < 2^90 ∧ t.2 < 58130) ∧
    candidateOK r.beta s.word s.targets 0 = true ∧
    xorWalk (candidateOK r.beta s.word s.targets) (tags r) r.components.length 0 = true := by
  simp only [fiberCheck,Bool.and_eq_true,Nat.blt_eq,Nat.beq_eq,List.all_eq_true,and_assoc] at h
  exact h.2.2.2.2.2 s hs

/-- Equal outside supports leave a difference supported on the shadow. -/
theorem supported_xor_of_outside_eq (beta a b : Nat)
    (h : outsideMask a beta = outsideMask b beta) :
    (a ^^^ b) &&& beta = a ^^^ b := by
  apply Nat.eq_of_testBit_eq
  intro q
  have hq := congrArg (fun x : Nat => x.testBit q) h
  simp only [outsideMask,Nat.testBit_xor,Nat.testBit_and] at hq ⊢
  cases ha : a.testBit q <;> cases hb : b.testBit q <;> cases hc : beta.testBit q <;> simp_all

/-- Selected forest rows vanish on a word with a zero full syndrome. -/
theorem selected_row_zero (r : Fiber) (value q : Nat) (hq : q < 90)
    (hs : value &&& r.beta = value) (hz : (reconX bottomEColumns value).testBit q = false) :
    cellEval (rowCells 90 (r.beta &&& bottomERow q)) value = 0 := by
  rw [Nat.and_comm r.beta,cellEval_restrict_support _ _ _ _ hs]
  exact cellEval_zero_of_adjoint 90 bottomEColumns bottomETransposeColumns
    bottomETranspose_single bottomEAdjoint_bounds.1
    (fun p hp => (bottomEAdjoint_bounds.2 p hp).1) value (bottomERow q) ⟨q,hq⟩
    (bottomETranspose_point ⟨q,hq⟩) hz

/-- Full-syndrome-zero differences are reconstructed by the checked forest roots. -/
theorem reconstruct_kernel (r : Fiber) (h : fiberCheck r = true)
    (himages : ∀ c ∈ r.components, reconX bottomEColumns c.word = c.image)
    (value : Nat) (hs : value &&& r.beta = value)
    (hz : reconX bottomEColumns value = 0) :
    value = reconX (r.components.map fun c => (c.root,c.word)) value := by
  have hb := fiberCheck_beta r h
  have hrowbound : ∀ q, r.beta &&& bottomERow q < 2^90 :=
    fun q => lt_of_le_of_lt Nat.and_le_left hb
  have hf := forest_reconstruct (fun q => r.beta &&& bottomERow q)
    (fun q => rowCells 90 (r.beta &&& bottomERow q))
    (fun q i => mem_rowCells (hrowbound q) i) (fun q => rowCells_nodup _ _)
    r.beta value (rootMask r) (forest r) (fiberCheck_peel r h)
  suffices hvalue : value = reconX ((forest r).map fun c => (c.1,c.2.1)) value by
    simpa [forest,List.map_map] using hvalue
  apply hf
  · simp [rootMask,forest,List.map_map,Nat.shiftLeft_eq,Function.comp_def]
  · intro c hc
    obtain ⟨d,hd,rfl⟩ := List.mem_map.mp hc
    exact (fiberCheck_components r h d hd).2.2.2.1
  · intro c hc
    obtain ⟨d,hd,rfl⟩ := List.mem_map.mp hc
    exact (fiberCheck_components r h d hd).2.2.1
  · intro c hc q hq d hd
    obtain ⟨cc,hcc,rfl⟩ := List.mem_map.mp hc
    obtain ⟨dd,hdd,rfl⟩ := List.mem_map.mp hd
    have hp := fiberCheck_components r h dd hdd
    apply selected_row_zero r dd.word q ((fiberCheck_components r h cc hcc).2.2.2.2.2 q hq) hp.2.2.1
    rw [himages dd hdd]
    have he := congrArg (fun x : Nat => x.testBit q) hp.2.2.2.2.1
    simpa [Nat.testBit_and,selectedRows_bit r cc hcc q hq] using he
  · exact hs
  · intro c hc q hq
    obtain ⟨cc,hcc,rfl⟩ := List.mem_map.mp hc
    apply selected_row_zero r value q ((fiberCheck_components r h cc hcc).2.2.2.2.2 q hq) hs
    simp [hz]

end Quantum.Stabilizer.Homological.BB.Bravyi360.BottomForest

namespace Quantum.Stabilizer.Homological.BB.Bravyi360.BottomForest
open F2Mask FiberData PackedDigits

/-- Every solution above a listed outside support reaches a checked deck-orbit representative. -/
theorem solution_target (r : Fiber) (h : fiberCheck r = true)
    (himages : ∀ c ∈ r.components, reconX bottomEColumns c.word = c.image)
    (s : Seed) (hs : s ∈ r.seeds) (hseed : reconX bottomEColumns s.word = r.rhs)
    (word : Nat) (he : reconX bottomEColumns word = r.rhs)
    (hoff : outsideMask word r.beta = s.off) :
    ∃ t ∈ s.targets, t.1 = word ∨ t.1 = word ^^^ r.beta := by
  have hb := fiberCheck_beta r h
  have hsp := fiberCheck_seed r h s hs
  let value := word ^^^ s.word
  have hsupport : value &&& r.beta = value :=
    supported_xor_of_outside_eq r.beta word s.word (hoff.trans hsp.2.1.symm)
  have hzero : reconX bottomEColumns value = 0 := by
    change reconX bottomEColumns (word ^^^ s.word) = 0
    rw [reconX_xor,he,hseed,Nat.xor_self]
  have hrec := reconstruct_kernel r h himages value hsupport hzero
  let rows := r.components.map fun c => (c.root,c.word ^^^ (c.image <<< 90))
  have hcb : ∀ c ∈ r.components, c.word < 2^90 := by
    intro c hc
    have hp := (fiberCheck_components r h c hc).2.2.1
    rw [← hp]
    exact lt_of_le_of_lt Nat.and_le_right hb
  have hlow : reconX (rows.map fun p => (p.1,p.2 &&& (2^90-1))) value = value := by
    calc
      reconX (rows.map fun p => (p.1,p.2 &&& (2^90-1))) value =
          reconX (r.components.map fun c => (c.root,c.word)) value := by
        congr 1
        rw [List.map_map]
        apply List.map_congr_left
        intro c hc
        simp only [Function.comp_apply,low_tag 90 c.word c.image (hcb c hc)]
      _ = value := hrec.symm
  have htag := tagged_reconstruction 90 bottomEColumns rows value value (by
    intro p hp
    obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hp
    rw [low_tag 90 c.word c.image (hcb c hc),high_tag 90 c.word c.image (hcb c hc),himages c hc]) hlow
  have hok := reconX_ok_of_full_walk (candidateOK r.beta s.word s.targets) rows hsp.2.2.2.1 (by
    simpa [rows,tags,List.map_map,Function.comp_def] using hsp.2.2.2.2) value
  have hcancel : s.word ^^^ value = word := by
    simp [value,Nat.xor_comm,Nat.xor_left_comm,Nat.xor_assoc]
  rw [hzero] at htag
  unfold candidateOK at hok
  have ht1 : Nat.land (reconX rows value) (2^90-1) = value := htag.1
  have ht2 : Nat.shiftRight (reconX rows value) 90 = 0 := htag.2
  have ht3 : Nat.xor s.word value = word := hcancel
  rw [ht2,ht1,ht3] at hok
  simp only [show Nat.beq 0 0 = true from rfl,if_true] at hok
  split_ifs at hok with hw
  · have hm : word ∈ s.targets.map Prod.fst := by simpa using hok
    obtain ⟨t,ht,heq⟩ := List.mem_map.mp hm
    exact ⟨t,ht,Or.inl heq⟩
  · have hm : word ^^^ r.beta ∈ s.targets.map Prod.fst := by simpa using hok
    obtain ⟨t,ht,heq⟩ := List.mem_map.mp hm
    exact ⟨t,ht,Or.inr heq⟩

#print axioms solution_target
end Quantum.Stabilizer.Homological.BB.Bravyi360.BottomForest
