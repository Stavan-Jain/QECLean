import QEC.Stabilizer.Framework.Homological.Certificate.MaskPeel
import QEC.Stabilizer.Framework.Homological.Certificate.ReconWalk
import QEC.Stabilizer.Framework.Homological.Certificate.MaskLinear

namespace Quantum.Stabilizer.Homological.F2Mask

/-- Evaluation of a binary row on a natural mask. -/
def cellEval (cells : List Nat) (value : Nat) : ZMod 2 :=
  (cells.map fun i => if value.testBit i then 1 else 0).sum

/-- Binary row evaluation respects XOR addition. -/
theorem cellEval_xor (cells : List Nat) (a b : Nat) :
    cellEval cells (a ^^^ b) = cellEval cells a + cellEval cells b := by
  induction cells with
  | nil => simp [cellEval]
  | cons q qs ih =>
    simp only [cellEval, List.map_cons, List.sum_cons, Nat.testBit_xor] at *
    rw [ih]
    have h : ∀ u v : Bool, (if u ^^ v then (1 : ZMod 2) else 0) = (if u then 1 else 0) + (if v then 1 else 0) := by decide
    rw [h]
    ac_rfl

/-- Reconstruction preserves every binary row that vanishes on its columns. -/
theorem cellEval_reconX_zero (cells : List Nat) (rows : List (Nat × Nat)) (value : Nat)
    (h : ∀ p ∈ rows, cellEval cells p.2 = 0) : cellEval cells (reconX rows value) = 0 := by
  have hall : ∀ x, XorSpan (rows.map Prod.snd) x → cellEval cells x = 0 := by
    intro x hx
    induction hx with
    | zero => simp [cellEval]
    | step hg _ ih =>
      obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hg
      rw [cellEval_xor,h p hp,ih,add_zero]
  exact hall _ (reconX_mem_span rows value)

/-- Reconstruction preserves a support mask shared by every column. -/
theorem reconX_supported (rows : List (Nat × Nat)) (value beta : Nat)
    (h : ∀ p ∈ rows, p.2 &&& beta = p.2) :
    reconX rows value &&& beta = reconX rows value := by
  rw [reconX_and]
  congr 1
  conv_rhs => rw [← List.map_id rows]
  apply List.map_congr_left
  intro p hp
  simp [h p hp]

/-- Singleton reconstruction reads precisely the named pivot coordinates. -/
theorem reconX_singletons (roots : List Nat) (value : Nat) :
    reconX (roots.map fun q => (q,2^q)) value =
      value &&& xorList (roots.map fun q => 2^q) := by
  induction roots with
  | nil => simp [reconX]
  | cons q qs ih =>
    simp only [List.map_cons, reconX, List.filter_cons, List.map_cons] at *
    rw [xorList_cons, Nat.and_xor_distrib_left, Nat.and_two_pow]
    cases h : value.testBit q <;> simp [h, xorList_cons, ih]

/-- Identity root columns recover all root coordinates after reconstruction. -/
theorem reconX_roots (rows : List (Nat × Nat)) (value roots : Nat)
    (hr : roots = xorList ((rows.map Prod.fst).map fun q => 2^q))
    (hc : ∀ p ∈ rows, p.2 &&& roots = 2^p.1) :
    reconX rows value &&& roots = value &&& roots := by
  rw [reconX_and]
  have he : rows.map (fun p => (p.1,p.2 &&& roots)) =
      (rows.map Prod.fst).map (fun q => (q,2^q)) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro p hp
    simp [hc p hp]
  rw [he,reconX_singletons,← hr]

/-- Peeling uses only the row equations actually named in its certificate. -/
theorem peelMaskOK_sound_local {Q : Type*} (row : Q → Nat) (cells : Q → List Nat)
    (hmem : ∀ q i, i ∈ cells q ↔ (row q).testBit i = true)
    (hnd : ∀ q, (cells q).Nodup) (zeta : Nat → ZMod 2)
    (target : Nat) (steps : List Q) :
    ∀ known, peelMaskOK row target known steps = true →
      (∀ q ∈ steps, ((cells q).map zeta).sum = 0) →
      (∀ i, known.testBit i = true → zeta i = 0) →
      ∀ i, target.testBit i = true → zeta i = 0 := by
  induction steps with
  | nil =>
    intro known h _ hk
    have heq : known = target := by simpa [peelMaskOK] using h
    simpa [← heq] using hk
  | cons q rest ih =>
    intro known h hr hk
    simp only [peelMaskOK, Bool.and_eq_true, Bool.not_eq_true', Nat.beq_eq] at h
    obtain ⟨⟨hn,hp⟩,hrest⟩ := h
    apply ih (known ||| row q) hrest (fun t ht => hr t (by simp [ht]))
    exact unknownMask_step_zero (cells q) (row q) known zeta (hmem q) (hnd q)
      (hr q (by simp)) hk (by simpa only [← Bool.not_eq_true,Nat.beq_eq] using hn) hp

/-- Forest uniqueness needs only its explicitly selected row equations. -/
theorem peelForestOK_sound_local {Q : Type*} (row : Q → Nat) (cells : Q → List Nat)
    (hmem : ∀ q i, i ∈ cells q ↔ (row q).testBit i = true)
    (hnd : ∀ q, (cells q).Nodup) (zeta : Nat → ZMod 2)
    (target : Nat) (forest : List (Nat × Nat × List Q)) :
    ∀ covered, peelForestOK row target covered forest = true →
      (∀ c ∈ forest, ∀ q ∈ c.2.2, ((cells q).map zeta).sum = 0) →
      (∀ c ∈ forest, zeta c.1 = 0) →
      (∀ i, covered.testBit i = true → zeta i = 0) →
      ∀ i, target.testBit i = true → zeta i = 0 := by
  induction forest with
  | nil =>
    intro covered h _ _ hc
    have heq : covered = target := by simpa [peelForestOK] using h
    simpa [← heq] using hc
  | cons c rest ih =>
    rcases c with ⟨root,component,steps⟩
    intro covered h hr hroot hc
    simp only [peelForestOK,Bool.and_eq_true] at h
    have ht := peelMaskOK_sound_local row cells hmem hnd zeta component steps
      (Nat.shiftLeft 1 root) h.1.2 (hr (root,component,steps) (by simp))
    have hcomp : ∀ i, component.testBit i = true → zeta i = 0 := by
      apply ht
      intro i hi
      have heq : root = i := by
        change (1 <<< root).testBit i = true at hi
        simpa only [Nat.shiftLeft_eq,Nat.one_mul,Nat.testBit_two_pow,decide_eq_true_eq] using hi
      subst i
      exact hroot (root,component,steps) (by simp)
    apply ih (covered ||| component) h.2
    · exact fun c hc q hq => hr c (by simp [hc]) q hq
    · exact fun c hc => hroot c (by simp [hc])
    · intro i hi
      rw [Nat.testBit_or,Bool.or_eq_true] at hi
      exact hi.elim (hc i) (hcomp i)

/-- Certified forest components reconstruct every supported solution of the selected rows. -/
theorem forest_reconstruct {Q : Type*} (row : Q → Nat) (cells : Q → List Nat)
    (hmem : ∀ q i, i ∈ cells q ↔ (row q).testBit i = true)
    (hnd : ∀ q, (cells q).Nodup) (beta value roots : Nat)
    (forest : List (Nat × Nat × List Q))
    (hforest : peelForestOK row beta 0 forest = true)
    (hrmask : roots = xorList (forest.map fun c => 2^c.1))
    (hroot : ∀ c ∈ forest, c.2.1 &&& roots = 2^c.1)
    (hcomp : ∀ c ∈ forest, c.2.1 &&& beta = c.2.1)
    (hcompzero : ∀ c ∈ forest, ∀ q ∈ c.2.2,
      ∀ d ∈ forest, cellEval (cells q) d.2.1 = 0)
    (hsupport : value &&& beta = value)
    (hzero : ∀ c ∈ forest, ∀ q ∈ c.2.2, cellEval (cells q) value = 0) :
    value = reconX (forest.map fun c => (c.1,c.2.1)) value := by
  let rows := forest.map fun c => (c.1,c.2.1)
  let result := reconX rows value
  have hresult : result &&& beta = result := by
    apply reconX_supported
    intro p hp
    obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hp
    exact hcomp c hc
  have hresultroots : result &&& roots = value &&& roots := by
    apply reconX_roots rows value roots
    · simpa [rows,List.map_map,Function.comp_def] using hrmask
    · intro p hp
      obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hp
      exact hroot c hc
  let zeta : Nat → ZMod 2 := fun i => if (value ^^^ result).testBit i then 1 else 0
  have hrow : ∀ c ∈ forest, ∀ q ∈ c.2.2, ((cells q).map zeta).sum = 0 := by
    intro c hc q hq
    change cellEval (cells q) (value ^^^ result) = 0
    rw [cellEval_xor,hzero c hc q hq]
    simp only [zero_add]
    apply cellEval_reconX_zero
    intro p hp
    obtain ⟨d,hd,rfl⟩ := List.mem_map.mp hp
    exact hcompzero c hc q hq d hd
  have hroots : ∀ c ∈ forest, zeta c.1 = 0 := by
    intro c hc
    have hb := congrArg (fun x : Nat => x.testBit c.1) (hroot c hc)
    simp only [Nat.testBit_and,Nat.testBit_two_pow_self,Bool.and_eq_true] at hb
    have he := congrArg (fun x : Nat => x.testBit c.1) hresultroots
    simp only [Nat.testBit_and,hb.2,Bool.and_true] at he
    simp [zeta,Nat.testBit_xor,he]
  have hz := peelForestOK_sound_local row cells hmem hnd zeta beta forest 0 hforest
    hrow hroots (by simp)
  have hxor : value ^^^ result = 0 := by
    apply Nat.eq_of_testBit_eq
    intro i
    have hs : (value ^^^ result) &&& beta = value ^^^ result := by
      rw [Nat.and_xor_distrib_right,hsupport,hresult]
    have hsbit := congrArg (fun x : Nat => x.testBit i) hs
    simp only [Nat.testBit_and] at hsbit
    cases hv : (value ^^^ result).testBit i
    · simp [hv]
    · have hb : beta.testBit i = true := by simpa [hv] using hsbit
      have hzi := hz i hb
      change (if (value ^^^ result).testBit i then (1 : ZMod 2) else 0) = 0 at hzi
      rw [hv] at hzi
      norm_num at hzi
  have he := congrArg (fun x => x ^^^ result) hxor
  simpa only [Nat.xor_assoc,Nat.xor_self,Nat.xor_zero,Nat.zero_xor] using he

#print axioms forest_reconstruct
end Quantum.Stabilizer.Homological.F2Mask
