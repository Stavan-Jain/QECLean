import QEC.Stabilizer.Framework.Homological.BZCertificate
import Init.Data.Nat.Power2
import Mathlib.Data.List.Nodup

namespace Quantum.Stabilizer.Homological.F2Mask

/-- The bits newly exposed by a row, after removing already known coordinates. -/
def unknownMask (row known : ℕ) : ℕ := Nat.xor row (Nat.land row known)

/-- Removing known bits leaves precisely the unknown row coordinates. -/
theorem testBit_unknownMask (row known i : ℕ) :
    (unknownMask row known).testBit i = (row.testBit i && !(known.testBit i)) := by
  change (row ^^^ (row &&& known)).testBit i = _
  simp only [Nat.testBit_xor, Nat.testBit_and]
  have h : ∀ a b : Bool, (a ^^ (a && b)) = (a && !b) := by decide
  exact h _ _

/-- A nonzero power-of-two remainder exposes exactly one unknown coordinate. -/
theorem unknownMask_single {row known : ℕ}
    (hn : unknownMask row known ≠ 0)
    (hp : (unknownMask row known &&& (unknownMask row known - 1)) = 0) :
    ∃ q, row.testBit q = true ∧ known.testBit q = false ∧
      ∀ x, row.testBit x = true → x = q ∨ known.testBit x = true := by
  obtain ⟨q, hq⟩ := (Nat.and_sub_one_eq_zero_iff_isPowerOfTwo hn).1 hp
  have hself : (unknownMask row known).testBit q = true := by rw [hq]; simp
  rw [testBit_unknownMask, Bool.and_eq_true, Bool.not_eq_true'] at hself
  refine ⟨q, hself.1, hself.2, ?_⟩
  intro x hx
  by_cases heq : x = q
  · exact Or.inl heq
  · right
    have hfalse : (unknownMask row known).testBit x = false := by
      rw [hq, Nat.testBit_two_pow_of_ne (Ne.symm heq)]
    rw [testBit_unknownMask, hx, Bool.true_and, Bool.not_eq_false'] at hfalse
    exact hfalse

/-- One packed peeling step is an instance of the existing sparse-row peeling theorem. -/
theorem unknownMask_step_zero (cells : List ℕ) (row known : ℕ) (ζ : ℕ → ZMod 2)
    (hcells : ∀ i, i ∈ cells ↔ row.testBit i = true) (hnd : cells.Nodup)
    (hrow : (cells.map ζ).sum = 0)
    (hknown : ∀ i, known.testBit i = true → ζ i = 0)
    (hn : unknownMask row known ≠ 0)
    (hp : (unknownMask row known &&& (unknownMask row known - 1)) = 0) :
    ∀ i, (known ||| row).testBit i = true → ζ i = 0 := by
  obtain ⟨q, hqr, _, hother⟩ := unknownMask_single hn hp
  let knownCells := cells.filter fun i => known.testBit i
  have hq : q ∈ cells := (hcells q).2 hqr
  have hok : peelOK (fun _ : Unit => cells) knownCells [(q, ())] = true := by
    simp only [peelOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, Bool.or_eq_true,
      List.contains_iff_mem]
    refine ⟨⟨List.count_eq_one_of_mem hnd hq, ?_⟩, trivial⟩
    intro x hx
    rcases hother x ((hcells x).1 hx) with rfl | hk
    · exact Or.inl rfl
    · exact Or.inr (List.mem_filter.mpr ⟨hx, hk⟩)
  have hqzero : ζ q = 0 := peelOK_sound (fun _ : Unit => cells) ζ
    (fun _ => hrow) [(q, ())] knownCells hok
    (fun x hx => hknown x (List.mem_filter.mp hx).2) q (by simp)
  intro i hi
  rw [Nat.testBit_or, Bool.or_eq_true] at hi
  rcases hi with hi | hi
  · exact hknown i hi
  · rcases hother i hi with rfl | hk
    · exact hqzero
    · exact hknown i hk

/-- A compact peeling certificate names only rows; each row must expose one new bit. -/
def peelMaskOK {Q : Type*} (row : Q → ℕ) (target : ℕ) : ℕ → List Q → Bool
  | known, [] => Nat.beq known target
  | known, q :: rest =>
      let u := unknownMask (row q) known
      (!Nat.beq u 0) && Nat.beq (Nat.land u (Nat.sub u 1)) 0 &&
        peelMaskOK row target (Nat.lor known (row q)) rest

/-- Packed peeling propagates vanishing from its roots to its full certified target. -/
theorem peelMaskOK_sound {Q : Type*} (row : Q → ℕ) (cells : Q → List ℕ)
    (hmem : ∀ q i, i ∈ cells q ↔ (row q).testBit i = true)
    (hnd : ∀ q, (cells q).Nodup) (ζ : ℕ → ZMod 2)
    (hrow : ∀ q, ((cells q).map ζ).sum = 0)
    (target : ℕ) (steps : List Q) :
    ∀ known, peelMaskOK row target known steps = true →
      (∀ i, known.testBit i = true → ζ i = 0) →
      ∀ i, target.testBit i = true → ζ i = 0 := by
  induction steps with
  | nil =>
    intro known h hk
    have heq : known = target := by simpa [peelMaskOK] using h
    simpa [← heq] using hk
  | cons q rest ih =>
    intro known h hk
    simp only [peelMaskOK, Bool.and_eq_true, Bool.not_eq_true', Nat.beq_eq] at h
    obtain ⟨⟨hn, hp⟩, hrest⟩ := h
    apply ih (known ||| row q) hrest
    exact unknownMask_step_zero (cells q) (row q) known ζ (hmem q) (hnd q)
      (hrow q) hk (by simpa only [← Bool.not_eq_true, Nat.beq_eq] using hn) hp

#print axioms peelMaskOK_sound

end Quantum.Stabilizer.Homological.F2Mask

namespace Quantum.Stabilizer.Homological.F2Mask

/-- Packed peeling gives uniqueness on a support once the root coordinates vanish. -/
theorem mask_eq_zero_of_peel {Q : Type*} (row : Q → Nat) (cells : Q → List Nat)
    (hmem : ∀ q i, i ∈ cells q ↔ (row q).testBit i = true)
    (hnd : ∀ q, (cells q).Nodup) (beta roots value : Nat) (steps : List Q)
    (hpeel : peelMaskOK row beta roots steps = true)
    (hsupport : value &&& beta = value) (hroots : value &&& roots = 0)
    (hrow : ∀ q, ((cells q).map fun i =>
      (if value.testBit i then (1 : ZMod 2) else 0)).sum = 0) : value = 0 := by
  let zeta : Nat → ZMod 2 := fun i => if value.testBit i then 1 else 0
  have hknown : ∀ i, roots.testBit i = true → zeta i = 0 := by
    intro i hi
    have h := congrArg (fun m : Nat => m.testBit i) hroots
    simp only [Nat.testBit_and, hi, Bool.and_true, Nat.zero_testBit] at h
    simp [zeta, h]
  have hzero := peelMaskOK_sound row cells hmem hnd zeta hrow beta steps roots hpeel hknown
  apply Nat.eq_of_testBit_eq
  intro i
  have hs := congrArg (fun m : Nat => m.testBit i) hsupport
  simp only [Nat.testBit_and] at hs
  cases hv : value.testBit i
  · simp [hv]
  · have hb : beta.testBit i = true := by simpa [hv] using hs
    have hz := hzero i hb
    simp [zeta, hv] at hz

/-- A supported residual with the same root coordinates is its certified kernel reconstruction. -/
theorem mask_reconstruct_of_peel {Q : Type*} (row : Q → Nat) (cells : Q → List Nat)
    (hmem : ∀ q i, i ∈ cells q ↔ (row q).testBit i = true)
    (hnd : ∀ q, (cells q).Nodup) (beta roots value reconstructed : Nat) (steps : List Q)
    (hpeel : peelMaskOK row beta roots steps = true)
    (hsupport : (value ^^^ reconstructed) &&& beta = value ^^^ reconstructed)
    (hroots : (value ^^^ reconstructed) &&& roots = 0)
    (hrow : ∀ q, ((cells q).map fun i =>
      (if (value ^^^ reconstructed).testBit i then (1 : ZMod 2) else 0)).sum = 0) :
    value = reconstructed := by
  have hzero := mask_eq_zero_of_peel row cells hmem hnd beta roots
    (value ^^^ reconstructed) steps hpeel hsupport hroots hrow
  have h := congrArg (fun x => x ^^^ reconstructed) hzero
  simpa only [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero, Nat.zero_xor] using h

#print axioms mask_reconstruct_of_peel
end Quantum.Stabilizer.Homological.F2Mask

namespace Quantum.Stabilizer.Homological.F2Mask

/-- A forest certificate peels each component from one root and covers its target. -/
def peelForestOK {Q : Type*} (row : Q → Nat) (target : Nat) :
    Nat → List (Nat × Nat × List Q) → Bool
  | covered, [] => Nat.beq covered target
  | covered, (root, component, steps) :: rest =>
      Nat.beq (Nat.land component covered) 0 &&
      peelMaskOK row component (Nat.shiftLeft 1 root) steps &&
      peelForestOK row target (Nat.lor covered component) rest

/-- Peeling all forest components propagates zero root values over the full target. -/
theorem peelForestOK_sound {Q : Type*} (row : Q → Nat) (cells : Q → List Nat)
    (hmem : ∀ q i, i ∈ cells q ↔ (row q).testBit i = true)
    (hnd : ∀ q, (cells q).Nodup) (zeta : Nat → ZMod 2)
    (hrow : ∀ q, ((cells q).map zeta).sum = 0)
    (target : Nat) (forest : List (Nat × Nat × List Q)) :
    ∀ covered, peelForestOK row target covered forest = true →
      (∀ c ∈ forest, zeta c.1 = 0) →
      (∀ i, covered.testBit i = true → zeta i = 0) →
      ∀ i, target.testBit i = true → zeta i = 0 := by
  induction forest with
  | nil =>
    intro covered h _ hc
    have heq : covered = target := by simpa [peelForestOK] using h
    simpa [← heq] using hc
  | cons c rest ih =>
    rcases c with ⟨root, component, steps⟩
    intro covered h hr hc
    simp only [peelForestOK, Bool.and_eq_true] at h
    have ht := peelMaskOK_sound row cells hmem hnd zeta hrow component steps
      (Nat.shiftLeft 1 root) h.1.2
    have hcomp : ∀ i, component.testBit i = true → zeta i = 0 := by
      apply ht
      intro i hi
      have heq : root = i := by
        change (1 <<< root).testBit i = true at hi
        simpa only [Nat.shiftLeft_eq, Nat.one_mul, Nat.testBit_two_pow, decide_eq_true_eq] using hi
      subst i
      exact hr (root, component, steps) (by simp)
    apply ih (covered ||| component) h.2
    · exact fun c hc => hr c (by simp [hc])
    · intro i hi
      rw [Nat.testBit_or, Bool.or_eq_true] at hi
      exact hi.elim (hc i) (hcomp i)

/-- A successful peel retains every coordinate that was known initially. -/
theorem peelMaskOK_preserves_known {Q : Type*} (row : Q → Nat) (target : Nat)
    (steps : List Q) :
    ∀ known, peelMaskOK row target known steps = true →
      ∀ i, known.testBit i = true → target.testBit i = true := by
  induction steps with
  | nil =>
    intro known h i hi
    have heq : known = target := by simpa [peelMaskOK] using h
    simpa [← heq] using hi
  | cons q rest ih =>
    intro known h i hi
    simp only [peelMaskOK, Bool.and_eq_true] at h
    apply ih (known ||| row q) h.2 i
    simp [Nat.testBit_or, hi]

/-- Forest peeling proves a supported residual is zero from its root and row values. -/
theorem mask_eq_zero_of_forest {Q : Type*} (row : Q → Nat) (cells : Q → List Nat)
    (hmem : ∀ q i, i ∈ cells q ↔ (row q).testBit i = true)
    (hnd : ∀ q, (cells q).Nodup) (beta value : Nat)
    (forest : List (Nat × Nat × List Q))
    (hforest : peelForestOK row beta 0 forest = true)
    (hsupport : value &&& beta = value)
    (hroots : ∀ c ∈ forest, value.testBit c.1 = false)
    (hrow : ∀ q, ((cells q).map fun i =>
      (if value.testBit i then (1 : ZMod 2) else 0)).sum = 0) : value = 0 := by
  let zeta : Nat → ZMod 2 := fun i => if value.testBit i then 1 else 0
  have hz := peelForestOK_sound row cells hmem hnd zeta hrow beta forest 0 hforest
    (fun c hc => by simp [zeta, hroots c hc]) (by simp)
  apply Nat.eq_of_testBit_eq
  intro i
  have hs := congrArg (fun m : Nat => m.testBit i) hsupport
  simp only [Nat.testBit_and] at hs
  cases hv : value.testBit i
  · simp [hv]
  · have hb : beta.testBit i = true := by simpa [hv] using hs
    have hzi := hz i hb
    simp [zeta, hv] at hzi

#print axioms mask_eq_zero_of_forest
end Quantum.Stabilizer.Homological.F2Mask
