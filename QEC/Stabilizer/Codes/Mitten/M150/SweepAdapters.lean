import QEC.Stabilizer.Codes.Mitten.M150.FloorCore

namespace Quantum.Stabilizer.Homological.LP.M150

/-- Every enumerated fixed-weight mask fits the declared number of bits. -/
theorem masksOfWt_bound : ∀ n k m : Nat, m ∈ masksOfWt n k → m < 2 ^ n := by
  intro n
  induction n with
  | zero =>
    intro k m hm
    cases k with
    | zero =>
      have hz : m = 0 := by simpa only [masksOfWt, List.mem_singleton] using hm
      subst m
      decide
    | succ k => simp only [masksOfWt, List.not_mem_nil] at hm
  | succ n ih =>
    intro k m hm
    cases k with
    | zero =>
      have hz : m = 0 := by simpa only [masksOfWt, List.mem_singleton] using hm
      subst m
      exact Nat.two_pow_pos _
    | succ k =>
      simp only [masksOfWt, List.mem_append, List.mem_map] at hm
      have hp : 2 ^ n < 2 ^ (n + 1) :=
        Nat.pow_lt_pow_right (by decide) (Nat.lt_succ_self n)
      rcases hm with hm | ⟨a, ha, rfl⟩
      · exact lt_trans (ih (k + 1) m hm) hp
      · apply Nat.or_lt_two_pow (lt_trans (ih k a ha) hp)
        simpa only [Nat.shiftLeft_eq, Nat.one_mul] using hp

/-- The first linear image in a split's two-mask reconstruction. -/
def sweepLeft (T : SweepTables) : Nat → Nat → Nat
  | 0, x => xorFold T.tUW x
  | 1, x => xorFold T.tUT x
  | 2, x => xorFold T.tP (xorFold T.tWC x)
  | _, x => xorFold T.tPT (xorFold T.tUC x)

/-- The second linear image in a split's two-mask reconstruction. -/
def sweepRight (T : SweepTables) : Nat → Nat → Nat
  | 0, y => xorFold T.tTW y
  | 1, y => xorFold T.tWT y
  | 2, y => xorFold T.tP (xorFold T.tTC y)
  | _, y => xorFold T.tPT (xorFold T.tWC2 y)

/-- The first reconstruction image sends zero to zero. -/
@[simp] theorem sweepLeft_zero (T : SweepTables) (mode : Nat) :
    sweepLeft T mode 0 = 0 := by
  rcases mode with _ | _ | _ | mode <;> simp only [sweepLeft, xorFold_zero]

/-- The second reconstruction image sends zero to zero. -/
@[simp] theorem sweepRight_zero (T : SweepTables) (mode : Nat) :
    sweepRight T mode 0 = 0 := by
  rcases mode with _ | _ | _ | mode <;> simp only [sweepRight, xorFold_zero]

/-- The first reconstruction image preserves XOR. -/
theorem sweepLeft_xor (T : SweepTables) (mode x y : Nat) :
    sweepLeft T mode (x ^^^ y) = sweepLeft T mode x ^^^ sweepLeft T mode y := by
  rcases mode with _ | _ | _ | mode <;> simp only [sweepLeft, xorFold_xor]

/-- The second reconstruction image preserves XOR. -/
theorem sweepRight_xor (T : SweepTables) (mode x y : Nat) :
    sweepRight T mode (x ^^^ y) = sweepRight T mode x ^^^ sweepRight T mode y := by
  rcases mode with _ | _ | _ | mode <;> simp only [sweepRight, xorFold_xor]

/-- The possible kernel corrections for one derivation mode. -/
def sweepAnn (T : SweepTables) : Nat → List Nat
  | 0 => [0]
  | 1 => [0]
  | 2 => T.ann
  | _ => T.annT

/-- The derived component from two chosen masks and a kernel correction. -/
def sweepOutput (T : SweepTables) (mode x y a : Nat) : Nat :=
  sweepLeft T mode x ^^^ sweepRight T mode y ^^^ a

/-- Bounded linear images and a bounded correction give a bounded output. -/
theorem sweepOutput_lt (T : SweepTables) (mode x y a : Nat)
    (hl : sweepLeft T mode x < 2 ^ 30)
    (hr : sweepRight T mode y < 2 ^ 30) (ha : a < 2 ^ 30) :
    sweepOutput T mode x y a < 2 ^ 30 :=
  Nat.xor_lt_two_pow (Nat.xor_lt_two_pow hl hr) ha

/-- Acceptance of a reconstructed low-weight component, including parity guards. -/
def sweepAccept (T : SweepTables) (mode x y a : Nat) : Bool :=
  let out := sweepOutput T mode x y a
  match mode with
  | 0 => okTriple T.cls x out y
  | 1 => okTriple T.cls x y out
  | 2 =>
      let c := xorFold T.tWC x ^^^ xorFold T.tTC y
      parity (T.ln0 &&& c) || parity (T.ln1 &&& c) || okTriple T.cls out x y
  | _ =>
      let c := xorFold T.tUC x ^^^ xorFold T.tWC2 y
      parity (T.lnT0 &&& c) || parity (T.lnT1 &&& c) || okTriple T.cls x y out

/-- The weight of the first enumerated mask. -/
def sweepOuterWeight (p q _r : Nat) : Nat → Nat
  | 2 => q
  | _ => p

/-- The weight of the second enumerated mask. -/
def sweepInnerWeight (_p q r : Nat) : Nat → Nat
  | 0 => r
  | 1 => q
  | 2 => r
  | _ => q

/-- The weight required of the reconstructed component. -/
def sweepTargetWeight (p q r : Nat) : Nat → Nat
  | 0 => q
  | 1 => r
  | 2 => p
  | _ => r

/-- A bounded component either has another weight or passes its acceptance test. -/
private theorem checkWeight_of_implication {out target : Nat} {valid : Bool}
    (hb : out < 2 ^ 30) (hv : popCntGo 30 out = target → valid = true) :
    (popCnt out != target || valid) = true := by
  by_cases he : popCnt out = target
  · exact Bool.or_eq_true_iff.mpr (Or.inr (hv (by rwa [← popCnt_eq hb])))
  · exact Bool.or_eq_true_iff.mpr (Or.inl (bne_iff_ne.mpr he))

/-- Pointwise reconstruction certificates close the unique-middle mode. -/
theorem checkSplit_zero_of_pairs (T : SweepTables) (p q r : Nat)
    (hb : ∀ x ∈ masksOfWt 30 p, ∀ y ∈ masksOfWt 30 r,
      sweepOutput T 0 x y 0 < 2 ^ 30)
    (hv : ∀ x ∈ masksOfWt 30 p, ∀ y ∈ masksOfWt 30 r,
      popCntGo 30 (sweepOutput T 0 x y 0) = q → sweepAccept T 0 x y 0 = true) :
    checkSplit T (p, q, r, 0) = true := by
  simp only [checkSplit, foldedPairs, List.all_map, Function.comp_apply, List.all_eq_true]
  intro x hx y hy
  have h := checkWeight_of_implication (hb x hx y hy) (hv x hx y hy)
  simpa only [sweepOutput, sweepLeft, sweepRight, sweepAccept, Nat.xor_zero] using h

/-- Pointwise reconstruction certificates close the unique-shared mode. -/
theorem checkSplit_one_of_pairs (T : SweepTables) (p q r : Nat)
    (hb : ∀ x ∈ masksOfWt 30 p, ∀ y ∈ masksOfWt 30 q,
      sweepOutput T 1 x y 0 < 2 ^ 30)
    (hv : ∀ x ∈ masksOfWt 30 p, ∀ y ∈ masksOfWt 30 q,
      popCntGo 30 (sweepOutput T 1 x y 0) = r → sweepAccept T 1 x y 0 = true) :
    checkSplit T (p, q, r, 1) = true := by
  simp only [checkSplit, foldedPairs, List.all_map, Function.comp_apply, List.all_eq_true]
  intro x hx y hy
  have h := checkWeight_of_implication (hb x hx y hy) (hv x hx y hy)
  simpa only [sweepOutput, sweepLeft, sweepRight, sweepAccept, Nat.xor_zero] using h

/-- Pointwise certificates close the first-component coset mode. -/
theorem checkSplit_two_of_pairs (T : SweepTables) (p q r : Nat)
    (hb : ∀ x ∈ masksOfWt 30 q, ∀ y ∈ masksOfWt 30 r, ∀ a ∈ T.ann,
      sweepOutput T 2 x y a < 2 ^ 30)
    (hv : ∀ x ∈ masksOfWt 30 q, ∀ y ∈ masksOfWt 30 r, ∀ a ∈ T.ann,
      popCntGo 30 (sweepOutput T 2 x y a) = p → sweepAccept T 2 x y a = true) :
    checkSplit T (p, q, r, 2) = true := by
  simp only [checkSplit, foldedPairs, List.all_map, Function.comp_apply, List.all_eq_true]
  intro x hx y hy
  by_cases hg : (parity (T.ln0 &&& (xorFold T.tWC x ^^^ xorFold T.tTC y)) ||
      parity (T.ln1 &&& (xorFold T.tWC x ^^^ xorFold T.tTC y))) = true
  · exact Bool.or_eq_true_iff.mpr (Or.inl hg)
  · have hfalse := Bool.eq_false_of_not_eq_true hg
    apply Bool.or_eq_true_iff.mpr
    right
    apply List.all_eq_true.mpr
    intro a ha
    have h := checkWeight_of_implication
      (valid := okTriple T.cls (sweepOutput T 2 x y a) x y)
      (hb x hx y hy a ha) (fun hw => by
        have hv' := hv x hx y hy a ha hw
        simpa only [sweepAccept, hfalse, Bool.false_or] using hv')
    simpa only [sweepOutput, sweepLeft, sweepRight, xorFold_xor] using h

/-- Pointwise certificates close the shared-component coset mode. -/
theorem checkSplit_many_of_pairs (T : SweepTables) (p q r mode : Nat)
    (hb : ∀ x ∈ masksOfWt 30 p, ∀ y ∈ masksOfWt 30 q, ∀ a ∈ T.annT,
      sweepOutput T (mode + 3) x y a < 2 ^ 30)
    (hv : ∀ x ∈ masksOfWt 30 p, ∀ y ∈ masksOfWt 30 q, ∀ a ∈ T.annT,
      popCntGo 30 (sweepOutput T (mode + 3) x y a) = r →
        sweepAccept T (mode + 3) x y a = true) :
    checkSplit T (p, q, r, mode + 3) = true := by
  simp only [checkSplit, foldedPairs, List.all_map, Function.comp_apply, List.all_eq_true]
  intro x hx y hy
  by_cases hg : (parity (T.lnT0 &&& (xorFold T.tUC x ^^^ xorFold T.tWC2 y)) ||
      parity (T.lnT1 &&& (xorFold T.tUC x ^^^ xorFold T.tWC2 y))) = true
  · exact Bool.or_eq_true_iff.mpr (Or.inl hg)
  · have hfalse := Bool.eq_false_of_not_eq_true hg
    apply Bool.or_eq_true_iff.mpr
    right
    apply List.all_eq_true.mpr
    intro a ha
    have h := checkWeight_of_implication
      (valid := okTriple T.cls x y (sweepOutput T (mode + 3) x y a))
      (hb x hx y hy a ha) (fun hw => by
        have hv' := hv x hx y hy a ha hw
        simpa only [sweepAccept, hfalse, Bool.false_or] using hv')
    simpa only [sweepOutput, sweepLeft, sweepRight, xorFold_xor] using h

/-- Uniform interface from packed pair certificates to the original split checker. -/
theorem checkSplit_of_pairs (T : SweepTables) (p q r mode : Nat)
    (hb : ∀ x ∈ masksOfWt 30 (sweepOuterWeight p q r mode),
      ∀ y ∈ masksOfWt 30 (sweepInnerWeight p q r mode), ∀ a ∈ sweepAnn T mode,
        sweepOutput T mode x y a < 2 ^ 30)
    (hv : ∀ x ∈ masksOfWt 30 (sweepOuterWeight p q r mode),
      ∀ y ∈ masksOfWt 30 (sweepInnerWeight p q r mode), ∀ a ∈ sweepAnn T mode,
        popCntGo 30 (sweepOutput T mode x y a) = sweepTargetWeight p q r mode →
          sweepAccept T mode x y a = true) :
    checkSplit T (p, q, r, mode) = true := by
  rcases mode with _ | mode
  · exact checkSplit_zero_of_pairs T p q r
      (fun x hx y hy => hb x hx y hy 0 (by simp [sweepAnn]))
      (fun x hx y hy => hv x hx y hy 0 (by simp [sweepAnn]))
  rcases mode with _ | mode
  · exact checkSplit_one_of_pairs T p q r
      (fun x hx y hy => hb x hx y hy 0 (by simp [sweepAnn]))
      (fun x hx y hy => hv x hx y hy 0 (by simp [sweepAnn]))
  rcases mode with _ | mode
  · exact checkSplit_two_of_pairs T p q r hb hv
  · exact checkSplit_many_of_pairs T p q r mode hb hv

end Quantum.Stabilizer.Homological.LP.M150
