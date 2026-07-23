import Mathlib.Data.Nat.Bitwise
import QEC.Stabilizer.Codes.BivariateBicycle.Z5Z15F2A6.WindowEngine

/-!
# Z5Z15F2A6 window kernel certificates

Pivot certificates for the window sweeps: instead of enumerating all
`2^L` masks per window (interpreter-hours), certify by Gaussian
elimination that the kernel of the syndrome map `lam ↦ syndFold cells
lam` is exactly the tabulated span — a millisecond-scale check.

A certificate is a pivot list `piv : List (Nat × Nat)` in elimination
order: entry `(j, r)` says check row `r` hits the column of cell
position `j`, no later pivot position's column, and `j` itself is
distinct from all later pivot positions.  `peel` shows a mask supported
on the pivot positions with zero syndrome must be zero;
`kernel_classify_dim1/dim2` add the free positions and the kernel
generators and classify every zero-syndrome mask into the span
(`{0, g}` resp. `{0, g₁, g₂, g₁ ^^^ g₂}`).  All certificate conditions
are one `Bool` (`cert1B`/`cert2B`) discharged per class by a cheap
`native_decide` in the sweep leaves.
-/

namespace Quantum
namespace Stabilizer
namespace Homological
namespace BB
namespace Z5Z15F2A6

/-! ## Bit-level helpers -/

lemma testBit_zero_iff (n : Nat) : n.testBit 0 = true ↔ n % 2 = 1 := by
  rw [Nat.testBit_zero]
  exact decide_eq_true_iff

lemma testBit_zero_false_iff (n : Nat) : n.testBit 0 = false ↔ n % 2 = 0 := by
  rw [Nat.testBit_zero, decide_eq_false_iff_not]
  omega

lemma xor_div_two (a b : Nat) : (a ^^^ b) / 2 = a / 2 ^^^ b / 2 := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp [Nat.testBit_div_two, Nat.testBit_xor]

lemma natSubset_or_left {a m m' : Nat} (h : natSubset a m) :
    natSubset a (m ||| m') := by
  unfold natSubset at h ⊢
  apply Nat.eq_of_testBit_eq
  intro i
  have hi := congrArg (fun x => x.testBit i) h
  simp only [Nat.testBit_and, Nat.testBit_or] at hi ⊢
  cases ha : a.testBit i <;> cases hm : m.testBit i <;>
    simp [ha, hm] at hi ⊢

lemma natSubset_or_right {a m m' : Nat} (h : natSubset a m') :
    natSubset a (m ||| m') := by
  unfold natSubset at h ⊢
  apply Nat.eq_of_testBit_eq
  intro i
  have hi := congrArg (fun x => x.testBit i) h
  simp only [Nat.testBit_and, Nat.testBit_or] at hi ⊢
  cases ha : a.testBit i <;> cases hm : m'.testBit i <;>
    simp [ha, hm] at hi ⊢

lemma natSubset_self (a : Nat) : natSubset a a := by
  unfold natSubset
  rw [Nat.and_self]

lemma natSubset_xor_or {a b A B : Nat} (ha : natSubset a A)
    (hb : natSubset b B) : natSubset (a ^^^ b) (A ||| B) := by
  unfold natSubset at ha hb ⊢
  apply Nat.eq_of_testBit_eq
  intro i
  have hia := congrArg (fun x => x.testBit i) ha
  have hib := congrArg (fun x => x.testBit i) hb
  simp only [Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor] at hia hib ⊢
  cases h1 : a.testBit i <;> cases h2 : b.testBit i <;>
    cases h3 : A.testBit i <;> cases h4 : B.testBit i <;>
    simp [h1, h2, h3, h4] at hia hib ⊢

lemma natSubset_testBit_false {a m : Nat} (h : natSubset a m) {i : Nat}
    (hm : m.testBit i = false) : a.testBit i = false := by
  unfold natSubset at h
  have hi := congrArg (fun x => x.testBit i) h
  simp only [Nat.testBit_and, hm, Bool.and_false] at hi
  exact hi.symm

lemma natSubset_or_elim_bit {a m : Nat} {j : Nat}
    (h : natSubset a ((1 <<< j) ||| m)) (hj : a.testBit j = false) :
    natSubset a m := by
  unfold natSubset at h ⊢
  apply Nat.eq_of_testBit_eq
  intro i
  have hi := congrArg (fun x => x.testBit i) h
  simp only [Nat.testBit_and, Nat.testBit_or, Nat.one_shiftLeft,
    Nat.testBit_two_pow] at hi
  simp only [Nat.testBit_and]
  by_cases hij : i = j
  · subst hij
    simp [hj]
  · have hne : ¬ (j = i) := fun hc => hij hc.symm
    simp only [hne, decide_false, Bool.false_or] at hi
    cases ha : a.testBit i <;> cases hm : m.testBit i <;>
      simp [ha, hm] at hi ⊢

lemma natSubset_xor_single {lam m : Nat} {j : Nat}
    (h : natSubset lam ((1 <<< j) ||| m)) (hm : m.testBit j = false)
    (hbit : lam.testBit j = true) :
    natSubset (lam ^^^ (1 <<< j)) m := by
  unfold natSubset at h ⊢
  apply Nat.eq_of_testBit_eq
  intro i
  have hi := congrArg (fun x => x.testBit i) h
  simp only [Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor,
    Nat.one_shiftLeft, Nat.testBit_two_pow] at hi ⊢
  by_cases hij : i = j
  · subst hij
    simp [hbit, hm]
  · have hne : ¬ (j = i) := fun hc => hij hc.symm
    simp only [hne, decide_false, Bool.false_or, Bool.xor_false] at hi ⊢
    cases ha : lam.testBit i <;> cases hmm : m.testBit i <;>
      simp [ha, hmm] at hi ⊢

lemma natSubset_of_lt_cover {x L : Nat} {pm : Nat} {fs : Nat}
    (hx : x < 2 ^ L) (hcov : (pm ||| fs) = 2 ^ L - 1)
    (hfs : ∀ i, fs.testBit i = true → x.testBit i = false) :
    natSubset x pm := by
  unfold natSubset
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_and]
  by_cases hiL : i < L
  · have hcovi := congrArg (fun y => y.testBit i) hcov
    simp only [Nat.testBit_or, Nat.testBit_two_pow_sub_one, hiL,
      decide_true] at hcovi
    cases hp : pm.testBit i
    · cases hf : fs.testBit i
      · simp [hp, hf] at hcovi
      · simp [hfs i hf]
    · simp
  · have hxi : x.testBit i = false := by
      apply Nat.testBit_eq_false_of_lt
      calc x < 2 ^ L := hx
        _ ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
    simp [hxi]

lemma xor_lt_two_pow {a b n : Nat} (ha : a < 2 ^ n) (hb : b < 2 ^ n) :
    a ^^^ b < 2 ^ n := by
  have hsub : ∀ x : Nat, x < 2 ^ n → natSubset x (2 ^ n - 1) := by
    intro x hx
    unfold natSubset
    rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt hx]
  have h := natSubset_xor_or (hsub a ha) (hsub b hb)
  rw [Nat.or_self] at h
  have hle : a ^^^ b ≤ 2 ^ n - 1 := by
    conv_lhs => rw [← h]
    exact Nat.and_le_right
  have hpos := Nat.two_pow_pos n
  omega

/-! ## Syndrome-fold algebra -/

lemma syndFold_zero_lam (cells : List Nat) : syndFold cells 0 = 0 := by
  induction cells with
  | nil => rfl
  | cons c cs ih => simp [syndFold_cons, ih]

lemma syndFold_xor (cells : List Nat) (a b : Nat) :
    syndFold cells (a ^^^ b) = syndFold cells a ^^^ syndFold cells b := by
  induction cells generalizing a b with
  | nil => simp [syndFold_nil]
  | cons c cs ih =>
    rw [syndFold_cons, syndFold_cons, syndFold_cons, xor_div_two, ih]
    by_cases ha : a % 2 = 1 <;> by_cases hb : b % 2 = 1
    · have hta := (testBit_zero_iff a).mpr ha
      have htb := (testBit_zero_iff b).mpr hb
      have hab : (a ^^^ b) % 2 = 0 := by
        apply (testBit_zero_false_iff _).mp
        simp only [Nat.testBit_xor, hta, htb]
        decide
      apply Nat.eq_of_testBit_eq
      intro i
      simp [hab, ha, hb, Nat.testBit_xor, Bool.xor_left_comm]
    · have hb0 : b % 2 = 0 := by omega
      have hta := (testBit_zero_iff a).mpr ha
      have htb := (testBit_zero_false_iff b).mpr hb0
      have hab : (a ^^^ b) % 2 = 1 := by
        apply (testBit_zero_iff _).mp
        simp only [Nat.testBit_xor, hta, htb]
        decide
      apply Nat.eq_of_testBit_eq
      intro i
      simp [hab, ha, hb, Nat.testBit_xor]
    · have ha0 : a % 2 = 0 := by omega
      have hta := (testBit_zero_false_iff a).mpr ha0
      have htb := (testBit_zero_iff b).mpr hb
      have hab : (a ^^^ b) % 2 = 1 := by
        apply (testBit_zero_iff _).mp
        simp only [Nat.testBit_xor, hta, htb]
        decide
      apply Nat.eq_of_testBit_eq
      intro i
      simp [hab, ha, hb, Nat.testBit_xor, Bool.xor_left_comm]
    · have ha0 : a % 2 = 0 := by omega
      have hb0 : b % 2 = 0 := by omega
      have hta := (testBit_zero_false_iff a).mpr ha0
      have htb := (testBit_zero_false_iff b).mpr hb0
      have hab : (a ^^^ b) % 2 = 0 := by
        apply (testBit_zero_false_iff _).mp
        simp only [Nat.testBit_xor, hta, htb]
        decide
      apply Nat.eq_of_testBit_eq
      intro i
      simp [hab, ha, hb, Nat.testBit_xor]

lemma syndFold_single (cells : List Nat) (j : Nat) (hj : j < cells.length) :
    syndFold cells (1 <<< j) = colMaskPacked (cells.getD j 0) := by
  induction cells generalizing j with
  | nil => simp at hj
  | cons c cs ih =>
    cases j with
    | zero =>
      have h1 : (1 <<< 0 : Nat) = 1 := by
        rw [Nat.one_shiftLeft, pow_zero]
      rw [syndFold_cons, h1, if_pos (by norm_num : (1 : Nat) % 2 = 1),
        (by norm_num : (1 : Nat) / 2 = 0), syndFold_zero_lam, Nat.xor_zero]
      rfl
    | succ j' =>
      rw [syndFold_cons, Nat.one_shiftLeft]
      have h2 : 2 ^ (j' + 1) % 2 = 0 := by
        rw [pow_succ, Nat.mul_mod_left]
      have hd : 2 ^ (j' + 1) / 2 = 2 ^ j' := by
        rw [pow_succ]
        exact Nat.mul_div_cancel _ (by norm_num)
      rw [if_neg (by omega), hd, ← Nat.one_shiftLeft, Nat.zero_xor]
      have hj' : j' < cs.length := by
        have : j' + 1 < cs.length + 1 := hj
        omega
      rw [ih j' hj']
      rfl

/-! ## Pivot certificates -/

/-- Packed position mask of a pivot list. -/
def posMask : List (Nat × Nat) → Nat
  | [] => 0
  | p :: rest => (1 <<< p.1) ||| posMask rest

/-- OR of the columns at a pivot list's positions. -/
def selCols (cells : List Nat) : List (Nat × Nat) → Nat
  | [] => 0
  | p :: rest => colMaskPacked (cells.getD p.1 0) ||| selCols cells rest

/-- Triangularity: each pivot `(j, r)` has row `r` in cell `j`'s column,
`r` absent from every later pivot's column, and position `j` distinct
from every later pivot position. -/
def pivB (cells : List Nat) : List (Nat × Nat) → Bool
  | [] => true
  | (j, r) :: rest =>
      decide (j < cells.length)
      && (colMaskPacked (cells.getD j 0)).testBit r
      && !((selCols cells rest).testBit r)
      && !((posMask rest).testBit j)
      && pivB cells rest

/-- The syndrome of a mask supported on a pivot list's positions lands in
the OR of that list's columns. -/
lemma syndFold_subset_selCols (cells : List Nat) :
    ∀ piv : List (Nat × Nat), pivB cells piv = true →
      ∀ lam, natSubset lam (posMask piv) →
        natSubset (syndFold cells lam) (selCols cells piv) := by
  intro piv
  induction piv with
  | nil =>
    intro _ lam hsub
    unfold posMask at hsub
    unfold natSubset at hsub
    rw [Nat.and_zero] at hsub
    rw [← hsub, syndFold_zero_lam]
    exact natSubset_zero _
  | cons q rest ih =>
    obtain ⟨j', r'⟩ := q
    intro hpiv lam hsub
    simp only [pivB, Bool.and_eq_true, Bool.not_eq_true',
      decide_eq_true_eq] at hpiv
    obtain ⟨⟨⟨⟨hj', _hcol'⟩, _hsel'⟩, hpos'⟩, hrest'⟩ := hpiv
    show natSubset (syndFold cells lam)
      (colMaskPacked (cells.getD j' 0) ||| selCols cells rest)
    cases hbit' : lam.testBit j'
    · exact natSubset_or_right
        (ih hrest' lam
          (natSubset_or_elim_bit
            (show natSubset lam ((1 <<< j') ||| posMask rest) from hsub)
            hbit'))
    · have hsub₃ : natSubset (lam ^^^ (1 <<< j')) (posMask rest) :=
        natSubset_xor_single
          (show natSubset lam ((1 <<< j') ||| posMask rest) from hsub)
          hpos' hbit'
      have hlam' : (lam ^^^ (1 <<< j')) ^^^ (1 <<< j') = lam := by
        rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
      have hdec : syndFold cells lam
          = syndFold cells (lam ^^^ (1 <<< j'))
            ^^^ colMaskPacked (cells.getD j' 0) := by
        rw [← syndFold_single cells j' hj', ← syndFold_xor, hlam']
      rw [hdec]
      have h2 := natSubset_xor_or (ih hrest' _ hsub₃)
        (natSubset_self (colMaskPacked (cells.getD j' 0)))
      rw [Nat.or_comm] at h2
      exact h2

/-- A zero-syndrome mask supported on the pivot positions is zero. -/
lemma peel (cells : List Nat) :
    ∀ piv : List (Nat × Nat), pivB cells piv = true →
      ∀ lam, natSubset lam (posMask piv) → syndFold cells lam = 0 →
        lam = 0 := by
  intro piv
  induction piv with
  | nil =>
    intro _ lam hsub _
    unfold posMask at hsub
    unfold natSubset at hsub
    rw [Nat.and_zero] at hsub
    exact hsub.symm
  | cons q rest ih =>
    obtain ⟨j, r⟩ := q
    intro hpiv lam hsub hsynd
    simp only [pivB, Bool.and_eq_true, Bool.not_eq_true',
      decide_eq_true_eq] at hpiv
    obtain ⟨⟨⟨⟨hj, hcol⟩, hsel⟩, hpos⟩, hrest⟩ := hpiv
    cases hbit : lam.testBit j
    · exact ih hrest lam
        (natSubset_or_elim_bit
          (show natSubset lam ((1 <<< j) ||| posMask rest) from hsub) hbit)
        hsynd
    · exfalso
      have hsub₂ : natSubset (lam ^^^ (1 <<< j)) (posMask rest) :=
        natSubset_xor_single
          (show natSubset lam ((1 <<< j) ||| posMask rest) from hsub)
          hpos hbit
      have hlam : (lam ^^^ (1 <<< j)) ^^^ (1 <<< j) = lam := by
        rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
      have hdecomp : syndFold cells (lam ^^^ (1 <<< j))
          = colMaskPacked (cells.getD j 0) := by
        have h0 : syndFold cells (lam ^^^ (1 <<< j))
            ^^^ syndFold cells (1 <<< j) = 0 := by
          rw [← syndFold_xor, hlam, hsynd]
        have h1 := congrArg (fun x => x ^^^ syndFold cells (1 <<< j)) h0
        simp only [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero,
          Nat.zero_xor] at h1
        rw [h1, syndFold_single cells j hj]
      have hbnd := syndFold_subset_selCols cells rest hrest _ hsub₂
      have hbitr := natSubset_testBit_false hbnd hsel
      rw [hdecomp, hcol] at hbitr
      exact Bool.noConfusion hbitr

/-! ## Kernel classification -/

/-- Dim-1 certificate: pivots + one free position `f` + one generator. -/
def cert1B (cells : List Nat) (piv : List (Nat × Nat)) (f g : Nat) : Bool :=
  pivB cells piv
  && ((posMask piv ||| (1 <<< f)) == 2 ^ cells.length - 1)
  && ((posMask piv &&& (1 <<< f)) == 0)
  && g.testBit f
  && decide (g < 2 ^ cells.length)
  && (syndFold cells g == 0)

/-- Dim-2 certificate: pivots + two free positions + two δ-normalized
generators. -/
def cert2B (cells : List Nat) (piv : List (Nat × Nat))
    (f₁ f₂ g₁ g₂ : Nat) : Bool :=
  pivB cells piv
  && ((posMask piv ||| (1 <<< f₁) ||| (1 <<< f₂)) == 2 ^ cells.length - 1)
  && ((posMask piv &&& ((1 <<< f₁) ||| (1 <<< f₂))) == 0)
  && g₁.testBit f₁ && !(g₁.testBit f₂)
  && g₂.testBit f₂ && !(g₂.testBit f₁)
  && decide (g₁ < 2 ^ cells.length)
  && decide (g₂ < 2 ^ cells.length)
  && (syndFold cells g₁ == 0)
  && (syndFold cells g₂ == 0)

/-- Every zero-syndrome mask below `2^L` is `0` or the generator. -/
theorem kernel_classify_dim1 {cells : List Nat} {piv : List (Nat × Nat)}
    {f g : Nat} (hc : cert1B cells piv f g = true) :
    ∀ lam, lam < 2 ^ cells.length → syndFold cells lam = 0 →
      lam = 0 ∨ lam = g := by
  simp only [cert1B, Bool.and_eq_true, beq_iff_eq,
    decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨hpiv, hcov⟩, _hdisj⟩, hgf⟩, hglt⟩, hgker⟩ := hc
  intro lam hlt hsynd
  have hfree : ∀ x : Nat, x.testBit f = false →
      ∀ i, ((1 <<< f) : Nat).testBit i = true → x.testBit i = false := by
    intro x hx i hi
    have hfi : f = i := by
      simpa [Nat.one_shiftLeft, Nat.testBit_two_pow] using hi
    rwa [← hfi]
  cases hbit : lam.testBit f
  · left
    exact peel cells piv hpiv lam
      (natSubset_of_lt_cover hlt hcov (hfree lam hbit)) hsynd
  · right
    have hlt₂ : lam ^^^ g < 2 ^ cells.length := xor_lt_two_pow hlt hglt
    have hsynd₂ : syndFold cells (lam ^^^ g) = 0 := by
      rw [syndFold_xor, hsynd, hgker, Nat.xor_self]
    have hbit₂ : (lam ^^^ g).testBit f = false := by
      simp [Nat.testBit_xor, hbit, hgf]
    have h0 := peel cells piv hpiv (lam ^^^ g)
      (natSubset_of_lt_cover hlt₂ hcov (hfree _ hbit₂)) hsynd₂
    have h1 := congrArg (fun x => x ^^^ g) h0
    simpa [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero,
      Nat.zero_xor] using h1

/-- Every zero-syndrome mask below `2^L` lies in the span of the two
generators. -/
theorem kernel_classify_dim2 {cells : List Nat} {piv : List (Nat × Nat)}
    {f₁ f₂ g₁ g₂ : Nat} (hc : cert2B cells piv f₁ f₂ g₁ g₂ = true) :
    ∀ lam, lam < 2 ^ cells.length → syndFold cells lam = 0 →
      lam = 0 ∨ lam = g₁ ∨ lam = g₂ ∨ lam = g₁ ^^^ g₂ := by
  simp only [cert2B, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq,
    decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hpiv, hcov⟩, _hdisj⟩, hg1f1⟩, hg1f2⟩, hg2f2⟩,
    hg2f1⟩, hg1lt⟩, hg2lt⟩, hg1ker⟩, hg2ker⟩ := hc
  intro lam hlt hsynd
  have hcov' : (posMask piv ||| ((1 <<< f₁) ||| (1 <<< f₂)))
      = 2 ^ cells.length - 1 := by
    rw [← Nat.or_assoc]
    exact hcov
  have main : ∀ c, (c = 0 ∨ c = g₁ ∨ c = g₂ ∨ c = g₁ ^^^ g₂) →
      (lam ^^^ c).testBit f₁ = false → (lam ^^^ c).testBit f₂ = false →
      c < 2 ^ cells.length → syndFold cells c = 0 →
      lam = 0 ∨ lam = g₁ ∨ lam = g₂ ∨ lam = g₁ ^^^ g₂ := by
    intro c hcmem hcb1 hcb2 hclt hcker
    have hlt₂ : lam ^^^ c < 2 ^ cells.length := xor_lt_two_pow hlt hclt
    have hsynd₂ : syndFold cells (lam ^^^ c) = 0 := by
      rw [syndFold_xor, hsynd, hcker, Nat.xor_self]
    have hfree : ∀ i, ((1 <<< f₁) ||| (1 <<< f₂) : Nat).testBit i = true →
        (lam ^^^ c).testBit i = false := by
      intro i hi
      have := hi
      simp only [Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow,
        Bool.or_eq_true, decide_eq_true_eq] at this
      rcases this with h | h
      · rwa [← h]
      · rwa [← h]
    have h0 := peel cells piv hpiv (lam ^^^ c)
      (natSubset_of_lt_cover hlt₂ hcov' hfree) hsynd₂
    have h1 := congrArg (fun x => x ^^^ c) h0
    simp only [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero,
      Nat.zero_xor] at h1
    rw [h1]
    exact hcmem
  have hg12lt : g₁ ^^^ g₂ < 2 ^ cells.length := xor_lt_two_pow hg1lt hg2lt
  have hg12ker : syndFold cells (g₁ ^^^ g₂) = 0 := by
    rw [syndFold_xor, hg1ker, hg2ker, Nat.xor_self]
  cases hb1 : lam.testBit f₁ <;> cases hb2 : lam.testBit f₂
  · exact main 0 (Or.inl rfl) (by simp [hb1]) (by simp [hb2])
      (Nat.two_pow_pos _) (syndFold_zero_lam cells)
  · exact main g₂ (Or.inr (Or.inr (Or.inl rfl)))
      (by simp [Nat.testBit_xor, hb1, hg2f1])
      (by simp [Nat.testBit_xor, hb2, hg2f2]) hg2lt hg2ker
  · exact main g₁ (Or.inr (Or.inl rfl))
      (by simp [Nat.testBit_xor, hb1, hg1f1])
      (by simp [Nat.testBit_xor, hb2, hg1f2]) hg1lt hg1ker
  · exact main (g₁ ^^^ g₂) (Or.inr (Or.inr (Or.inr rfl)))
      (by simp [Nat.testBit_xor, hb1, hg1f1, hg2f1])
      (by simp [Nat.testBit_xor, hb2, hg1f2, hg2f2]) hg12lt hg12ker

end Z5Z15F2A6
end BB
end Homological
end Stabilizer
end Quantum
