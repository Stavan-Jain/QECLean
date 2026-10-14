/-
# Brouwer–Zimmermann certificates for `𝔽₂` codes

A *weight floor* — every word of a binary linear code of weight `≤ W` has some
property — is certified here by the Brouwer–Zimmermann argument, made
kernel-checkable on packed `Nat` masks (`F2Mask.lean`).

* **Windows.** A window is a list of `(pivot bit, row)` pairs whose rows are a
  systematic generator matrix: every codeword `M` is the XOR of the rows whose
  pivot bit is set in `M` (`reconX w M = M`). Rows may carry *tag* bits above
  the word length `n`, so the reconstruction also reports which coset of a
  subcode the word lies in.
* **The walk.** `xorWalk ok rows t 0` visits the XOR of every non-empty sub-list
  of at most `t` rows (`xorWalk_sound`).
* **The two-window argument** (`bz_two_window`). With two windows on disjoint
  pivot sets, a word of weight `< t₁ + t₂ + 2` has at most `t₁` pivots in the
  first window or at most `t₂` in the second, so one of the two walks visited
  it.
* **Generators.** `bz_ok_of_xorSpan` applies this to every word in the XOR-span
  of a generator list, given that each window reconstructs each generator.

The kernel cost is the size of the walks, so `xor_walk_decide` splits a walk
into one `decide +kernel` per first-chosen row: each becomes its own auxiliary
lemma with its own kernel cache.

`peelOK_sound` / `kernel_eq_sum_of_peel` are the companion certificate for a
kernel basis: Gaussian elimination written out as its elimination order.
-/

import QEC.Stabilizer.Framework.Homological.F2Mask
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.CharP.Two
import Mathlib.Data.ZMod.Basic

namespace Quantum
namespace Stabilizer
namespace Homological
namespace F2Mask

/-! ## The walk -/

/-- `xorWalk ok rows t acc` is `true` iff `ok (acc ^^^ xorList S)` holds for
every non-empty sub-list `S` of `rows` with at most `t` entries. (`Nat.xor`
rather than `^^^`: the kernel evaluates it without unfolding the notation's
instances.) -/
def xorWalk (ok : ℕ → Bool) : List ℕ → ℕ → ℕ → Bool
  | [], _, _ => true
  | _ :: _, 0, _ => true
  | r :: rs, t + 1, acc =>
      (ok (Nat.xor acc r) && xorWalk ok rs t (Nat.xor acc r)) && xorWalk ok rs (t + 1) acc

theorem xorWalk_sound {ok : ℕ → Bool} {rows : List ℕ} :
    ∀ {t acc : ℕ}, xorWalk ok rows t acc = true →
      ∀ {S : List ℕ}, S.Sublist rows → S ≠ [] → S.length ≤ t →
        ok (acc ^^^ xorList S) = true := by
  induction rows with
  | nil =>
    intro t acc _ S hS hne _
    exact absurd (List.sublist_nil.mp hS) hne
  | cons r rs ih =>
    intro t acc h S hS hne hlen
    cases t with
    | zero => exact absurd (List.length_eq_zero_iff.mp (by omega)) hne
    | succ t =>
      simp only [xorWalk, Bool.and_eq_true] at h
      rcases List.sublist_cons_iff.mp hS with hS' | ⟨S', rfl, hS'⟩
      · exact ih h.2 hS' hne hlen
      · rw [xorList_cons, ← Nat.xor_assoc]
        by_cases hS'0 : S' = []
        · subst hS'0
          rw [xorList_nil, Nat.xor_zero]
          exact h.1.1
        · exact ih h.1.2 hS' hS'0 (by simpa using hlen)

/-- Peel off the first row of a walk: the sub-lists containing it (one Boolean),
then the rest. -/
theorem xorWalk_cons_intro {ok : ℕ → Bool} {r : ℕ} {rs : List ℕ} {t acc : ℕ}
    (h₁ : (ok (Nat.xor acc r) && xorWalk ok rs t (Nat.xor acc r)) = true)
    (h₂ : xorWalk ok rs (t + 1) acc = true) : xorWalk ok (r :: rs) (t + 1) acc = true := by
  rw [xorWalk, h₁, h₂]
  rfl

/-- Close `xorWalk ok rows t acc = true` for a literal `rows`, with one
`decide +kernel` — one auxiliary lemma, so one kernel cache — per first-chosen
row. -/
syntax "xor_walk_decide" : tactic
macro_rules
  | `(tactic| xor_walk_decide) => `(tactic|
      first
      | (refine xorWalk_cons_intro (by decide +kernel) ?_
         xor_walk_decide)
      | decide +kernel)

/-- `xor_walk_decide`, splitting two levels deep (one kernel check per pair of
first-chosen rows), for walks whose one-level chunks are still large. -/
syntax "xor_walk_decide₂" : tactic
macro_rules
  | `(tactic| xor_walk_decide₂) => `(tactic|
      first
      | (refine xorWalk_cons_intro ?_ ?_
         · rw [Bool.and_eq_true]
           exact ⟨by decide +kernel, by xor_walk_decide⟩
         xor_walk_decide₂)
      | decide +kernel)

/-! ## Reconstruction through a window -/

/-- The XOR of the rows of window `w` whose pivot bit is set in `M`. -/
def reconX (w : List (ℕ × ℕ)) (M : ℕ) : ℕ :=
  xorList ((w.filter fun pr => M.testBit pr.1).map Prod.snd)

private lemma xor_left_comm (x y z : ℕ) : x ^^^ (y ^^^ z) = y ^^^ (x ^^^ z) := by
  rw [← Nat.xor_assoc, Nat.xor_comm x y, Nat.xor_assoc]

private lemma xor_xor_cancel (r x y : ℕ) : (r ^^^ x) ^^^ (r ^^^ y) = x ^^^ y := by
  rw [Nat.xor_assoc, xor_left_comm x, ← Nat.xor_assoc r r, Nat.xor_self, Nat.zero_xor]

lemma reconX_zero (w : List (ℕ × ℕ)) : reconX w 0 = 0 := by
  simp [reconX]

lemma reconX_xor (w : List (ℕ × ℕ)) (a b : ℕ) :
    reconX w (a ^^^ b) = reconX w a ^^^ reconX w b := by
  induction w with
  | nil => simp [reconX]
  | cons pr w ih =>
    simp only [reconX] at ih ⊢
    rw [List.filter_cons, List.filter_cons, List.filter_cons, Nat.testBit_xor]
    cases ha : a.testBit pr.1 <;> cases hb : b.testBit pr.1 <;>
      simp only [Bool.xor_false, Bool.xor_true, Bool.not_true,
        Bool.not_false, Bool.false_eq_true, if_false, if_true, List.map_cons,
        xorList_cons, ih]
    · rw [xor_left_comm]
    · rw [Nat.xor_assoc]
    · rw [xor_xor_cancel]

/-! ## The two-window argument -/

/-- Distinct pivots below `n` set in `M` number at most `bitCount n M`. -/
lemma filter_testBit_length_le {n M : ℕ} {P : List ℕ} (hnd : P.Nodup)
    (hlt : ∀ p ∈ P, p < n) : (P.filter fun p => M.testBit p).length ≤ bitCount n M := by
  rw [bitCount_eq_card, ← List.toFinset_card_of_nodup (hnd.filter _)]
  refine Finset.card_le_card fun p hp => ?_
  simp only [List.mem_toFinset, List.mem_filter] at hp
  simp [hlt p hp.1, hp.2]

lemma window_length (w : List (ℕ × ℕ)) (M : ℕ) :
    (w.filter fun pr => M.testBit pr.1).length
      = ((w.map Prod.fst).filter fun p => M.testBit p).length := by
  rw [List.filter_map, List.length_map]
  rfl

/-- A walk over a window covers every word with at most `t` pivots set. -/
lemma ok_reconX_of_walk {ok : ℕ → Bool} (h0 : ok 0 = true) {w : List (ℕ × ℕ)} {t : ℕ}
    (hw : xorWalk ok (w.map Prod.snd) t 0 = true) {M : ℕ}
    (hlen : (w.filter fun pr => M.testBit pr.1).length ≤ t) : ok (reconX w M) = true := by
  by_cases hS : (w.filter fun pr => M.testBit pr.1).map Prod.snd = []
  · rw [reconX, hS, xorList_nil]
    exact h0
  · have := xorWalk_sound hw (List.filter_sublist.map _) hS (by simpa using hlen)
    rwa [Nat.zero_xor] at this

/-- **The two-window argument.** If the pivots of the two windows are distinct
and below `n`, every word of weight `< t₁ + t₂ + 2` is reconstructed through a
window whose walk visited it. -/
theorem bz_two_window {ok : ℕ → Bool} {w₁ w₂ : List (ℕ × ℕ)} {n t₁ t₂ : ℕ}
    (hnd : (w₁.map Prod.fst ++ w₂.map Prod.fst).Nodup)
    (hlt : ∀ p ∈ w₁.map Prod.fst ++ w₂.map Prod.fst, p < n)
    (h0 : ok 0 = true)
    (hw₁ : xorWalk ok (w₁.map Prod.snd) t₁ 0 = true)
    (hw₂ : xorWalk ok (w₂.map Prod.snd) t₂ 0 = true)
    {M : ℕ} (hM : bitCount n M < t₁ + t₂ + 2) :
    ok (reconX w₁ M) = true ∨ ok (reconX w₂ M) = true := by
  have hsum := filter_testBit_length_le (M := M) hnd hlt
  rw [List.filter_append, List.length_append, ← window_length, ← window_length] at hsum
  by_cases h₁ : (w₁.filter fun pr => M.testBit pr.1).length ≤ t₁
  · exact Or.inl (ok_reconX_of_walk h0 hw₁ h₁)
  · exact Or.inr (ok_reconX_of_walk h0 hw₂ (by omega))

/-! ## Codes given by generators -/

/-- The XOR-span of a list of masks. -/
inductive XorSpan (gens : List ℕ) : ℕ → Prop
  | zero : XorSpan gens 0
  | step {g x : ℕ} : g ∈ gens → XorSpan gens x → XorSpan gens (g ^^^ x)

lemma XorSpan.of_mem {gens : List ℕ} {g : ℕ} (hg : g ∈ gens) : XorSpan gens g := by
  simpa using XorSpan.step hg .zero

lemma XorSpan.xor {gens : List ℕ} {a b : ℕ} (ha : XorSpan gens a) (hb : XorSpan gens b) :
    XorSpan gens (a ^^^ b) := by
  induction ha with
  | zero => simpa using hb
  | step hg _ ih => rw [Nat.xor_assoc]; exact .step hg ih

lemma xor_mod_two_pow (a b n : ℕ) : (a ^^^ b) % 2 ^ n = a % 2 ^ n ^^^ b % 2 ^ n := by
  refine Nat.eq_of_testBit_eq fun i => ?_
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_xor]
  cases decide (i < n) <;> simp

/-- A window that reconstructs every generator (from its low `n` bits)
reconstructs every word of the span. -/
lemma reconX_of_xorSpan {w : List (ℕ × ℕ)} {n : ℕ} {gens : List ℕ}
    (hgen : ∀ g ∈ gens, reconX w (g % 2 ^ n) = g) {X : ℕ} (hX : XorSpan gens X) :
    reconX w (X % 2 ^ n) = X := by
  induction hX with
  | zero => simp [reconX_zero]
  | step hg _ ih => rw [xor_mod_two_pow, reconX_xor, hgen _ hg, ih]

/-- **Brouwer–Zimmermann for a code given by generators.** Every word `X` of the
XOR-span of `gens` whose low `n` bits have weight `< t₁ + t₂ + 2` satisfies
`ok`, provided both windows reconstruct every generator and both walks pass. -/
theorem bz_ok_of_xorSpan {ok : ℕ → Bool} {w₁ w₂ : List (ℕ × ℕ)} {n t₁ t₂ : ℕ}
    (hnd : (w₁.map Prod.fst ++ w₂.map Prod.fst).Nodup)
    (hlt : ∀ p ∈ w₁.map Prod.fst ++ w₂.map Prod.fst, p < n)
    (h0 : ok 0 = true)
    (hw₁ : xorWalk ok (w₁.map Prod.snd) t₁ 0 = true)
    (hw₂ : xorWalk ok (w₂.map Prod.snd) t₂ 0 = true)
    {gens : List ℕ} (hgen₁ : ∀ g ∈ gens, reconX w₁ (g % 2 ^ n) = g)
    (hgen₂ : ∀ g ∈ gens, reconX w₂ (g % 2 ^ n) = g)
    {X : ℕ} (hX : XorSpan gens X) (hwt : bitCount n X < t₁ + t₂ + 2) : ok X = true := by
  rw [← bitCount_mod] at hwt
  rcases bz_two_window hnd hlt h0 hw₁ hw₂ hwt with h | h
  · rwa [reconX_of_xorSpan hgen₁ hX] at h
  · rwa [reconX_of_xorSpan hgen₂ hX] at h

/-! ## Kernel bases by peeling -/

section Peel

variable {H Q : Type*} [DecidableEq H]

/-- A peeling certificate: each step `(h, q)` reads row `q`, which meets `h`
exactly once and whose other cells are already known to vanish; `h` then joins
the known cells. -/
def peelOK (rowCells : Q → List H) : List H → List (H × Q) → Bool
  | _, [] => true
  | known, (h, q) :: rest =>
      ((rowCells q).count h == 1 && (rowCells q).all fun x => x == h || known.contains x)
        && peelOK rowCells (h :: known) rest

private lemma sum_map_eq_count {l : List H} {h : H} {ζ : H → ZMod 2}
    (hz : ∀ x ∈ l, x ≠ h → ζ x = 0) : (l.map ζ).sum = (l.count h : ZMod 2) * ζ h := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.map_cons, List.sum_cons, ih fun x hx => hz x (List.mem_cons_of_mem a hx),
      List.count_cons]
    by_cases ha : a = h
    · subst ha
      simp only [beq_self_eq_true, if_true]
      push_cast
      ring
    · rw [hz a List.mem_cons_self ha]
      simp [ha]

/-- **Peeling.** A chain with vanishing rows that vanishes on the known cells
vanishes on every peeled cell. -/
theorem peelOK_sound (rowCells : Q → List H) (ζ : H → ZMod 2)
    (hrow : ∀ q, ((rowCells q).map ζ).sum = 0) :
    ∀ (steps : List (H × Q)) (known : List H), peelOK rowCells known steps = true →
      (∀ x ∈ known, ζ x = 0) → ∀ x ∈ steps.map Prod.fst, ζ x = 0 := by
  intro steps
  induction steps with
  | nil => simp
  | cons s rest ih =>
    obtain ⟨h, q⟩ := s
    intro known hok hknown
    simp only [peelOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, Bool.or_eq_true,
      List.contains_iff_mem] at hok
    obtain ⟨⟨hcount, hall⟩, hrest⟩ := hok
    have hh : ζ h = 0 := by
      have hsum := hrow q
      rw [sum_map_eq_count fun x hx hne => hknown x ((hall x hx).resolve_left hne),
        hcount, Nat.cast_one, one_mul] at hsum
      exact hsum
    have hknown' : ∀ x ∈ h :: known, ζ x = 0 := by
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hh
      · exact hknown x hx
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hh
    · exact ih (h :: known) hrest hknown' x hx

omit [DecidableEq H] in
private lemma list_sum_apply {α : Type*} (L : List (α → ZMod 2)) (x : α) :
    L.sum x = (L.map fun c => c x).sum := by
  induction L with
  | nil => simp
  | cons c L ih => simp [ih]

omit [DecidableEq H] in
private lemma sum_map_add_fn (l : List H) (x y : H → ZMod 2) :
    (l.map (x + y)).sum = (l.map x).sum + (l.map y).sum :=
  List.sum_map_add

omit [DecidableEq H] in
private lemma rowSum_listSum (l : List H) (L : List (H → ZMod 2)) :
    (l.map L.sum).sum = (L.map fun c => (l.map c).sum).sum := by
  induction L with
  | nil =>
    simp only [List.sum_nil, List.map_nil]
    exact List.sum_eq_zero fun y hy => by
      obtain ⟨x, _, rfl⟩ := List.mem_map.mp hy
      rfl
  | cons c L ih => rw [List.sum_cons, List.map_cons, List.sum_cons, ← ih, sum_map_add_fn]

omit [DecidableEq H] in
private lemma basis_eval {basis : List ((H → ZMod 2) × H)} (ζ : H → ZMod 2)
    (hdiag : ∀ b ∈ basis, b.1 b.2 = 1)
    (hpair : basis.Pairwise fun b b' => b.1 b'.2 = 0 ∧ b'.1 b.2 = 0) :
    ∀ b' ∈ basis, (basis.map fun b => ζ b.2 • b.1).sum b'.2 = ζ b'.2 := by
  induction basis with
  | nil => simp
  | cons c rest ih =>
    rw [List.pairwise_cons] at hpair
    intro b' hb'
    rw [List.map_cons, List.sum_cons, Pi.add_apply]
    by_cases hrest : b' ∈ rest
    · rw [ih (fun b hb => hdiag b (List.mem_cons_of_mem c hb)) hpair.2 b' hrest,
        Pi.smul_apply, (hpair.1 b' hrest).1, smul_zero, zero_add]
    · have hbc : b' = c := (List.mem_cons.mp hb').resolve_right hrest
      subst hbc
      have hzero : (rest.map fun b => ζ b.2 • b.1).sum b'.2 = 0 := by
        rw [list_sum_apply, List.map_map]
        refine List.sum_eq_zero fun y hy => ?_
        obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hy
        simp [(hpair.1 b hb).2]
      rw [hzero, add_zero, Pi.smul_apply, hdiag b' List.mem_cons_self, smul_eq_mul, mul_one]

/-- **A kernel basis from a peeling certificate.** If each basis vector `(k, F)`
is in the kernel of a row-sparse map `T`, is `1` at its free cell `F` and `0` at
the others, and peeling from the free cells reaches every cell, then every
kernel element is the combination of the basis read off its free cells. -/
theorem kernel_eq_sum_of_peel {T : (H → ZMod 2) → Q → ZMod 2} (rowCells : Q → List H)
    (hT : ∀ ζ q, T ζ q = ((rowCells q).map ζ).sum)
    (basis : List ((H → ZMod 2) × H)) (hker : ∀ b ∈ basis, T b.1 = 0)
    (hdiag : ∀ b ∈ basis, b.1 b.2 = 1)
    (hpair : basis.Pairwise fun b b' => b.1 b'.2 = 0 ∧ b'.1 b.2 = 0)
    (steps : List (H × Q)) (hpeel : peelOK rowCells (basis.map Prod.snd) steps = true)
    (hcover : ∀ x, x ∈ basis.map Prod.snd ∨ x ∈ steps.map Prod.fst)
    (ζ : H → ZMod 2) (hζ : T ζ = 0) : ζ = (basis.map fun b => ζ b.2 • b.1).sum := by
  obtain ⟨s, hs⟩ : ∃ s, s = (basis.map fun b => ζ b.2 • b.1).sum := ⟨_, rfl⟩
  have hrow : ∀ q, ((rowCells q).map (ζ + s)).sum = 0 := by
    intro q
    have hsq : ((rowCells q).map s).sum = 0 := by
      rw [hs, rowSum_listSum, List.map_map]
      refine List.sum_eq_zero fun y hy => ?_
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hy
      have hb0 := congrFun (hker b hb) q
      rw [hT, Pi.zero_apply] at hb0
      change ((rowCells q).map fun x => ζ b.2 * b.1 x).sum = 0
      rw [List.sum_map_mul_left, hb0, mul_zero]
    have hz := congrFun hζ q
    rw [hT, Pi.zero_apply] at hz
    rw [sum_map_add_fn, hz, hsq, add_zero]
  have hknown : ∀ x ∈ basis.map Prod.snd, (ζ + s) x = 0 := by
    intro x hx
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hx
    rw [Pi.add_apply, hs, basis_eval ζ hdiag hpair b hb, CharTwo.add_self_eq_zero]
  have key : ∀ a c : ZMod 2, a + c = 0 → a = c := by decide
  funext x
  rw [← hs]
  refine key _ _ ?_
  rcases hcover x with hx | hx
  · exact hknown x hx
  · exact peelOK_sound rowCells (ζ + s) hrow steps _ hpeel hknown x hx

end Peel

end F2Mask
end Homological
end Stabilizer
end Quantum
