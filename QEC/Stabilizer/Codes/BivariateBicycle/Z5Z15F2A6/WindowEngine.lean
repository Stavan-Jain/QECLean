/-
# Z5Z15F2A6 — the window sweep engine and its soundness bridge

Discharges the `hW` hypothesis of `dangerous_bound_of_window_general` for
the 19 near-kernel classes: every base 1-cycle with at most `t − 1` cells
outside the class window is one of the tabulated boundaries.

Architecture (the `Fin`-mask pattern of the Z3Z6 sweeps): chains
supported in a window are enumerated as *local* masks `λ < 2^m` over the
window's cell list (`m = |W| ≤ 26`); `localChainOf`/`localMaskOf`
convert by structural recursion on the list (bit 0 = head), so every
bridge lemma is a clean list induction; the cycle test is a packed-`Nat`
XOR fold of per-cell `∂₁`-column masks, certified against the semantic
columns by one `native_decide`.  The sweeps themselves are decidable
`∀ λ : Fin (2^m)` statements discharged per class in `SweepWin.lean`.

This file proves the `|O| = 0` bridge (`window_sound_base`): a cycle
supported inside the window is `0` or the tabulated window cycle, hence
a boundary.  The `|O| ∈ {1, 2}` extensions (extra cells + the escape
argument) build on the same keystones.
-/

import QEC.Stabilizer.Codes.BivariateBicycle.Z5Z15F2A6.Classification

namespace Quantum
namespace Stabilizer
namespace Homological
namespace BB
namespace Z5Z15F2A6

open scoped BigOperators

set_option maxRecDepth 4096

/-! ## Cell coordinates -/

/-- Global coordinate of a 1-chain cell id (total; the engine only uses
ids `< 150`). -/
def coordOfC1 (i : Nat) : G150 × Fin 2 :=
  ((((i % 75) / 15 : ℕ), ((i % 75) % 15 : ℕ)),
    ⟨(i / 75) % 2, Nat.mod_lt _ (by norm_num)⟩)

theorem coordOfC1_cellIdx : ∀ j : G150 × Fin 2, coordOfC1 (cellIdx j) = j := by
  decide

theorem cellIdx_coordOfC1 : ∀ i : Fin 150, cellIdx (coordOfC1 i.val) = i.val := by
  decide

theorem cellIdx_lt : ∀ j : G150 × Fin 2, cellIdx j < 150 := by
  decide

/-! ## The 75-bit syndrome pack -/

/-- Unpack a `Nat` as a 2-chain (75 bits). -/
def packFn75 (n : Nat) : G150 → ZMod 2 := fun g =>
  if n.testBit (cell2Idx g) then 1 else 0

lemma packFn75_xor (a b : Nat) :
    packFn75 (a ^^^ b) = packFn75 a + packFn75 b := by
  funext g
  have hkey : ∀ x y : Bool, (if (x ^^ y) then (1 : ZMod 2) else 0)
      = (if x then (1 : ZMod 2) else 0) + (if y then 1 else 0) := by decide
  simp only [packFn75, Nat.testBit_xor, Pi.add_apply]
  exact hkey _ _

lemma packFn75_zero : packFn75 0 = 0 := by
  funext g
  simp [packFn75]

/-- `cell2Idx` reaches every index below 75. -/
lemma exists_cell2Idx {i : Nat} (hi : i < 75) : ∃ g : G150, cell2Idx g = i := by
  refine ⟨((i / 15 : ℕ), (i % 15 : ℕ)), ?_⟩
  have h5 : i / 15 < 5 := by omega
  have h15 : i % 15 < 15 := by omega
  unfold cell2Idx
  simp only [ZMod.val_natCast]
  rw [Nat.mod_eq_of_lt h5, Nat.mod_eq_of_lt h15]
  omega

/-- `packFn75` reflects zero below `2^75`. -/
lemma packFn75_eq_zero {n : Nat} (hn : n < 2 ^ 75)
    (h : packFn75 n = 0) : n = 0 := by
  refine Nat.eq_of_testBit_eq fun i => ?_
  rw [Nat.zero_testBit]
  by_cases hi : i < 75
  · obtain ⟨g, hg⟩ := exists_cell2Idx hi
    have hv := congrFun h g
    simp only [packFn75, Pi.zero_apply, hg] at hv
    rcases hb : n.testBit i
    · rfl
    · rw [hb] at hv
      simp at hv
  · push Not at hi
    exact Nat.testBit_lt_two_pow
      (lt_of_lt_of_le hn (Nat.pow_le_pow_right (by omega) hi))

/-! ## Column masks and the semantic bridge -/

/-- The packed `∂₁` column of 1-chain cell `j` (three distinct check
bits). -/
def colMaskPacked (j : Nat) : Nat :=
  (1 <<< COLS.getD (3 * j) 99) ^^^ (1 <<< COLS.getD (3 * j + 1) 99) ^^^
    (1 <<< COLS.getD (3 * j + 2) 99)

/-- The column bridge: packed columns match the semantic `∂₁` on the
`δ`-basis. -/
theorem colMaskPacked_certs : ∀ j : G150 × Fin 2,
    packFn75 (colMaskPacked (cellIdx j))
      = bbBoundary1Fn a150 b150 (Pi.single j 1) := by
  native_decide

/-- Column masks stay below `2^75`. -/
theorem colMaskPacked_lt : ∀ j : G150 × Fin 2,
    colMaskPacked (cellIdx j) < 2 ^ 75 := by
  native_decide

/-! ## Local chains, masks, and syndromes over a cell list -/

/-- The chain of a local mask over a cell list (bit 0 = head). -/
def localChainOf : List Nat → Nat → (G150 × Fin 2 → ZMod 2)
  | [], _ => 0
  | c :: cs, lam =>
      (if lam % 2 = 1 then Pi.single (coordOfC1 c) 1 else 0)
        + localChainOf cs (lam / 2)

/-- The local mask of a chain over a cell list. -/
def localMaskOf : List Nat → (G150 × Fin 2 → ZMod 2) → Nat
  | [], _ => 0
  | c :: cs, u =>
      (if u (coordOfC1 c) ≠ 0 then 1 else 0) + 2 * localMaskOf cs u

/-- The packed syndrome of a local mask over a cell list. -/
def syndFold : List Nat → Nat → Nat
  | [], _ => 0
  | c :: cs, lam =>
      (if lam % 2 = 1 then colMaskPacked c else 0) ^^^ syndFold cs (lam / 2)

lemma localChainOf_cons (c : Nat) (cs : List Nat) (lam : Nat) :
    localChainOf (c :: cs) lam
      = (if lam % 2 = 1 then Pi.single (coordOfC1 c) 1 else 0)
        + localChainOf cs (lam / 2) := rfl

lemma syndFold_cons (c : Nat) (cs : List Nat) (lam : Nat) :
    syndFold (c :: cs) lam
      = (if lam % 2 = 1 then colMaskPacked c else 0)
        ^^^ syndFold cs (lam / 2) := rfl

/-- Local masks are bounded by the list length. -/
lemma localMaskOf_lt (cells : List Nat) (u : G150 × Fin 2 → ZMod 2) :
    localMaskOf cells u < 2 ^ cells.length := by
  induction cells with
  | nil => simp [localMaskOf]
  | cons c cs ih =>
    simp only [localMaskOf, List.length_cons, pow_succ]
    split <;> omega

/-- Bit `0` and the shift of a local mask, in arithmetic form. -/
lemma localMaskOf_cons (c : Nat) (cs : List Nat)
    (u : G150 × Fin 2 → ZMod 2) :
    localMaskOf (c :: cs) u
      = (if u (coordOfC1 c) ≠ 0 then 1 else 0) + 2 * localMaskOf cs u := rfl

/-- Syndromes stay below `2^75` when every listed cell is a real cell. -/
lemma syndFold_lt {cells : List Nat} (hc : ∀ c ∈ cells, c < 150)
    (lam : Nat) : syndFold cells lam < 2 ^ 75 := by
  induction cells generalizing lam with
  | nil =>
    simp only [syndFold]
    positivity
  | cons c cs ih =>
    simp only [syndFold]
    have hcs : ∀ c' ∈ cs, c' < 150 :=
      fun c' h => hc c' (List.mem_cons_of_mem _ h)
    have hrest := ih hcs (lam / 2)
    by_cases hbit : lam % 2 = 1
    · rw [if_pos hbit]
      have hlt : c < 150 := hc c (List.mem_cons_self ..)
      have hcol : colMaskPacked c < 2 ^ 75 := by
        have := colMaskPacked_lt (coordOfC1 c)
        rwa [cellIdx_coordOfC1 ⟨c, hlt⟩] at this
      exact Nat.xor_lt_two_pow hcol hrest
    · rw [if_neg hbit, Nat.zero_xor]
      exact hrest

/-- The syndrome fold computes `∂₁` of the local chain. -/
lemma boundary1_localChainOf {cells : List Nat}
    (hc : ∀ c ∈ cells, c < 150) (lam : Nat) :
    bbBoundary1Fn a150 b150 (localChainOf cells lam)
      = packFn75 (syndFold cells lam) := by
  induction cells generalizing lam with
  | nil =>
    simp only [localChainOf, syndFold, packFn75_zero]
    have h : (bbChainComplex a150 b150).boundary1 0 = 0 := map_zero _
    exact h
  | cons c cs ih =>
    have hcs : ∀ c' ∈ cs, c' < 150 :=
      fun c' h => hc c' (List.mem_cons_of_mem _ h)
    have hlt : c < 150 := hc c (List.mem_cons_self ..)
    rw [localChainOf_cons, syndFold_cons]
    by_cases hbit : lam % 2 = 1
    · rw [if_pos hbit, if_pos hbit, bbBoundary1Fn_add, ih hcs, packFn75_xor]
      have hcert := colMaskPacked_certs (coordOfC1 c)
      rw [cellIdx_coordOfC1 ⟨c, hlt⟩] at hcert
      rw [hcert]
    · rw [if_neg hbit, if_neg hbit, zero_add, Nat.zero_xor]
      exact ih hcs (lam / 2)

/-- The support of a local chain lies on the listed cells. -/
lemma localChainOf_support {cells : List Nat}
    (hc : ∀ c ∈ cells, c < 150) {lam : Nat}
    {p : G150 × Fin 2} (h : localChainOf cells lam p ≠ 0) :
    cellIdx p ∈ cells := by
  induction cells generalizing lam with
  | nil => simp [localChainOf] at h
  | cons c cs ih =>
    have hcs : ∀ c' ∈ cs, c' < 150 :=
      fun c' h' => hc c' (List.mem_cons_of_mem _ h')
    rw [localChainOf_cons] at h
    by_cases hbit : lam % 2 = 1
    · rw [if_pos hbit, Pi.add_apply] at h
      by_cases hp : p = coordOfC1 c
      · have hcell : cellIdx p = c := by
          rw [hp]
          exact cellIdx_coordOfC1 ⟨c, hc c (List.mem_cons_self ..)⟩
        rw [hcell]
        exact List.mem_cons_self ..
      · rw [Pi.single_eq_of_ne hp, zero_add] at h
        exact List.mem_cons_of_mem _ (ih hcs h)
    · rw [if_neg hbit, zero_add] at h
      exact List.mem_cons_of_mem _ (ih hcs h)

/-- `localChainOf` of the zero mask is the zero chain. -/
lemma localChainOf_zero (cells : List Nat) :
    localChainOf cells 0 = 0 := by
  induction cells with
  | nil => rfl
  | cons c cs ih =>
    simp only [localChainOf, Nat.zero_mod, Nat.zero_div, ih]
    norm_num

/-- **Pointwise round trip**: over a `Nodup` cell list, the local chain
of a chain's local mask agrees with the chain on listed cells and
vanishes off them. -/
lemma localChainOf_localMaskOf_apply {cells : List Nat}
    (hnd : cells.Nodup) (hc : ∀ c ∈ cells, c < 150)
    (u : G150 × Fin 2 → ZMod 2) (p : G150 × Fin 2) :
    localChainOf cells (localMaskOf cells u) p
      = if cellIdx p ∈ cells then u p else 0 := by
  induction cells with
  | nil => simp [localChainOf]
  | cons c cs ih =>
    have hcs : ∀ c' ∈ cs, c' < 150 :=
      fun c' h' => hc c' (List.mem_cons_of_mem _ h')
    have hlt : c < 150 := hc c (List.mem_cons_self ..)
    have hnd' : cs.Nodup := (List.nodup_cons.mp hnd).2
    have hcnotin : c ∉ cs := (List.nodup_cons.mp hnd).1
    rw [localChainOf_cons, localMaskOf_cons]
    by_cases hu : u (coordOfC1 c) ≠ 0
    · rw [if_pos hu]
      have hmod : (1 + 2 * localMaskOf cs u) % 2 = 1 := by omega
      have hdiv : (1 + 2 * localMaskOf cs u) / 2 = localMaskOf cs u := by
        omega
      rw [hmod, hdiv, if_pos rfl, Pi.add_apply, ih hnd' hcs]
      by_cases hp : p = coordOfC1 c
      · have hcell : cellIdx p = c := by
          rw [hp]
          exact cellIdx_coordOfC1 ⟨c, hlt⟩
        have htail : cellIdx p ∉ cs := by
          rw [hcell]
          exact hcnotin
        have hval : u p = 1 := by
          have hkey : ∀ a : ZMod 2, a ≠ 0 → a = 1 := by decide
          rw [hp]
          exact hkey _ hu
        rw [if_neg htail, add_zero,
          if_pos (by rw [hcell]; exact List.mem_cons_self ..), hval, hp]
        simp
      · have hne : cellIdx p ≠ c := by
          intro he
          apply hp
          have hco := coordOfC1_cellIdx p
          rw [he] at hco
          exact hco.symm
        rw [Pi.single_eq_of_ne hp, zero_add]
        by_cases hmem : cellIdx p ∈ cs
        · rw [if_pos hmem, if_pos (List.mem_cons_of_mem _ hmem)]
        · rw [if_neg hmem, if_neg (by
            intro hin
            rcases List.mem_cons.mp hin with h | h
            · exact hne h
            · exact hmem h)]
    · rw [if_neg hu]
      push Not at hu
      have hmod : (0 + 2 * localMaskOf cs u) % 2 = 0 := by omega
      have hdiv : (0 + 2 * localMaskOf cs u) / 2 = localMaskOf cs u := by
        omega
      rw [hmod, hdiv, if_neg (by omega), zero_add, ih hnd' hcs]
      by_cases hp : p = coordOfC1 c
      · have hcell : cellIdx p = c := by
          rw [hp]
          exact cellIdx_coordOfC1 ⟨c, hlt⟩
        have htail : cellIdx p ∉ cs := by
          rw [hcell]
          exact hcnotin
        rw [if_neg htail,
          if_pos (by rw [hcell]; exact List.mem_cons_self ..), hp, hu]
      · have hne : cellIdx p ≠ c := by
          intro he
          apply hp
          have hco := coordOfC1_cellIdx p
          rw [he] at hco
          exact hco.symm
        by_cases hmem : cellIdx p ∈ cs
        · rw [if_pos hmem, if_pos (List.mem_cons_of_mem _ hmem)]
        · rw [if_neg hmem, if_neg (by
            intro hin
            rcases List.mem_cons.mp hin with h | h
            · exact hne h
            · exact hmem h)]

/-- **The mask round trip**: a chain supported on a `Nodup` cell list is
the local chain of its local mask. -/
lemma localChainOf_localMaskOf {cells : List Nat}
    (hnd : cells.Nodup) (hc : ∀ c ∈ cells, c < 150)
    {u : G150 × Fin 2 → ZMod 2}
    (hsupp : ∀ p : G150 × Fin 2, u p ≠ 0 → cellIdx p ∈ cells) :
    localChainOf cells (localMaskOf cells u) = u := by
  funext p
  rw [localChainOf_localMaskOf_apply hnd hc]
  by_cases hmem : cellIdx p ∈ cells
  · rw [if_pos hmem]
  · rw [if_neg hmem]
    by_contra hne
    have hu : u p ≠ 0 := fun hz => hne hz.symm
    exact hmem (hsupp p hu)

/-! ## Window cell lists -/

/-- The window's 1-chain cells, ascending. -/
def winCellList (k : Fin 113) : List Nat :=
  (List.range 150).filter (WMASK.getD k.val 0).testBit

/-- Window size. -/
def mWin (k : Fin 113) : Nat := (winCellList k).length

lemma winCellList_nodup (k : Fin 113) : (winCellList k).Nodup :=
  (List.nodup_range).filter _

lemma winCellList_lt (k : Fin 113) : ∀ c ∈ winCellList k, c < 150 := by
  intro c hcmem
  have := (List.mem_filter.mp hcmem).1
  exact List.mem_range.mp this

/-- Membership in the window cell list is window membership. -/
lemma mem_winCellList (k : Fin 113) (p : G150 × Fin 2) :
    cellIdx p ∈ winCellList k ↔ winMem k p = true := by
  unfold winCellList winMem
  rw [List.mem_filter, List.mem_range]
  constructor
  · intro h
    exact h.2
  · intro h
    exact ⟨cellIdx_lt p, h⟩

/-- The local mask of the tabulated window cycle. -/
def zLocalMask (k : Fin 113) : Nat :=
  localMaskOf (winCellList k) (winZChain k)

/-! ## The base soundness bridge (`|O| = 0`) -/

/-- **Window soundness, base case**: if the class sweep certifies that
every in-window cycle mask is `0` or the tabulated cycle, then every
1-cycle supported inside the window is a boundary.  The two `hz*` inputs
are the generated certificates (`win_z_certs`). -/
theorem window_sound_base (k : Fin 113)
    (hzb : bbBoundary2Fn a150 b150 (winZPreChain k) = winZChain k)
    (hzsupp : ∀ j : G150 × Fin 2, winZChain k j ≠ 0 → winMem k j = true)
    (hsweep : ∀ lam : Fin (2 ^ mWin k),
      syndFold (winCellList k) lam.val = 0 →
      lam.val = 0 ∨ lam.val = zLocalMask k)
    {u : G150 × Fin 2 → ZMod 2}
    (hcyc : bbBoundary1Fn a150 b150 u = 0)
    (hsupp : ∀ j : G150 × Fin 2, u j ≠ 0 → winMem k j = true) :
    u ∈ base150Complex.boundaries := by
  have hnd := winCellList_nodup k
  have hlt := winCellList_lt k
  have hsupp' : ∀ p : G150 × Fin 2, u p ≠ 0 → cellIdx p ∈ winCellList k :=
    fun p hp => (mem_winCellList k p).mpr (hsupp p hp)
  have hrt : localChainOf (winCellList k) (localMaskOf (winCellList k) u)
      = u := localChainOf_localMaskOf hnd hlt hsupp'
  have hbound : localMaskOf (winCellList k) u < 2 ^ mWin k :=
    localMaskOf_lt _ u
  have hsynd : syndFold (winCellList k) (localMaskOf (winCellList k) u)
      = 0 := by
    apply packFn75_eq_zero (syndFold_lt hlt _)
    rw [← boundary1_localChainOf hlt, hrt]
    exact hcyc
  rcases hsweep ⟨_, hbound⟩ hsynd with h0 | hz
  · have hu0 : u = 0 := by
      rw [← hrt]
      simp only at h0
      rw [h0, localChainOf_zero]
    rw [hu0]
    exact zero_mem _
  · have hzsupp' : ∀ p : G150 × Fin 2,
        winZChain k p ≠ 0 → cellIdx p ∈ winCellList k :=
      fun p hp => (mem_winCellList k p).mpr (hzsupp p hp)
    have hu_eq : u = winZChain k := by
      rw [← hrt]
      simp only at hz
      rw [hz]
      exact localChainOf_localMaskOf hnd hlt hzsupp'
    refine ⟨show G150 → ZMod 2 from winZPreChain k, ?_⟩
    change bbBoundary2Fn a150 b150 (winZPreChain k) = u
    rw [hzb, hu_eq]


/-! ## The check-neighbourhood mask and the escape argument -/

/-- The packed union of the window cells' check columns. -/
def cwMask (k : Fin 113) : Nat :=
  (winCellList k).foldr (fun c acc => colMaskPacked c ||| acc) 0

/-- Bit-subset as a `Nat` test. -/
def natSubset (a m : Nat) : Prop := a &&& m = a

/-- Members of an OR-fold are bit-subsets of it. -/
lemma mem_orFold_subset {c : Nat} :
    ∀ {cells : List Nat}, c ∈ cells →
      natSubset (colMaskPacked c)
        (cells.foldr (fun d acc => colMaskPacked d ||| acc) 0) := by
  intro cells hmem
  induction cells with
  | nil => simp at hmem
  | cons d ds ih =>
    rw [List.foldr_cons]
    rcases List.mem_cons.mp hmem with h | h
    · subst h
      refine Nat.eq_of_testBit_eq fun i => ?_
      simp only [Nat.testBit_and, Nat.testBit_or]
      cases (colMaskPacked c).testBit i <;> simp
    · have hsub := ih h
      refine Nat.eq_of_testBit_eq fun i => ?_
      have hbit := congrArg (fun n => n.testBit i) hsub
      simp only [Nat.testBit_and] at hbit
      simp only [Nat.testBit_and, Nat.testBit_or]
      cases hc : (colMaskPacked c).testBit i
      · simp
      · rw [hc] at hbit
        simp only [Bool.true_and] at hbit
        rw [hbit]
        simp

/-- The window instantiation. -/
lemma colMask_subset_cwMask {k : Fin 113} {c : Nat}
    (hmem : c ∈ winCellList k) :
    natSubset (colMaskPacked c) (cwMask k) :=
  mem_orFold_subset hmem

/-- Bit-subsets are closed under XOR. -/
lemma natSubset_xor {a b m : Nat} (ha : natSubset a m)
    (hb : natSubset b m) : natSubset (a ^^^ b) m := by
  unfold natSubset at *
  rw [Nat.and_xor_distrib_right, ha, hb]

/-- `0` is a bit-subset of anything. -/
lemma natSubset_zero (m : Nat) : natSubset 0 m := by
  unfold natSubset
  simp

/-- Window syndromes are bit-subsets of the check neighbourhood. -/
lemma syndFold_subset_cwMask (k : Fin 113) {cells : List Nat}
    (hcells : ∀ c ∈ cells, c ∈ winCellList k) (lam : Nat) :
    natSubset (syndFold cells lam) (cwMask k) := by
  induction cells generalizing lam with
  | nil => exact natSubset_zero _
  | cons c cs ih =>
    rw [syndFold_cons]
    have hcs : ∀ c' ∈ cs, c' ∈ winCellList k :=
      fun c' h' => hcells c' (List.mem_cons_of_mem _ h')
    refine natSubset_xor ?_ (ih hcs (lam / 2))
    by_cases hbit : lam % 2 = 1
    · rw [if_pos hbit]
      exact colMask_subset_cwMask (hcells c (List.mem_cons_self ..))
    · rw [if_neg hbit]
      exact natSubset_zero _

/-- A failed bit-subset test yields a witnessing bit. -/
lemma exists_bit_of_not_natSubset {a m : Nat} (h : ¬ natSubset a m) :
    ∃ i : Nat, a.testBit i = true ∧ m.testBit i = false := by
  by_contra hno
  push Not at hno
  apply h
  refine Nat.eq_of_testBit_eq fun i => ?_
  simp only [Nat.testBit_and]
  cases ha : a.testBit i
  · simp
  · have := hno i ha
    simp [this]

/-- XOR with an escaping summand is nonzero: if `a` stays inside `m` and
`b` has a bit outside `m`, then `a ^^^ b ≠ 0`. -/
lemma xor_ne_zero_of_escape {a b m : Nat} (ha : natSubset a m)
    (hb : ¬ natSubset b m) : a ^^^ b ≠ 0 := by
  obtain ⟨i, hbi, hmi⟩ := exists_bit_of_not_natSubset hb
  have hai : a.testBit i = false := by
    have hband := congrArg (fun n => n.testBit i) ha
    simp only [Nat.testBit_and] at hband
    rw [hmi, Bool.and_false] at hband
    exact hband.symm
  intro hzero
  have hbit : (a ^^^ b).testBit i = (0 : Nat).testBit i := by rw [hzero]
  rw [Nat.testBit_xor, hai, hbi, Nat.zero_testBit] at hbit
  simp at hbit

/-! ## Syndromes and masks over appended cells -/

lemma syndFold_nil (lam : Nat) : syndFold [] lam = 0 := rfl

lemma localChainOf_nil (lam : Nat) : localChainOf [] lam = 0 := rfl

lemma shiftRight_cons_length (c : Nat) (cs : List Nat) (lam : Nat) :
    (lam / 2) >>> cs.length = lam >>> (c :: cs).length := by
  simp only [List.length_cons, Nat.shiftRight_eq_div_pow]
  rw [Nat.div_div_eq_div_mul]
  congr 1
  rw [pow_succ]
  omega

lemma syndFold_append_singleton (cells : List Nat) (e : Nat) (lam : Nat) :
    syndFold (cells ++ [e]) lam
      = syndFold cells lam
        ^^^ (if (lam >>> cells.length) % 2 = 1 then colMaskPacked e
             else 0) := by
  induction cells generalizing lam with
  | nil =>
    rw [show ([] : List Nat) ++ [e] = [e] from rfl, syndFold_cons,
      syndFold_nil, syndFold_nil, Nat.xor_zero, Nat.zero_xor,
      List.length_nil, Nat.shiftRight_zero]
  | cons c cs ih =>
    rw [show (c :: cs) ++ [e] = c :: (cs ++ [e]) from rfl, syndFold_cons,
      syndFold_cons, ih (lam / 2), ← Nat.xor_assoc,
      shiftRight_cons_length c cs lam]

lemma localChainOf_append_singleton (cells : List Nat) (e : Nat)
    (lam : Nat) :
    localChainOf (cells ++ [e]) lam
      = localChainOf cells lam
        + (if (lam >>> cells.length) % 2 = 1 then
            Pi.single (coordOfC1 e) 1 else 0) := by
  induction cells generalizing lam with
  | nil =>
    rw [show ([] : List Nat) ++ [e] = [e] from rfl, localChainOf_cons,
      localChainOf_nil, localChainOf_nil, add_zero, zero_add,
      List.length_nil, Nat.shiftRight_zero]
  | cons c cs ih =>
    rw [show (c :: cs) ++ [e] = c :: (cs ++ [e]) from rfl,
      localChainOf_cons, localChainOf_cons, ih (lam / 2), ← add_assoc,
      shiftRight_cons_length c cs lam]


/-- Transport membership through a certified filter evaluation: if the
filter of `l` by `p` is the literal list `out`, every member of `l`
satisfying `p` is a member of `out`.  Used with `native_decide`-certified
survivor lists to dispatch the extension sweeps over the finitely many
surviving extra cells. -/
theorem mem_of_filter_eq {p : Nat → Bool} {l out : List Nat}
    (hf : l.filter p = out) {c : Nat} (hc : c ∈ l) (hp : p c = true) :
    c ∈ out :=
  hf ▸ List.mem_filter.mpr ⟨hc, hp⟩

/-! ## Survivor tests and the extended candidate table -/

/-- Single-cell survivor test: the extra cell's checks stay inside the
window's check neighbourhood. -/
def survivorB (k : Fin 113) (e : Nat) : Bool :=
  colMaskPacked e &&& cwMask k == colMaskPacked e

/-- Pair survivor test: the two extra columns cancel outside the
neighbourhood. -/
def pairSurvivorB (k : Fin 113) (e₁ e₂ : Nat) : Bool :=
  (colMaskPacked e₁ ^^^ colMaskPacked e₂) &&& cwMask k
    == colMaskPacked e₁ ^^^ colMaskPacked e₂

/-- The candidate table for class `k` with one admissible extra cell `e`:
preimage/cycle pairs for `0`, the base window cycle, and the extras owned
by `(k, e)` together with their sums with the base cycle. -/
def tableEntries (k : Fin 113) (e : Nat) :
    List ((G150 → ZMod 2) × (G150 × Fin 2 → ZMod 2)) :=
  (0, 0) :: (winZPreChain k, winZChain k) ::
    ((List.finRange nExtras).filterMap fun ei =>
      if XCLS.getD ei.val 0 = k.val ∧ XCELL.getD ei.val 0 = e then
        some (xZPreChain ei, xZChain ei)
      else none)
    ++ ((List.finRange nExtras).filterMap fun ei =>
      if XCLS.getD ei.val 0 = k.val ∧ XCELL.getD ei.val 0 = e then
        some (winZPreChain k + xZPreChain ei, winZChain k + xZChain ei)
      else none)

/-- Every table entry is a boundary pair supported in the window plus the
extra cell. -/
lemma tableEntries_spec (k : Fin 113) (e : Nat)
    (hkind : KIND.getD k.val 0 = 1)
    {pr : (G150 → ZMod 2) × (G150 × Fin 2 → ZMod 2)}
    (hmem : pr ∈ tableEntries k e) :
    bbBoundary2Fn a150 b150 pr.1 = pr.2 ∧
    (∀ j : G150 × Fin 2, pr.2 j ≠ 0 →
      winMem k j = true ∨ cellIdx j = e) := by
  have hz := win_z_certs k hkind
  unfold tableEntries at hmem
  rcases List.mem_cons.mp hmem with h0 | hmem
  · subst h0
    refine ⟨?_, ?_⟩
    · have h : (bbChainComplex a150 b150).boundary2 0 = 0 := map_zero _
      exact h
    · intro j hj
      simp at hj
  rcases List.mem_cons.mp hmem with h1 | hmem
  · subst h1
    exact ⟨hz.1, fun j hj => Or.inl (hz.2 j hj)⟩
  rcases List.mem_append.mp hmem with hx | hxz
  · obtain ⟨ei, _, heq⟩ := List.mem_filterMap.mp hx
    by_cases hcond : XCLS.getD ei.val 0 = k.val ∧ XCELL.getD ei.val 0 = e
    · rw [if_pos hcond] at heq
      have hpr : pr = (xZPreChain ei, xZChain ei) :=
        (Option.some_inj.mp heq).symm
      have hclsx : xClsIdx ei = k := by
        unfold xClsIdx
        apply Fin.ext
        simp only
        rw [hcond.1]
        exact Nat.mod_eq_of_lt k.isLt
      have hxx := x_z_certs ei
      have hpr1 : pr.1 = xZPreChain ei := by rw [hpr]
      have hpr2 : pr.2 = xZChain ei := by rw [hpr]
      rw [hpr1, hpr2]
      refine ⟨hxx.1, ?_⟩
      intro j hj
      rcases hxx.2 j hj with h | h
      · rw [hclsx] at h
        exact Or.inl h
      · rw [hcond.2] at h
        exact Or.inr h
    · rw [if_neg hcond] at heq
      exact absurd heq (by simp)
  · obtain ⟨ei, _, heq⟩ := List.mem_filterMap.mp hxz
    by_cases hcond : XCLS.getD ei.val 0 = k.val ∧ XCELL.getD ei.val 0 = e
    · rw [if_pos hcond] at heq
      have hpr : pr = (winZPreChain k + xZPreChain ei,
          winZChain k + xZChain ei) :=
        (Option.some_inj.mp heq).symm
      have hclsx : xClsIdx ei = k := by
        unfold xClsIdx
        apply Fin.ext
        simp only
        rw [hcond.1]
        exact Nat.mod_eq_of_lt k.isLt
      have hxx := x_z_certs ei
      have hpr1 : pr.1 = winZPreChain k + xZPreChain ei := by rw [hpr]
      have hpr2 : pr.2 = winZChain k + xZChain ei := by rw [hpr]
      rw [hpr1, hpr2]
      refine ⟨?_, ?_⟩
      · rw [bbBoundary2Fn_add, hz.1, hxx.1]
      · intro j hj
        have hsplit : winZChain k j ≠ 0 ∨ xZChain ei j ≠ 0 := by
          by_contra hno
          push Not at hno
          rw [Pi.add_apply, hno.1, hno.2, add_zero] at hj
          exact hj rfl
        rcases hsplit with h | h
        · exact Or.inl (hz.2 j h)
        · rcases hxx.2 j h with h' | h'
          · rw [hclsx] at h'
            exact Or.inl h'
          · rw [hcond.2] at h'
            exact Or.inr h'
    · rw [if_neg hcond] at heq
      exact absurd heq (by simp)


/-! ## The appended-mask bit -/

lemma localMaskOf_append_singleton (cells : List Nat) (e : Nat)
    (u : G150 × Fin 2 → ZMod 2) :
    localMaskOf (cells ++ [e]) u
      = localMaskOf cells u
        + 2 ^ cells.length * (if u (coordOfC1 e) ≠ 0 then 1 else 0) := by
  induction cells with
  | nil =>
    rw [show ([] : List Nat) ++ [e] = [e] from rfl]
    show (if u (coordOfC1 e) ≠ 0 then 1 else 0) + 2 * localMaskOf [] u
      = localMaskOf [] u + 2 ^ 0 * (if u (coordOfC1 e) ≠ 0 then 1 else 0)
    show (if u (coordOfC1 e) ≠ 0 then 1 else 0) + 2 * 0
      = 0 + 2 ^ 0 * (if u (coordOfC1 e) ≠ 0 then 1 else 0)
    split <;> norm_num
  | cons c cs ih =>
    rw [show (c :: cs) ++ [e] = c :: (cs ++ [e]) from rfl,
      localMaskOf_cons, localMaskOf_cons, ih]
    simp only [List.length_cons, pow_succ]
    ring

/-- The appended bit of the extended mask. -/
lemma localMaskOf_append_top (cells : List Nat) (e : Nat)
    (u : G150 × Fin 2 → ZMod 2) :
    (localMaskOf (cells ++ [e]) u >>> cells.length) % 2
      = if u (coordOfC1 e) ≠ 0 then 1 else 0 := by
  rw [localMaskOf_append_singleton, Nat.shiftRight_eq_div_pow]
  have hlow := localMaskOf_lt cells u
  have hb : (if u (coordOfC1 e) ≠ 0 then 1 else 0) ≤ 1 := by
    split <;> omega
  set b : Nat := if u (coordOfC1 e) ≠ 0 then 1 else 0
  have hpow : 0 < 2 ^ cells.length := Nat.two_pow_pos _
  rw [Nat.add_mul_div_left _ _ hpow, Nat.div_eq_of_lt hlow]
  omega

/-! ## The generic soundness core -/

/-- **The sweep-to-boundary core**: over any admissible cell list, a
sweep hit maps a cycle supported on the list to a tabulated boundary. -/
theorem window_sound_core (cells : List Nat)
    (T : List ((G150 → ZMod 2) × (G150 × Fin 2 → ZMod 2)))
    (hnd : cells.Nodup)
    (hbnd : ∀ c ∈ cells, c < 150)
    (hT : ∀ pr ∈ T, bbBoundary2Fn a150 b150 pr.1 = pr.2)
    (hTsupp : ∀ pr ∈ T, ∀ p : G150 × Fin 2, pr.2 p ≠ 0 →
      cellIdx p ∈ cells)
    (hsweep : ∀ lam : Fin (2 ^ cells.length),
      syndFold cells lam.val = 0 →
      T.any (fun pr => lam.val == localMaskOf cells pr.2) = true)
    {u : G150 × Fin 2 → ZMod 2}
    (hcyc : bbBoundary1Fn a150 b150 u = 0)
    (hsupp : ∀ p : G150 × Fin 2, u p ≠ 0 → cellIdx p ∈ cells) :
    u ∈ base150Complex.boundaries := by
  have hrt : localChainOf cells (localMaskOf cells u) = u :=
    localChainOf_localMaskOf hnd hbnd hsupp
  have hbound : localMaskOf cells u < 2 ^ cells.length :=
    localMaskOf_lt _ u
  have hsynd : syndFold cells (localMaskOf cells u) = 0 := by
    apply packFn75_eq_zero (syndFold_lt hbnd _)
    rw [← boundary1_localChainOf hbnd, hrt]
    exact hcyc
  have hhit := hsweep ⟨_, hbound⟩ hsynd
  obtain ⟨pr, hprmem, hpreq⟩ := List.any_eq_true.mp hhit
  have hlam : localMaskOf cells u = localMaskOf cells pr.2 :=
    beq_iff_eq.mp hpreq
  have hu_eq : u = pr.2 := by
    rw [← hrt, hlam]
    exact localChainOf_localMaskOf hnd hbnd (hTsupp pr hprmem)
  refine ⟨show G150 → ZMod 2 from pr.1, ?_⟩
  change bbBoundary2Fn a150 b150 pr.1 = u
  rw [hT pr hprmem, hu_eq]

/-! ## Off-window support extraction -/

/-- The off-window support as the extension list, with all side facts. -/
lemma ext_facts (k : Fin 113)
    {ecell : G150 × Fin 2} (hoff : winMem k ecell = false) :
    (winCellList k ++ [cellIdx ecell]).Nodup ∧
    (∀ c ∈ winCellList k ++ [cellIdx ecell], c < 150) := by
  constructor
  · rw [List.nodup_append]
    refine ⟨winCellList_nodup k, List.nodup_singleton _, ?_⟩
    intro c hcmem d hdin hcd
    have hd : d = cellIdx ecell := List.mem_singleton.mp hdin
    rw [hcd, hd] at hcmem
    have hin := (mem_winCellList k ecell).mp hcmem
    rw [hoff] at hin
    exact Bool.false_ne_true hin
  · intro c hcmem
    rcases List.mem_append.mp hcmem with h | h
    · exact winCellList_lt k c h
    · rw [List.mem_singleton.mp h]
      exact cellIdx_lt ecell


/-! ## The three soundness wrappers -/

/-- `t = 1`: cycles supported inside the window. -/
theorem window_sound_t1 (k : Fin 113) (hkind : KIND.getD k.val 0 = 1)
    (hsweep0 : ∀ lam : Fin (2 ^ (winCellList k).length),
      syndFold (winCellList k) lam.val = 0 →
      (tableEntries k 150).any
        (fun pr => lam.val == localMaskOf (winCellList k) pr.2) = true)
    {u : G150 × Fin 2 → ZMod 2}
    (hcyc : bbBoundary1Fn a150 b150 u = 0)
    (hsupp : ∀ j : G150 × Fin 2, u j ≠ 0 → winMem k j = true) :
    u ∈ base150Complex.boundaries := by
  refine window_sound_core (winCellList k) (tableEntries k 150)
    (winCellList_nodup k) (winCellList_lt k) ?_ ?_ hsweep0 hcyc ?_
  · intro pr hpr
    exact (tableEntries_spec k 150 hkind hpr).1
  · intro pr hpr p hp
    rcases (tableEntries_spec k 150 hkind hpr).2 p hp with h | h
    · exact (mem_winCellList k p).mpr h
    · exact absurd h (by have := cellIdx_lt p; omega)
  · intro p hp
    exact (mem_winCellList k p).mpr (hsupp p hp)

/-- Bool flip for window membership. -/
lemma winMem_eq_false {k : Fin 113} {p : G150 × Fin 2}
    (h : ¬ winMem k p = true) : winMem k p = false := by
  cases hwm : winMem k p
  · rfl
  · exact absurd hwm h

/-- The survivor test unfolds to the subset property. -/
lemma not_natSubset_of_survivorB_false {k : Fin 113} {e : Nat}
    (h : ¬ survivorB k e = true) :
    ¬ natSubset (colMaskPacked e) (cwMask k) := by
  intro hns
  apply h
  unfold survivorB
  unfold natSubset at hns
  exact beq_iff_eq.mpr hns

/-- `t = 2`: cycles with at most one cell outside the window. -/
theorem window_sound_t2 (k : Fin 113) (hkind : KIND.getD k.val 0 = 1)
    (hsweep0 : ∀ lam : Fin (2 ^ (winCellList k).length),
      syndFold (winCellList k) lam.val = 0 →
      (tableEntries k 150).any
        (fun pr => lam.val == localMaskOf (winCellList k) pr.2) = true)
    (hsweepE : ∀ e : G150 × Fin 2, winMem k e = false →
      survivorB k (cellIdx e) = true →
      ∀ lam : Fin (2 ^ (winCellList k ++ [cellIdx e]).length),
        syndFold (winCellList k ++ [cellIdx e]) lam.val = 0 →
        (tableEntries k (cellIdx e)).any (fun pr =>
          lam.val == localMaskOf (winCellList k ++ [cellIdx e]) pr.2)
          = true)
    {u : G150 × Fin 2 → ZMod 2}
    (hcyc : bbBoundary1Fn a150 b150 u = 0)
    (hcard : (Finset.univ.filter fun j : G150 × Fin 2 =>
      u j ≠ 0 ∧ ¬ winMem k j = true).card ≤ 1) :
    u ∈ base150Complex.boundaries := by
  by_cases hzero : (Finset.univ.filter fun j : G150 × Fin 2 =>
      u j ≠ 0 ∧ ¬ winMem k j = true).card = 0
  · have hsupp : ∀ j : G150 × Fin 2, u j ≠ 0 → winMem k j = true := by
      intro j hj
      by_contra hnm
      have hjmem : j ∈ Finset.univ.filter fun j : G150 × Fin 2 =>
          u j ≠ 0 ∧ ¬ winMem k j = true :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj, hnm⟩
      rw [Finset.card_eq_zero.mp hzero] at hjmem
      exact Finset.notMem_empty j hjmem
    exact window_sound_t1 k hkind hsweep0 hcyc hsupp
  · have hone : (Finset.univ.filter fun j : G150 × Fin 2 =>
        u j ≠ 0 ∧ ¬ winMem k j = true).card = 1 := by omega
    obtain ⟨ecell, hset⟩ := Finset.card_eq_one.mp hone
    have hemem : ecell ∈ Finset.univ.filter fun j : G150 × Fin 2 =>
        u j ≠ 0 ∧ ¬ winMem k j = true := by
      rw [hset]
      exact Finset.mem_singleton_self ecell
    obtain ⟨-, hu_e, hnm_e⟩ := Finset.mem_filter.mp hemem
    have hoffB : winMem k ecell = false := winMem_eq_false hnm_e
    have hsupp' : ∀ p : G150 × Fin 2, u p ≠ 0 →
        cellIdx p ∈ winCellList k ++ [cellIdx ecell] := by
      intro p hp
      by_cases hin : winMem k p = true
      · exact List.mem_append_left _ ((mem_winCellList k p).mpr hin)
      · have hpmem : p ∈ Finset.univ.filter fun j : G150 × Fin 2 =>
            u j ≠ 0 ∧ ¬ winMem k j = true :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ p, hp, hin⟩
        rw [hset] at hpmem
        rw [Finset.mem_singleton.mp hpmem]
        exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
    obtain ⟨hnd', hbnd'⟩ := ext_facts k hoffB
    by_cases hsurv : survivorB k (cellIdx ecell) = true
    · refine window_sound_core _ (tableEntries k (cellIdx ecell)) hnd'
        hbnd' ?_ ?_ (hsweepE ecell hoffB hsurv) hcyc hsupp'
      · intro pr hpr
        exact (tableEntries_spec k _ hkind hpr).1
      · intro pr hpr p hp
        rcases (tableEntries_spec k _ hkind hpr).2 p hp with h | h
        · exact List.mem_append_left _ ((mem_winCellList k p).mpr h)
        · rw [h]
          exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
    · exfalso
      have hrt : localChainOf (winCellList k ++ [cellIdx ecell])
          (localMaskOf (winCellList k ++ [cellIdx ecell]) u) = u :=
        localChainOf_localMaskOf hnd' hbnd' hsupp'
      have hsynd0 : syndFold (winCellList k ++ [cellIdx ecell])
          (localMaskOf (winCellList k ++ [cellIdx ecell]) u) = 0 := by
        apply packFn75_eq_zero (syndFold_lt hbnd' _)
        rw [← boundary1_localChainOf hbnd', hrt]
        exact hcyc
      have htop : (localMaskOf (winCellList k ++ [cellIdx ecell]) u
          >>> (winCellList k).length) % 2 = 1 := by
        rw [localMaskOf_append_top]
        rw [coordOfC1_cellIdx ecell]
        rw [if_pos hu_e]
      have hdec := syndFold_append_singleton (winCellList k)
        (cellIdx ecell) (localMaskOf (winCellList k ++ [cellIdx ecell]) u)
      rw [htop] at hdec
      rw [if_pos rfl] at hdec
      have ha : natSubset
          (syndFold (winCellList k)
            (localMaskOf (winCellList k ++ [cellIdx ecell]) u))
          (cwMask k) :=
        syndFold_subset_cwMask k (fun c h => h) _
      have hb := not_natSubset_of_survivorB_false hsurv
      have hne := xor_ne_zero_of_escape ha hb
      rw [← hdec] at hne
      exact hne hsynd0


/-! ## The pair case (`t = 3`) -/

/-- Cell indices are injective. -/
lemma cellIdx_inj {p q : G150 × Fin 2} (h : cellIdx p = cellIdx q) :
    p = q := by
  have hp := coordOfC1_cellIdx p
  have hq := coordOfC1_cellIdx q
  rw [← hp, ← hq, h]

/-- List facts for the doubly-extended window. -/
lemma ext_facts2 (k : Fin 113) {e₁ e₂ : G150 × Fin 2}
    (hoff₁ : winMem k e₁ = false) (hoff₂ : winMem k e₂ = false)
    (hne : e₁ ≠ e₂) :
    ((winCellList k ++ [cellIdx e₁]) ++ [cellIdx e₂]).Nodup ∧
    (∀ c ∈ (winCellList k ++ [cellIdx e₁]) ++ [cellIdx e₂], c < 150) := by
  obtain ⟨hnd₁, hbnd₁⟩ := ext_facts k hoff₁
  constructor
  · rw [List.nodup_append]
    refine ⟨hnd₁, List.nodup_singleton _, ?_⟩
    intro c hcmem d hdin hcd
    have hd : d = cellIdx e₂ := List.mem_singleton.mp hdin
    rw [hcd, hd] at hcmem
    rcases List.mem_append.mp hcmem with h | h
    · have hin := (mem_winCellList k e₂).mp h
      rw [hoff₂] at hin
      exact Bool.false_ne_true hin
    · have h12 : cellIdx e₂ = cellIdx e₁ := List.mem_singleton.mp h
      exact hne (cellIdx_inj h12.symm)
  · intro c hcmem
    rcases List.mem_append.mp hcmem with h | h
    · exact hbnd₁ c h
    · rw [List.mem_singleton.mp h]
      exact cellIdx_lt e₂
/-- Middle bits survive adding high multiples. -/
lemma bit_mid (x b m : Nat) :
    ((x + 2 ^ (m + 1) * b) >>> m) % 2 = (x >>> m) % 2 := by
  have hrw : 2 ^ (m + 1) * b = 2 ^ m * (2 * b) := by
    rw [pow_succ]
    ring
  rw [hrw, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow,
    Nat.add_mul_div_left _ _ (Nat.two_pow_pos m)]
  omega

/-- `t = 3`: cycles with at most two cells outside the window. -/
theorem window_sound_t3 (k : Fin 113) (hkind : KIND.getD k.val 0 = 1)
    (hsweep0 : ∀ lam : Fin (2 ^ (winCellList k).length),
      syndFold (winCellList k) lam.val = 0 →
      (tableEntries k 150).any
        (fun pr => lam.val == localMaskOf (winCellList k) pr.2) = true)
    (hsweepE : ∀ e : G150 × Fin 2, winMem k e = false →
      survivorB k (cellIdx e) = true →
      ∀ lam : Fin (2 ^ (winCellList k ++ [cellIdx e]).length),
        syndFold (winCellList k ++ [cellIdx e]) lam.val = 0 →
        (tableEntries k (cellIdx e)).any (fun pr =>
          lam.val == localMaskOf (winCellList k ++ [cellIdx e]) pr.2)
          = true)
    (hsweepP : ∀ e₁ e₂ : G150 × Fin 2, winMem k e₁ = false →
      winMem k e₂ = false → e₁ ≠ e₂ →
      pairSurvivorB k (cellIdx e₁) (cellIdx e₂) = true →
      ∀ lam : Fin (2 ^ ((winCellList k ++ [cellIdx e₁]) ++ [cellIdx e₂]).length),
        syndFold ((winCellList k ++ [cellIdx e₁]) ++ [cellIdx e₂]) lam.val
          = 0 →
        ((tableEntries k (cellIdx e₁)) ++ tableEntries k (cellIdx e₂)).any
          (fun pr => lam.val ==
            localMaskOf ((winCellList k ++ [cellIdx e₁]) ++ [cellIdx e₂])
              pr.2) = true)
    {u : G150 × Fin 2 → ZMod 2}
    (hcyc : bbBoundary1Fn a150 b150 u = 0)
    (hcard : (Finset.univ.filter fun j : G150 × Fin 2 =>
      u j ≠ 0 ∧ ¬ winMem k j = true).card ≤ 2) :
    u ∈ base150Complex.boundaries := by
  by_cases hle1 : (Finset.univ.filter fun j : G150 × Fin 2 =>
      u j ≠ 0 ∧ ¬ winMem k j = true).card ≤ 1
  · exact window_sound_t2 k hkind hsweep0 hsweepE hcyc hle1
  · have htwo : (Finset.univ.filter fun j : G150 × Fin 2 =>
        u j ≠ 0 ∧ ¬ winMem k j = true).card = 2 := by omega
    obtain ⟨e₁, e₂, hne, hset⟩ := Finset.card_eq_two.mp htwo
    have hmem₁ : e₁ ∈ Finset.univ.filter fun j : G150 × Fin 2 =>
        u j ≠ 0 ∧ ¬ winMem k j = true := by
      rw [hset]
      exact Finset.mem_insert_self e₁ {e₂}
    have hmem₂ : e₂ ∈ Finset.univ.filter fun j : G150 × Fin 2 =>
        u j ≠ 0 ∧ ¬ winMem k j = true := by
      rw [hset]
      exact Finset.mem_insert_of_mem (Finset.mem_singleton_self e₂)
    obtain ⟨-, hu₁, hnm₁⟩ := Finset.mem_filter.mp hmem₁
    obtain ⟨-, hu₂, hnm₂⟩ := Finset.mem_filter.mp hmem₂
    have hoff₁ : winMem k e₁ = false := winMem_eq_false hnm₁
    have hoff₂ : winMem k e₂ = false := winMem_eq_false hnm₂
    obtain ⟨hnd'', hbnd''⟩ := ext_facts2 k hoff₁ hoff₂ hne
    have hsupp' : ∀ p : G150 × Fin 2, u p ≠ 0 →
        cellIdx p ∈ (winCellList k ++ [cellIdx e₁]) ++ [cellIdx e₂] := by
      intro p hp
      by_cases hin : winMem k p = true
      · exact List.mem_append_left _ (List.mem_append_left _
          ((mem_winCellList k p).mpr hin))
      · have hpmem : p ∈ Finset.univ.filter fun j : G150 × Fin 2 =>
            u j ≠ 0 ∧ ¬ winMem k j = true :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ p, hp, hin⟩
        rw [hset] at hpmem
        rcases Finset.mem_insert.mp hpmem with h | h
        · rw [h]
          exact List.mem_append_left _
            (List.mem_append_right _ (List.mem_singleton.mpr rfl))
        · rw [Finset.mem_singleton.mp h]
          exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
    by_cases hsurv : pairSurvivorB k (cellIdx e₁) (cellIdx e₂) = true
    · refine window_sound_core _
        ((tableEntries k (cellIdx e₁)) ++ tableEntries k (cellIdx e₂))
        hnd'' hbnd'' ?_ ?_ (hsweepP e₁ e₂ hoff₁ hoff₂ hne hsurv) hcyc
        hsupp'
      · intro pr hpr
        rcases List.mem_append.mp hpr with h | h
        · exact (tableEntries_spec k _ hkind h).1
        · exact (tableEntries_spec k _ hkind h).1
      · intro pr hpr p hp
        rcases List.mem_append.mp hpr with h | h
        · rcases (tableEntries_spec k _ hkind h).2 p hp with h' | h'
          · exact List.mem_append_left _ (List.mem_append_left _
              ((mem_winCellList k p).mpr h'))
          · rw [h']
            exact List.mem_append_left _ (List.mem_append_right _
              (List.mem_singleton.mpr rfl))
        · rcases (tableEntries_spec k _ hkind h).2 p hp with h' | h'
          · exact List.mem_append_left _ (List.mem_append_left _
              ((mem_winCellList k p).mpr h'))
          · rw [h']
            exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
    · exfalso
      set cells₂ := (winCellList k ++ [cellIdx e₁]) ++ [cellIdx e₂]
        with hcells₂
      have hrt : localChainOf cells₂ (localMaskOf cells₂ u) = u :=
        localChainOf_localMaskOf hnd'' hbnd'' hsupp'
      have hsynd0 : syndFold cells₂ (localMaskOf cells₂ u) = 0 := by
        apply packFn75_eq_zero (syndFold_lt hbnd'' _)
        rw [← boundary1_localChainOf hbnd'', hrt]
        exact hcyc
      -- the outer appended bit (cell e₂)
      have htop₂ : (localMaskOf cells₂ u
          >>> (winCellList k ++ [cellIdx e₁]).length) % 2 = 1 := by
        rw [hcells₂, localMaskOf_append_top, coordOfC1_cellIdx e₂,
          if_pos hu₂]
      -- the inner appended bit (cell e₁)
      have htop₁ : (localMaskOf cells₂ u
          >>> (winCellList k).length) % 2 = 1 := by
        rw [hcells₂, localMaskOf_append_singleton]
        have hlen : (winCellList k ++ [cellIdx e₁]).length
            = (winCellList k).length + 1 := by
          simp [List.length_append]
        rw [hlen, bit_mid, localMaskOf_append_top, coordOfC1_cellIdx e₁,
          if_pos hu₁]
      -- decompose the syndrome twice
      have hdec₂ := syndFold_append_singleton
        (winCellList k ++ [cellIdx e₁]) (cellIdx e₂)
        (localMaskOf cells₂ u)
      rw [htop₂, if_pos rfl] at hdec₂
      have hdec₁ := syndFold_append_singleton (winCellList k)
        (cellIdx e₁) (localMaskOf cells₂ u)
      rw [htop₁, if_pos rfl] at hdec₁
      have hfull : syndFold cells₂ (localMaskOf cells₂ u)
          = syndFold (winCellList k) (localMaskOf cells₂ u)
            ^^^ (colMaskPacked (cellIdx e₁)
              ^^^ colMaskPacked (cellIdx e₂)) := by
        rw [hcells₂] at hdec₂ ⊢
        rw [hdec₂, hdec₁, Nat.xor_assoc]
      have ha : natSubset
          (syndFold (winCellList k) (localMaskOf cells₂ u)) (cwMask k) :=
        syndFold_subset_cwMask k (fun c h => h) _
      have hb : ¬ natSubset
          (colMaskPacked (cellIdx e₁) ^^^ colMaskPacked (cellIdx e₂))
          (cwMask k) := by
        intro hns
        apply hsurv
        unfold pairSurvivorB
        unfold natSubset at hns
        exact beq_iff_eq.mpr hns
      have hne0 := xor_ne_zero_of_escape ha hb
      rw [← hfull] at hne0
      exact hne0 hsynd0

end Z5Z15F2A6
end BB
end Homological
end Stabilizer
end Quantum
