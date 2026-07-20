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

end Z5Z15F2A6
end BB
end Homological
end Stabilizer
end Quantum
