/-
# Mask encoding and `ker ∂₂` data for the [[36,4,4]] base

Shared definitions for the five `2¹⁸` kernel-sweep leaves
(`Sweep*.lean`) and their consumers:

* the systematic `ker ∂₂` basis (`kb0`, `kb1`, `kcombo`; free cells
  `(0,0)`, `(0,1)`);
* the **mask encoding** of base 2-chains: the sweeps quantify over
  `Fin (2¹⁸)` bitmasks read through `chainOf`, NOT over the function
  space `G36 → ZMod 2` — the `Fintype` enumeration of a Pi type
  materializes 262144 list-backed closures and multiplies every chain
  application by a lookup.  `chainOf_maskOf` round-trips the encoding so
  the public statements still speak about arbitrary chains.  (Same
  device as `Codes/BivariateBicycle/LightStabClassify.lean`, whose
  generic `foldl_testBit` keystone is reproduced here for the 18-cell
  index; a future cleanup can hoist it to the Framework layer.)
* `SeamGood` — the single-shape-rung hypothesis shape.
* the **boundary bitmask layer**: `bndMask` computes the boundary of a decoded
  chain as an XOR of 18 tabulated literal row masks (`bndRowsLit`, certified by
  `bndRowsLit_correct`), and `card_support_eq_natWt` converts support counts to
  popcounts — so the sweep leaves run on pure `Nat` ops instead of re-deriving
  convolutions and `Finset` universes per mask (the previous form cost ~1 h of
  native compute per sweep; `native_decide` evaluates through the IR
  interpreter, so per-mask allocation churn dominates).

The sweeps themselves live in one file each so `lake` builds them in
parallel (the `MImFloorY*` pattern): each takes minutes of native
compute.
-/

import QEC.Stabilizer.Codes.BivariateBicycle.Z3Z6.Defs

namespace Quantum
namespace Stabilizer
namespace Homological
namespace BB
namespace Z3Z6

/-! ## The systematic `ker ∂₂` basis -/

/-- First kernel basis vector (systematic at the free cells:
`kb0 (0,0) = 1`, `kb0 (0,1) = 0`). -/
def kb0 : G36 → ZMod 2 := fun g =>
  if g = (0, 0) ∨ g = (0, 2) ∨ g = (0, 3) ∨ g = (0, 5) ∨
     g = (1, 1) ∨ g = (1, 2) ∨ g = (1, 4) ∨ g = (1, 5) ∨
     g = (2, 0) ∨ g = (2, 1) ∨ g = (2, 3) ∨ g = (2, 4) then 1 else 0

/-- Second kernel basis vector (`kb1 (0,0) = 0`, `kb1 (0,1) = 1`). -/
def kb1 : G36 → ZMod 2 := fun g =>
  if g = (0, 1) ∨ g = (0, 2) ∨ g = (0, 4) ∨ g = (0, 5) ∨
     g = (1, 0) ∨ g = (1, 1) ∨ g = (1, 3) ∨ g = (1, 4) ∨
     g = (2, 0) ∨ g = (2, 2) ∨ g = (2, 3) ∨ g = (2, 5) then 1 else 0

/-- The 2-parameter combination of the kernel basis. -/
def kcombo (c0 c1 : ZMod 2) : G36 → ZMod 2 := fun g =>
  c0 * kb0 g + c1 * kb1 g

theorem kcombo_mem_ker :
    ∀ c0 c1 : ZMod 2, bbBoundary2Fn a36 b36 (kcombo c0 c1) = 0 := by
  native_decide

theorem kcombo_at_free :
    ∀ c0 c1 : ZMod 2, kcombo c0 c1 (0, 0) = c0 ∧ kcombo c0 c1 (0, 1) = c1 := by
  native_decide

/-! ## The mask encoding of base 2-chains -/

/-- Cell of a bit index (`i = 6·x + y`). -/
def cellOf36 (i : Nat) : G36 := ((i / 6 : ℕ), (i % 6 : ℕ))

/-- Bit index of a cell. -/
def idxOf36 (g : G36) : Nat := g.1.val * 6 + g.2.val

/-- The 2-chain read off a bitmask. -/
def chainOf (m : Nat) : G36 → ZMod 2 := fun g =>
  if m.testBit (idxOf36 g) then 1 else 0

/-- The bitmask of a 2-chain. -/
def maskOf (f : G36 → ZMod 2) : Nat :=
  (List.range 18).foldl
    (fun acc i => if f (cellOf36 i) = 1 then acc ^^^ (1 <<< i) else acc) 0

/-- Keystone (reproduced from
`Codes/BivariateBicycle/LightStabClassify.lean`): a nodup select-XOR fold
of shifted ones has exactly the selected bits. -/
theorem foldl_testBit36 (P : Nat → Prop) [DecidablePred P] (i : Nat) :
    ∀ (L : List Nat), L.Nodup → ∀ (a0 : Nat),
    (L.foldl (fun acc j => if P j then acc ^^^ (1 <<< j) else acc) a0).testBit i
      = (a0.testBit i ^^ (decide (i ∈ L) && decide (P i))) := by
  intro L
  induction L with
  | nil =>
    intro _ a0
    simp
  | cons j t ih =>
    intro hnd a0
    rw [List.foldl_cons]
    have hjt : j ∉ t := (List.nodup_cons.mp hnd).1
    have hndt : t.Nodup := (List.nodup_cons.mp hnd).2
    rw [ih hndt]
    have hstep : ((if P j then a0 ^^^ (1 <<< j) else a0).testBit i)
        = (a0.testBit i ^^ (decide (P j) && decide (j = i))) := by
      by_cases hpj : P j
      · rw [if_pos hpj, Nat.testBit_xor, Nat.shiftLeft_eq, one_mul,
          Nat.testBit_two_pow]
        simp [hpj]
      · rw [if_neg hpj]
        simp [hpj]
    rw [hstep]
    by_cases hij : i = j
    · subst hij
      have h1 : decide (i ∈ t) = false := by simp [hjt]
      have h2 : decide (i = i) = true := by simp
      rw [h1, h2]
      simp [Bool.and_comm]
    · have h3 : decide (j = i) = false := by simp [Ne.symm hij]
      rw [h3]
      simp only [List.mem_cons, hij, false_or, Bool.and_false,
        Bool.xor_false]

theorem testBit_maskOf (f : G36 → ZMod 2) (i : Nat) :
    (maskOf f).testBit i
      = (decide (i ∈ List.range 18) && decide (f (cellOf36 i) = 1)) := by
  unfold maskOf
  rw [foldl_testBit36 (fun i => f (cellOf36 i) = 1) i (List.range 18)
    List.nodup_range 0]
  simp

theorem cellOf36_idxOf36 : ∀ g : G36, cellOf36 (idxOf36 g) = g := by
  decide

theorem idxOf36_lt : ∀ g : G36, idxOf36 g < 18 := by
  decide

/-- Masks of 2-chains stay below `2¹⁸` (fold invariant via
`Nat.xor_lt_two_pow`). -/
theorem maskOf_lt (f : G36 → ZMod 2) : maskOf f < 2 ^ 18 := by
  unfold maskOf
  have key : ∀ L : List Nat, (∀ i ∈ L, i < 18) → ∀ a0 : Nat, a0 < 2 ^ 18 →
      (L.foldl (fun acc i =>
        if f (cellOf36 i) = 1 then acc ^^^ (1 <<< i) else acc) a0) < 2 ^ 18 := by
    intro L
    induction L with
    | nil =>
      intro _ a0 h
      simpa using h
    | cons j t ih =>
      intro hmem a0 ha0
      rw [List.foldl_cons]
      refine ih (fun i hi => hmem i (List.mem_cons_of_mem j hi)) _ ?_
      by_cases hj : f (cellOf36 j) = 1
      · rw [if_pos hj]
        have hjlt : (1 <<< j) < 2 ^ 18 := by
          rw [Nat.shiftLeft_eq, one_mul]
          exact Nat.pow_lt_pow_right (by norm_num)
            (hmem j List.mem_cons_self)
        exact Nat.xor_lt_two_pow ha0 hjlt
      · rw [if_neg hj]
        exact ha0
  refine key (List.range 18) (fun i hi => List.mem_range.mp hi) 0 ?_
  positivity

/-- The round trip: every 2-chain is `chainOf` of its mask. -/
theorem chainOf_maskOf (f : G36 → ZMod 2) : chainOf (maskOf f) = f := by
  funext g
  unfold chainOf
  have h18 : decide (idxOf36 g ∈ List.range 18) = true := by
    simp [List.mem_range, idxOf36_lt g]
  rw [testBit_maskOf, h18, Bool.true_and, cellOf36_idxOf36 g]
  have key : ∀ a : ZMod 2, (if decide (a = 1) = true then (1 : ZMod 2) else 0) = a := by
    decide
  exact key (f g)

/-! ## Generic xor-fold and popcount helpers

(Reproduced from `Codes/BivariateBicycle/LightStabClassify.lean` for the same
reason as `foldl_testBit36` above — importing it would couple this subtree to
the gross tower.) -/

theorem foldl_xor_split36 (g h : Nat → Nat) :
    ∀ (row : List Nat) (a b : Nat),
      row.foldl (fun acc i => acc ^^^ (g i ^^^ h i)) (a ^^^ b)
      = (row.foldl (fun acc i => acc ^^^ g i) a) ^^^ (row.foldl (fun acc i => acc ^^^ h i) b) := by
  intro row
  induction row with
  | nil => intro a b; rfl
  | cons i t ih =>
    intro a b
    simp only [List.foldl_cons]
    rw [show (a ^^^ b) ^^^ (g i ^^^ h i) = (a ^^^ g i) ^^^ (b ^^^ h i) from by
      simp only [Nat.xor_assoc]
      congr 1
      rw [← Nat.xor_assoc, Nat.xor_comm b (g i), Nat.xor_assoc]]
    exact ih _ _

/-- Generic "select-and-XOR": XOR of `cols i` over the set bits `i < n` of `m`. -/
def selXor36 (cols : Nat → Nat) (n : Nat) (m : Nat) : Nat :=
  (List.range n).foldl (fun acc i => if m.testBit i then acc ^^^ cols i else acc) 0

theorem selXor36_zero (cols : Nat → Nat) (n : Nat) : selXor36 cols n 0 = 0 := by
  unfold selXor36
  have : (fun (acc : Nat) (i : Nat) => if (0 : Nat).testBit i then acc ^^^ cols i else acc)
      = (fun acc _ => acc) := by funext acc i; rw [Nat.zero_testBit]; rfl
  rw [this]
  clear this
  induction (List.range n) with
  | nil => rfl
  | cons a t ih => rw [List.foldl_cons]; exact ih

theorem selXor36_xor (cols : Nat → Nat) (n m m' : Nat) :
    selXor36 cols n (m ^^^ m') = selXor36 cols n m ^^^ selXor36 cols n m' := by
  unfold selXor36
  rw [show (fun acc i => if (m ^^^ m').testBit i then acc ^^^ cols i else acc)
        = (fun acc i => acc ^^^ ((if m.testBit i then cols i else 0)
            ^^^ (if m'.testBit i then cols i else 0))) from by
      funext acc i; rw [Nat.testBit_xor]; cases m.testBit i <;> cases m'.testBit i <;> simp]
  rw [show (fun acc i => if m.testBit i then acc ^^^ cols i else acc)
        = (fun acc i => acc ^^^ (if m.testBit i then cols i else 0)) from by
      funext acc i; cases m.testBit i <;> simp]
  rw [show (fun acc i => if m'.testBit i then acc ^^^ cols i else acc)
        = (fun acc i => acc ^^^ (if m'.testBit i then cols i else 0)) from by
      funext acc i; cases m'.testBit i <;> simp]
  have h := foldl_xor_split36 (fun i => if m.testBit i then cols i else 0)
    (fun i => if m'.testBit i then cols i else 0) (List.range n) 0 0
  simpa using h

theorem selXor36_low_zero (cols : Nat → Nat) :
    ∀ (n m : Nat), (∀ j, j < n → m.testBit j = false) → selXor36 cols n m = 0 := by
  intro n
  induction n with
  | zero => intro m _; rfl
  | succ k ih =>
    intro m hm
    unfold selXor36
    rw [List.range_succ, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    rw [if_neg (by simp [hm k (Nat.lt_succ_self k)])]
    exact ih m (fun j hj => hm j (Nat.lt_succ_of_lt hj))

theorem selXor36_shiftLeft (cols : Nat → Nat) :
    ∀ (n i : Nat), i < n → selXor36 cols n (1 <<< i) = cols i := by
  intro n
  induction n with
  | zero => intro i hi; exact absurd hi (Nat.not_lt_zero i)
  | succ k ih =>
    intro i hi
    have htb : ∀ j, (1 <<< i).testBit j = decide (i = j) := by
      intro j; rw [Nat.shiftLeft_eq, one_mul, Nat.testBit_two_pow]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hik | rfl
    · unfold selXor36
      rw [List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [if_neg (by simp [htb k]; omega)]
      exact ih i hik
    · unfold selXor36
      rw [List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [if_pos (by simp [htb i])]
      have hpre : (List.range i).foldl
          (fun acc j => if (1 <<< i).testBit j then acc ^^^ cols j else acc) 0 = 0 := by
        have := selXor36_low_zero cols i (1 <<< i) (fun j hj => by
          rw [htb j]; simp; omega)
        simpa [selXor36] using this
      rw [hpre, Nat.zero_xor]

theorem nat_xor_xor_shuffle (a b c d : Nat) :
    (a ^^^ b) ^^^ (c ^^^ d) = (a ^^^ c) ^^^ (b ^^^ d) := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [Nat.testBit_xor]
  cases a.testBit i <;> cases b.testBit i <;> cases c.testBit i <;> cases d.testBit i <;> rfl

theorem nat_xor_eq_zero {a b : Nat} (h : a ^^^ b = 0) : a = b := by
  apply Nat.eq_of_testBit_eq; intro i
  have hbit := congrArg (Nat.testBit · i) h
  simp only [Nat.testBit_xor, Nat.zero_testBit] at hbit
  cases ha : a.testBit i <;> cases hb : b.testBit i <;> simp_all

/-- The `Nat` bit-weight (popcount below `k`): clone of `LightStabClassify.wtM`. -/
def natWt (k n : Nat) : Nat :=
  (List.range k).foldl (fun acc i => acc + ((n >>> i) &&& 1)) 0

theorem bit_and_one36 (m i : Nat) : (m >>> i) &&& 1 = if m.testBit i then 1 else 0 := by
  have hdef : m.testBit i = (1 &&& (m >>> i) != 0) := rfl
  rw [hdef, Nat.and_comm 1 (m >>> i), Nat.and_one_is_mod]
  rcases Nat.mod_two_eq_zero_or_one (m >>> i) with h | h <;> rw [h] <;> rfl

theorem natWt_eq_sum (k n : Nat) :
    natWt k n = ∑ i ∈ Finset.range k, (if n.testBit i then 1 else 0) := by
  induction k with
  | zero => rfl
  | succ j ih =>
    unfold natWt at *
    rw [List.range_succ, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    rw [Finset.sum_range_succ, ← ih, bit_and_one36]

/-! ## Mask-encoding lemmas (C2 side) -/

theorem idxOf36_cellOf36 : ∀ i : Fin 18, idxOf36 (cellOf36 i.val) = i.val := by decide

theorem maskOf_zero : maskOf (0 : G36 → ZMod 2) = 0 := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [testBit_maskOf]; simp

theorem maskOf_add (f g : G36 → ZMod 2) : maskOf (f + g) = maskOf f ^^^ maskOf g := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_xor, testBit_maskOf, testBit_maskOf, testBit_maskOf]
  by_cases hi : i ∈ List.range 18
  · simp only [hi, decide_true, Bool.true_and]
    have hpt : (f + g) (cellOf36 i) = f (cellOf36 i) + g (cellOf36 i) := rfl
    rw [hpt]
    have key : ∀ u v : ZMod 2, decide (u + v = 1) = (decide (u = 1) ^^ decide (v = 1)) := by
      decide
    rw [key]
  · simp [hi]

theorem maskOf_single (g : G36) : maskOf (Pi.single g 1) = 1 <<< idxOf36 g := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [testBit_maskOf, Nat.shiftLeft_eq, one_mul, Nat.testBit_two_pow]
  by_cases hi : i ∈ List.range 18
  · have hlt : i < 18 := List.mem_range.mp hi
    simp only [hi, decide_true, Bool.true_and]
    by_cases hgi : cellOf36 i = g
    · have hidx : idxOf36 g = i := by
        rw [← hgi, idxOf36_cellOf36 ⟨i, hlt⟩]
      simp [Pi.single_apply, hgi, hidx]
    · have hidx : idxOf36 g ≠ i := fun h => hgi (by rw [← h, cellOf36_idxOf36])
      simp [hgi, hidx]
  · have h18 : ¬ i < 18 := by simpa [List.mem_range] using hi
    have hidx : idxOf36 g ≠ i := by have := idxOf36_lt g; omega
    simp [hi, hidx]

theorem maskOf_chainOf {m : Nat} (hm : m < 2 ^ 18) : maskOf (chainOf m) = m := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [testBit_maskOf]
  by_cases hi : i ∈ List.range 18
  · have hlt : i < 18 := List.mem_range.mp hi
    simp only [hi, decide_true, Bool.true_and]
    unfold chainOf
    rw [idxOf36_cellOf36 ⟨i, hlt⟩]
    cases htb : m.testBit i <;> simp
  · have h18 : ¬ i < 18 := by simpa [List.mem_range] using hi
    have hbit : m.testBit i = false := by
      apply Nat.testBit_lt_two_pow
      calc m < 2 ^ 18 := hm
        _ ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
    simp [hi, hbit]

theorem chainOf_zero : chainOf 0 = 0 := by
  funext g; unfold chainOf; rw [Nat.zero_testBit]; rfl

theorem chainOf_apply_eq_zero_iff (m : Nat) (g : G36) :
    chainOf m g = 0 ↔ m.testBit (idxOf36 g) = false := by
  unfold chainOf
  cases htb : m.testBit (idxOf36 g) <;> simp

theorem chainOf_eq_zero_iff {m : Nat} (hm : m < 2 ^ 18) : chainOf m = 0 ↔ m = 0 := by
  constructor
  · intro h
    have hround := maskOf_chainOf hm
    rw [h, maskOf_zero] at hround
    exact hround.symm
  · rintro rfl; exact chainOf_zero

/-! ## The C1 (boundary-side) mask encoding -/

def idxOfC1 (j : G36 × Fin 2) : Nat := idxOf36 j.1 + 18 * j.2.val

def coordOfC1 (i : Nat) : G36 × Fin 2 :=
  (cellOf36 (i % 18), ⟨i / 18 % 2, Nat.mod_lt _ (by norm_num)⟩)

def c1MaskOf (F : G36 × Fin 2 → ZMod 2) : Nat :=
  (List.range 36).foldl
    (fun acc i => if F (coordOfC1 i) = 1 then acc ^^^ (1 <<< i) else acc) 0

theorem testBit_c1MaskOf (F : G36 × Fin 2 → ZMod 2) (i : Nat) :
    (c1MaskOf F).testBit i
      = (decide (i ∈ List.range 36) && decide (F (coordOfC1 i) = 1)) := by
  unfold c1MaskOf
  rw [foldl_testBit36 (fun i => F (coordOfC1 i) = 1) i (List.range 36)
    List.nodup_range 0]
  simp

theorem coordOfC1_idxOfC1 : ∀ j : G36 × Fin 2, coordOfC1 (idxOfC1 j) = j := by decide

theorem idxOfC1_lt : ∀ j : G36 × Fin 2, idxOfC1 j < 36 := by decide

theorem idxOfC1_coordOfC1 : ∀ i : Fin 36, idxOfC1 (coordOfC1 i.val) = i.val := by decide

theorem c1MaskOf_testBit_iff (F : G36 × Fin 2 → ZMod 2) (j : G36 × Fin 2) :
    (c1MaskOf F).testBit (idxOfC1 j) = true ↔ F j ≠ 0 := by
  rw [testBit_c1MaskOf, coordOfC1_idxOfC1 j]
  have h36 : idxOfC1 j ∈ List.range 36 := List.mem_range.mpr (idxOfC1_lt j)
  simp only [h36, decide_true, Bool.true_and, decide_eq_true_eq]
  constructor
  · intro h; rw [h]; exact one_ne_zero
  · intro h
    have key : ∀ a : ZMod 2, a ≠ 0 → a = 1 := by decide
    exact key _ h

theorem c1MaskOf_zero : c1MaskOf 0 = 0 := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [testBit_c1MaskOf]; simp

theorem c1MaskOf_add (F G : G36 × Fin 2 → ZMod 2) :
    c1MaskOf (F + G) = c1MaskOf F ^^^ c1MaskOf G := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_xor, testBit_c1MaskOf, testBit_c1MaskOf, testBit_c1MaskOf]
  by_cases hi : i ∈ List.range 36
  · simp only [hi, decide_true, Bool.true_and]
    have hpt : (F + G) (coordOfC1 i) = F (coordOfC1 i) + G (coordOfC1 i) := rfl
    rw [hpt]
    have key : ∀ u v : ZMod 2, decide (u + v = 1) = (decide (u = 1) ^^ decide (v = 1)) := by
      decide
    rw [key]
  · simp [hi]

theorem c1MaskOf_eq_zero_iff (F : G36 × Fin 2 → ZMod 2) : c1MaskOf F = 0 ↔ F = 0 := by
  constructor
  · intro h
    funext j
    have := c1MaskOf_testBit_iff F j
    rw [h, Nat.zero_testBit] at this
    by_contra hne
    exact absurd (this.mpr hne) (by simp)
  · rintro rfl; exact c1MaskOf_zero

/-- **Support-count = popcount**: the support cardinality of a C1 chain is the
bit-weight of its mask (the `idxOfC1` bijection). -/
theorem card_support_eq_natWt (F : G36 × Fin 2 → ZMod 2) :
    (Finset.univ.filter fun j : G36 × Fin 2 => F j ≠ 0).card = natWt 36 (c1MaskOf F) := by
  rw [natWt_eq_sum, ← Finset.card_filter]
  apply Finset.card_bij (fun j _ => idxOfC1 j)
  · intro j hj
    have hFj : F j ≠ 0 := (Finset.mem_filter.mp hj).2
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨idxOfC1_lt j, (c1MaskOf_testBit_iff F j).mpr hFj⟩
  · intro j1 _ j2 _ heq
    rw [← coordOfC1_idxOfC1 j1, heq, coordOfC1_idxOfC1 j2]
  · intro i hi
    obtain ⟨hir, htb⟩ := Finset.mem_filter.mp hi
    have hi36 : i < 36 := Finset.mem_range.mp hir
    refine ⟨coordOfC1 i, ?_, idxOfC1_coordOfC1 ⟨i, hi36⟩⟩
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    have := (c1MaskOf_testBit_iff F (coordOfC1 i))
    rw [idxOfC1_coordOfC1 ⟨i, hi36⟩] at this
    exact this.mp htb

/-! ## Indicator / xor-lift machinery (cloned from CRTFrame / LightStabClassify) -/

def ind36 (S : Finset G36) : G36 → ZMod 2 := fun g => if g ∈ S then 1 else 0

theorem ind36_empty : ind36 ∅ = 0 := by funext g; simp [ind36]

theorem ind36_insert {p : G36} {S : Finset G36} (hp : p ∉ S) :
    ind36 (insert p S) = Pi.single p 1 + ind36 S := by
  funext g
  simp only [ind36, Finset.mem_insert, Pi.add_apply, Pi.single_apply]
  by_cases hgp : g = p
  · have hgS : g ∉ S := by rw [hgp]; exact hp
    rw [if_pos (Or.inl hgp), if_pos hgp, if_neg hgS, add_zero]
  · by_cases hgS : g ∈ S
    · rw [if_pos (Or.inr hgS), if_neg hgp, if_pos hgS, zero_add]
    · rw [if_neg (not_or.mpr ⟨hgp, hgS⟩), if_neg hgp, if_neg hgS, add_zero]

theorem self_eq_ind36_filter (z : G36 → ZMod 2) :
    z = ind36 (Finset.univ.filter (fun p => z p = 1)) := by
  have hz : ∀ a : ZMod 2, (if a = 1 then (1 : ZMod 2) else 0) = a := by decide
  funext g
  simp only [ind36, Finset.mem_filter, Finset.mem_univ, true_and]
  exact (hz (z g)).symm

theorem xorLift36 (M : (G36 → ZMod 2) → Nat) (P : Nat → Prop)
    (hM0 : M 0 = 0)
    (hadd : ∀ a b, M (a + b) = M a ^^^ M b)
    (hP0 : P 0)
    (hPxor : ∀ m n, P m → P n → P (m ^^^ n))
    (hbasis : ∀ g, P (M (Pi.single g 1)))
    (b : G36 → ZMod 2) : P (M b) := by
  have key : ∀ S : Finset G36, P (M (ind36 S)) := by
    intro S
    induction S using Finset.induction with
    | empty => rw [ind36_empty, hM0]; exact hP0
    | @insert p S hp ih => rw [ind36_insert hp, hadd]; exact hPxor _ _ (hbasis p) ih
  rw [self_eq_ind36_filter b]; exact key _

/-! ## Tabulated boundary rows and the fast boundary mask -/

theorem bbBoundary2Fn_zero36 : bbBoundary2Fn a36 b36 (0 : G36 → ZMod 2) = 0 := by
  have h : bbBoundary2Fn a36 b36 ((0 : G36 → ZMod 2) + 0)
      = bbBoundary2Fn a36 b36 0 + bbBoundary2Fn a36 b36 0 := bbBoundary2Fn_add a36 b36 0 0
  rw [add_zero] at h
  have h2 : bbBoundary2Fn a36 b36 0 + bbBoundary2Fn a36 b36 0
      = bbBoundary2Fn a36 b36 0 + 0 := by rw [add_zero]; exact h.symm
  exact add_left_cancel h2

/-- The 18 boundary-row masks (`c1MaskOf (∂ (Pi.single (cellOf36 i) 1))`), tabulated
as literals so the sweeps' native code never recomputes a convolution;
`bndRowsLit_correct` certifies every row. -/
def bndRowsLit : List Nat :=
  [18092042, 36184084, 72368168, 144736273, 272957474, 545914885,
   1157628545, 2315257090, 4630514180, 9261024328, 17465084048, 34930164064,
   5369012288, 10738024576, 21476049152, 42951840256, 18257945600, 36515633152]

theorem bndRowsLit_correct : ∀ g : G36,
    bndRowsLit.getD (idxOf36 g) 0
      = c1MaskOf (bbBoundary2Fn a36 b36 (Pi.single g 1)) := by
  native_decide

/-- The boundary bitmask of the 2-chain with mask `m`: XOR of the tabulated rows
at the set bits of `m`. -/
def bndMask (m : Nat) : Nat := selXor36 (fun i => bndRowsLit.getD i 0) 18 m

/-- **The bridge**: the tabulated row-XOR boundary mask agrees with the semantic
boundary of the decoded chain, for every 2-chain — by F₂-linearity over the basis
chains (`xorLift36`; no `2¹⁸` enumeration). -/
theorem bndMask_maskOf (f : G36 → ZMod 2) :
    bndMask (maskOf f) = c1MaskOf (bbBoundary2Fn a36 b36 f) := by
  apply nat_xor_eq_zero
  apply xorLift36
    (fun w => bndMask (maskOf w) ^^^ c1MaskOf (bbBoundary2Fn a36 b36 w))
    (fun n => n = 0)
  · show bndMask (maskOf 0) ^^^ c1MaskOf (bbBoundary2Fn a36 b36 0) = 0
    rw [maskOf_zero, bbBoundary2Fn_zero36, c1MaskOf_zero]
    unfold bndMask
    rw [selXor36_zero]
    exact Nat.xor_self 0
  · intro a b
    show bndMask (maskOf (a + b)) ^^^ c1MaskOf (bbBoundary2Fn a36 b36 (a + b)) = _
    unfold bndMask
    rw [maskOf_add, selXor36_xor, bbBoundary2Fn_add, c1MaskOf_add]
    exact nat_xor_xor_shuffle _ _ _ _
  · rfl
  · intro m n hm hn
    rw [hm, hn]
    exact Nat.xor_self 0
  · intro g
    show bndMask (maskOf (Pi.single g 1))
        ^^^ c1MaskOf (bbBoundary2Fn a36 b36 (Pi.single g 1)) = 0
    rw [maskOf_single]
    unfold bndMask
    rw [selXor36_shiftLeft _ 18 (idxOf36 g) (idxOf36_lt g), bndRowsLit_correct g]
    exact Nat.xor_self _

/-! ## The assembled sweep bridges -/

theorem bnd_c1MaskOf {m : Nat} (hm : m < 2 ^ 18) :
    c1MaskOf (bbBoundary2Fn a36 b36 (chainOf m)) = bndMask m := by
  rw [← bndMask_maskOf, maskOf_chainOf hm]

theorem bnd_eq_zero_iff {m : Nat} (hm : m < 2 ^ 18) :
    bbBoundary2Fn a36 b36 (chainOf m) = 0 ↔ bndMask m = 0 := by
  rw [← c1MaskOf_eq_zero_iff, bnd_c1MaskOf hm]

/-! ## Seam-goodness (the single-shape-rung hypothesis) -/

/-- Seam-goodness of a base 2-chain: the sheet-0 seam of its lifted
stabilizer is supported inside its boundary. -/
def SeamGood (f₀ : G36 → ZMod 2) : Prop :=
  ∀ j : G36 × Fin 2,
    coverData.sheet0 (coverData.liftStab f₀) j ≠ 0 →
    bbBoundary2Fn a36 b36 f₀ j ≠ 0

instance (f₀ : G36 → ZMod 2) : Decidable (SeamGood f₀) := by
  unfold SeamGood
  infer_instance

end Z3Z6
end BB
end Homological
end Stabilizer
end Quantum
