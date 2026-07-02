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
