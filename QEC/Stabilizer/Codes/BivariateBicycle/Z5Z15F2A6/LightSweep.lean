/-
# A22: the light-classification sweep

The two batched sweep obligations over the certificate data:

* `checkA_all` — the mincost prefilter is complete: every span code `e`
  outside the emitted survivor list has per-site optimal cost > 14
  (sound to skip, since a chain's weight dominates its mincost);
* `checkB_all` — every surviving span element, completed by any in-rep
  ε-pattern (`2⁷`) and at most one outside ε-flip, that reconstructs to
  weight ≤ 14 lands in the translate table.

The ε-pattern plumbing (`expandMask`/`extractS`) comes with the generic
bit-level round trip `expand_extract_or` consumed by the assembly.
-/

import QEC.Stabilizer.Codes.BivariateBicycle.Z5Z15F2A6.LightChecks

namespace Quantum
namespace Stabilizer
namespace Homological
namespace BB
namespace Z5Z15F2A6

set_option maxRecDepth 4096

/-! ## Site lists and ε-pattern packing -/

/-- The rep's sites, ascending. -/
def siteList (j : ℕ) : List ℕ :=
  (List.range 15).filter fun s => (REP7.getD j 0).testBit s

/-- The complement sites, ascending. -/
def outList (j : ℕ) : List ℕ :=
  (List.range 15).filter fun s => !(REP7.getD j 0).testBit s

/-- Every rep has exactly 7 sites. -/
theorem siteList_length : ∀ j : Fin 429, (siteList j.val).length = 7 := by
  native_decide

/-- Spread a local ε-pattern onto a site list (bit `k` ↦ site `sites[k]`,
LSB first). -/
def expandMask : List ℕ → ℕ → ℕ
  | [], _ => 0
  | s :: rest, hS =>
      (if hS % 2 = 1 then 1 <<< s else 0) ||| expandMask rest (hS / 2)

/-- Extract the local ε-pattern of a mask on a site list. -/
def extractS (hm : ℕ) : List ℕ → ℕ
  | [] => 0
  | s :: rest => (if hm.testBit s then 1 else 0) + 2 * extractS hm rest

lemma extractS_lt (hm : ℕ) : ∀ sites : List ℕ,
    extractS hm sites < 2 ^ sites.length := by
  intro sites
  induction sites with
  | nil => simp [extractS]
  | cons s rest ih =>
    show (if hm.testBit s then 1 else 0) + 2 * extractS hm rest
      < 2 ^ (rest.length + 1)
    rw [pow_succ]
    split <;> omega

/-- Bits of the expanded extraction: exactly the mask's bits on listed
sites. -/
lemma expandMask_extractS_testBit (hm : ℕ) : ∀ (sites : List ℕ) (t : ℕ),
    (expandMask sites (extractS hm sites)).testBit t
      = (hm.testBit t && decide (t ∈ sites)) := by
  intro sites
  induction sites with
  | nil =>
    intro t
    simp [expandMask, Nat.zero_testBit]
  | cons s rest ih =>
    intro t
    have hmod : ((if hm.testBit s then 1 else 0) + 2 * extractS hm rest) % 2
        = if hm.testBit s then 1 else 0 := by
      split <;> omega
    have hdiv : ((if hm.testBit s then 1 else 0) + 2 * extractS hm rest) / 2
        = extractS hm rest := by
      split <;> omega
    show ((if ((if hm.testBit s then 1 else 0) + 2 * extractS hm rest) % 2 = 1
        then 1 <<< s else 0)
        ||| expandMask rest
          (((if hm.testBit s then 1 else 0) + 2 * extractS hm rest) / 2)).testBit t
      = _
    rw [hmod, hdiv, Nat.testBit_or, ih t]
    by_cases hts : t = s
    · subst hts
      rcases hb : hm.testBit t with _ | _
      · norm_num [Nat.zero_testBit]
      · norm_num [Nat.one_shiftLeft, Nat.testBit_two_pow, List.mem_cons]
    · have hshift : (if (if hm.testBit s then (1 : ℕ) else 0) = 1
          then 1 <<< s else 0).testBit t = false := by
        split
        · simp [Nat.one_shiftLeft, Nat.testBit_two_pow, Ne.symm hts]
        · simp [Nat.zero_testBit]
      rw [hshift, Bool.false_or]
      have hmem : (t ∈ s :: rest) ↔ (t ∈ rest) := by
        simp [List.mem_cons, hts]
      by_cases hmr : t ∈ rest
      · simp [hmem, hmr]
      · simp [hmem, hmr]

/-- **The ε-pattern round trip**: a 15-bit mask whose bits split into
listed sites plus an optional single outside bit is recovered by
`expandMask ∘ extractS` OR-ed with that bit. -/
lemma expand_extract_or (hm : ℕ) (sites : List ℕ) (ob : ℕ)
    (hhm : hm < 2 ^ 15)
    (hsplit : ∀ t : ℕ, t < 15 → hm.testBit t = true → t ∈ sites ∨
      (ob = 1 <<< t ∧ (1 <<< t : ℕ) &&& hm = 1 <<< t))
    (hob : ob = 0 ∨ ∃ t : ℕ, t < 15 ∧ ob = 1 <<< t ∧ hm.testBit t = true
      ∧ t ∉ sites) :
    expandMask sites (extractS hm sites) ||| ob = hm := by
  apply Nat.eq_of_testBit_eq
  intro t
  rw [Nat.testBit_or, expandMask_extractS_testBit hm sites t]
  by_cases ht15 : t < 15
  · rcases hb : hm.testBit t with _ | _
    · -- mask bit clear: both parts must be clear
      have hobt : ob.testBit t = false := by
        rcases hob with h0 | ⟨t', _, hobv, hbt', _⟩
        · rw [h0]
          exact Nat.zero_testBit t
        · rw [hobv, Nat.one_shiftLeft, Nat.testBit_two_pow]
          by_cases htt : t' = t
          · rw [htt] at hbt'
            rw [hbt'] at hb
            exact absurd hb (by simp)
          · simp [htt]
      rw [hobt]
      simp
    · -- mask bit set: sites case or the outside bit
      rcases hsplit t ht15 hb with hmem | ⟨hobv, _⟩
      · simp [hmem]
      · have : ob.testBit t = true := by
          rw [hobv, Nat.one_shiftLeft, Nat.testBit_two_pow]
          simp
        rw [this]
        simp
  · -- beyond 15 bits everything is clear
    have hhi : hm.testBit t = false :=
      Nat.testBit_eq_false_of_lt
        (lt_of_lt_of_le hhm (Nat.pow_le_pow_right (by norm_num) (by omega)))
    have hobt : ob.testBit t = false := by
      rcases hob with h0 | ⟨t', ht', hobv, _, _⟩
      · rw [h0]
        exact Nat.zero_testBit t
      · rw [hobv, Nat.one_shiftLeft, Nat.testBit_two_pow]
        have : t' ≠ t := by omega
        simp [this]
    rw [hhi, hobt]
    have : (t ∈ sites → False) ∨ True := Or.inr trivial
    simp

/-! ## Packed weights -/

/-- Per-site table weight sum below `k` (h-bit from `hm`, nibbles from
`M`). -/
def wtSites (M hm : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 =>
      W5TAB.getD (16 * (if hm.testBit k then 1 else 0) + M >>> (8 * k) % 16) 0
        + W5TAB.getD (16 * (if hm.testBit k then 1 else 0)
            + M >>> (8 * k + 4) % 16) 0
        + wtSites M hm k

/-- The packed weight of a reconstruction candidate. -/
def wtOf (M hm : ℕ) : ℕ := wtSites M hm 15

/-- Per-site optimal (h-minimized) cost sum below `k`. -/
def minCostSites (M : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 =>
      min (W5TAB.getD (M >>> (8 * k) % 16) 0
            + W5TAB.getD (M >>> (8 * k + 4) % 16) 0)
          (W5TAB.getD (16 + M >>> (8 * k) % 16) 0
            + W5TAB.getD (16 + M >>> (8 * k + 4) % 16) 0)
        + minCostSites M k

/-- The packed mincost of a span element. -/
def minCost (M : ℕ) : ℕ := minCostSites M 15

/-- Mincost bounds the weight of every completion. -/
lemma minCost_le_wtOf (M hm : ℕ) : minCost M ≤ wtOf M hm := by
  have key : ∀ k, minCostSites M k ≤ wtSites M hm k := by
    intro k
    induction k with
    | zero => exact Nat.le_refl 0
    | succ k ih =>
      have hsite : min (W5TAB.getD (M >>> (8 * k) % 16) 0
            + W5TAB.getD (M >>> (8 * k + 4) % 16) 0)
          (W5TAB.getD (16 + M >>> (8 * k) % 16) 0
            + W5TAB.getD (16 + M >>> (8 * k + 4) % 16) 0)
          ≤ W5TAB.getD (16 * (if hm.testBit k then 1 else 0)
              + M >>> (8 * k) % 16) 0
            + W5TAB.getD (16 * (if hm.testBit k then 1 else 0)
              + M >>> (8 * k + 4) % 16) 0 := by
        rcases hb : hm.testBit k with _ | _
        · simp only [hb, Bool.false_eq_true, if_false, Nat.mul_zero,
            Nat.zero_add]
          exact min_le_left _ _
        · simp only [hb, if_true, Nat.mul_one]
          exact min_le_right _ _
      show min (W5TAB.getD (M >>> (8 * k) % 16) 0
            + W5TAB.getD (M >>> (8 * k + 4) % 16) 0)
          (W5TAB.getD (16 + M >>> (8 * k) % 16) 0
            + W5TAB.getD (16 + M >>> (8 * k + 4) % 16) 0)
          + minCostSites M k
        ≤ W5TAB.getD (16 * (if hm.testBit k then 1 else 0)
              + M >>> (8 * k) % 16) 0
            + W5TAB.getD (16 * (if hm.testBit k then 1 else 0)
              + M >>> (8 * k + 4) % 16) 0
          + wtSites M hm k
      exact Nat.add_le_add hsite ih
  exact key 15

/-- The packed reconstruction key. -/
def reconPack (hm M : ℕ) : ℕ :=
  packChain (reconFn (maskFun15 hm) (maskFun120 M))

/-! ## The sweep checks -/

/-- Prefilter completeness: non-survivors have mincost > 14. -/
def checkA (j : ℕ) : Bool :=
  (List.range (2 ^ nGen j)).all fun e =>
    (e == 0) || (survList j).contains e
      || decide (14 < minCost (xorGensE j e))

/-- Survivor completion: every light reconstruction is tabulated. -/
def checkB (j : ℕ) : Bool :=
  ((0 : ℕ) :: survList j).all fun e =>
    let M := xorGensE j e
    (List.range 128).all fun hS =>
      let hm := expandMask (siteList j) hS
      let w := wtOf M hm
      (if 14 < w then true
       else if e == 0 && hS == 0 then true
       else memberTT (reconPack hm M))
      && (if 4 < w then true
          else (outList j).all fun os =>
            memberTT (reconPack (hm ||| (1 <<< os)) M))

theorem checkA_all : ∀ j : Fin 429, checkA j.val = true := by
  native_decide

theorem checkB_all : ∀ j : Fin 429, checkB j.val = true := by
  native_decide

end Z5Z15F2A6
end BB
end Homological
end Stabilizer
end Quantum
