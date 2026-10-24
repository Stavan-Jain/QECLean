import QEC.Stabilizer.Framework.Homological.Certificate.PairMaskBasics
import QEC.Stabilizer.Framework.Homological.Certificate.BitDilation
import QEC.Stabilizer.Framework.Homological.Certificate.BitPlaneFilter

namespace Quantum.Stabilizer.Homological.F2Mask
open PackedDigits

/-- The pair-indexed XOR values of a binary parity plane. -/
def pairPlaneGrid (width count plane : Nat) : Nat :=
  dilate width count plane * (2^count-1) ^^^ plane * packF width count (fun _ => 1)

/-- The square of the coordinates outside a shadow, including zero sentinels. -/
def pairDomain (width count beta : Nat) : Nat :=
  let off := (2^count-1) ^^^ beta
  (dilate width count off * (2^count-1)) &&& (off * packF width count (fun _ => 1))

/-- A family of parity planes takes the successive bits of the required syndrome. -/
def planeConstraints (k : Nat) : List Nat → Nat → Nat → Prop
  | [], _, _ => True
  | p :: ps, target, word =>
      parityFold k (p &&& word) = (if target.testBit 0 then 1 else 0) ∧
        planeConstraints k ps (target >>> 1) word

/-- Canonically encoded outside supports use only coordinates outside the shadow. -/
theorem pair_coordinates_outside (n beta q r : Nat) (hb : beta < 2^n)
    (hpair : (q < r ∧ r ≤ n) ∨ (q = n ∧ r = n))
    (hout : pairMask n q r &&& beta = 0) :
    beta.testBit q = false ∧ beta.testBit r = false := by
  have hsent : beta.testBit n = false := Nat.testBit_eq_false_of_lt hb
  rcases hpair with ⟨hqr,hr⟩ | ⟨rfl,rfl⟩
  · have hq : q < n := by omega
    have hqb := congrArg (fun x : Nat => x.testBit q) hout
    simp only [Nat.testBit_and,pairMask,Nat.testBit_xor,singletonMask,if_pos hq,
      Nat.testBit_two_pow] at hqb
    have hqn : q ≠ r := by omega
    have hrn : r ≠ q := by omega
    by_cases hrl : r < n
    · have hrb := congrArg (fun x : Nat => x.testBit r) hout
      simp only [Nat.testBit_and,pairMask,Nat.testBit_xor,singletonMask,if_pos hq,
        if_pos hrl,Nat.testBit_two_pow] at hrb
      simp only [if_pos hrl, Nat.testBit_two_pow, hqn, hrn,
        decide_true, decide_false, Nat.zero_testBit, Bool.xor_false,
        Bool.false_xor, Bool.true_and] at hqb hrb
      exact ⟨hqb,hrb⟩
    · have hre : r = n := by omega
      simp only [if_neg hrl, decide_true, Nat.zero_testBit,
        Bool.xor_false, Bool.true_and] at hqb
      exact ⟨hqb,by simpa [hre] using hsent⟩
  · exact ⟨hsent,hsent⟩

/-- Every pair of outside coordinates is present in the parallel square domain. -/
theorem pairDomain_bit (width count beta q r : Nat) (hw : 0 < width)
    (hc : count < width) (hb : beta < 2^count) (hq : q < count) (hr : r < count)
    (hbq : beta.testBit q = false) (hbr : beta.testBit r = false) :
    (pairDomain width count beta).testBit (width*q+r) = true := by
  let off := (2^count-1) ^^^ beta
  have hoff : off < 2^count := Nat.xor_lt_two_pow (Nat.sub_lt (Nat.two_pow_pos _) (by decide)) hb
  have hoffq : off.testBit q = true := by simp [off,Nat.testBit_xor,hq,hbq]
  have hoffr : off.testBit r = true := by simp [off,Nat.testBit_xor,hr,hbr]
  change ((dilate width count off * (2^count-1)) &&&
    (off * packF width count (fun _ => 1))).testBit (width*q+r) = true
  rw [dilate_fill,repeat_word,Nat.testBit_and]
  have hfull : 2^count-1 < 2^width := (Nat.sub_lt (Nat.two_pow_pos _) (by decide)).trans
    (Nat.pow_lt_pow_right (by decide) hc)
  have hbound : ∀ i < count, (if off.testBit i then 2^count-1 else 0) < 2^width := by
    intro i hi
    split <;> omega
  rw [testBit_packF_at _ _ _ _ _ hbound (by omega),if_pos hq,
    testBit_packF_at _ _ _ _ _ (fun _ _ => hoff.trans (Nat.pow_lt_pow_right (by decide) hc))
      (by omega),if_pos hq]
  simp [hoffq,hoffr,hr]

/-- Pairwise XOR evaluation transfers parity constraints to the bit-plane relation. -/
theorem pair_plane_relation (n k width count q r : Nat) (hn : n ≤ 2^k)
    (hw : 0 < width) (hc : count < width) (hnc : n < count)
    (hq : q ≤ n) (hr : r ≤ n) (ps : List Nat)
    (hp : ∀ p ∈ ps, p < 2^n) :
    ∀ target, planeConstraints k ps target (pairMask n q r) →
      trieRel ((ps.map (pairPlaneGrid width count)).map fun p => (p,0)) target (width*q+r) 0 := by
  induction ps with
  | nil => simp [planeConstraints,trieRel]
  | cons p ps ih =>
    intro target h
    have hpc := (hp p (by simp)).trans_le (Nat.pow_le_pow_right (by decide) (by omega : n ≤ count))
    have hhead := h.1
    rw [parityFold_pairMask n k p q r hn (hp p (by simp)) hq hr] at hhead
    simp only [List.map_cons,trieRel,Nat.zero_testBit,Bool.false_xor]
    constructor
    · rw [pairPlaneGrid,pairPlane_bit width count p q r hw hc hpc (by omega) (by omega)]
      cases hpq : p.testBit q <;> cases hpr : p.testBit r <;> cases ht : target.testBit 0 <;>
        simp_all
    · exact ih (fun a ha => hp a (by simp [ha])) _ h.2

/-- The checked pair plane census contains every outside mask of weight at most two. -/
theorem cap_two_pair_coverage (n k width count beta word target expected : Nat)
    (ps : List Nat) (hn : n ≤ 2^k) (hw : 0 < width) (hc : count < width) (hnc : n < count)
    (hb : beta < 2^n) (hx : word < 2^n) (hweight : bitCount n word ≤ 2)
    (hout : word &&& beta = 0) (hp : ∀ p ∈ ps, p < 2^n)
    (hconstraints : planeConstraints k ps target word)
    (hcheck : filterPlanes (ps.map (pairPlaneGrid width count)) target
      (pairDomain width count beta) = expected) :
    ∃ q r, ((q < r ∧ r ≤ n) ∨ (q = n ∧ r = n)) ∧
      word = pairMask n q r ∧ expected.testBit (width*q+r) = true := by
  obtain ⟨q,r,hpair,rfl⟩ := small_mask_pair n word hx hweight
  have hqr : q ≤ n ∧ r ≤ n := by rcases hpair with h | h <;> omega
  obtain ⟨hbq,hbr⟩ := pair_coordinates_outside n beta q r hb hpair hout
  refine ⟨q,r,hpair,rfl,?_⟩
  apply filterPlanes_complete _ _ _ _ _ hcheck
  · exact pairDomain_bit width count beta q r hw hc
      (hb.trans_le (Nat.pow_le_pow_right (by decide) (by omega))) (by omega) (by omega) hbq hbr
  · exact pair_plane_relation n k width count q r hn hw hc hnc hqr.1 hqr.2 ps hp target hconstraints

/-- An empty pair census excludes every outside mask of weight at most two. -/
theorem cap_two_impossible (n k width count beta word target : Nat)
    (ps : List Nat) (hn : n ≤ 2^k) (hw : 0 < width) (hc : count < width) (hnc : n < count)
    (hb : beta < 2^n) (hx : word < 2^n) (hweight : bitCount n word ≤ 2)
    (hout : word &&& beta = 0) (hp : ∀ p ∈ ps, p < 2^n)
    (hconstraints : planeConstraints k ps target word)
    (hcheck : filterPlanes (ps.map (pairPlaneGrid width count)) target
      (pairDomain width count beta) = 0) : False := by
  obtain ⟨q,r,_,_,h⟩ := cap_two_pair_coverage n k width count beta word target 0 ps
    hn hw hc hnc hb hx hweight hout hp hconstraints hcheck
  simp at h

/-- A listed pair census gives an explicit allowed-list statement for every outside mask. -/
theorem cap_two_allowed (n k width count beta word target : Nat)
    (ps codes allowed : List Nat) (hn : n ≤ 2^k) (hw : 0 < width) (hc : count < width)
    (hnc : n < count) (hb : beta < 2^n) (hx : word < 2^n) (hweight : bitCount n word ≤ 2)
    (hout : word &&& beta = 0) (hp : ∀ p ∈ ps, p < 2^n)
    (hconstraints : planeConstraints k ps target word)
    (hcheck : filterPlanes (ps.map (pairPlaneGrid width count)) target
      (pairDomain width count beta) = listedBits codes)
    (hallowed : ∀ c ∈ codes, pairMask n (c/width) (c%width) ∈ allowed) : word ∈ allowed := by
  obtain ⟨q,r,hpair,he,hbit⟩ := cap_two_pair_coverage n k width count beta word target
    (listedBits codes) ps hn hw hc hnc hb hx hweight hout hp hconstraints hcheck
  have hr : r < width := by rcases hpair with h | h <;> omega
  have hmem := pair_mem_of_listed_bit n width q r (listedBits codes) codes hw hr rfl hbit
  obtain ⟨c,hc,hec⟩ := List.mem_map.mp hmem
  rw [he,← hec]
  exact hallowed c hc

end Quantum.Stabilizer.Homological.F2Mask
