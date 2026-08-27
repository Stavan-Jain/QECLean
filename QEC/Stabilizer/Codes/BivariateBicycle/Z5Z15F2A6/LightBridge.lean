/-
# A22: semantic ↔ packed bridges for the light-classification assembly

The lemma layer connecting a boundary's semantic (ε, δ)-data to the
packed quantities the sweep enumerates:

* `packH`/`maskFun15_packH` — 15-bit ε-vector round trip, and the
  active-site popcount bridge `countBits_packH_eq_card`;
* `nibVal_shift` — δ-nibbles of unpacked masks are the shift-mod-16
  fields the tables index by;
* `weight_eq_wtOf` — a chain's weight *is* the sweep's packed
  table-weight of its own (h, αβ) codes;
* `xorGensE_support` — span elements stay inside the rep's bytes;
* `wtOf_or_single` — an outside ε-flip adds exactly 10;
* the `translate1`-transport of the (ε, δ)-extraction along
  site translations (`dU_translate` etc.) and weight invariance
  (`chainWeight_translate1`).
-/

import QEC.Stabilizer.Codes.BivariateBicycle.Z5Z15F2A6.LightSweep

namespace Quantum
namespace Stabilizer
namespace Homological
namespace BB
namespace Z5Z15F2A6

open scoped BigOperators

set_option maxRecDepth 4096

/-! ## The 15-bit ε-vector pack -/

/-- Total lookup of an ε-vector. -/
def hAt (h : Fin 15 → ZMod 2) (k : ℕ) : ZMod 2 :=
  if hk : k < 15 then h ⟨k, hk⟩ else 0

/-- Pack the first `k` ε-bits. -/
def packHUpTo (h : Fin 15 → ZMod 2) : ℕ → ℕ
  | 0 => 0
  | k + 1 => (if hAt h k = 1 then 1 <<< k else 0) ^^^ packHUpTo h k

/-- The packed ε-vector. -/
def packH (h : Fin 15 → ZMod 2) : ℕ := packHUpTo h 15

lemma packHUpTo_lt (h : Fin 15 → ZMod 2) : ∀ k, packHUpTo h k < 2 ^ k := by
  intro k
  induction k with
  | zero => simp [packHUpTo]
  | succ k ih =>
    show ((if hAt h k = 1 then 1 <<< k else 0) ^^^ packHUpTo h k) < 2 ^ (k + 1)
    have h1 : (if hAt h k = 1 then 1 <<< k else 0) < 2 ^ (k + 1) := by
      split
      · rw [Nat.one_shiftLeft]
        exact Nat.pow_lt_pow_right (by norm_num) (by omega)
      · positivity
    have h2 : packHUpTo h k < 2 ^ (k + 1) :=
      lt_trans ih (Nat.pow_lt_pow_right (by norm_num) (by omega))
    exact xor_lt_two_pow h1 h2

lemma packH_lt (h : Fin 15 → ZMod 2) : packH h < 2 ^ 15 := packHUpTo_lt h 15

lemma packHUpTo_testBit (h : Fin 15 → ZMod 2) :
    ∀ k i : ℕ, (packHUpTo h k).testBit i
      = (decide (i < k) && decide (hAt h i = 1)) := by
  intro k
  induction k with
  | zero =>
    intro i
    simp [packHUpTo]
  | succ k ih =>
    intro i
    show ((if hAt h k = 1 then 1 <<< k else 0) ^^^ packHUpTo h k).testBit i = _
    rw [Nat.testBit_xor, ih i]
    by_cases hik : i = k
    · subst hik
      have h2 : ¬ i < i := by omega
      have h3 : i < i + 1 := by omega
      simp only [h2, decide_false, Bool.false_and, Bool.xor_false, h3,
        decide_true, Bool.true_and]
      split
      · next hb => simp [Nat.one_shiftLeft, Nat.testBit_two_pow, hb]
      · next hb => simp [Nat.zero_testBit, hb]
    · have hbit0 : (if hAt h k = 1 then 1 <<< k else 0).testBit i = false := by
        split
        · simp [Nat.one_shiftLeft, Nat.testBit_two_pow, Ne.symm hik]
        · simp [Nat.zero_testBit]
      rw [hbit0, Bool.false_xor]
      congr 1
      simp only [decide_eq_decide]
      omega

/-- Round trip: unpacking the packed ε-vector restores it. -/
lemma maskFun15_packH (h : Fin 15 → ZMod 2) : maskFun15 (packH h) = h := by
  funext s
  show (if (packHUpTo h 15).testBit s.val then (1 : ZMod 2) else 0) = h s
  rw [packHUpTo_testBit h 15 s.val]
  have hlt : s.val < 15 := s.isLt
  have hha : hAt h s.val = h s := by
    rw [hAt, dif_pos hlt]
  simp only [hlt, decide_true, Bool.true_and, hha]
  have hz : ∀ a : ZMod 2, (if decide (a = 1) = true then (1 : ZMod 2) else 0) = a := by
    decide
  exact hz (h s)

/-- The popcount of a packed indicator is the predicate's filter card. -/
lemma countBits_packH_eq_card (P : Fin 15 → Prop) [DecidablePred P] :
    countBits (packH (fun s => if P s then 1 else 0)) 15
      = (Finset.univ.filter P).card := by
  have hbit : ∀ s : Fin 15,
      (packH (fun s => if P s then (1 : ZMod 2) else 0)).testBit s.val
        = decide (P s) := by
    intro s
    rw [packH, packHUpTo_testBit]
    have hlt : s.val < 15 := s.isLt
    have hha : hAt (fun s => if P s then (1 : ZMod 2) else 0) s.val
        = if P s then 1 else 0 := by
      rw [hAt, dif_pos hlt]
    simp only [hlt, decide_true, Bool.true_and, hha]
    by_cases hP : P s
    · simp [hP]
    · simp [hP]
  have hsum : ∀ k : ℕ, k ≤ 15 →
      countBits (packH (fun s => if P s then (1 : ZMod 2) else 0)) k
        = ∑ t ∈ Finset.range k,
            (if (packH (fun s => if P s then (1 : ZMod 2) else 0)).testBit t
             then 1 else 0) := by
    intro k
    induction k with
    | zero => simp [countBits]
    | succ k ih =>
      intro hk
      show (if _ then 1 else 0) + countBits _ k = _
      rw [Finset.sum_range_succ, ih (by omega), add_comm]
  rw [hsum 15 le_rfl, Finset.card_filter, ← Fin.sum_univ_eq_sum_range
    (fun t => if (packH (fun s => if P s then (1 : ZMod 2) else 0)).testBit t
      then 1 else 0) 15]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [hbit s]
  by_cases hP : P s
  · simp [hP]
  · simp [hP]

/-! ## Nibble arithmetic -/

lemma nib_arith (x : ℕ) : x % 16
    = (if x.testBit 0 then 1 else 0) + 2 * (if x.testBit 1 then 1 else 0)
      + 4 * (if x.testBit 2 then 1 else 0)
      + 8 * (if x.testBit 3 then 1 else 0) := by
  have key : ∀ i : ℕ, (if x.testBit i then (1 : ℕ) else 0) = x / 2 ^ i % 2 := by
    intro i
    rw [Nat.testBit_eq_decide_div_mod_eq]
    rcases Nat.mod_two_eq_zero_or_one (x / 2 ^ i) with h | h
    · rw [h]
      simp
    · rw [h]
      simp
  rw [key 0, key 1, key 2, key 3]
  norm_num
  omega

/-- δ-nibble of an unpacked mask at offset `k`. -/
lemma nibVal_shift (M k : ℕ) (d : Fin 4 → ZMod 2)
    (hd : ∀ n : Fin 4, d n = if M.testBit (k + n.val) then 1 else 0) :
    nibVal d = M >>> k % 16 := by
  rw [nib_arith (M >>> k)]
  have hsh : ∀ n : ℕ, (M >>> k).testBit n = M.testBit (k + n) := fun n =>
    Nat.testBit_shiftRight ..
  rw [hsh 0, hsh 1, hsh 2, hsh 3, nibVal, hd 0, hd 1, hd 2, hd 3]
  have hz : ∀ c : Bool, (if (if c then (1 : ZMod 2) else 0) = 1
      then (1 : ℕ) else 0) = if c then 1 else 0 := by decide
  rw [hz, hz, hz, hz]
  rfl

/-! ## The weight bridge -/

lemma wtSites_eq_sum (M hm : ℕ) : ∀ k : ℕ,
    wtSites M hm k = ∑ t ∈ Finset.range k,
      (W5TAB.getD (16 * (if hm.testBit t then 1 else 0) + M >>> (8 * t) % 16) 0
        + W5TAB.getD (16 * (if hm.testBit t then 1 else 0)
            + M >>> (8 * t + 4) % 16) 0) := by
  intro k
  induction k with
  | zero => simp [wtSites]
  | succ k ih =>
    show _ + _ + wtSites M hm k = _
    rw [Finset.sum_range_succ, ih, add_comm]

/-- **The weight bridge**: a chain's weight is the packed table weight of
its own codes. -/
theorem weight_eq_wtOf (b : G150 × Fin 2 → ZMod 2)
    (hEps : ∀ s : Fin 15, hV b s = hU b s) (M hm : ℕ)
    (hy : deltaData b = maskFun120 M) (hh : hU b = maskFun15 hm) :
    (Finset.univ.filter fun j : G150 × Fin 2 => b j ≠ 0).card = wtOf M hm := by
  rw [chainWeight_eq_sum_sites, wtOf, wtSites_eq_sum,
    ← Fin.sum_univ_eq_sum_range (fun t =>
      W5TAB.getD (16 * (if hm.testBit t then 1 else 0) + M >>> (8 * t) % 16) 0
        + W5TAB.getD (16 * (if hm.testBit t then 1 else 0)
            + M >>> (8 * t + 4) % 16) 0) 15]
  refine Finset.sum_congr rfl fun s _ => ?_
  have hhs : hU b s = (if hm.testBit s.val then 1 else 0) := by
    rw [hh]
    rfl
  have hidx : (if hU b s = 1 then 16 else 0)
      = 16 * (if hm.testBit s.val then 1 else 0) := by
    rcases hb : hm.testBit s.val with _ | _ <;> rw [hb] at hhs
    · rw [hhs]
      norm_num
    · rw [hhs]
      norm_num
  have hanib : nibVal (fun n : Fin 4 => dU b s n) = M >>> (8 * s.val) % 16 := by
    refine nibVal_shift M (8 * s.val) _ fun n => ?_
    have := deltaData_apply_u b s n ⟨8 * s.val + n.val, by
      have := s.isLt; have := n.isLt; omega⟩ rfl
    rw [← this, hy]
    rfl
  have hbnib : nibVal (fun n : Fin 4 => dV b s n)
      = M >>> (8 * s.val + 4) % 16 := by
    refine nibVal_shift M (8 * s.val + 4) _ fun n => ?_
    have := deltaData_apply_v b s n ⟨8 * s.val + 4 + n.val, by
      have := s.isLt; have := n.isLt; omega⟩ rfl
    rw [← this, hy]
    rfl
  have hwu : wU b s = W5TAB.getD
      (16 * (if hm.testBit s.val then 1 else 0) + M >>> (8 * s.val) % 16) 0 := by
    have := fiber_weight_eq_table (fun a => b (uCell s a))
    rw [wU, this, ← hidx]
    congr 1
    rw [← hanib]
    rfl
  have hwv : wV b s = W5TAB.getD
      (16 * (if hm.testBit s.val then 1 else 0)
        + M >>> (8 * s.val + 4) % 16) 0 := by
    have := fiber_weight_eq_table (fun a => b (vCell s a))
    rw [wV, this]
    have hveps : (∑ j : Fin 5, b (vCell s j)) = hU b s := hEps s
    rw [hveps, ← hidx]
    congr 1
    rw [← hbnib]
    rfl
  rw [hwu, hwv]

/-! ## Span support and the outside flip -/

/-- Span elements stay inside the rep's byte positions. -/
lemma xorGensE_support (j : ℕ) (hj : subCertOK j = true) (e : ℕ) :
    ∀ p : ℕ, p < 120 → (xorGensE j e).testBit p = true → byteBit j p = true := by
  have hcert := hj
  rw [subCertOK, Bool.and_eq_true, Bool.and_eq_true] at hcert
  rw [genOK, List.all_eq_true] at hcert
  have hgen : ∀ i < nGen j, ∀ p < 120,
      (genMask j i).testBit p = true → byteBit j p = true := by
    intro i hi p hp hbit
    have := hcert.1.2 i (List.mem_range.mpr hi)
    simp only [Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true,
      Bool.not_eq_true'] at this
    rcases this.1.2 p (List.mem_range.mpr hp) with h | h
    · rw [hbit] at h
      exact absurd h (by simp)
    · exact h
  rw [xorGensE]
  have hfold : ∀ k, k ≤ nGen j → ∀ p < 120,
      (xorSelTab e.testBit (genMask j) k).testBit p = true →
        byteBit j p = true := by
    intro k
    induction k with
    | zero =>
      intro _ p _ hbit
      rw [show xorSelTab e.testBit (genMask j) 0 = 0 from rfl,
        Nat.zero_testBit] at hbit
      exact absurd hbit (by simp)
    | succ k ih =>
      intro hk p hp hbit
      have hstep : xorSelTab e.testBit (genMask j) (k + 1)
          = (if e.testBit k then genMask j k else 0)
            ^^^ xorSelTab e.testBit (genMask j) k := rfl
      rw [hstep, Nat.testBit_xor] at hbit
      rcases hx : (if e.testBit k then genMask j k else 0).testBit p with _ | _
      · rw [hx, Bool.false_xor] at hbit
        exact ih (by omega) p hp hbit
      · rcases hsel : e.testBit k with _ | _
        · rw [hsel] at hx
          simp only [Bool.false_eq_true, if_false, Nat.zero_testBit] at hx
        · rw [hsel, if_pos rfl] at hx
          exact hgen k (by omega) p hp hx
  exact hfold (nGen j) le_rfl

/-- A mask with four clear low bits has zero low nibble. -/
lemma nib16_zero (x : ℕ) (h : ∀ n, n < 4 → x.testBit n = false) :
    x % 16 = 0 := by
  rw [nib_arith x, h 0 (by omega), h 1 (by omega), h 2 (by omega),
    h 3 (by omega)]
  simp

/-- An outside ε-flip adds exactly 10 to the packed weight. -/
lemma wtOf_or_single (M hm os : ℕ) (hos15 : os < 15)
    (hnib : ∀ n, n < 8 → M.testBit (8 * os + n) = false)
    (hbit : hm.testBit os = false) :
    wtOf M (hm ||| 1 <<< os) = wtOf M hm + 10 := by
  have key : ∀ k, k ≤ 15 →
      wtSites M (hm ||| 1 <<< os) k
        = wtSites M hm k + (if os < k then 10 else 0) := by
    intro k
    induction k with
    | zero => simp [wtSites]
    | succ k ih =>
      intro hk
      have hbits : ∀ t, t ≠ os → (hm ||| 1 <<< os).testBit t = hm.testBit t := by
        intro t ht
        rw [Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow]
        simp [Ne.symm ht]
      show W5TAB.getD (16 * (if (hm ||| 1 <<< os).testBit k then 1 else 0)
          + M >>> (8 * k) % 16) 0
        + W5TAB.getD (16 * (if (hm ||| 1 <<< os).testBit k then 1 else 0)
            + M >>> (8 * k + 4) % 16) 0
        + wtSites M (hm ||| 1 <<< os) k = _
      by_cases hko : k = os
      · subst hko
        have hbitk : (hm ||| 1 <<< k).testBit k = true := by
          rw [Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow]
          simp
        have hm16a : M >>> (8 * k) % 16 = 0 := by
          refine nib16_zero _ fun n hn => ?_
          rw [Nat.testBit_shiftRight]
          exact hnib n (by omega)
        have hm16b : M >>> (8 * k + 4) % 16 = 0 := by
          refine nib16_zero _ fun n hn => ?_
          rw [Nat.testBit_shiftRight]
          have := hnib (4 + n) (by omega)
          rwa [show 8 * k + (4 + n) = 8 * k + 4 + n by omega] at this
        have hself : wtSites M (hm ||| 1 <<< k) k = wtSites M hm k := by
          have hall : ∀ k', k' ≤ k →
              wtSites M (hm ||| 1 <<< k) k' = wtSites M hm k' := by
            intro k'
            induction k' with
            | zero => intro _; rfl
            | succ k' ih' =>
              intro hk'
              show W5TAB.getD (16 * (if (hm ||| 1 <<< k).testBit k'
                  then 1 else 0) + _) 0 + _ + wtSites M (hm ||| 1 <<< k) k' = _
              rw [hbits k' (by omega), ih' (by omega)]
              rfl
          exact hall k le_rfl
        have hstep : wtSites M hm (k + 1)
            = W5TAB.getD (16 * (if hm.testBit k then 1 else 0)
                + M >>> (8 * k) % 16) 0
              + W5TAB.getD (16 * (if hm.testBit k then 1 else 0)
                  + M >>> (8 * k + 4) % 16) 0
              + wtSites M hm k := rfl
        rw [hstep, hbitk, hm16a, hm16b, hself, hbit]
        have hlt : k < k + 1 := by omega
        rw [if_pos hlt]
        have e5 : W5TAB.getD (16 * (if true = true then 1 else 0) + 0) 0
            = 5 := rfl
        have e0 : W5TAB.getD (16 * (if false = true then 1 else 0) + 0) 0
            = 0 := rfl
        rw [e5, e0]
        omega
      · have hstep : wtSites M hm (k + 1)
            = W5TAB.getD (16 * (if hm.testBit k then 1 else 0)
                + M >>> (8 * k) % 16) 0
              + W5TAB.getD (16 * (if hm.testBit k then 1 else 0)
                  + M >>> (8 * k + 4) % 16) 0
              + wtSites M hm k := rfl
        rw [hstep, hbits k hko, ih (by omega)]
        have hne : os ≠ k := fun h => hko h.symm
        by_cases hos : os < k
        · rw [if_pos hos, if_pos (by omega : os < k + 1)]
          omega
        · rw [if_neg hos, if_neg (by omega : ¬ os < k + 1)]
          omega
  have h1 := key 15 le_rfl
  rw [wtOf, wtOf, h1, if_pos hos15]

/-! ## Translation transport of the (ε, δ)-extraction -/

/-- The translation element realizing site shift `τ` (no fiber
rotation). -/
def gOfTau (τ : Fin 15) : G150 :=
  ((τ.val / 3 : ℕ), (5 * (τ.val % 3) : ℕ))

lemma uCell_translate : ∀ (s τ : Fin 15) (a : Fin 5),
    ((uCell s a).1 + gOfTau τ, (uCell s a).2) = uCell (siteAdd s τ) a := by
  decide

lemma vCell_translate : ∀ (s τ : Fin 15) (a : Fin 5),
    ((vCell s a).1 + gOfTau τ, (vCell s a).2) = vCell (siteAdd s τ) a := by
  decide

lemma dU_translate (b : G150 × Fin 2 → ZMod 2) (τ s : Fin 15) (n : Fin 4) :
    dU (translate1 (gOfTau τ) b) s n = dU b (siteAdd s τ) n := by
  show b ((uCell s ⟨n.val, by omega⟩).1 + gOfTau τ, (uCell s ⟨n.val, by omega⟩).2)
      + b ((uCell s 4).1 + gOfTau τ, (uCell s 4).2) = _
  rw [uCell_translate s τ ⟨n.val, by omega⟩, uCell_translate s τ 4]
  rfl

lemma dV_translate (b : G150 × Fin 2 → ZMod 2) (τ s : Fin 15) (n : Fin 4) :
    dV (translate1 (gOfTau τ) b) s n = dV b (siteAdd s τ) n := by
  show b ((vCell s ⟨n.val, by omega⟩).1 + gOfTau τ, (vCell s ⟨n.val, by omega⟩).2)
      + b ((vCell s 4).1 + gOfTau τ, (vCell s 4).2) = _
  rw [vCell_translate s τ ⟨n.val, by omega⟩, vCell_translate s τ 4]
  rfl

lemma hU_translate (b : G150 × Fin 2 → ZMod 2) (τ s : Fin 15) :
    hU (translate1 (gOfTau τ) b) s = hU b (siteAdd s τ) := by
  refine Finset.sum_congr rfl fun a _ => ?_
  show b ((uCell s a).1 + gOfTau τ, (uCell s a).2) = _
  rw [uCell_translate s τ a]

lemma siteActive_translate (b : G150 × Fin 2 → ZMod 2) (τ s : Fin 15) :
    siteActive (translate1 (gOfTau τ) b) s ↔ siteActive b (siteAdd s τ) := by
  unfold siteActive
  constructor
  · rintro (⟨n, hn⟩ | ⟨n, hn⟩)
    · exact Or.inl ⟨n, by rwa [dU_translate] at hn⟩
    · exact Or.inr ⟨n, by rwa [dV_translate] at hn⟩
  · rintro (⟨n, hn⟩ | ⟨n, hn⟩)
    · exact Or.inl ⟨n, by rwa [dU_translate]⟩
    · exact Or.inr ⟨n, by rwa [dV_translate]⟩

/-- `translate1` composition. -/
lemma translate1_comp (c c' : G150) (v : G150 × Fin 2 → ZMod 2) :
    translate1 c (translate1 c' v) = translate1 (c' + c) v := by
  funext p
  show v ((p.1 + c) + c', p.2) = v (p.1 + (c' + c), p.2)
  rw [add_assoc, add_comm c c']

/-- Translation preserves chain weight. -/
lemma chainWeight_translate1 (c : G150) (b : G150 × Fin 2 → ZMod 2) :
    (Finset.univ.filter fun j : G150 × Fin 2 =>
        translate1 c b j ≠ 0).card
      = (Finset.univ.filter fun j : G150 × Fin 2 => b j ≠ 0).card := by
  refine Finset.card_bij' (fun p _ => (p.1 + c, p.2))
    (fun p _ => (p.1 - c, p.2)) ?_ ?_ ?_ ?_
  · intro p hp
    rw [Finset.mem_filter] at hp ⊢
    exact ⟨Finset.mem_univ _, hp.2⟩
  · intro p hp
    rw [Finset.mem_filter] at hp ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    show b ((p.1 - c) + c, p.2) ≠ 0
    rw [sub_add_cancel]
    simpa using hp.2
  · intro p _
    show (p.1 + c - c, p.2) = p
    rw [add_sub_cancel_right]
  · intro p _
    show (p.1 - c + c, p.2) = p
    rw [sub_add_cancel]

end Z5Z15F2A6
end BB
end Homological
end Stabilizer
end Quantum
