/-
# A22: batched certificate checks and the translate-table interface

The `native_decide` obligations of the light classification outside the
sweep itself:

* `subCert_all` — all 429 per-rep pivot/generator/coverage certificates;
* `shift_all` — the `SHIFT_ANS` table: every ≤ 7-site mask shifts into
  its designated orbit rep;
* `siteList_length` — each rep has exactly 7 sites;
* `tt_decode` — every translate-table row unpacks to
  `translate1 c (repChain i)` for its decoded `(i, c)`;
* `memberTT` — fuel-bounded binary search over the sorted table, with
  the one-sided soundness lemma the sweep consumes (a positive result
  exhibits a row; completeness of the search is *not* needed — a missed
  row would only make the sweep check fail at build time).
-/

import QEC.Stabilizer.Codes.BivariateBicycle.Z5Z15F2A6.LightPeel
import QEC.Stabilizer.Codes.BivariateBicycle.Z5Z15F2A6.LightTTData

namespace Quantum
namespace Stabilizer
namespace Homological
namespace BB
namespace Z5Z15F2A6

set_option maxRecDepth 4096

/-! ## Site translation and popcount -/

/-- Site addition on `Fin 15` (`s = 3·i + b`, componentwise mod 5/mod 3). -/
def siteAdd (s t : Fin 15) : Fin 15 :=
  ⟨3 * ((s.val / 3 + t.val / 3) % 5) + (s.val % 3 + t.val % 3) % 3, by omega⟩

/-- Bit count below `k`. -/
def countBits (m : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => (if m.testBit k then 1 else 0) + countBits m k

/-! ## Batched certificate natives -/

/-- All 429 per-rep certificates are valid. -/
theorem subCert_all : ∀ j : Fin 429, subCertOK j.val = true := by
  native_decide

/-- The shift table: every ≤ 7-site mask shifts into its designated
rep — `τ = ans % 15`, `j = ans / 15 < 429`, and every site of the mask
lands inside `REP7 j` after the shift. -/
theorem shift_all : ∀ m : Fin 32768, countBits m.val 15 ≤ 7 →
    shiftAnsGet m.val / 15 < 429 ∧
    ∀ s : Fin 15,
      m.val.testBit (siteAdd s
        ⟨shiftAnsGet m.val % 15, Nat.mod_lt _ (by norm_num)⟩).val = true →
      (REP7.getD (shiftAnsGet m.val / 15) 0).testBit s.val = true := by
  native_decide

/-! ## The translate table -/

/-- Decoded class index of a table row. -/
def ttCls (r : ℕ) : Fin 113 :=
  ⟨ttIGet r % 113, Nat.mod_lt _ (by norm_num)⟩

/-- Decoded translate element of a table row. -/
def ttTrans (r : ℕ) : G150 :=
  ((ttCGet r / 15 : ℕ), (ttCGet r % 15 : ℕ))

/-- Every table row unpacks to the tabulated translate of its class rep. -/
theorem tt_decode : ∀ r : Fin 8475, ∀ p : G150 × Fin 2,
    maskFun150 (ttGet r.val) p
      = translate1 (ttTrans r.val) (repChain (ttCls r.val)) p := by
  native_decide

/-- Fuel-bounded binary search on the sorted table. -/
def ttSearchAux (key : ℕ) : ℕ → ℕ → ℕ → Option ℕ
  | _, _, 0 => none
  | lo, hi, fuel + 1 =>
    if lo < hi then
      let mid := (lo + hi) / 2
      let v := ttGet mid
      if v == key then some mid
      else if v < key then ttSearchAux key (mid + 1) hi fuel
      else ttSearchAux key lo mid fuel
    else none

/-- Table membership by binary search. -/
def memberTT (key : ℕ) : Bool :=
  match ttSearchAux key 0 8475 20 with
  | some r => decide (r < 8475) && (ttGet r == key)
  | none => false

/-- A positive search exhibits a matching row. -/
lemma memberTT_sound {key : ℕ} (h : memberTT key = true) :
    ∃ r : ℕ, r < 8475 ∧ ttGet r = key := by
  unfold memberTT at h
  rcases hs : ttSearchAux key 0 8475 20 with _ | r
  · rw [hs] at h
    exact absurd h (by simp)
  · rw [hs, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    exact ⟨r, h.1, h.2⟩

/-- Membership yields the tabulated translate form. -/
lemma memberTT_translate {key : ℕ} (h : memberTT key = true) :
    ∃ i : Fin 113, ∃ c : G150,
      maskFun150 key = translate1 c (repChain i) := by
  obtain ⟨r, hr, hkey⟩ := memberTT_sound h
  refine ⟨ttCls r, ttTrans r, ?_⟩
  funext p
  rw [← hkey]
  exact tt_decode ⟨r, hr⟩ p

end Z5Z15F2A6
end BB
end Homological
end Stabilizer
end Quantum
