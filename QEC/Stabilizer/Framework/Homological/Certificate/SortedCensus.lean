import Mathlib.Data.List.Sort
import Mathlib.Data.Finset.Card

namespace Quantum.Stabilizer.Homological

/-- A linear-size certificate simultaneously checks strict keys, entries, and size. -/
def checkOrdered (valid : ℕ → Bool) : ℕ → ℕ → List ℕ → Bool
  | n, _, [] => Nat.beq n 0
  | 0, _, _ :: _ => false
  | n + 1, prev, key :: rest =>
      Nat.blt prev (Nat.add key 1) && valid key &&
        checkOrdered valid n (Nat.add key 1) rest

/-- Every accepted ordered certificate has its stated size and strictly increasing keys. -/
theorem checkOrdered_sound (valid : ℕ → Bool) (keys : List ℕ) :
    ∀ n prev, checkOrdered valid n prev keys = true →
      keys.length = n ∧ keys.Pairwise (· < ·) ∧
        keys.all valid = true ∧ ∀ k ∈ keys, prev < k + 1 := by
  induction keys with
  | nil =>
    intro n prev h
    have hn : n = 0 := by simpa only [checkOrdered, Nat.beq_eq] using h
    subst n
    simp
  | cons k ks ih =>
    intro n prev h
    cases n with
    | zero => simp [checkOrdered] at h
    | succ n =>
      simp only [checkOrdered, Bool.and_eq_true, Nat.blt_eq, decide_eq_true_eq] at h
      obtain ⟨⟨hk, hv⟩, ht⟩ := h
      change prev < k + 1 at hk
      obtain ⟨hlen, hsort, hall, hlower⟩ := ih n (k + 1) ht
      refine ⟨by simp [hlen], ?_, by simp [hv, hall], ?_⟩
      · rw [List.pairwise_cons]
        exact ⟨fun x hx => by have := hlower x hx; omega, hsort⟩
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hk
        · have := hlower x hx; omega

/-- An ordered certificate may carry payload bits outside its ordering key. -/
def checkOrderedBy (key : ℕ → ℕ) (valid : ℕ → Bool) : ℕ → ℕ → List ℕ → Bool
  | n, _, [] => Nat.beq n 0
  | 0, _, _ :: _ => false
  | n + 1, prev, entry :: rest =>
      Nat.blt prev (Nat.add (key entry) 1) && valid entry &&
        checkOrderedBy key valid n (Nat.add (key entry) 1) rest

/-- Accepted payload certificates have strictly increasing keys and valid entries. -/
theorem checkOrderedBy_sound (key : ℕ → ℕ) (valid : ℕ → Bool) (entries : List ℕ) :
    ∀ n prev, checkOrderedBy key valid n prev entries = true →
      entries.length = n ∧ (entries.map key).Pairwise (· < ·) ∧
        entries.all valid = true ∧ ∀ e ∈ entries, prev < key e + 1 := by
  induction entries with
  | nil =>
    intro n prev h
    have hn : n = 0 := by simpa only [checkOrderedBy, Nat.beq_eq] using h
    subst n
    simp
  | cons e es ih =>
    intro n prev h
    cases n with
    | zero => simp [checkOrderedBy] at h
    | succ n =>
      simp only [checkOrderedBy, Bool.and_eq_true, Nat.blt_eq, decide_eq_true_eq] at h
      obtain ⟨⟨hk, hv⟩, ht⟩ := h
      change prev < key e + 1 at hk
      obtain ⟨hlen, hsort, hall, hlower⟩ := ih n (key e + 1) ht
      refine ⟨by simp [hlen], ?_, by simp [hv, hall], ?_⟩
      · simp only [List.map_cons, List.pairwise_cons]
        refine ⟨?_, hsort⟩
        intro x hx
        obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
        have := hlower y hy
        omega
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hk
        · have := hlower x hx; omega

/-- A strictly ordered list of valid, uniquely decoded entries with full cardinality
covers its target. The decoder need only be injective on the certified entries. -/
theorem ordered_census_complete {α : Type*} [DecidableEq α]
    (target : Finset α) (keys : List ℕ) (decode : ℕ → α)
    (hsort : keys.Pairwise (· < ·))
    (hvalid : ∀ k ∈ keys, decode k ∈ target)
    (hinj : ∀ a ∈ keys, ∀ b ∈ keys, decode a = decode b → a = b)
    (hcard : target.card ≤ keys.length) :
    ∀ x ∈ target, ∃ k ∈ keys, decode k = x := by
  have hnd : keys.Nodup := hsort.imp fun h => ne_of_lt h
  have hmap : (keys.map decode).Nodup := hnd.map_on hinj
  have hsub : (keys.map decode).toFinset ⊆ target := by
    intro x hx
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hx)
    exact hvalid k hk
  have heq : (keys.map decode).toFinset = target := by
    apply Finset.eq_of_subset_of_card_le hsub
    simpa [List.toFinset_card_of_nodup hmap] using hcard
  intro x hx
  rw [← heq] at hx
  simpa using hx

#print axioms checkOrdered_sound
#print axioms ordered_census_complete

end Quantum.Stabilizer.Homological
