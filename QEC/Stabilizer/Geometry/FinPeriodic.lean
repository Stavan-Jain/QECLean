import Mathlib.Tactic

/-!
# Cyclic successor and predecessor on `Fin L`

`next L i` and `prev L i` are `i + 1` and `i - 1` modulo `L`. They are mutually
inverse (`next_prev`, `prev_next`) and, for `2 ≤ L`, have no fixed points
(`next_ne_self`, `prev_ne_self`). Stating facts about periodic lattices through
these lemmas avoids reasoning about `%` directly.
-/

namespace Quantum
namespace Stabilizer
namespace Lattice

/-- A lattice size `2 ≤ L` is positive. -/
instance factPosOfTwoLE (L : ℕ) [Fact (2 ≤ L)] : Fact (0 < L) :=
  ⟨Nat.lt_of_lt_of_le Nat.zero_lt_two Fact.out⟩

/-- The lattice size `2` is positive. -/
instance factPosTwo : Fact (0 < 2) := ⟨by decide⟩

/-- The successor of `i` modulo `L`. -/
def next (L : ℕ) [Fact (0 < L)] (i : Fin L) : Fin L :=
  ⟨(i.val + 1) % L, Nat.mod_lt _ Fact.out⟩

/-- The predecessor of `i` modulo `L`. -/
def prev (L : ℕ) [Fact (0 < L)] (i : Fin L) : Fin L :=
  ⟨(i.val + (L - 1)) % L, Nat.mod_lt _ Fact.out⟩

@[simp] lemma next_val (L : ℕ) [Fact (0 < L)] (i : Fin L) :
    (next L i).val = (i.val + 1) % L := rfl

@[simp] lemma prev_val (L : ℕ) [Fact (0 < L)] (i : Fin L) :
    (prev L i).val = (i.val + (L - 1)) % L := rfl

@[simp] lemma next_prev (L : ℕ) [Fact (0 < L)] (i : Fin L) :
    next L (prev L i) = i := by
  have hL : 0 < L := Fact.out
  apply Fin.ext
  rw [next_val, prev_val, Nat.mod_add_mod, show i.val + (L - 1) + 1 = i.val + L by omega,
    Nat.add_mod_right, Nat.mod_eq_of_lt i.isLt]

@[simp] lemma prev_next (L : ℕ) [Fact (0 < L)] (i : Fin L) :
    prev L (next L i) = i := by
  have hL : 0 < L := Fact.out
  apply Fin.ext
  rw [prev_val, next_val, Nat.mod_add_mod, show i.val + 1 + (L - 1) = i.val + L by omega,
    Nat.add_mod_right, Nat.mod_eq_of_lt i.isLt]

@[simp] lemma prev_eq_iff_eq_next (L : ℕ) [Fact (0 < L)] (a b : Fin L) :
    prev L a = b ↔ a = next L b :=
  ⟨fun h => by rw [← h, next_prev], fun h => by rw [h, prev_next]⟩

@[simp] lemma eq_prev_iff_next_eq (L : ℕ) [Fact (0 < L)] (a b : Fin L) :
    a = prev L b ↔ next L a = b :=
  ⟨fun h => by rw [h, next_prev], fun h => by rw [← h, prev_next]⟩

/-- For `2 ≤ L`, `next` has no fixed points. -/
lemma next_ne_self (L : ℕ) [Fact (2 ≤ L)] (i : Fin L) : next L i ≠ i := by
  intro h
  have h2 : 2 ≤ L := Fact.out
  have hi := i.isLt
  have hval : (i.val + 1) % L = i.val := congrArg Fin.val h
  by_cases htop : i.val + 1 = L
  · rw [htop, Nat.mod_self] at hval
    omega
  · rw [Nat.mod_eq_of_lt (by omega)] at hval
    omega

/-- For `2 ≤ L`, `prev` has no fixed points. -/
lemma prev_ne_self (L : ℕ) [Fact (2 ≤ L)] (i : Fin L) : prev L i ≠ i :=
  fun h => next_ne_self L i (by simpa using (congrArg (next L) h).symm)

end Lattice
end Stabilizer
end Quantum
