import QEC.Stabilizer.Framework.Homological.Certificate.SparsePopBound
import Mathlib.Data.Finset.Prod
import Init.Data.Nat.Power2

namespace Quantum.Stabilizer.Homological.F2Mask

/-- The finite support of a packed bitset. -/
def maskSet (bits x : Nat) : Finset Nat := (Finset.range bits).filter (fun i => x.testBit i)

/-- The bitset support has the established finite bit count. -/
theorem maskSet_card (bits x : Nat) : (maskSet bits x).card = bitCount bits x := by
  simpa [maskSet] using (bitCount_eq_card bits x).symm

/-- Intersecting a bitset with a plane selects its true branch. -/
theorem maskSet_and (bits a p : Nat) :
    maskSet bits (a &&& p) = (maskSet bits a).filter (fun i => p.testBit i) := by
  ext i
  simp [maskSet, Nat.testBit_and, and_assoc]

/-- Removing a plane selects the complementary branch. -/
theorem maskSet_without (bits a p : Nat) :
    maskSet bits (a ^^^ (a &&& p)) = (maskSet bits a).filter (fun i => !(p.testBit i)) := by
  ext i
  simp only [maskSet, Finset.mem_filter, Finset.mem_range, Nat.testBit_xor, Nat.testBit_and]
  cases a.testBit i <;> cases p.testBit i <;> simp

/-- The recursive relation checked by a binary collision trie. -/
def trieRel : List (Nat × Nat) → Nat → Nat → Nat → Prop
  | [], _, _, _ => True
  | (p,q)::ps, t, i, j =>
      (p.testBit i = (q.testBit j ^^ t.testBit 0)) ∧ trieRel ps (t >>> 1) i j

instance trieRel_decidable (ps : List (Nat × Nat)) (t i j : Nat) : Decidable (trieRel ps t i j) := by
  induction ps generalizing t with
  | nil => exact isTrue trivial
  | cons p ps ih => exact instDecidableAnd

/-- The colliding ordered pairs represented at one trie node. -/
def collisions (bits : Nat) (ps : List (Nat × Nat)) (t a b : Nat) : Finset (Nat × Nat) :=
  ((maskSet bits a).product (maskSet bits b)).filter (fun ij => trieRel ps t ij.1 ij.2)

/-- Splitting a collision node partitions it into its two matching branches. -/
theorem collisions_split (bits p q : Nat) (ps : List (Nat × Nat)) (t a b : Nat) :
    let a1 := a &&& p
    let raw := b &&& q
    let b1 := if t.testBit 0 then b ^^^ raw else raw
    collisions bits ((p,q)::ps) t a b =
      collisions bits ps (t >>> 1) (a ^^^ a1) (b ^^^ b1) ∪
      collisions bits ps (t >>> 1) a1 b1 := by
  dsimp only
  ext ij
  rcases ij with ⟨i,j⟩
  simp only [collisions, Finset.mem_filter, Finset.mem_product, Finset.mem_union,
    maskSet, Finset.mem_range, Nat.testBit_xor, Nat.testBit_and, trieRel]
  cases ha : a.testBit i <;> cases hb : b.testBit j <;> cases hp : p.testBit i <;>
    cases hq : q.testBit j <;> cases ht : t.testBit 0 <;> simp_all [maskSet, Finset.mem_product]

/-- The two branches of a collision split are disjoint. -/
theorem collisions_split_disjoint (bits p : Nat) (ps : List (Nat × Nat)) (t a b0 b1 : Nat) :
    Disjoint (collisions bits ps t (a ^^^ (a &&& p)) b0)
      (collisions bits ps t (a &&& p) b1) := by
  rw [Finset.disjoint_left]
  rintro ⟨i,j⟩ h0 h1
  have hz := (Finset.mem_product.mp (Finset.mem_filter.mp h0).1).1
  have ho := (Finset.mem_product.mp (Finset.mem_filter.mp h1).1).1
  rw [maskSet_without] at hz
  rw [maskSet_and] at ho
  have hz' := (Finset.mem_filter.mp hz).2
  have ho' := (Finset.mem_filter.mp ho).2
  simp_all

/-- A leaf contains at most the product of the sparse support bounds. -/
theorem collisions_leaf_bound (bits fuel t a b : Nat) :
    (collisions bits [] t a b).card ≤ sparsePopBound bits fuel a * sparsePopBound bits fuel b := by
  simp only [collisions, trieRel, Finset.filter_true, Finset.card_product, maskSet_card]
  change ((maskSet bits a) ×ˢ (maskSet bits b)).card ≤ _
  rw [Finset.card_product, maskSet_card, maskSet_card]
  exact Nat.mul_le_mul (bitCount_le_sparsePopBound _ _ _) (bitCount_le_sparsePopBound _ _ _)

/-- A zero bitset leaves no colliding pairs on either side. -/
theorem collisions_zero (bits : Nat) (ps : List (Nat × Nat)) (t a b : Nat)
    (h : a = 0 ∨ b = 0) : collisions bits ps t a b = ∅ := by
  rcases h with rfl | rfl <;> simp [collisions, maskSet]

/-- A safe upper bound on the number of pairs in a bitset collision trie. -/
def trieBound (bits fuel : Nat) : List (Nat × Nat) → Nat → Nat → Nat → Nat
  | [], t, a, b => sparsePopBound bits fuel a * sparsePopBound bits fuel b
  | (p,q)::ps, t, a, b =>
      if Nat.beq a 0 || Nat.beq b 0 then 0 else
      let a1 := a &&& p
      let raw := b &&& q
      let b1 := if t.testBit 0 then b ^^^ raw else raw
      trieBound bits fuel ps (t >>> 1) (a ^^^ a1) (b ^^^ b1) +
        trieBound bits fuel ps (t >>> 1) a1 b1

/-- The recursive collision bound is valid for every input and every fuel value. -/
theorem collisions_card_le_trieBound (bits fuel : Nat) (ps : List (Nat × Nat)) :
    ∀ t a b, (collisions bits ps t a b).card ≤ trieBound bits fuel ps t a b := by
  induction ps with
  | nil => exact collisions_leaf_bound bits fuel
  | cons pq ps ih =>
    rcases pq with ⟨p,q⟩
    intro t a b
    by_cases hz : a = 0 ∨ b = 0
    · rw [collisions_zero _ _ _ _ _ hz]
      exact Nat.zero_le _
    · have ha : a ≠ 0 := fun h => hz (Or.inl h)
      have hb : b ≠ 0 := fun h => hz (Or.inr h)
      rw [collisions_split, Finset.card_union_of_disjoint (collisions_split_disjoint _ _ _ _ _ _ _)]
      have ha0 : Nat.beq a 0 = false := by
        cases h : Nat.beq a 0
        · rfl
        · exact False.elim (ha (Nat.beq_eq.mp h))
      have hb0 : Nat.beq b 0 = false := by
        cases h : Nat.beq b 0
        · rfl
        · exact False.elim (hb (Nat.beq_eq.mp h))
      have hzbool : (Nat.beq a 0 || Nat.beq b 0) = false := by rw [ha0,hb0]; rfl
      simp only [trieBound, hzbool, Bool.false_eq_true, if_false]
      exact Nat.add_le_add (ih _ _ _) (ih _ _ _)

#print axioms collisions_card_le_trieBound
end Quantum.Stabilizer.Homological.F2Mask

namespace Quantum.Stabilizer.Homological.F2Mask
/-- A singleton bitset has at most one ordered collision with itself. -/
theorem collisions_powerTwo_bound (bits : Nat) (ps : List (Nat × Nat)) (t a : Nat)
    (ha : a ≠ 0) (hp : a &&& (a-1) = 0) :
    (collisions bits ps t a a).card ≤ 1 := by
  obtain ⟨q,hq⟩ := (Nat.and_sub_one_eq_zero_iff_isPowerOfTwo ha).1 hp
  have hsub : maskSet bits a ⊆ {q} := by
    intro i hi
    have ht := (Finset.mem_filter.mp hi).2
    rw [hq, Nat.testBit_two_pow] at ht
    have he : q = i := of_decide_eq_true ht
    simpa [he]
  have hc : (maskSet bits a).card ≤ 1 := by simpa using Finset.card_le_card hsub
  have hle := Finset.card_filter_le ((maskSet bits a).product (maskSet bits a))
    (fun ij : Nat × Nat => trieRel ps t ij.1 ij.2)
  change (collisions bits ps t a a).card ≤ _ at hle
  change (collisions bits ps t a a).card ≤ ((maskSet bits a) ×ˢ (maskSet bits a)).card at hle
  rw [Finset.card_product] at hle
  exact le_trans hle (by simpa using Nat.mul_le_mul hc hc)

/-- A trie bound specialized to equal sets and equal labels can stop at singleton nodes. -/
def selfTrieBound (bits fuel : Nat) : List Nat → Nat → Nat
  | ps, a => if Nat.beq a 0 then 0 else if Nat.beq (Nat.land a (Nat.sub a 1)) 0 then 1 else
    match ps with
    | [] => let n := sparsePopBound bits fuel a; n*n
    | p::rest =>
      let a1 := a &&& p
      selfTrieBound bits fuel rest (a ^^^ a1) + selfTrieBound bits fuel rest a1

/-- The specialized trie is a sound upper bound on self collisions. -/
theorem collisions_card_le_selfTrieBound (bits fuel : Nat) (ps : List Nat) :
    ∀ a, (collisions bits (ps.map (fun p => (p,p))) 0 a a).card ≤ selfTrieBound bits fuel ps a := by
  induction ps with
  | nil =>
    intro a
    by_cases ha : a = 0
    · subst a
      simp [collisions, maskSet, selfTrieBound]
    · by_cases hp : a &&& (a-1) = 0
      · have h := collisions_powerTwo_bound bits [] 0 a ha hp
        simpa [selfTrieBound, ha, hp] using h
      · simpa [selfTrieBound, ha, hp] using collisions_leaf_bound bits fuel 0 a a
  | cons p ps ih =>
    intro a
    by_cases ha : a = 0
    · subst a
      simp [collisions, maskSet, selfTrieBound]
    · by_cases hp : a &&& (a-1) = 0
      · have h := collisions_powerTwo_bound bits ((p::ps).map (fun q => (q,q))) 0 a ha hp
        simpa [selfTrieBound, ha, hp] using h
      · rw [List.map_cons, collisions_split,
          Finset.card_union_of_disjoint (collisions_split_disjoint _ _ _ _ _ _ _)]
        simp only [Nat.zero_testBit, Bool.false_eq_true, if_false, Nat.zero_shiftRight]
        have h := Nat.add_le_add (ih (a ^^^ (a &&& p))) (ih (a &&& p))
        simpa [selfTrieBound, ha, hp] using h

#print axioms collisions_card_le_selfTrieBound
end Quantum.Stabilizer.Homological.F2Mask
