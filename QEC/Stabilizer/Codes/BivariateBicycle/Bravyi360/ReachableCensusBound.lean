import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.ReachableBasisChecks
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.ConcreteCensusBounds
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.ConcretePermutations
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.ReachabilityData

noncomputable section

namespace Quantum.Stabilizer.Homological.F2Mask

/-- Enlarging a generator list preserves its XOR-span. -/
theorem XorSpan.mono {small large : List Nat} {word : Nat}
    (h : XorSpan small word) (hsub : ∀ g ∈ small, g ∈ large) : XorSpan large word := by
  induction h with
  | zero => exact .zero
  | step hg _ ih => exact .step (hsub _ hg) ih

/-- One additional binary generator divides its span into at most two cosets. -/
theorem XorSpan.cons_cases {g word : Nat} {generators : List Nat}
    (h : XorSpan (g :: generators) word) :
    XorSpan generators word ∨ XorSpan generators (word ^^^ g) := by
  induction h with
  | zero => exact Or.inl .zero
  | @step a word ha _ ih =>
    rcases List.mem_cons.mp ha with rfl | ha
    · rcases ih with hi | hi
      · right
        simpa [Nat.xor_assoc, Nat.xor_comm, Nat.xor_left_comm] using hi
      · left
        simpa [Nat.xor_comm] using hi
    · rcases ih with hi | hi
      · exact Or.inl (.step ha hi)
      · right
        simpa only [Nat.xor_assoc] using (XorSpan.step ha hi)

end Quantum.Stabilizer.Homological.F2Mask

namespace Quantum.Stabilizer.Homological.BB.Bravyi360
open F2Mask F2Mask.Trellis.Bravyi90

/--
The two additional reachable directions together with the 41 stabilizer
directions cover the frame.
-/
theorem reachable_generator_members : ∀ g ∈ ReachabilityData.reachableGenerators.map Prod.snd,
    g ∈ 1065874952622347 :: 1518104189649061 :: reachableStableChecks.map Prod.fst := by
  decide +kernel

/--
Every reachable mask belongs to one of the four affine classes counted by the
trellis.
-/
theorem reachable_four_cosets {word : Nat}
    (h : XorSpan (ReachabilityData.reachableGenerators.map Prod.snd) word) :
    XorSpan stabGenerators (reconX stabPermutation word) ∨
    XorSpan stabGenerators (reconX stabPermutation word ^^^ W121Offset) ∨
    XorSpan stabGenerators (reconX stabPermutation word ^^^ W151Offset) ∨
    XorSpan stabGenerators (reconX stabPermutation word ^^^ W238Offset) := by
  have hh := (h.mono reachable_generator_members).cons_cases
  rcases hh with h | h
  · rcases h.cons_cases with h | h
    · exact Or.inl (reachable_stable_span h)
    · have hh := reachable_stable_span h
      rw [reconX_xor, reachable_offset_2] at hh
      exact Or.inr (Or.inr (Or.inl hh))
  · rcases h.cons_cases with h | h
    · have hh := reachable_stable_span h
      rw [reconX_xor, reachable_offset_1] at hh
      exact Or.inr (Or.inl hh)
    · have hx : 1065874952622347 ^^^ 1518104189649061 = 1880016524267950 := by decide
      rw [Nat.xor_assoc, hx] at h
      have hh := reachable_stable_span h
      rw [reconX_xor, reachable_offset_3] at hh
      exact Or.inr (Or.inr (Or.inr hh))

/--
Every finite family of reachable masks of weight at most 22 has the counted
size bound.
-/
theorem reachable_light_card_le (target : Finset Nat)
    (hspan : ∀ word ∈ target, XorSpan (ReachabilityData.reachableGenerators.map Prod.snd) word)
    (hlight : ∀ word ∈ target, bitCount 90 word ≤ 22) :
    target.card ≤ 12329961 := by
  classical
  have hfit : ∀ word ∈ target, word < 2^90 := by
    intro word hw
    apply (hspan word hw).lt
    intro g hg
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hg
    exact ReachabilityData.reachableGenerators_bounded p hp
  let t := target.image (reconX stabPermutation)
  have hc : t.card = target.card := Finset.card_image_iff.mpr (by
    intro a ha b hb he
    exact stab_permutation_injective (hfit a ha) (hfit b hb) he)
  have ht : ∀ word ∈ t, bitCount 90 word ≤ 22 := by
    intro word hmem
    obtain ⟨w,hw0,rfl⟩ := Finset.mem_image.mp hmem
    rw [stab_permutation_weight (hfit w hw0)]
    exact hlight w hw0
  let t0 := t.filter (XorSpan stabGenerators)
  let t1 := t.filter (fun w => XorSpan stabGenerators (w ^^^ W121Offset))
  let t2 := t.filter (fun w => XorSpan stabGenerators (w ^^^ W151Offset))
  let t3 := t.filter (fun w => XorSpan stabGenerators (w ^^^ W238Offset))
  have h0 := stab_card_le t0 (fun _ h => (Finset.mem_filter.mp h).2)
    (fun _ h => ht _ (Finset.mem_filter.mp h).1)
  have h1 := W121_card_le t1 (fun _ h => (Finset.mem_filter.mp h).2)
    (fun _ h => ht _ (Finset.mem_filter.mp h).1)
  have h2 := W151_card_le t2 (fun _ h => (Finset.mem_filter.mp h).2)
    (fun _ h => ht _ (Finset.mem_filter.mp h).1)
  have h3 := W238_card_le t3 (fun _ h => (Finset.mem_filter.mp h).2)
    (fun _ h => ht _ (Finset.mem_filter.mp h).1)
  have hs : t ⊆ t0 ∪ t1 ∪ t2 ∪ t3 := by
    intro word hw
    obtain ⟨w,hw',he⟩ := Finset.mem_image.mp hw
    have hd := reachable_four_cosets (hspan w hw')
    rw [he] at hd
    simpa only [t0,t1,t2,t3,Finset.mem_union,Finset.mem_filter,and_true,
      hw,true_and,or_assoc] using hd
  have hcard := Finset.card_le_card hs
  have ha := Finset.card_union_le (t0 ∪ t1 ∪ t2) t3
  have hb := Finset.card_union_le (t0 ∪ t1) t2
  have hd := Finset.card_union_le t0 t1
  omega

end Quantum.Stabilizer.Homological.BB.Bravyi360
