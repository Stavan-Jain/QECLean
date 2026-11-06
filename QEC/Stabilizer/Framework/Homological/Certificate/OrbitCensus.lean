import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace Quantum.Stabilizer.Homological.OrbitCensus

variable {G α : Type*} [Group G] [Fintype G] [LinearOrder α] [MulAction G α]

/-- The finite orbit of a point under a finite group action. -/
def orbit (a : α) : Finset α := Finset.univ.image (fun g : G => g • a)

/-- Membership in the finite orbit is witnessed by a group element. -/
theorem mem_orbit {a b : α} : b ∈ orbit (G := G) a ↔ ∃ g : G, g • a = b := by
  simp [orbit]

/-- Every point is in its own finite orbit. -/
theorem self_mem_orbit (a : α) : a ∈ orbit (G := G) a :=
  mem_orbit.mpr ⟨1, one_smul G a⟩

/-- A canonical point is the least point in its orbit. -/
def IsCanonical (a : α) : Prop := ∀ g : G, a ≤ g • a

/-- Two canonical points in the same orbit are equal. -/
theorem canonical_eq_of_mem {a b : α} (ha : IsCanonical (G := G) a)
    (hb : IsCanonical (G := G) b) (h : b ∈ orbit (G := G) a) : a = b := by
  obtain ⟨g, rfl⟩ := mem_orbit.mp h
  apply le_antisymm (ha g)
  simpa only [inv_smul_smul] using hb g⁻¹

/-- Distinct canonical points have disjoint orbits. -/
theorem canonical_orbits_disjoint {a b : α} (ha : IsCanonical (G := G) a)
    (hb : IsCanonical (G := G) b) (hab : a ≠ b) :
    Disjoint (orbit (G := G) a) (orbit (G := G) b) := by
  apply Finset.disjoint_left.mpr
  intro c hca hcb
  obtain ⟨g, hg⟩ := mem_orbit.mp hca
  obtain ⟨h, hh⟩ := mem_orbit.mp hcb
  apply hab
  apply canonical_eq_of_mem ha hb
  apply mem_orbit.mpr
  refine ⟨h⁻¹ * g, ?_⟩
  rw [mul_smul, hg, ← hh, inv_smul_smul]

/-- Canonical representatives whose orbit sizes exhaust a finite invariant set form a
complete census of that set. -/
theorem census_complete (representatives target : Finset α)
    (hcanonical : ∀ a ∈ representatives, IsCanonical (G := G) a)
    (hinside : ∀ a ∈ representatives, a ∈ target)
    (hclosed : ∀ g : G, ∀ a ∈ target, g • a ∈ target)
    (hcount : target.card ≤ ∑ a ∈ representatives, (orbit (G := G) a).card) :
    representatives.biUnion (orbit (G := G)) = target := by
  apply Finset.eq_of_subset_of_card_le
  · intro b hb
    obtain ⟨a, ha, hba⟩ := Finset.mem_biUnion.mp hb
    obtain ⟨g, rfl⟩ := mem_orbit.mp hba
    exact hclosed g a (hinside a ha)
  · rw [Finset.card_biUnion]
    · exact hcount
    · intro a ha b hb hab
      exact canonical_orbits_disjoint (hcanonical a ha) (hcanonical b hb) hab

/-- A complete canonical census supplies a representative and translation for each
member of the target set. -/
theorem exists_representative (representatives target : Finset α)
    (hcanonical : ∀ a ∈ representatives, IsCanonical (G := G) a)
    (hinside : ∀ a ∈ representatives, a ∈ target)
    (hclosed : ∀ g : G, ∀ a ∈ target, g • a ∈ target)
    (hcount : target.card ≤ ∑ a ∈ representatives, (orbit (G := G) a).card)
    {b : α} (hb : b ∈ target) :
    ∃ a ∈ representatives, ∃ g : G, g • a = b := by
  rw [← census_complete representatives target hcanonical hinside hclosed hcount] at hb
  obtain ⟨a, ha, hba⟩ := Finset.mem_biUnion.mp hb
  exact ⟨a, ha, mem_orbit.mp hba⟩

/-- The fixed group elements of a point, as a finite set. -/
def fixed (a : α) : Finset G := Finset.univ.filter (fun g => g • a = a)

/-- A checked fixed-point count determines the finite orbit size. -/
theorem orbit_card_mul_fixed_card (a : α) :
    (orbit (G := G) a).card * (fixed (G := G) a).card = Fintype.card G := by
  classical
  letI : Fintype (MulAction.orbit G a) := (Set.finite_range (fun g : G => g • a)).fintype
  letI : Fintype (MulAction.stabilizer G a) := Fintype.ofFinite _
  have ho : (orbit (G := G) a).card = Fintype.card (MulAction.orbit G a) := by
    have he : (↑(orbit (G := G) a) : Set α) = MulAction.orbit G a := by
      ext b
      simp only [Finset.mem_coe, mem_orbit, MulAction.mem_orbit_iff]
    have hc := Fintype.card_congr (Equiv.setCongr he)
    change Fintype.card (orbit (G := G) a) = Fintype.card (MulAction.orbit G a) at hc
    simpa only [Fintype.card_coe] using hc
  have hf : (fixed (G := G) a).card = Fintype.card (MulAction.stabilizer G a) := by
    have he : (↑(fixed (G := G) a) : Set G) = (MulAction.stabilizer G a : Set G) := by
      ext g
      simp [fixed, MulAction.mem_stabilizer_iff]
    have hc := Fintype.card_congr (Equiv.setCongr he)
    change Fintype.card (fixed (G := G) a) = Fintype.card (MulAction.stabilizer G a) at hc
    simpa only [Fintype.card_coe] using hc
  rw [ho, hf]
  exact MulAction.card_orbit_mul_card_stabilizer_eq_card_group G a

/-- A positive fixed-point count converts orbit-stabilizer multiplication to division. -/
theorem orbit_card_eq_div (a : α) :
    (orbit (G := G) a).card = Fintype.card G / (fixed (G := G) a).card := by
  have hpos : 0 < (fixed (G := G) a).card := by
    apply Finset.card_pos.mpr
    exact ⟨1, by simp [fixed]⟩
  rw [← orbit_card_mul_fixed_card (G := G) a, Nat.mul_div_cancel _ hpos]

end Quantum.Stabilizer.Homological.OrbitCensus

#print axioms Quantum.Stabilizer.Homological.OrbitCensus.census_complete
