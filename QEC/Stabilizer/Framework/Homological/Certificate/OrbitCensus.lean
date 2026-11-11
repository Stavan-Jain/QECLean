import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Orbit censuses for finite group actions

A finite group `G` acts on a linearly ordered type `α`. A point is *canonical*
(`IsCanonical`) if it is the least point of its orbit, so each orbit contains
at most one canonical point (`canonical_eq_of_mem`) and distinct canonical
points have disjoint orbits (`canonical_orbits_disjoint`).

A *census* of a finite `G`-invariant set `target` is a set of canonical points
of `target` whose orbit sizes add up to at least `target.card`. Such a census
is complete: its orbits exhaust `target` (`census_complete`), so every member
of `target` is a translate of a listed representative
(`exists_representative`).

Orbit sizes are computed from fixed-point counts by the orbit–stabilizer
theorem: `orbit_card_mul_fixed_card` and `orbit_card_eq_div`.
-/

namespace Quantum.Stabilizer.Homological.OrbitCensus

variable {G α : Type*} [Group G] [Fintype G] [LinearOrder α] [MulAction G α]

/-- The finite orbit of a point under a finite group action. -/
def orbit (a : α) : Finset α := Finset.univ.image (fun g : G => g • a)

/-- Membership in the finite orbit is witnessed by a group element. -/
lemma mem_orbit {a b : α} : b ∈ orbit (G := G) a ↔ ∃ g : G, g • a = b := by
  simp [orbit]

/-- Every point is in its own finite orbit. -/
lemma self_mem_orbit (a : α) : a ∈ orbit (G := G) a :=
  mem_orbit.mpr ⟨1, one_smul G a⟩

/-- A canonical point is the least point in its orbit. -/
def IsCanonical (a : α) : Prop := ∀ g : G, a ≤ g • a

/-- Two canonical points in the same orbit are equal. -/
lemma canonical_eq_of_mem {a b : α} (ha : IsCanonical (G := G) a)
    (hb : IsCanonical (G := G) b) (h : b ∈ orbit (G := G) a) : a = b := by
  obtain ⟨g, rfl⟩ := mem_orbit.mp h
  exact le_antisymm (ha g) (by simpa only [inv_smul_smul] using hb g⁻¹)

/-- Distinct canonical points have disjoint orbits. -/
lemma canonical_orbits_disjoint {a b : α} (ha : IsCanonical (G := G) a)
    (hb : IsCanonical (G := G) b) (hab : a ≠ b) :
    Disjoint (orbit (G := G) a) (orbit (G := G) b) := by
  refine Finset.disjoint_left.mpr fun c hca hcb => hab (canonical_eq_of_mem ha hb ?_)
  obtain ⟨g, rfl⟩ := mem_orbit.mp hca
  obtain ⟨h, hh⟩ := mem_orbit.mp hcb
  exact mem_orbit.mpr ⟨h⁻¹ * g, by rw [mul_smul, ← hh, inv_smul_smul]⟩

/-- Canonical representatives whose orbit sizes exhaust a finite invariant set
form a complete census of that set. -/
theorem census_complete (representatives target : Finset α)
    (hcanonical : ∀ a ∈ representatives, IsCanonical (G := G) a)
    (hinside : ∀ a ∈ representatives, a ∈ target)
    (hclosed : ∀ g : G, ∀ a ∈ target, g • a ∈ target)
    (hcount : target.card ≤ ∑ a ∈ representatives, (orbit (G := G) a).card) :
    representatives.biUnion (orbit (G := G)) = target := by
  refine Finset.eq_of_subset_of_card_le (fun b hb => ?_) ?_
  · obtain ⟨a, ha, hba⟩ := Finset.mem_biUnion.mp hb
    obtain ⟨g, rfl⟩ := mem_orbit.mp hba
    exact hclosed g a (hinside a ha)
  · rwa [Finset.card_biUnion fun a ha b hb hab =>
      canonical_orbits_disjoint (hcanonical a ha) (hcanonical b hb) hab]

/-- A complete canonical census supplies a representative and translation for
each member of the target set. -/
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

/-- The group elements fixing a point, as a finite set. -/
def fixed (a : α) : Finset G := Finset.univ.filter (fun g => g • a = a)

/-- Orbit–stabilizer: the orbit size times the number of group elements fixing
the point is the order of the group. -/
theorem orbit_card_mul_fixed_card (a : α) :
    (orbit (G := G) a).card * (fixed (G := G) a).card = Fintype.card G := by
  have ho : (orbit (G := G) a : Set α) = MulAction.orbit G a := by
    ext b
    simp [mem_orbit, MulAction.mem_orbit_iff]
  have hf : (fixed (G := G) a : Set G) = MulAction.stabilizer G a := by
    ext g
    simp [fixed, MulAction.mem_stabilizer_iff]
  rw [← Nat.card_eq_finsetCard, ← Nat.card_eq_finsetCard, ← Nat.card_eq_fintype_card,
    ← Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup G a), Nat.card_prod]
  exact congrArg₂ _ (Nat.card_congr (Equiv.setCongr ho)) (Nat.card_congr (Equiv.setCongr hf))

/-- The orbit size is the order of the group divided by the number of group
elements fixing the point. -/
theorem orbit_card_eq_div (a : α) :
    (orbit (G := G) a).card = Fintype.card G / (fixed (G := G) a).card := by
  rw [← orbit_card_mul_fixed_card (G := G) a,
    Nat.mul_div_cancel _ (Finset.card_pos.mpr ⟨1, by simp [fixed]⟩)]

end Quantum.Stabilizer.Homological.OrbitCensus
