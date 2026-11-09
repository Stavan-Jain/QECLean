import QEC.Stabilizer.Framework.Homological.Certificate.OrbitCensus

/-!
# Orbit censuses indexed by a finite type

`indexed_normalize` is the form of `OrbitCensus.exists_representative` for a
census given as an injective family of canonical representatives: every member
of the target set is carried onto one of the listed representatives by some
group element.
-/

namespace Quantum.Stabilizer.Homological.OrbitCensus

variable {G α ι : Type*} [Group G] [Fintype G] [LinearOrder α] [MulAction G α] [Fintype ι]

/-- An injective indexed canonical census whose orbit sizes reach the target
bound normalizes every target member to one indexed representative. -/
theorem indexed_normalize (representative : ι → α) (target : Finset α)
    (hinjective : Function.Injective representative)
    (hcanonical : ∀ i, IsCanonical (G := G) (representative i))
    (hinside : ∀ i, representative i ∈ target)
    (hclosed : ∀ g : G, ∀ a ∈ target, g • a ∈ target)
    (hcount : target.card ≤ ∑ i, (orbit (G := G) (representative i)).card)
    {a : α} (ha : a ∈ target) :
    ∃ (i : ι) (g : G), g • a = representative i := by
  obtain ⟨r, hr, g, hg⟩ := exists_representative (Finset.univ.image representative) target
    (Finset.forall_mem_image.mpr fun i _ => hcanonical i)
    (Finset.forall_mem_image.mpr fun i _ => hinside i) hclosed
    (by rwa [Finset.sum_image fun i _ j _ he => hinjective he]) ha
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hr
  exact ⟨i, g⁻¹, by rw [← hg, inv_smul_smul]⟩

end Quantum.Stabilizer.Homological.OrbitCensus
