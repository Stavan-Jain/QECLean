import QEC.Stabilizer.Framework.Homological.Certificate.OrbitCensus

namespace Quantum.Stabilizer.Homological.OrbitCensus
variable {G α ι : Type*} [Group G] [Fintype G] [LinearOrder α] [MulAction G α]
variable [Fintype ι]

/-- An injective indexed canonical census whose orbit sizes reach the target bound
normalizes every target member to one indexed representative. -/
theorem indexed_normalize (representative : ι → α) (target : Finset α)
    (hinjective : Function.Injective representative)
    (hcanonical : ∀ i, IsCanonical (G := G) (representative i))
    (hinside : ∀ i, representative i ∈ target)
    (hclosed : ∀ g : G, ∀ a ∈ target, g • a ∈ target)
    (hcount : target.card ≤ ∑ i, (orbit (G := G) (representative i)).card)
    {a : α} (ha : a ∈ target) :
    ∃ (i : ι) (g : G), g • a = representative i := by
  classical
  let reps := Finset.univ.image representative
  have hc : ∀ a ∈ reps, IsCanonical (G := G) a := by
    intro a ha
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp ha
    exact hcanonical i
  have hi : ∀ a ∈ reps, a ∈ target := by
    intro a ha
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp ha
    exact hinside i
  have hn : target.card ≤ ∑ a ∈ reps, (orbit (G := G) a).card := by
    rw [Finset.sum_image (fun i _ j _ he => hinjective he)]
    exact hcount
  obtain ⟨r,hr,g,hg⟩ := exists_representative reps target hc hi hclosed hn ha
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hr
  refine ⟨i,g⁻¹,?_⟩
  rw [← hg, inv_smul_smul]

end Quantum.Stabilizer.Homological.OrbitCensus
