import QEC.Stabilizer.Framework.Homological.Code

namespace Quantum.Stabilizer.Homological

/-!
An affine fiber can be certified without trusting Gaussian elimination.
The identity `P ∘ E + K ∘ D = id` supplies all solutions; a second identity
`E ∘ K = 0` verifies that the free directions are genuine kernel vectors.
-/

variable {R V W F : Type*} [Ring R]
  [AddCommGroup V] [Module R V]
  [AddCommGroup W] [Module R W]
  [AddCommGroup F] [Module R F]

/-- A certificate recovering a vector from its image and free coordinates. -/
structure AffineFiberCertificate (E : V →ₗ[R] W) (F : Type*)
    [AddCommGroup F] [Module R F] where
  /-- A candidate section of the linear constraint map. -/
  sectionMap : W →ₗ[R] V
  /-- The directions spanning the kernel. -/
  kernelMap : F →ₗ[R] V
  /-- Free coordinates of a solution. -/
  freeMap : V →ₗ[R] F
  /-- Every vector is recovered from its image and free coordinates. -/
  reconstruct : sectionMap.comp E + kernelMap.comp freeMap = LinearMap.id
  /-- Every free direction is killed by the constraint map. -/
  kernel_zero : E.comp kernelMap = 0

namespace AffineFiberCertificate

variable {E : V →ₗ[R] W} (C : AffineFiberCertificate E F)

/-- Every solution has the certified particular-plus-kernel form. -/
theorem solution_eq {v : V} {rhs : W} (hv : E v = rhs) :
    v = C.sectionMap rhs + C.kernelMap (C.freeMap v) := by
  have h := LinearMap.congr_fun C.reconstruct v
  simpa only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply, hv] using h.symm

/-- A compatible right-hand side is fixed by the constraint followed by its section. -/
theorem section_apply_eq {v : V} {rhs : W} (hv : E v = rhs) :
    E (C.sectionMap rhs) = rhs := by
  have hzero : E (C.kernelMap (C.freeMap v)) = 0 :=
    LinearMap.congr_fun C.kernel_zero (C.freeMap v)
  conv_rhs => rw [← hv, C.solution_eq hv, map_add, hzero, add_zero]

/-- The certificate describes exactly the affine fiber of a compatible right-hand side. -/
theorem apply_eq_iff {v : V} {rhs : W} :
    E v = rhs ↔ E (C.sectionMap rhs) = rhs ∧
      ∃ f : F, v = C.sectionMap rhs + C.kernelMap f := by
  constructor
  · intro hv
    exact ⟨C.section_apply_eq hv, C.freeMap v, C.solution_eq hv⟩
  · rintro ⟨hcompat, f, rfl⟩
    have hzero : E (C.kernelMap f) = 0 := LinearMap.congr_fun C.kernel_zero f
    rw [map_add, hzero, add_zero, hcompat]

/-- A property checked on all certified candidates holds on every solution. -/
theorem forall_solutions {rhs : W} (p : V → Prop)
    (hcheck : ∀ f : F, p (C.sectionMap rhs + C.kernelMap f)) :
    ∀ v : V, E v = rhs → p v := by
  intro v hv
  rw [C.solution_eq hv]
  exact hcheck _

end AffineFiberCertificate

/-- A list of candidate fibers with the full target cardinality is exhaustive. -/
theorem finite_census_complete {α : Type*} [DecidableEq α]
    (target census : Finset α) (hmem : census ⊆ target)
    (hcount : target.card ≤ census.card) : target = census := by
  exact (Finset.eq_of_subset_of_card_le hmem hcount).symm


end Quantum.Stabilizer.Homological
