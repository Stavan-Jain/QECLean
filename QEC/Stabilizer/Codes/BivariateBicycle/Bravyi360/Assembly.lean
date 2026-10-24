import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.Defs
import QEC.Stabilizer.Framework.Homological.BBFlatLift

noncomputable section

namespace Quantum.Stabilizer.Homological.BB.Bravyi360
set_option maxRecDepth 10000

/-- Zero-shadow cycles inherit twice the logical floor of the quotient. -/
lemma weight_ge_double_of_top_shadow_zero
    (hfloor : topCover.LogicalFloor 12) {v : Group × Fin 2 → ZMod 2}
    (hv : v ∈ complex.cycles) (hn : v ∉ complex.boundaries)
    (hz : topCover.push1 v = 0) : 24 ≤ complex.chainWeight v := by
  apply topCover.chainWeight_ge_double_of_flat_boundary hfloor (c := 0)
    (zero_mem _) (by intro i hi; simp [XDoubleCoverData.sheet0] at hi) hv hn
  simpa only [map_zero] using hz

/-- The bottom distance floor and all nonzero light fibers establish the middle floor. -/
theorem middle_floor_of_certificates (hbase : baseCover.LogicalFloor 8)
    (hnonzero : ∀ v : MiddleGroup × Fin 2 → ZMod 2,
      v ∈ middleComplex.cycles → middleComplex.chainWeight v ≤ 10 →
      baseCover.push1 v ≠ 0 → v ∈ middleComplex.boundaries) :
    topCover.LogicalFloor 12 := by
  intro v hv hn
  by_contra hweight
  change ¬12 ≤ middleComplex.chainWeight v at hweight
  obtain ⟨k, hk⟩ := middle_cycle_even hv
  have hsmall : middleComplex.chainWeight v ≤ 10 := by omega
  by_cases hz : baseCover.push1 v = 0
  · have hdouble : 16 ≤ middleComplex.chainWeight v := by
      apply baseCover.chainWeight_ge_double_of_flat_boundary hbase (c := 0)
        (zero_mem _) (by intro i hi; simp [XDoubleCoverData.sheet0] at hi) hv hn
      simpa only [map_zero] using hz
    omega
  · exact hn (hnonzero v hv hsmall hz)

/-- The two quotient layers reduce the 360-qubit distance floor to the certified
nonzero bottom fibers and the small diagonal fibers above the zero bottom shadow. -/
theorem distance_floor_of_certificates
    (hmiddle : topCover.LogicalFloor 12)
    (hdiagonal : ∀ u : BaseGroup × Fin 2 → ZMod 2,
      u ∈ baseComplex.cycles → baseComplex.chainWeight u ≤ 10 → u ≠ 0 →
      ∀ v : Group × Fin 2 → ZMod 2,
        v ∈ complex.cycles → complex.chainWeight v ≤ 22 →
        topCover.push1 v = baseCover.pull1 u → v ∈ complex.boundaries)
    (hnonzero : ∀ v : Group × Fin 2 → ZMod 2,
      v ∈ complex.cycles → complex.chainWeight v ≤ 22 →
      baseCover.push1 (topCover.push1 v) ≠ 0 → v ∈ complex.boundaries) :
    ∀ v : Group × Fin 2 → ZMod 2,
      v ∈ complex.cycles → v ∉ complex.boundaries → 24 ≤ complex.chainWeight v := by
  intro v hv hn
  by_contra hweight
  obtain ⟨k, hk⟩ := cycle_even hv
  have hsmall : complex.chainWeight v ≤ 22 := by omega
  by_cases hz : topCover.push1 v = 0
  · have hdouble := weight_ge_double_of_top_shadow_zero hmiddle hv hn hz
    omega
  by_cases hbottom : baseCover.push1 (topCover.push1 v) = 0
  · obtain ⟨u, hu⟩ := (baseCover.push1_eq_zero_iff (topCover.push1 v)).mp hbottom
    have hcycle : u ∈ baseComplex.cycles := by
      apply baseCover.descend_cycle
      rw [← hu]
      exact topCover.push1_mem_cycles hv
    have hweightu : 2 * baseComplex.chainWeight u ≤ 22 := by
      change 2 * baseCover.baseComplex.chainWeight u ≤ 22
      rw [← baseCover.chainWeight_pull1, ← hu]
      exact (topCover.chainWeight_push_le v).trans hsmall
    obtain ⟨j, hj⟩ := base_cycle_even hcycle
    have hsmallu : baseComplex.chainWeight u ≤ 10 := by omega
    have hne : u ≠ 0 := by
      intro heq
      apply hz
      rw [hu, heq, map_zero]
    exact hn (hdiagonal u hcycle hsmallu hne v hv hsmall hu)
  · exact hn (hnonzero v hv hsmall hbottom)

end Quantum.Stabilizer.Homological.BB.Bravyi360
