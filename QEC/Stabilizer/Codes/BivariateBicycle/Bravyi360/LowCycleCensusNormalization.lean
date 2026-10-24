import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.LowCycleNormalization
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.BaseCycleCensus

noncomputable section

namespace Quantum.Stabilizer.Homological.BB.Bravyi360.LowCycleNormalization
open F2Mask
set_option maxRecDepth 200000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/--
The normalization table is indexed by exactly the independently complete
light-cycle census.
-/
theorem census_indices : List.ofFn (fun i : Fin 1954 => maskAt i.val) =
    F2Mask.Trellis.Bravyi90.allBaseCycles10 := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/--
Every chain in the complete light-cycle census is zero or translates to one of
45 representatives.
-/
theorem normalize_census (v : BaseGroup × Fin 2 → ZMod 2)
    (h : maskOf baseQubitEnum v ∈ F2Mask.Trellis.Bravyi90.allBaseCycles10) :
    v = 0 ∨ ∃ (j : Fin 45) (g : BaseGroup),
      maskOf baseQubitEnum (translate1 g v) = repAt j.val := by
  rw [← census_indices, List.mem_ofFn] at h
  obtain ⟨i,hi⟩ := h
  exact normalize i v hi.symm

end Quantum.Stabilizer.Homological.BB.Bravyi360.LowCycleNormalization
