/-
GENERATED FILE — DO NOT HAND-EDIT
Generator: qec-lab:experiments/bb_lab/scripts/bravyi360_kernel/generate.py
Emitter, relative to generator directory:
  emitters/generate_highcap_search.py
Data and SHA-256 hashes: audit_manifest.json
Regenerate:
  QECLEAN_ROOT=/path/to/QECLean \
    python3 experiments/bb_lab/scripts/bravyi360_kernel/generate.py --force
-/

import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.BottomForest
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.BottomHighSearchPart0
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.BottomHighSearchPart1
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.BottomHighSearchPart2
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.BottomHighSearchPart3
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.BottomHighSearchPart4
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.BottomHighSearchPart5
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.BottomHighSearchPart6
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.BottomHighSearchPart7
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.BottomHighSearchPart8
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.BottomHighSearchPart9
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.BottomHighSearchPart10
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.BottomHighSearchPart11
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.BottomHighSearchPart12
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.BottomHighSearchPart13

noncomputable section
namespace Quantum.Stabilizer.Homological.BB.Bravyi360.BottomForest
open F2Mask FiberData
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every high-cap record in the canonical forest has a checked outside-support census. -/
theorem highRecords_complete (b : Fin 112) (r : Fiber) (hr : r ∈ recordsAt b.val)
    (hweight : r.weight = 16 ∨ r.weight = 14) (word : Nat) (hw : word < 2^90)
    (he : reconX bottomEColumns word = reconX bottomRColumns r.beta)
    (hoff : bitCount 90 (outsideMask word r.beta) ≤ outsideBudget r) :
    outsideMask word r.beta ∈ r.seeds.map Seed.off := by
  fin_cases b
  · change r ∈ records0 at hr
    exact HighSearch.chunk_complete0 r hr hweight word hw he hoff
  · change r ∈ records250 at hr
    exact HighSearch.chunk_complete250 r hr hweight word hw he hoff
  · change r ∈ records500 at hr
    exact HighSearch.chunk_complete500 r hr hweight word hw he hoff
  · change r ∈ records750 at hr
    exact HighSearch.chunk_complete750 r hr hweight word hw he hoff
  · change r ∈ records1000 at hr
    exact HighSearch.chunk_complete1000 r hr hweight word hw he hoff
  · change r ∈ records1250 at hr
    exact HighSearch.chunk_complete1250 r hr hweight word hw he hoff
  · change r ∈ records1500 at hr
    exact HighSearch.chunk_complete1500 r hr hweight word hw he hoff
  · change r ∈ records1750 at hr
    exact HighSearch.chunk_complete1750 r hr hweight word hw he hoff
  · change r ∈ records2000 at hr
    exact HighSearch.chunk_complete2000 r hr hweight word hw he hoff
  · change r ∈ records2250 at hr
    exact HighSearch.chunk_complete2250 r hr hweight word hw he hoff
  · change r ∈ records2500 at hr
    exact HighSearch.chunk_complete2500 r hr hweight word hw he hoff
  · change r ∈ records2750 at hr
    exact HighSearch.chunk_complete2750 r hr hweight word hw he hoff
  · change r ∈ records3000 at hr
    exact HighSearch.chunk_complete3000 r hr hweight word hw he hoff
  · change r ∈ records3250 at hr
    exact HighSearch.chunk_complete3250 r hr hweight word hw he hoff
  · change r ∈ records3500 at hr
    exact HighSearch.chunk_complete3500 r hr hweight word hw he hoff
  · change r ∈ records3750 at hr
    exact HighSearch.chunk_complete3750 r hr hweight word hw he hoff
  · change r ∈ records4000 at hr
    exact HighSearch.chunk_complete4000 r hr hweight word hw he hoff
  · change r ∈ records4250 at hr
    exact HighSearch.chunk_complete4250 r hr hweight word hw he hoff
  · change r ∈ records4500 at hr
    exact HighSearch.chunk_complete4500 r hr hweight word hw he hoff
  · change r ∈ records4750 at hr
    exact HighSearch.chunk_complete4750 r hr hweight word hw he hoff
  · change r ∈ records5000 at hr
    exact HighSearch.chunk_complete5000 r hr hweight word hw he hoff
  · change r ∈ records5250 at hr
    exact HighSearch.chunk_complete5250 r hr hweight word hw he hoff
  · change r ∈ records5500 at hr
    exact HighSearch.chunk_complete5500 r hr hweight word hw he hoff
  · change r ∈ records5750 at hr
    exact HighSearch.chunk_complete5750 r hr hweight word hw he hoff
  · change r ∈ records6000 at hr
    exact HighSearch.chunk_complete6000 r hr hweight word hw he hoff
  · change r ∈ records6250 at hr
    exact HighSearch.chunk_complete6250 r hr hweight word hw he hoff
  · change r ∈ records6500 at hr
    exact HighSearch.chunk_complete6500 r hr hweight word hw he hoff
  · change r ∈ records6750 at hr
    exact HighSearch.chunk_complete6750 r hr hweight word hw he hoff
  · change r ∈ records7000 at hr
    exact HighSearch.chunk_complete7000 r hr hweight word hw he hoff
  · change r ∈ records7250 at hr
    exact HighSearch.chunk_complete7250 r hr hweight word hw he hoff
  · change r ∈ records7500 at hr
    exact HighSearch.chunk_complete7500 r hr hweight word hw he hoff
  · change r ∈ records7750 at hr
    exact HighSearch.chunk_complete7750 r hr hweight word hw he hoff
  · change r ∈ records8000 at hr
    exact HighSearch.chunk_complete8000 r hr hweight word hw he hoff
  · change r ∈ records8250 at hr
    exact HighSearch.chunk_complete8250 r hr hweight word hw he hoff
  · change r ∈ records8500 at hr
    exact HighSearch.chunk_complete8500 r hr hweight word hw he hoff
  · change r ∈ records8750 at hr
    exact HighSearch.chunk_complete8750 r hr hweight word hw he hoff
  · change r ∈ records9000 at hr
    exact HighSearch.chunk_complete9000 r hr hweight word hw he hoff
  · change r ∈ records9250 at hr
    exact HighSearch.chunk_complete9250 r hr hweight word hw he hoff
  · change r ∈ records9500 at hr
    exact HighSearch.chunk_complete9500 r hr hweight word hw he hoff
  · change r ∈ records9750 at hr
    exact HighSearch.chunk_complete9750 r hr hweight word hw he hoff
  · change r ∈ records10000 at hr
    exact HighSearch.chunk_complete10000 r hr hweight word hw he hoff
  · change r ∈ records10250 at hr
    exact HighSearch.chunk_complete10250 r hr hweight word hw he hoff
  · change r ∈ records10500 at hr
    exact HighSearch.chunk_complete10500 r hr hweight word hw he hoff
  · change r ∈ records10750 at hr
    exact HighSearch.chunk_complete10750 r hr hweight word hw he hoff
  · change r ∈ records11000 at hr
    exact HighSearch.chunk_complete11000 r hr hweight word hw he hoff
  · change r ∈ records11250 at hr
    exact HighSearch.chunk_complete11250 r hr hweight word hw he hoff
  · change r ∈ records11500 at hr
    exact HighSearch.chunk_complete11500 r hr hweight word hw he hoff
  · change r ∈ records11750 at hr
    exact HighSearch.chunk_complete11750 r hr hweight word hw he hoff
  · change r ∈ records12000 at hr
    exact HighSearch.chunk_complete12000 r hr hweight word hw he hoff
  · change r ∈ records12250 at hr
    exact HighSearch.chunk_complete12250 r hr hweight word hw he hoff
  · change r ∈ records12500 at hr
    exact HighSearch.chunk_complete12500 r hr hweight word hw he hoff
  · change r ∈ records12750 at hr
    exact HighSearch.chunk_complete12750 r hr hweight word hw he hoff
  · change r ∈ records13000 at hr
    exact HighSearch.chunk_complete13000 r hr hweight word hw he hoff
  · change r ∈ records13250 at hr
    exact HighSearch.chunk_complete13250 r hr hweight word hw he hoff
  · change r ∈ records13500 at hr
    exact HighSearch.chunk_complete13500 r hr hweight word hw he hoff
  · change r ∈ records13750 at hr
    exact HighSearch.chunk_complete13750 r hr hweight word hw he hoff
  · change r ∈ records14000 at hr
    exact HighSearch.chunk_complete14000 r hr hweight word hw he hoff
  · change r ∈ records14250 at hr
    exact HighSearch.chunk_complete14250 r hr hweight word hw he hoff
  · change r ∈ records14500 at hr
    exact HighSearch.chunk_complete14500 r hr hweight word hw he hoff
  · change r ∈ records14750 at hr
    exact HighSearch.chunk_complete14750 r hr hweight word hw he hoff
  · change r ∈ records15000 at hr
    exact HighSearch.chunk_complete15000 r hr hweight word hw he hoff
  · change r ∈ records15250 at hr
    exact HighSearch.chunk_complete15250 r hr hweight word hw he hoff
  · change r ∈ records15500 at hr
    exact HighSearch.chunk_complete15500 r hr hweight word hw he hoff
  · change r ∈ records15750 at hr
    exact HighSearch.chunk_complete15750 r hr hweight word hw he hoff
  · change r ∈ records16000 at hr
    exact HighSearch.chunk_complete16000 r hr hweight word hw he hoff
  · change r ∈ records16250 at hr
    exact HighSearch.chunk_complete16250 r hr hweight word hw he hoff
  · change r ∈ records16500 at hr
    exact HighSearch.chunk_complete16500 r hr hweight word hw he hoff
  · change r ∈ records16750 at hr
    exact HighSearch.chunk_complete16750 r hr hweight word hw he hoff
  · change r ∈ records17000 at hr
    exact HighSearch.chunk_complete17000 r hr hweight word hw he hoff
  · change r ∈ records17250 at hr
    exact HighSearch.chunk_complete17250 r hr hweight word hw he hoff
  · change r ∈ records17500 at hr
    exact HighSearch.chunk_complete17500 r hr hweight word hw he hoff
  · change r ∈ records17750 at hr
    exact HighSearch.chunk_complete17750 r hr hweight word hw he hoff
  · change r ∈ records18000 at hr
    exact HighSearch.chunk_complete18000 r hr hweight word hw he hoff
  · change r ∈ records18250 at hr
    exact HighSearch.chunk_complete18250 r hr hweight word hw he hoff
  · change r ∈ records18500 at hr
    exact HighSearch.chunk_complete18500 r hr hweight word hw he hoff
  · change r ∈ records18750 at hr
    exact HighSearch.chunk_complete18750 r hr hweight word hw he hoff
  · change r ∈ records19000 at hr
    exact HighSearch.chunk_complete19000 r hr hweight word hw he hoff
  · change r ∈ records19250 at hr
    exact HighSearch.chunk_complete19250 r hr hweight word hw he hoff
  · change r ∈ records19500 at hr
    exact HighSearch.chunk_complete19500 r hr hweight word hw he hoff
  · change r ∈ records19750 at hr
    exact HighSearch.chunk_complete19750 r hr hweight word hw he hoff
  · change r ∈ records20000 at hr
    exact HighSearch.chunk_complete20000 r hr hweight word hw he hoff
  · change r ∈ records20250 at hr
    exact HighSearch.chunk_complete20250 r hr hweight word hw he hoff
  · change r ∈ records20500 at hr
    exact HighSearch.chunk_complete20500 r hr hweight word hw he hoff
  · change r ∈ records20750 at hr
    exact HighSearch.chunk_complete20750 r hr hweight word hw he hoff
  · change r ∈ records21000 at hr
    exact HighSearch.chunk_complete21000 r hr hweight word hw he hoff
  · change r ∈ records21250 at hr
    exact HighSearch.chunk_complete21250 r hr hweight word hw he hoff
  · change r ∈ records21500 at hr
    exact HighSearch.chunk_complete21500 r hr hweight word hw he hoff
  · change r ∈ records21750 at hr
    exact HighSearch.chunk_complete21750 r hr hweight word hw he hoff
  · change r ∈ records22000 at hr
    exact HighSearch.chunk_complete22000 r hr hweight word hw he hoff
  · change r ∈ records22250 at hr
    exact HighSearch.chunk_complete22250 r hr hweight word hw he hoff
  · change r ∈ records22500 at hr
    exact HighSearch.chunk_complete22500 r hr hweight word hw he hoff
  · change r ∈ records22750 at hr
    exact HighSearch.chunk_complete22750 r hr hweight word hw he hoff
  · change r ∈ records23000 at hr
    exact HighSearch.chunk_complete23000 r hr hweight word hw he hoff
  · change r ∈ records23250 at hr
    exact HighSearch.chunk_complete23250 r hr hweight word hw he hoff
  · change r ∈ records23500 at hr
    exact HighSearch.chunk_complete23500 r hr hweight word hw he hoff
  · change r ∈ records23750 at hr
    exact HighSearch.chunk_complete23750 r hr hweight word hw he hoff
  · change r ∈ records24000 at hr
    exact HighSearch.chunk_complete24000 r hr hweight word hw he hoff
  · change r ∈ records24250 at hr
    exact HighSearch.chunk_complete24250 r hr hweight word hw he hoff
  · change r ∈ records24500 at hr
    exact HighSearch.chunk_complete24500 r hr hweight word hw he hoff
  · change r ∈ records24750 at hr
    exact HighSearch.chunk_complete24750 r hr hweight word hw he hoff
  · change r ∈ records25000 at hr
    exact HighSearch.chunk_complete25000 r hr hweight word hw he hoff
  · change r ∈ records25250 at hr
    exact HighSearch.chunk_complete25250 r hr hweight word hw he hoff
  · change r ∈ records25500 at hr
    exact HighSearch.chunk_complete25500 r hr hweight word hw he hoff
  · change r ∈ records25750 at hr
    exact HighSearch.chunk_complete25750 r hr hweight word hw he hoff
  · change r ∈ records26000 at hr
    exact HighSearch.chunk_complete26000 r hr hweight word hw he hoff
  · change r ∈ records26250 at hr
    exact HighSearch.chunk_complete26250 r hr hweight word hw he hoff
  · change r ∈ records26500 at hr
    exact HighSearch.chunk_complete26500 r hr hweight word hw he hoff
  · change r ∈ records26750 at hr
    exact HighSearch.chunk_complete26750 r hr hweight word hw he hoff
  · change r ∈ records27000 at hr
    exact HighSearch.chunk_complete27000 r hr hweight word hw he hoff
  · change r ∈ records27250 at hr
    exact HighSearch.chunk_complete27250 r hr hweight word hw he hoff
  · change r ∈ records27500 at hr
    exact HighSearch.chunk_complete27500 r hr hweight word hw he hoff
  · change r ∈ records27750 at hr
    exact HighSearch.chunk_complete27750 r hr hweight word hw he hoff
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every canonical high-cap fiber contains the outside support of each actual solution. -/
theorem highFiberAt_complete (j : Fin 27867)
    (hweight : (fiberAt j.val).weight = 16 ∨ (fiberAt j.val).weight = 14)
    (word : Nat) (hw : word < 2^90)
    (he : reconX bottomEColumns word = reconX bottomRColumns (fiberAt j.val).beta)
    (hoff : bitCount 90 (outsideMask word (fiberAt j.val).beta) ≤ outsideBudget (fiberAt j.val)) :
    outsideMask word (fiberAt j.val).beta ∈ (fiberAt j.val).seeds.map Seed.off :=
  highRecords_complete ⟨j.val/250,by omega⟩ (fiberAt j.val) (fiberAt_mem j)
    hweight word hw he hoff
#print axioms highFiberAt_complete
end Quantum.Stabilizer.Homological.BB.Bravyi360.BottomForest
