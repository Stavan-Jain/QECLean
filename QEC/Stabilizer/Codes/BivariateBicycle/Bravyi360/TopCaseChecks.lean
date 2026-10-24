/-
GENERATED FILE — DO NOT HAND-EDIT
Generator: qec-lab:experiments/bb_lab/scripts/bravyi360_kernel/generate.py
Emitter, relative to generator directory:
  emitters/generate_top_case.py
Data and SHA-256 hashes: root_manifest.json
Regenerate:
  QECLEAN_ROOT=/path/to/QECLean \
    python3 experiments/bb_lab/scripts/bravyi360_kernel/generate.py --force
-/

import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.TopCasePart0
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.TopCasePart1
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.TopCasePart2
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.TopCasePart3
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.TopCasePart4
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.TopCasePart5

noncomputable section
namespace Quantum.Stabilizer.Homological.BB.Bravyi360.TopCaseData
set_option maxRecDepth 200000
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every packed chunk passes the family-association check. -/
theorem all_chunks (c : Fin 57) :
    (List.range (min 1024 (58130 - 1024 * c.val))).all
      (fun j => entryCheck (1024 * c.val + j)) = true := by
  fin_cases c
  · exact checked0
  · exact checked1
  · exact checked2
  · exact checked3
  · exact checked4
  · exact checked5
  · exact checked6
  · exact checked7
  · exact checked8
  · exact checked9
  · exact checked10
  · exact checked11
  · exact checked12
  · exact checked13
  · exact checked14
  · exact checked15
  · exact checked16
  · exact checked17
  · exact checked18
  · exact checked19
  · exact checked20
  · exact checked21
  · exact checked22
  · exact checked23
  · exact checked24
  · exact checked25
  · exact checked26
  · exact checked27
  · exact checked28
  · exact checked29
  · exact checked30
  · exact checked31
  · exact checked32
  · exact checked33
  · exact checked34
  · exact checked35
  · exact checked36
  · exact checked37
  · exact checked38
  · exact checked39
  · exact checked40
  · exact checked41
  · exact checked42
  · exact checked43
  · exact checked44
  · exact checked45
  · exact checked46
  · exact checked47
  · exact checked48
  · exact checked49
  · exact checked50
  · exact checked51
  · exact checked52
  · exact checked53
  · exact checked54
  · exact checked55
  · exact checked56
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every top-bank entry belongs to its certified family with the required overflow bound. -/
theorem all_checked (i : Fin 58130) : Valid i := by
  have hc : i.val / 1024 < 57 := by omega
  have hj : i.val % 1024 < min 1024 (58130 - 1024 * (i.val / 1024)) := by omega
  have h := (List.all_eq_true.mp (all_chunks ⟨i.val / 1024, hc⟩))
    (i.val % 1024) (List.mem_range.mpr hj)
  have heq : 1024 * (i.val / 1024) + i.val % 1024 = i.val := by omega
  change entryCheck (1024 * (i.val / 1024) + i.val % 1024) = true at h
  rw [heq] at h
  exact entryCheck_sound _ h
end Quantum.Stabilizer.Homological.BB.Bravyi360.TopCaseData
