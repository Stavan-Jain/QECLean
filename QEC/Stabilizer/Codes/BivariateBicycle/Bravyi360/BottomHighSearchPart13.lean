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

import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.BottomHighSearchSupport
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.BottomForestFastPart13

noncomputable section
set_option maxRecDepth 100000
set_option synthInstance.maxSize 100000
namespace Quantum.Stabilizer.Homological.BB.Bravyi360.BottomForest.HighSearch
open F2Mask PackedDigits FiberData

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every high-cap record in canonical chunk 104 matches a certified search. -/
theorem matches26000 : records26000.all (fun r => decide (
    (r.weight = 16 ∨ r.weight = 14) → False)) = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The checked searches give the exact seed-support list for canonical chunk 104. -/
theorem chunk_complete26000 (r : Fiber) (hr : r ∈ records26000)
    (hweight : r.weight = 16 ∨ r.weight = 14) (word : Nat) (_hw : word < 2^90)
    (_he : reconX bottomEColumns word = reconX bottomRColumns r.beta)
    (_hoff : bitCount 90 (outsideMask word r.beta) ≤ outsideBudget r) :
    outsideMask word r.beta ∈ r.seeds.map Seed.off := by
  have h := (of_decide_eq_true ((List.all_eq_true.mp matches26000) r hr)) hweight
  exact False.elim h

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every high-cap record in canonical chunk 105 matches a certified search. -/
theorem matches26250 : records26250.all (fun r => decide (
    (r.weight = 16 ∨ r.weight = 14) → False)) = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The checked searches give the exact seed-support list for canonical chunk 105. -/
theorem chunk_complete26250 (r : Fiber) (hr : r ∈ records26250)
    (hweight : r.weight = 16 ∨ r.weight = 14) (word : Nat) (_hw : word < 2^90)
    (_he : reconX bottomEColumns word = reconX bottomRColumns r.beta)
    (_hoff : bitCount 90 (outsideMask word r.beta) ≤ outsideBudget r) :
    outsideMask word r.beta ∈ r.seeds.map Seed.off := by
  have h := (of_decide_eq_true ((List.all_eq_true.mp matches26250) r hr)) hweight
  exact False.elim h

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every high-cap record in canonical chunk 106 matches a certified search. -/
theorem matches26500 : records26500.all (fun r => decide (
    (r.weight = 16 ∨ r.weight = 14) → False)) = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The checked searches give the exact seed-support list for canonical chunk 106. -/
theorem chunk_complete26500 (r : Fiber) (hr : r ∈ records26500)
    (hweight : r.weight = 16 ∨ r.weight = 14) (word : Nat) (_hw : word < 2^90)
    (_he : reconX bottomEColumns word = reconX bottomRColumns r.beta)
    (_hoff : bitCount 90 (outsideMask word r.beta) ≤ outsideBudget r) :
    outsideMask word r.beta ∈ r.seeds.map Seed.off := by
  have h := (of_decide_eq_true ((List.all_eq_true.mp matches26500) r hr)) hweight
  exact False.elim h

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every high-cap record in canonical chunk 107 matches a certified search. -/
theorem matches26750 : records26750.all (fun r => decide (
    (r.weight = 16 ∨ r.weight = 14) → False)) = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The checked searches give the exact seed-support list for canonical chunk 107. -/
theorem chunk_complete26750 (r : Fiber) (hr : r ∈ records26750)
    (hweight : r.weight = 16 ∨ r.weight = 14) (word : Nat) (_hw : word < 2^90)
    (_he : reconX bottomEColumns word = reconX bottomRColumns r.beta)
    (_hoff : bitCount 90 (outsideMask word r.beta) ≤ outsideBudget r) :
    outsideMask word r.beta ∈ r.seeds.map Seed.off := by
  have h := (of_decide_eq_true ((List.all_eq_true.mp matches26750) r hr)) hweight
  exact False.elim h

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every high-cap record in canonical chunk 108 matches a certified search. -/
theorem matches27000 : records27000.all (fun r => decide (
    (r.weight = 16 ∨ r.weight = 14) → False)) = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The checked searches give the exact seed-support list for canonical chunk 108. -/
theorem chunk_complete27000 (r : Fiber) (hr : r ∈ records27000)
    (hweight : r.weight = 16 ∨ r.weight = 14) (word : Nat) (_hw : word < 2^90)
    (_he : reconX bottomEColumns word = reconX bottomRColumns r.beta)
    (_hoff : bitCount 90 (outsideMask word r.beta) ≤ outsideBudget r) :
    outsideMask word r.beta ∈ r.seeds.map Seed.off := by
  have h := (of_decide_eq_true ((List.all_eq_true.mp matches27000) r hr)) hweight
  exact False.elim h

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every high-cap record in canonical chunk 109 matches a certified search. -/
theorem matches27250 : records27250.all (fun r => decide (
    (r.weight = 16 ∨ r.weight = 14) → False)) = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The checked searches give the exact seed-support list for canonical chunk 109. -/
theorem chunk_complete27250 (r : Fiber) (hr : r ∈ records27250)
    (hweight : r.weight = 16 ∨ r.weight = 14) (word : Nat) (_hw : word < 2^90)
    (_he : reconX bottomEColumns word = reconX bottomRColumns r.beta)
    (_hoff : bitCount 90 (outsideMask word r.beta) ≤ outsideBudget r) :
    outsideMask word r.beta ∈ r.seeds.map Seed.off := by
  have h := (of_decide_eq_true ((List.all_eq_true.mp matches27250) r hr)) hweight
  exact False.elim h

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every high-cap record in canonical chunk 110 matches a certified search. -/
theorem matches27500 : records27500.all (fun r => decide (
    (r.weight = 16 ∨ r.weight = 14) → False)) = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The checked searches give the exact seed-support list for canonical chunk 110. -/
theorem chunk_complete27500 (r : Fiber) (hr : r ∈ records27500)
    (hweight : r.weight = 16 ∨ r.weight = 14) (word : Nat) (_hw : word < 2^90)
    (_he : reconX bottomEColumns word = reconX bottomRColumns r.beta)
    (_hoff : bitCount 90 (outsideMask word r.beta) ≤ outsideBudget r) :
    outsideMask word r.beta ∈ r.seeds.map Seed.off := by
  have h := (of_decide_eq_true ((List.all_eq_true.mp matches27500) r hr)) hweight
  exact False.elim h

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every high-cap record in canonical chunk 111 matches a certified search. -/
theorem matches27750 : records27750.all (fun r => decide (
    (r.weight = 16 ∨ r.weight = 14) → False)) = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The checked searches give the exact seed-support list for canonical chunk 111. -/
theorem chunk_complete27750 (r : Fiber) (hr : r ∈ records27750)
    (hweight : r.weight = 16 ∨ r.weight = 14) (word : Nat) (_hw : word < 2^90)
    (_he : reconX bottomEColumns word = reconX bottomRColumns r.beta)
    (_hoff : bitCount 90 (outsideMask word r.beta) ≤ outsideBudget r) :
    outsideMask word r.beta ∈ r.seeds.map Seed.off := by
  have h := (of_decide_eq_true ((List.all_eq_true.mp matches27750) r hr)) hweight
  exact False.elim h

#print axioms chunk_complete26000
end Quantum.Stabilizer.Homological.BB.Bravyi360.BottomForest.HighSearch
