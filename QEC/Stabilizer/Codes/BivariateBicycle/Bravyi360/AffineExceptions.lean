/-
GENERATED FILE — DO NOT HAND-EDIT
Generator: qec-lab:experiments/bb_lab/scripts/bravyi360_kernel/generate.py
Emitter, relative to generator directory:
  emitters/generate_affine_search.py
Data and SHA-256 hashes: audit_manifest.json
Regenerate:
  QECLEAN_ROOT=/path/to/QECLean \
    python3 experiments/bb_lab/scripts/bravyi360_kernel/generate.py --force
-/

import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.AffineInitialExceptions
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.DeepCensusData

noncomputable section

namespace Quantum.Stabilizer.Homological.BB.Bravyi360.AffineExceptions
open F2Mask F2Mask.AffineSearchData FiberData

/-- No solution exists in this exceptional top fiber with at most three outside bits. -/
theorem empty4 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x40000018000018020011002000000000092482040)
    (hweight : bitCount 180 (outsideMask word 0x40000018000018020011002000000000092482040) ≤ 3) : False := by
  have h := complete4 hw he hweight
  simpa only [allowed4, List.not_mem_nil] using h

/-- No solution exists in this exceptional top fiber with at most three outside bits. -/
theorem empty14 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x6000000c00000030000c06c00180000000000000c0)
    (hweight : bitCount 180 (outsideMask word 0x6000000c00000030000c06c00180000000000000c0) ≤ 3) : False := by
  have h := complete14 hw he hweight
  simpa only [allowed14, List.not_mem_nil] using h

/-- No solution exists in this exceptional top fiber with at most three outside bits. -/
theorem empty18 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x1000000400000180480120810100020000000000921)
    (hweight : bitCount 180 (outsideMask word 0x1000000400000180480120810100020000000000921) ≤ 3) : False := by
  have h := complete18 hw he hweight
  simpa only [allowed18, List.not_mem_nil] using h

/-- No solution exists in this exceptional top fiber with at most three outside bits. -/
theorem empty19 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x1000000400000500400120800100020000000005921)
    (hweight : bitCount 180 (outsideMask word 0x1000000400000500400120800100020000000005921) ≤ 3) : False := by
  have h := complete19 hw he hweight
  simpa only [allowed19, List.not_mem_nil] using h

/-- No solution exists in this exceptional top fiber with at most three outside bits. -/
theorem empty655 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0xc00180000006000c0000000003000600000018003)
    (hweight : bitCount 180 (outsideMask word 0xc00180000006000c0000000003000600000018003) ≤ 3) : False := by
  have h := complete655 hw he hweight
  simpa only [allowed655, List.not_mem_nil] using h

/-- No solution exists in this exceptional top fiber with at most three outside bits. -/
theorem empty656 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x1c0000008000e00000040000040008001200200040009)
    (hweight : bitCount 180 (outsideMask word 0x1c0000008000e00000040000040008001200200040009) ≤ 3) : False := by
  have h := complete656 hw he hweight
  simpa only [allowed656, List.not_mem_nil] using h

/-- The outside-support census in the deep affine certificate is the checked search census. -/
theorem deepOutside0 : (DeepCensusData.cert0).seeds.map Prod.fst = allowed653 := by decide +kernel

/-- Every sheet in the deep base fiber is a listed normalized lift or its deck translate. -/
theorem deepComplete0 {word : Nat} (hw : word < 2^90)
    (he : reconX bottomEColumns word = reconX bottomRColumns 0x7008000c00001200200049)
    (hweight : bitCount 90 (outsideMask word 0x7008000c00001200200049) ≤ 5) :
    word ∈ DeepCensusData.lifts0 ∨ (word ^^^ 0x7008000c00001200200049) ∈ DeepCensusData.lifts0 := by
  apply AffineMaskCertificate.census_of_check (DeepCensusData.cert0) 90 bottomEColumns bottomRColumns
    (DeepCensusData.lifts0) (DeepCensusData.checked0) hw he
  rw [deepOutside0]
  exact complete653 hw he hweight

/-- The outside-support census in the deep affine certificate is the checked search census. -/
theorem deepOutside1 : (DeepCensusData.cert1).seeds.map Prod.fst = allowed654 := by decide +kernel

/-- Every sheet in the deep base fiber is a listed normalized lift or its deck translate. -/
theorem deepComplete1 {word : Nat} (hw : word < 2^90)
    (he : reconX bottomEColumns word = reconX bottomRColumns 0x100020004018007000e001)
    (hweight : bitCount 90 (outsideMask word 0x100020004018007000e001) ≤ 5) :
    word ∈ DeepCensusData.lifts1 ∨ (word ^^^ 0x100020004018007000e001) ∈ DeepCensusData.lifts1 := by
  apply AffineMaskCertificate.census_of_check (DeepCensusData.cert1) 90 bottomEColumns bottomRColumns
    (DeepCensusData.lifts1) (DeepCensusData.checked1) hw he
  rw [deepOutside1]
  exact complete654 hw he hweight

#print axioms empty655
#print axioms deepComplete0
end Quantum.Stabilizer.Homological.BB.Bravyi360.AffineExceptions
