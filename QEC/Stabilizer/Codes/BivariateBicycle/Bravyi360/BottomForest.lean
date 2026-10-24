/-
GENERATED FILE — DO NOT HAND-EDIT
Generator: qec-lab:experiments/bb_lab/scripts/bravyi360_kernel/generate.py
Emitter, relative to generator directory:
  emitters/compression_forest_global.py
Data and SHA-256 hashes: compression_manifest.json
Regenerate:
  QECLEAN_ROOT=/path/to/QECLean \
    python3 experiments/bb_lab/scripts/bravyi360_kernel/generate.py --force
-/

import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.BottomForestGroup
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.BottomForestFastPart0
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.BottomForestFastPart1
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.BottomForestFastPart2
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.BottomForestFastPart3
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.BottomForestFastPart4
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.BottomForestFastPart5
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.BottomForestFastPart6
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.BottomForestFastPart7
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.BottomForestFastPart8
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.BottomForestFastPart9
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.BottomForestFastPart10
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.BottomForestFastPart11
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.BottomForestFastPart12
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.BottomForestFastPart13

noncomputable section
set_option maxRecDepth 100000
namespace Quantum.Stabilizer.Homological.BB.Bravyi360.BottomForest
open F2Mask FiberData
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Balanced lookup of canonical shallow-fiber record chunks. -/
noncomputable def recordsAt (b : Nat) : List Fiber := (if Nat.blt b 56 then (if Nat.blt b 28 then (if Nat.blt b 14 then (if Nat.blt b 7 then (if Nat.blt b 3 then (if Nat.blt b 1 then records0 else (if Nat.blt b 2 then records250 else records500)) else (if Nat.blt b 5 then (if Nat.blt b 4 then records750 else records1000) else (if Nat.blt b 6 then records1250 else records1500))) else (if Nat.blt b 10 then (if Nat.blt b 8 then records1750 else (if Nat.blt b 9 then records2000 else records2250)) else (if Nat.blt b 12 then (if Nat.blt b 11 then records2500 else records2750) else (if Nat.blt b 13 then records3000 else records3250)))) else (if Nat.blt b 21 then (if Nat.blt b 17 then (if Nat.blt b 15 then records3500 else (if Nat.blt b 16 then records3750 else records4000)) else (if Nat.blt b 19 then (if Nat.blt b 18 then records4250 else records4500) else (if Nat.blt b 20 then records4750 else records5000))) else (if Nat.blt b 24 then (if Nat.blt b 22 then records5250 else (if Nat.blt b 23 then records5500 else records5750)) else (if Nat.blt b 26 then (if Nat.blt b 25 then records6000 else records6250) else (if Nat.blt b 27 then records6500 else records6750))))) else (if Nat.blt b 42 then (if Nat.blt b 35 then (if Nat.blt b 31 then (if Nat.blt b 29 then records7000 else (if Nat.blt b 30 then records7250 else records7500)) else (if Nat.blt b 33 then (if Nat.blt b 32 then records7750 else records8000) else (if Nat.blt b 34 then records8250 else records8500))) else (if Nat.blt b 38 then (if Nat.blt b 36 then records8750 else (if Nat.blt b 37 then records9000 else records9250)) else (if Nat.blt b 40 then (if Nat.blt b 39 then records9500 else records9750) else (if Nat.blt b 41 then records10000 else records10250)))) else (if Nat.blt b 49 then (if Nat.blt b 45 then (if Nat.blt b 43 then records10500 else (if Nat.blt b 44 then records10750 else records11000)) else (if Nat.blt b 47 then (if Nat.blt b 46 then records11250 else records11500) else (if Nat.blt b 48 then records11750 else records12000))) else (if Nat.blt b 52 then (if Nat.blt b 50 then records12250 else (if Nat.blt b 51 then records12500 else records12750)) else (if Nat.blt b 54 then (if Nat.blt b 53 then records13000 else records13250) else (if Nat.blt b 55 then records13500 else records13750)))))) else (if Nat.blt b 84 then (if Nat.blt b 70 then (if Nat.blt b 63 then (if Nat.blt b 59 then (if Nat.blt b 57 then records14000 else (if Nat.blt b 58 then records14250 else records14500)) else (if Nat.blt b 61 then (if Nat.blt b 60 then records14750 else records15000) else (if Nat.blt b 62 then records15250 else records15500))) else (if Nat.blt b 66 then (if Nat.blt b 64 then records15750 else (if Nat.blt b 65 then records16000 else records16250)) else (if Nat.blt b 68 then (if Nat.blt b 67 then records16500 else records16750) else (if Nat.blt b 69 then records17000 else records17250)))) else (if Nat.blt b 77 then (if Nat.blt b 73 then (if Nat.blt b 71 then records17500 else (if Nat.blt b 72 then records17750 else records18000)) else (if Nat.blt b 75 then (if Nat.blt b 74 then records18250 else records18500) else (if Nat.blt b 76 then records18750 else records19000))) else (if Nat.blt b 80 then (if Nat.blt b 78 then records19250 else (if Nat.blt b 79 then records19500 else records19750)) else (if Nat.blt b 82 then (if Nat.blt b 81 then records20000 else records20250) else (if Nat.blt b 83 then records20500 else records20750))))) else (if Nat.blt b 98 then (if Nat.blt b 91 then (if Nat.blt b 87 then (if Nat.blt b 85 then records21000 else (if Nat.blt b 86 then records21250 else records21500)) else (if Nat.blt b 89 then (if Nat.blt b 88 then records21750 else records22000) else (if Nat.blt b 90 then records22250 else records22500))) else (if Nat.blt b 94 then (if Nat.blt b 92 then records22750 else (if Nat.blt b 93 then records23000 else records23250)) else (if Nat.blt b 96 then (if Nat.blt b 95 then records23500 else records23750) else (if Nat.blt b 97 then records24000 else records24250)))) else (if Nat.blt b 105 then (if Nat.blt b 101 then (if Nat.blt b 99 then records24500 else (if Nat.blt b 100 then records24750 else records25000)) else (if Nat.blt b 103 then (if Nat.blt b 102 then records25250 else records25500) else (if Nat.blt b 104 then records25750 else records26000))) else (if Nat.blt b 108 then (if Nat.blt b 106 then records26250 else (if Nat.blt b 107 then records26500 else records26750)) else (if Nat.blt b 110 then (if Nat.blt b 109 then records27000 else records27250) else (if Nat.blt b 111 then records27500 else records27750)))))))
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Canonical shallow-fiber record at its fixed family position. -/
noncomputable def fiberAt (i : Nat) : Fiber := (recordsAt (i/250)).getD (i%250) default
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Number of records in forest chunk 0. -/
theorem length0 : records0.length = 250 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Number of records in forest chunk 1. -/
theorem length1 : records250.length = 250 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Number of records in forest chunk 2. -/
theorem length2 : records500.length = 250 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Number of records in forest chunk 3. -/
theorem length3 : records750.length = 250 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Number of records in forest chunk 4. -/
theorem length4 : records1000.length = 250 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Number of records in forest chunk 5. -/
theorem length5 : records1250.length = 250 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Number of records in forest chunk 6. -/
theorem length6 : records1500.length = 250 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Number of records in forest chunk 7. -/
theorem length7 : records1750.length = 250 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Number of records in forest chunk 8. -/
theorem length8 : records2000.length = 250 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Number of records in forest chunk 9. -/
theorem length9 : records2250.length = 250 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Number of records in forest chunk 10. -/
theorem length10 : records2500.length = 250 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Number of records in forest chunk 11. -/
theorem length11 : records2750.length = 250 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Number of records in forest chunk 12. -/
theorem length12 : records3000.length = 250 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Number of records in forest chunk 13. -/
theorem length13 : records3250.length = 250 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Number of records in forest chunk 14. -/
theorem length14 : records3500.length = 250 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Number of records in forest chunk 15. -/
theorem length15 : records3750.length = 250 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Number of records in forest chunk 16. -/
theorem length16 : records4000.length = 250 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Number of records in forest chunk 17. -/
theorem length17 : records4250.length = 250 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Number of records in forest chunk 18. -/
theorem length18 : records4500.length = 250 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Number of records in forest chunk 19. -/
theorem length19 : records4750.length = 250 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Number of records in forest chunk 20. -/
theorem length20 : records5000.length = 250 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Number of records in forest chunk 21. -/
theorem length21 : records5250.length = 250 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Number of records in forest chunk 22. -/
theorem length22 : records5500.length = 250 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Number of records in forest chunk 23. -/
theorem length23 : records5750.length = 250 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Number of records in forest chunk 24. -/
theorem length24 : records6000.length = 250 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Number of records in forest chunk 25. -/
theorem length25 : records6250.length = 250 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Number of records in forest chunk 26. -/
theorem length26 : records6500.length = 250 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Number of records in forest chunk 27. -/
theorem length27 : records6750.length = 250 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Number of records in forest chunk 28. -/
theorem length28 : records7000.length = 250 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Number of records in forest chunk 29. -/
theorem length29 : records7250.length = 250 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Number of records in forest chunk 30. -/
theorem length30 : records7500.length = 250 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Number of records in forest chunk 31. -/
theorem length31 : records7750.length = 250 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Number of records in forest chunk 32. -/
theorem length32 : records8000.length = 250 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Number of records in forest chunk 33. -/
theorem length33 : records8250.length = 250 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Number of records in forest chunk 34. -/
theorem length34 : records8500.length = 250 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Number of records in forest chunk 35. -/
theorem length35 : records8750.length = 250 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Number of records in forest chunk 36. -/
theorem length36 : records9000.length = 250 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Number of records in forest chunk 37. -/
theorem length37 : records9250.length = 250 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Number of records in forest chunk 38. -/
theorem length38 : records9500.length = 250 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Number of records in forest chunk 39. -/
theorem length39 : records9750.length = 250 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Number of records in forest chunk 40. -/
theorem length40 : records10000.length = 250 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Number of records in forest chunk 41. -/
theorem length41 : records10250.length = 250 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Number of records in forest chunk 42. -/
theorem length42 : records10500.length = 250 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Number of records in forest chunk 43. -/
theorem length43 : records10750.length = 250 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Number of records in forest chunk 44. -/
theorem length44 : records11000.length = 250 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Number of records in forest chunk 45. -/
theorem length45 : records11250.length = 250 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Number of records in forest chunk 46. -/
theorem length46 : records11500.length = 250 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Number of records in forest chunk 47. -/
theorem length47 : records11750.length = 250 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Number of records in forest chunk 48. -/
theorem length48 : records12000.length = 250 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Number of records in forest chunk 49. -/
theorem length49 : records12250.length = 250 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Number of records in forest chunk 50. -/
theorem length50 : records12500.length = 250 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Number of records in forest chunk 51. -/
theorem length51 : records12750.length = 250 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Number of records in forest chunk 52. -/
theorem length52 : records13000.length = 250 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Number of records in forest chunk 53. -/
theorem length53 : records13250.length = 250 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Number of records in forest chunk 54. -/
theorem length54 : records13500.length = 250 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Number of records in forest chunk 55. -/
theorem length55 : records13750.length = 250 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Number of records in forest chunk 56. -/
theorem length56 : records14000.length = 250 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Number of records in forest chunk 57. -/
theorem length57 : records14250.length = 250 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Number of records in forest chunk 58. -/
theorem length58 : records14500.length = 250 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Number of records in forest chunk 59. -/
theorem length59 : records14750.length = 250 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Number of records in forest chunk 60. -/
theorem length60 : records15000.length = 250 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Number of records in forest chunk 61. -/
theorem length61 : records15250.length = 250 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Number of records in forest chunk 62. -/
theorem length62 : records15500.length = 250 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Number of records in forest chunk 63. -/
theorem length63 : records15750.length = 250 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Number of records in forest chunk 64. -/
theorem length64 : records16000.length = 250 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Number of records in forest chunk 65. -/
theorem length65 : records16250.length = 250 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Number of records in forest chunk 66. -/
theorem length66 : records16500.length = 250 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Number of records in forest chunk 67. -/
theorem length67 : records16750.length = 250 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Number of records in forest chunk 68. -/
theorem length68 : records17000.length = 250 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Number of records in forest chunk 69. -/
theorem length69 : records17250.length = 250 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Number of records in forest chunk 70. -/
theorem length70 : records17500.length = 250 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Number of records in forest chunk 71. -/
theorem length71 : records17750.length = 250 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Number of records in forest chunk 72. -/
theorem length72 : records18000.length = 250 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Number of records in forest chunk 73. -/
theorem length73 : records18250.length = 250 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Number of records in forest chunk 74. -/
theorem length74 : records18500.length = 250 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Number of records in forest chunk 75. -/
theorem length75 : records18750.length = 250 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Number of records in forest chunk 76. -/
theorem length76 : records19000.length = 250 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Number of records in forest chunk 77. -/
theorem length77 : records19250.length = 250 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Number of records in forest chunk 78. -/
theorem length78 : records19500.length = 250 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Number of records in forest chunk 79. -/
theorem length79 : records19750.length = 250 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Number of records in forest chunk 80. -/
theorem length80 : records20000.length = 250 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Number of records in forest chunk 81. -/
theorem length81 : records20250.length = 250 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Number of records in forest chunk 82. -/
theorem length82 : records20500.length = 250 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Number of records in forest chunk 83. -/
theorem length83 : records20750.length = 250 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Number of records in forest chunk 84. -/
theorem length84 : records21000.length = 250 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Number of records in forest chunk 85. -/
theorem length85 : records21250.length = 250 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Number of records in forest chunk 86. -/
theorem length86 : records21500.length = 250 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Number of records in forest chunk 87. -/
theorem length87 : records21750.length = 250 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Number of records in forest chunk 88. -/
theorem length88 : records22000.length = 250 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Number of records in forest chunk 89. -/
theorem length89 : records22250.length = 250 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Number of records in forest chunk 90. -/
theorem length90 : records22500.length = 250 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Number of records in forest chunk 91. -/
theorem length91 : records22750.length = 250 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Number of records in forest chunk 92. -/
theorem length92 : records23000.length = 250 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Number of records in forest chunk 93. -/
theorem length93 : records23250.length = 250 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Number of records in forest chunk 94. -/
theorem length94 : records23500.length = 250 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Number of records in forest chunk 95. -/
theorem length95 : records23750.length = 250 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Number of records in forest chunk 96. -/
theorem length96 : records24000.length = 250 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Number of records in forest chunk 97. -/
theorem length97 : records24250.length = 250 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Number of records in forest chunk 98. -/
theorem length98 : records24500.length = 250 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Number of records in forest chunk 99. -/
theorem length99 : records24750.length = 250 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Number of records in forest chunk 100. -/
theorem length100 : records25000.length = 250 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Number of records in forest chunk 101. -/
theorem length101 : records25250.length = 250 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Number of records in forest chunk 102. -/
theorem length102 : records25500.length = 250 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Number of records in forest chunk 103. -/
theorem length103 : records25750.length = 250 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Number of records in forest chunk 104. -/
theorem length104 : records26000.length = 250 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Number of records in forest chunk 105. -/
theorem length105 : records26250.length = 250 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Number of records in forest chunk 106. -/
theorem length106 : records26500.length = 250 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Number of records in forest chunk 107. -/
theorem length107 : records26750.length = 250 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Number of records in forest chunk 108. -/
theorem length108 : records27000.length = 250 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Number of records in forest chunk 109. -/
theorem length109 : records27250.length = 250 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Number of records in forest chunk 110. -/
theorem length110 : records27500.length = 250 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Number of records in forest chunk 111. -/
theorem length111 : records27750.length = 117 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every canonical record chunk passes its full checker. -/
theorem recordsAt_checked (b : Nat) (hb : b < 112) : groupCheck (recordsAt b) = true := by
  by_cases h56 : b < 56
  · by_cases h28 : b < 28
    · by_cases h14 : b < 14
      · by_cases h7 : b < 7
        · by_cases h3 : b < 3
          · by_cases h1 : b < 1
            · have heq : b = 0 := by omega
              subst b
              exact checked0
            · by_cases h2 : b < 2
              · have heq : b = 1 := by omega
                subst b
                exact checked250
              · have heq : b = 2 := by omega
                subst b
                exact checked500
          · by_cases h5 : b < 5
            · by_cases h4 : b < 4
              · have heq : b = 3 := by omega
                subst b
                exact checked750
              · have heq : b = 4 := by omega
                subst b
                exact checked1000
            · by_cases h6 : b < 6
              · have heq : b = 5 := by omega
                subst b
                exact checked1250
              · have heq : b = 6 := by omega
                subst b
                exact checked1500
        · by_cases h10 : b < 10
          · by_cases h8 : b < 8
            · have heq : b = 7 := by omega
              subst b
              exact checked1750
            · by_cases h9 : b < 9
              · have heq : b = 8 := by omega
                subst b
                exact checked2000
              · have heq : b = 9 := by omega
                subst b
                exact checked2250
          · by_cases h12 : b < 12
            · by_cases h11 : b < 11
              · have heq : b = 10 := by omega
                subst b
                exact checked2500
              · have heq : b = 11 := by omega
                subst b
                exact checked2750
            · by_cases h13 : b < 13
              · have heq : b = 12 := by omega
                subst b
                exact checked3000
              · have heq : b = 13 := by omega
                subst b
                exact checked3250
      · by_cases h21 : b < 21
        · by_cases h17 : b < 17
          · by_cases h15 : b < 15
            · have heq : b = 14 := by omega
              subst b
              exact checked3500
            · by_cases h16 : b < 16
              · have heq : b = 15 := by omega
                subst b
                exact checked3750
              · have heq : b = 16 := by omega
                subst b
                exact checked4000
          · by_cases h19 : b < 19
            · by_cases h18 : b < 18
              · have heq : b = 17 := by omega
                subst b
                exact checked4250
              · have heq : b = 18 := by omega
                subst b
                exact checked4500
            · by_cases h20 : b < 20
              · have heq : b = 19 := by omega
                subst b
                exact checked4750
              · have heq : b = 20 := by omega
                subst b
                exact checked5000
        · by_cases h24 : b < 24
          · by_cases h22 : b < 22
            · have heq : b = 21 := by omega
              subst b
              exact checked5250
            · by_cases h23 : b < 23
              · have heq : b = 22 := by omega
                subst b
                exact checked5500
              · have heq : b = 23 := by omega
                subst b
                exact checked5750
          · by_cases h26 : b < 26
            · by_cases h25 : b < 25
              · have heq : b = 24 := by omega
                subst b
                exact checked6000
              · have heq : b = 25 := by omega
                subst b
                exact checked6250
            · by_cases h27 : b < 27
              · have heq : b = 26 := by omega
                subst b
                exact checked6500
              · have heq : b = 27 := by omega
                subst b
                exact checked6750
    · by_cases h42 : b < 42
      · by_cases h35 : b < 35
        · by_cases h31 : b < 31
          · by_cases h29 : b < 29
            · have heq : b = 28 := by omega
              subst b
              exact checked7000
            · by_cases h30 : b < 30
              · have heq : b = 29 := by omega
                subst b
                exact checked7250
              · have heq : b = 30 := by omega
                subst b
                exact checked7500
          · by_cases h33 : b < 33
            · by_cases h32 : b < 32
              · have heq : b = 31 := by omega
                subst b
                exact checked7750
              · have heq : b = 32 := by omega
                subst b
                exact checked8000
            · by_cases h34 : b < 34
              · have heq : b = 33 := by omega
                subst b
                exact checked8250
              · have heq : b = 34 := by omega
                subst b
                exact checked8500
        · by_cases h38 : b < 38
          · by_cases h36 : b < 36
            · have heq : b = 35 := by omega
              subst b
              exact checked8750
            · by_cases h37 : b < 37
              · have heq : b = 36 := by omega
                subst b
                exact checked9000
              · have heq : b = 37 := by omega
                subst b
                exact checked9250
          · by_cases h40 : b < 40
            · by_cases h39 : b < 39
              · have heq : b = 38 := by omega
                subst b
                exact checked9500
              · have heq : b = 39 := by omega
                subst b
                exact checked9750
            · by_cases h41 : b < 41
              · have heq : b = 40 := by omega
                subst b
                exact checked10000
              · have heq : b = 41 := by omega
                subst b
                exact checked10250
      · by_cases h49 : b < 49
        · by_cases h45 : b < 45
          · by_cases h43 : b < 43
            · have heq : b = 42 := by omega
              subst b
              exact checked10500
            · by_cases h44 : b < 44
              · have heq : b = 43 := by omega
                subst b
                exact checked10750
              · have heq : b = 44 := by omega
                subst b
                exact checked11000
          · by_cases h47 : b < 47
            · by_cases h46 : b < 46
              · have heq : b = 45 := by omega
                subst b
                exact checked11250
              · have heq : b = 46 := by omega
                subst b
                exact checked11500
            · by_cases h48 : b < 48
              · have heq : b = 47 := by omega
                subst b
                exact checked11750
              · have heq : b = 48 := by omega
                subst b
                exact checked12000
        · by_cases h52 : b < 52
          · by_cases h50 : b < 50
            · have heq : b = 49 := by omega
              subst b
              exact checked12250
            · by_cases h51 : b < 51
              · have heq : b = 50 := by omega
                subst b
                exact checked12500
              · have heq : b = 51 := by omega
                subst b
                exact checked12750
          · by_cases h54 : b < 54
            · by_cases h53 : b < 53
              · have heq : b = 52 := by omega
                subst b
                exact checked13000
              · have heq : b = 53 := by omega
                subst b
                exact checked13250
            · by_cases h55 : b < 55
              · have heq : b = 54 := by omega
                subst b
                exact checked13500
              · have heq : b = 55 := by omega
                subst b
                exact checked13750
  · by_cases h84 : b < 84
    · by_cases h70 : b < 70
      · by_cases h63 : b < 63
        · by_cases h59 : b < 59
          · by_cases h57 : b < 57
            · have heq : b = 56 := by omega
              subst b
              exact checked14000
            · by_cases h58 : b < 58
              · have heq : b = 57 := by omega
                subst b
                exact checked14250
              · have heq : b = 58 := by omega
                subst b
                exact checked14500
          · by_cases h61 : b < 61
            · by_cases h60 : b < 60
              · have heq : b = 59 := by omega
                subst b
                exact checked14750
              · have heq : b = 60 := by omega
                subst b
                exact checked15000
            · by_cases h62 : b < 62
              · have heq : b = 61 := by omega
                subst b
                exact checked15250
              · have heq : b = 62 := by omega
                subst b
                exact checked15500
        · by_cases h66 : b < 66
          · by_cases h64 : b < 64
            · have heq : b = 63 := by omega
              subst b
              exact checked15750
            · by_cases h65 : b < 65
              · have heq : b = 64 := by omega
                subst b
                exact checked16000
              · have heq : b = 65 := by omega
                subst b
                exact checked16250
          · by_cases h68 : b < 68
            · by_cases h67 : b < 67
              · have heq : b = 66 := by omega
                subst b
                exact checked16500
              · have heq : b = 67 := by omega
                subst b
                exact checked16750
            · by_cases h69 : b < 69
              · have heq : b = 68 := by omega
                subst b
                exact checked17000
              · have heq : b = 69 := by omega
                subst b
                exact checked17250
      · by_cases h77 : b < 77
        · by_cases h73 : b < 73
          · by_cases h71 : b < 71
            · have heq : b = 70 := by omega
              subst b
              exact checked17500
            · by_cases h72 : b < 72
              · have heq : b = 71 := by omega
                subst b
                exact checked17750
              · have heq : b = 72 := by omega
                subst b
                exact checked18000
          · by_cases h75 : b < 75
            · by_cases h74 : b < 74
              · have heq : b = 73 := by omega
                subst b
                exact checked18250
              · have heq : b = 74 := by omega
                subst b
                exact checked18500
            · by_cases h76 : b < 76
              · have heq : b = 75 := by omega
                subst b
                exact checked18750
              · have heq : b = 76 := by omega
                subst b
                exact checked19000
        · by_cases h80 : b < 80
          · by_cases h78 : b < 78
            · have heq : b = 77 := by omega
              subst b
              exact checked19250
            · by_cases h79 : b < 79
              · have heq : b = 78 := by omega
                subst b
                exact checked19500
              · have heq : b = 79 := by omega
                subst b
                exact checked19750
          · by_cases h82 : b < 82
            · by_cases h81 : b < 81
              · have heq : b = 80 := by omega
                subst b
                exact checked20000
              · have heq : b = 81 := by omega
                subst b
                exact checked20250
            · by_cases h83 : b < 83
              · have heq : b = 82 := by omega
                subst b
                exact checked20500
              · have heq : b = 83 := by omega
                subst b
                exact checked20750
    · by_cases h98 : b < 98
      · by_cases h91 : b < 91
        · by_cases h87 : b < 87
          · by_cases h85 : b < 85
            · have heq : b = 84 := by omega
              subst b
              exact checked21000
            · by_cases h86 : b < 86
              · have heq : b = 85 := by omega
                subst b
                exact checked21250
              · have heq : b = 86 := by omega
                subst b
                exact checked21500
          · by_cases h89 : b < 89
            · by_cases h88 : b < 88
              · have heq : b = 87 := by omega
                subst b
                exact checked21750
              · have heq : b = 88 := by omega
                subst b
                exact checked22000
            · by_cases h90 : b < 90
              · have heq : b = 89 := by omega
                subst b
                exact checked22250
              · have heq : b = 90 := by omega
                subst b
                exact checked22500
        · by_cases h94 : b < 94
          · by_cases h92 : b < 92
            · have heq : b = 91 := by omega
              subst b
              exact checked22750
            · by_cases h93 : b < 93
              · have heq : b = 92 := by omega
                subst b
                exact checked23000
              · have heq : b = 93 := by omega
                subst b
                exact checked23250
          · by_cases h96 : b < 96
            · by_cases h95 : b < 95
              · have heq : b = 94 := by omega
                subst b
                exact checked23500
              · have heq : b = 95 := by omega
                subst b
                exact checked23750
            · by_cases h97 : b < 97
              · have heq : b = 96 := by omega
                subst b
                exact checked24000
              · have heq : b = 97 := by omega
                subst b
                exact checked24250
      · by_cases h105 : b < 105
        · by_cases h101 : b < 101
          · by_cases h99 : b < 99
            · have heq : b = 98 := by omega
              subst b
              exact checked24500
            · by_cases h100 : b < 100
              · have heq : b = 99 := by omega
                subst b
                exact checked24750
              · have heq : b = 100 := by omega
                subst b
                exact checked25000
          · by_cases h103 : b < 103
            · by_cases h102 : b < 102
              · have heq : b = 101 := by omega
                subst b
                exact checked25250
              · have heq : b = 102 := by omega
                subst b
                exact checked25500
            · by_cases h104 : b < 104
              · have heq : b = 103 := by omega
                subst b
                exact checked25750
              · have heq : b = 104 := by omega
                subst b
                exact checked26000
        · by_cases h108 : b < 108
          · by_cases h106 : b < 106
            · have heq : b = 105 := by omega
              subst b
              exact checked26250
            · by_cases h107 : b < 107
              · have heq : b = 106 := by omega
                subst b
                exact checked26500
              · have heq : b = 107 := by omega
                subst b
                exact checked26750
          · by_cases h110 : b < 110
            · by_cases h109 : b < 109
              · have heq : b = 108 := by omega
                subst b
                exact checked27000
              · have heq : b = 109 := by omega
                subst b
                exact checked27250
            · by_cases h111 : b < 111
              · have heq : b = 110 := by omega
                subst b
                exact checked27500
              · have heq : b = 111 := by omega
                subst b
                exact checked27750
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The last forest record chunk has its precise smaller size. -/
theorem recordsAt_length (b : Nat) (hb : b < 112) :
    (recordsAt b).length = if b < 111 then 250 else 117 := by
  by_cases h56 : b < 56
  · by_cases h28 : b < 28
    · by_cases h14 : b < 14
      · by_cases h7 : b < 7
        · by_cases h3 : b < 3
          · by_cases h1 : b < 1
            · have heq : b = 0 := by omega
              subst b
              exact length0
            · by_cases h2 : b < 2
              · have heq : b = 1 := by omega
                subst b
                exact length1
              · have heq : b = 2 := by omega
                subst b
                exact length2
          · by_cases h5 : b < 5
            · by_cases h4 : b < 4
              · have heq : b = 3 := by omega
                subst b
                exact length3
              · have heq : b = 4 := by omega
                subst b
                exact length4
            · by_cases h6 : b < 6
              · have heq : b = 5 := by omega
                subst b
                exact length5
              · have heq : b = 6 := by omega
                subst b
                exact length6
        · by_cases h10 : b < 10
          · by_cases h8 : b < 8
            · have heq : b = 7 := by omega
              subst b
              exact length7
            · by_cases h9 : b < 9
              · have heq : b = 8 := by omega
                subst b
                exact length8
              · have heq : b = 9 := by omega
                subst b
                exact length9
          · by_cases h12 : b < 12
            · by_cases h11 : b < 11
              · have heq : b = 10 := by omega
                subst b
                exact length10
              · have heq : b = 11 := by omega
                subst b
                exact length11
            · by_cases h13 : b < 13
              · have heq : b = 12 := by omega
                subst b
                exact length12
              · have heq : b = 13 := by omega
                subst b
                exact length13
      · by_cases h21 : b < 21
        · by_cases h17 : b < 17
          · by_cases h15 : b < 15
            · have heq : b = 14 := by omega
              subst b
              exact length14
            · by_cases h16 : b < 16
              · have heq : b = 15 := by omega
                subst b
                exact length15
              · have heq : b = 16 := by omega
                subst b
                exact length16
          · by_cases h19 : b < 19
            · by_cases h18 : b < 18
              · have heq : b = 17 := by omega
                subst b
                exact length17
              · have heq : b = 18 := by omega
                subst b
                exact length18
            · by_cases h20 : b < 20
              · have heq : b = 19 := by omega
                subst b
                exact length19
              · have heq : b = 20 := by omega
                subst b
                exact length20
        · by_cases h24 : b < 24
          · by_cases h22 : b < 22
            · have heq : b = 21 := by omega
              subst b
              exact length21
            · by_cases h23 : b < 23
              · have heq : b = 22 := by omega
                subst b
                exact length22
              · have heq : b = 23 := by omega
                subst b
                exact length23
          · by_cases h26 : b < 26
            · by_cases h25 : b < 25
              · have heq : b = 24 := by omega
                subst b
                exact length24
              · have heq : b = 25 := by omega
                subst b
                exact length25
            · by_cases h27 : b < 27
              · have heq : b = 26 := by omega
                subst b
                exact length26
              · have heq : b = 27 := by omega
                subst b
                exact length27
    · by_cases h42 : b < 42
      · by_cases h35 : b < 35
        · by_cases h31 : b < 31
          · by_cases h29 : b < 29
            · have heq : b = 28 := by omega
              subst b
              exact length28
            · by_cases h30 : b < 30
              · have heq : b = 29 := by omega
                subst b
                exact length29
              · have heq : b = 30 := by omega
                subst b
                exact length30
          · by_cases h33 : b < 33
            · by_cases h32 : b < 32
              · have heq : b = 31 := by omega
                subst b
                exact length31
              · have heq : b = 32 := by omega
                subst b
                exact length32
            · by_cases h34 : b < 34
              · have heq : b = 33 := by omega
                subst b
                exact length33
              · have heq : b = 34 := by omega
                subst b
                exact length34
        · by_cases h38 : b < 38
          · by_cases h36 : b < 36
            · have heq : b = 35 := by omega
              subst b
              exact length35
            · by_cases h37 : b < 37
              · have heq : b = 36 := by omega
                subst b
                exact length36
              · have heq : b = 37 := by omega
                subst b
                exact length37
          · by_cases h40 : b < 40
            · by_cases h39 : b < 39
              · have heq : b = 38 := by omega
                subst b
                exact length38
              · have heq : b = 39 := by omega
                subst b
                exact length39
            · by_cases h41 : b < 41
              · have heq : b = 40 := by omega
                subst b
                exact length40
              · have heq : b = 41 := by omega
                subst b
                exact length41
      · by_cases h49 : b < 49
        · by_cases h45 : b < 45
          · by_cases h43 : b < 43
            · have heq : b = 42 := by omega
              subst b
              exact length42
            · by_cases h44 : b < 44
              · have heq : b = 43 := by omega
                subst b
                exact length43
              · have heq : b = 44 := by omega
                subst b
                exact length44
          · by_cases h47 : b < 47
            · by_cases h46 : b < 46
              · have heq : b = 45 := by omega
                subst b
                exact length45
              · have heq : b = 46 := by omega
                subst b
                exact length46
            · by_cases h48 : b < 48
              · have heq : b = 47 := by omega
                subst b
                exact length47
              · have heq : b = 48 := by omega
                subst b
                exact length48
        · by_cases h52 : b < 52
          · by_cases h50 : b < 50
            · have heq : b = 49 := by omega
              subst b
              exact length49
            · by_cases h51 : b < 51
              · have heq : b = 50 := by omega
                subst b
                exact length50
              · have heq : b = 51 := by omega
                subst b
                exact length51
          · by_cases h54 : b < 54
            · by_cases h53 : b < 53
              · have heq : b = 52 := by omega
                subst b
                exact length52
              · have heq : b = 53 := by omega
                subst b
                exact length53
            · by_cases h55 : b < 55
              · have heq : b = 54 := by omega
                subst b
                exact length54
              · have heq : b = 55 := by omega
                subst b
                exact length55
  · by_cases h84 : b < 84
    · by_cases h70 : b < 70
      · by_cases h63 : b < 63
        · by_cases h59 : b < 59
          · by_cases h57 : b < 57
            · have heq : b = 56 := by omega
              subst b
              exact length56
            · by_cases h58 : b < 58
              · have heq : b = 57 := by omega
                subst b
                exact length57
              · have heq : b = 58 := by omega
                subst b
                exact length58
          · by_cases h61 : b < 61
            · by_cases h60 : b < 60
              · have heq : b = 59 := by omega
                subst b
                exact length59
              · have heq : b = 60 := by omega
                subst b
                exact length60
            · by_cases h62 : b < 62
              · have heq : b = 61 := by omega
                subst b
                exact length61
              · have heq : b = 62 := by omega
                subst b
                exact length62
        · by_cases h66 : b < 66
          · by_cases h64 : b < 64
            · have heq : b = 63 := by omega
              subst b
              exact length63
            · by_cases h65 : b < 65
              · have heq : b = 64 := by omega
                subst b
                exact length64
              · have heq : b = 65 := by omega
                subst b
                exact length65
          · by_cases h68 : b < 68
            · by_cases h67 : b < 67
              · have heq : b = 66 := by omega
                subst b
                exact length66
              · have heq : b = 67 := by omega
                subst b
                exact length67
            · by_cases h69 : b < 69
              · have heq : b = 68 := by omega
                subst b
                exact length68
              · have heq : b = 69 := by omega
                subst b
                exact length69
      · by_cases h77 : b < 77
        · by_cases h73 : b < 73
          · by_cases h71 : b < 71
            · have heq : b = 70 := by omega
              subst b
              exact length70
            · by_cases h72 : b < 72
              · have heq : b = 71 := by omega
                subst b
                exact length71
              · have heq : b = 72 := by omega
                subst b
                exact length72
          · by_cases h75 : b < 75
            · by_cases h74 : b < 74
              · have heq : b = 73 := by omega
                subst b
                exact length73
              · have heq : b = 74 := by omega
                subst b
                exact length74
            · by_cases h76 : b < 76
              · have heq : b = 75 := by omega
                subst b
                exact length75
              · have heq : b = 76 := by omega
                subst b
                exact length76
        · by_cases h80 : b < 80
          · by_cases h78 : b < 78
            · have heq : b = 77 := by omega
              subst b
              exact length77
            · by_cases h79 : b < 79
              · have heq : b = 78 := by omega
                subst b
                exact length78
              · have heq : b = 79 := by omega
                subst b
                exact length79
          · by_cases h82 : b < 82
            · by_cases h81 : b < 81
              · have heq : b = 80 := by omega
                subst b
                exact length80
              · have heq : b = 81 := by omega
                subst b
                exact length81
            · by_cases h83 : b < 83
              · have heq : b = 82 := by omega
                subst b
                exact length82
              · have heq : b = 83 := by omega
                subst b
                exact length83
    · by_cases h98 : b < 98
      · by_cases h91 : b < 91
        · by_cases h87 : b < 87
          · by_cases h85 : b < 85
            · have heq : b = 84 := by omega
              subst b
              exact length84
            · by_cases h86 : b < 86
              · have heq : b = 85 := by omega
                subst b
                exact length85
              · have heq : b = 86 := by omega
                subst b
                exact length86
          · by_cases h89 : b < 89
            · by_cases h88 : b < 88
              · have heq : b = 87 := by omega
                subst b
                exact length87
              · have heq : b = 88 := by omega
                subst b
                exact length88
            · by_cases h90 : b < 90
              · have heq : b = 89 := by omega
                subst b
                exact length89
              · have heq : b = 90 := by omega
                subst b
                exact length90
        · by_cases h94 : b < 94
          · by_cases h92 : b < 92
            · have heq : b = 91 := by omega
              subst b
              exact length91
            · by_cases h93 : b < 93
              · have heq : b = 92 := by omega
                subst b
                exact length92
              · have heq : b = 93 := by omega
                subst b
                exact length93
          · by_cases h96 : b < 96
            · by_cases h95 : b < 95
              · have heq : b = 94 := by omega
                subst b
                exact length94
              · have heq : b = 95 := by omega
                subst b
                exact length95
            · by_cases h97 : b < 97
              · have heq : b = 96 := by omega
                subst b
                exact length96
              · have heq : b = 97 := by omega
                subst b
                exact length97
      · by_cases h105 : b < 105
        · by_cases h101 : b < 101
          · by_cases h99 : b < 99
            · have heq : b = 98 := by omega
              subst b
              exact length98
            · by_cases h100 : b < 100
              · have heq : b = 99 := by omega
                subst b
                exact length99
              · have heq : b = 100 := by omega
                subst b
                exact length100
          · by_cases h103 : b < 103
            · by_cases h102 : b < 102
              · have heq : b = 101 := by omega
                subst b
                exact length101
              · have heq : b = 102 := by omega
                subst b
                exact length102
            · by_cases h104 : b < 104
              · have heq : b = 103 := by omega
                subst b
                exact length103
              · have heq : b = 104 := by omega
                subst b
                exact length104
        · by_cases h108 : b < 108
          · by_cases h106 : b < 106
            · have heq : b = 105 := by omega
              subst b
              exact length105
            · by_cases h107 : b < 107
              · have heq : b = 106 := by omega
                subst b
                exact length106
              · have heq : b = 107 := by omega
                subst b
                exact length107
          · by_cases h110 : b < 110
            · by_cases h109 : b < 109
              · have heq : b = 108 := by omega
                subst b
                exact length108
              · have heq : b = 109 := by omega
                subst b
                exact length109
            · by_cases h111 : b < 111
              · have heq : b = 110 := by omega
                subst b
                exact length110
              · have heq : b = 111 := by omega
                subst b
                exact length111
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- A valid global fiber index selects a real record of its chunk. -/
theorem fiberAt_mem (i : Fin 27867) : fiberAt i.val ∈ recordsAt (i.val/250) := by
  have hm := Nat.mod_lt i.val (by decide : 0 < 250)
  have he := Nat.mod_add_div i.val 250
  have hb : i.val/250 < 112 := by omega
  have hi : i.val%250 < (recordsAt (i.val/250)).length := by
    rw [recordsAt_length _ hb]
    split_ifs <;> omega
  unfold fiberAt
  rw [List.getD_eq_getElem _ _ hi]
  exact List.getElem_mem hi
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every valid global forest record passes the structural checker. -/
theorem fiberAt_checked (i : Fin 27867) : fiberCheck (fiberAt i.val) = true :=
  groupCheck_member _ (recordsAt_checked _ (by omega)) _ (fiberAt_mem i)
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every shallow forest solution above a listed outside support reaches the common top bank. -/
theorem fiberAt_complete (i : Fin 27867) (word : Nat)
    (he : reconX bottomEColumns word = reconX bottomRColumns (fiberAt i.val).beta)
    (hoff : outsideMask word (fiberAt i.val).beta ∈ (fiberAt i.val).seeds.map Seed.off) :
    ∃ j : Fin 58130, bottomJoin word (fiberAt i.val).beta = topBankMask j ∨
      bottomJoin (word ^^^ (fiberAt i.val).beta) (fiberAt i.val).beta = topBankMask j :=
  group_solution_bank _ (recordsAt_checked _ (by omega)) _ (fiberAt_mem i) word he hoff
#print axioms fiberAt_complete
end Quantum.Stabilizer.Homological.BB.Bravyi360.BottomForest
