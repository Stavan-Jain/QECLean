/-
GENERATED FILE — DO NOT HAND-EDIT
Generator: qec-lab:experiments/bb_lab/scripts/bravyi360_kernel/generate.py
Emitter, relative to generator directory:
  emitters/compression_positive_one_global.py
Data and SHA-256 hashes: compression_manifest.json
Regenerate:
  QECLEAN_ROOT=/path/to/QECLean \
    python3 experiments/bb_lab/scripts/bravyi360_kernel/generate.py --force
-/

import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.BottomForest
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.BottomPositiveOnePart0
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.BottomPositiveOnePart1
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.BottomPositiveOnePart2
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.BottomPositiveOnePart3
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.BottomPositiveOnePart4
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.BottomPositiveOnePart5
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.BottomPositiveOnePart6
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.BottomPositiveOnePart7
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.BottomPositiveOnePart8
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.BottomPositiveOnePart9
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.BottomPositiveOnePart10
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.BottomPositiveOnePart11
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.BottomPositiveOnePart12
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.BottomPositiveOnePart13

noncomputable section
set_option maxRecDepth 100000
namespace Quantum.Stabilizer.Homological.BB.Bravyi360.BottomForest
open F2Mask FiberData
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every cap-one forest chunk has complete outside-support seeds. -/
theorem one_records_complete (b : Nat) (hb : b < 112) (r : Fiber)
    (hr : r ∈ recordsAt b) (hweight : r.weight = 20)
    (word : Nat) (hw : word < 2^90)
    (he : reconX bottomEColumns word = reconX bottomRColumns r.beta)
    (hoff : bitCount 90 (outsideMask word r.beta) ≤ 1) :
    outsideMask word r.beta ∈ r.seeds.map Seed.off := by
  by_cases h56 : b < 56
  · by_cases h28 : b < 28
    · by_cases h14 : b < 14
      · by_cases h7 : b < 7
        · by_cases h3 : b < 3
          · by_cases h1 : b < 1
            · have heq : b = 0 := by omega
              subst b
              exact oneGroup_complete records0 oneCovers0 onePacked0 checked0 oneChecked0 r hr hweight word hw he hoff
            · by_cases h2 : b < 2
              · have heq : b = 1 := by omega
                subst b
                exact oneGroup_complete records250 oneCovers250 onePacked250 checked250 oneChecked250 r hr hweight word hw he hoff
              · have heq : b = 2 := by omega
                subst b
                exact oneGroup_complete records500 oneCovers500 onePacked500 checked500 oneChecked500 r hr hweight word hw he hoff
          · by_cases h5 : b < 5
            · by_cases h4 : b < 4
              · have heq : b = 3 := by omega
                subst b
                exact oneGroup_complete records750 oneCovers750 onePacked750 checked750 oneChecked750 r hr hweight word hw he hoff
              · have heq : b = 4 := by omega
                subst b
                exact oneGroup_complete records1000 oneCovers1000 onePacked1000 checked1000 oneChecked1000 r hr hweight word hw he hoff
            · by_cases h6 : b < 6
              · have heq : b = 5 := by omega
                subst b
                exact oneGroup_complete records1250 oneCovers1250 onePacked1250 checked1250 oneChecked1250 r hr hweight word hw he hoff
              · have heq : b = 6 := by omega
                subst b
                exact oneGroup_complete records1500 oneCovers1500 onePacked1500 checked1500 oneChecked1500 r hr hweight word hw he hoff
        · by_cases h10 : b < 10
          · by_cases h8 : b < 8
            · have heq : b = 7 := by omega
              subst b
              exact oneGroup_complete records1750 oneCovers1750 onePacked1750 checked1750 oneChecked1750 r hr hweight word hw he hoff
            · by_cases h9 : b < 9
              · have heq : b = 8 := by omega
                subst b
                exact oneGroup_complete records2000 oneCovers2000 onePacked2000 checked2000 oneChecked2000 r hr hweight word hw he hoff
              · have heq : b = 9 := by omega
                subst b
                exact oneGroup_complete records2250 oneCovers2250 onePacked2250 checked2250 oneChecked2250 r hr hweight word hw he hoff
          · by_cases h12 : b < 12
            · by_cases h11 : b < 11
              · have heq : b = 10 := by omega
                subst b
                exact oneGroup_complete records2500 oneCovers2500 onePacked2500 checked2500 oneChecked2500 r hr hweight word hw he hoff
              · have heq : b = 11 := by omega
                subst b
                exact oneGroup_complete records2750 oneCovers2750 onePacked2750 checked2750 oneChecked2750 r hr hweight word hw he hoff
            · by_cases h13 : b < 13
              · have heq : b = 12 := by omega
                subst b
                exact oneGroup_complete records3000 oneCovers3000 onePacked3000 checked3000 oneChecked3000 r hr hweight word hw he hoff
              · have heq : b = 13 := by omega
                subst b
                exact oneGroup_complete records3250 oneCovers3250 onePacked3250 checked3250 oneChecked3250 r hr hweight word hw he hoff
      · by_cases h21 : b < 21
        · by_cases h17 : b < 17
          · by_cases h15 : b < 15
            · have heq : b = 14 := by omega
              subst b
              exact oneGroup_complete records3500 oneCovers3500 onePacked3500 checked3500 oneChecked3500 r hr hweight word hw he hoff
            · by_cases h16 : b < 16
              · have heq : b = 15 := by omega
                subst b
                exact oneGroup_complete records3750 oneCovers3750 onePacked3750 checked3750 oneChecked3750 r hr hweight word hw he hoff
              · have heq : b = 16 := by omega
                subst b
                exact oneGroup_complete records4000 oneCovers4000 onePacked4000 checked4000 oneChecked4000 r hr hweight word hw he hoff
          · by_cases h19 : b < 19
            · by_cases h18 : b < 18
              · have heq : b = 17 := by omega
                subst b
                exact oneGroup_complete records4250 oneCovers4250 onePacked4250 checked4250 oneChecked4250 r hr hweight word hw he hoff
              · have heq : b = 18 := by omega
                subst b
                exact oneGroup_complete records4500 oneCovers4500 onePacked4500 checked4500 oneChecked4500 r hr hweight word hw he hoff
            · by_cases h20 : b < 20
              · have heq : b = 19 := by omega
                subst b
                exact oneGroup_complete records4750 oneCovers4750 onePacked4750 checked4750 oneChecked4750 r hr hweight word hw he hoff
              · have heq : b = 20 := by omega
                subst b
                exact oneGroup_complete records5000 oneCovers5000 onePacked5000 checked5000 oneChecked5000 r hr hweight word hw he hoff
        · by_cases h24 : b < 24
          · by_cases h22 : b < 22
            · have heq : b = 21 := by omega
              subst b
              exact oneGroup_complete records5250 oneCovers5250 onePacked5250 checked5250 oneChecked5250 r hr hweight word hw he hoff
            · by_cases h23 : b < 23
              · have heq : b = 22 := by omega
                subst b
                exact oneGroup_complete records5500 oneCovers5500 onePacked5500 checked5500 oneChecked5500 r hr hweight word hw he hoff
              · have heq : b = 23 := by omega
                subst b
                exact oneGroup_complete records5750 oneCovers5750 onePacked5750 checked5750 oneChecked5750 r hr hweight word hw he hoff
          · by_cases h26 : b < 26
            · by_cases h25 : b < 25
              · have heq : b = 24 := by omega
                subst b
                exact oneGroup_complete records6000 oneCovers6000 onePacked6000 checked6000 oneChecked6000 r hr hweight word hw he hoff
              · have heq : b = 25 := by omega
                subst b
                exact oneGroup_complete records6250 oneCovers6250 onePacked6250 checked6250 oneChecked6250 r hr hweight word hw he hoff
            · by_cases h27 : b < 27
              · have heq : b = 26 := by omega
                subst b
                exact oneGroup_complete records6500 oneCovers6500 onePacked6500 checked6500 oneChecked6500 r hr hweight word hw he hoff
              · have heq : b = 27 := by omega
                subst b
                exact oneGroup_complete records6750 oneCovers6750 onePacked6750 checked6750 oneChecked6750 r hr hweight word hw he hoff
    · by_cases h42 : b < 42
      · by_cases h35 : b < 35
        · by_cases h31 : b < 31
          · by_cases h29 : b < 29
            · have heq : b = 28 := by omega
              subst b
              exact oneGroup_complete records7000 oneCovers7000 onePacked7000 checked7000 oneChecked7000 r hr hweight word hw he hoff
            · by_cases h30 : b < 30
              · have heq : b = 29 := by omega
                subst b
                exact oneGroup_complete records7250 oneCovers7250 onePacked7250 checked7250 oneChecked7250 r hr hweight word hw he hoff
              · have heq : b = 30 := by omega
                subst b
                exact oneGroup_complete records7500 oneCovers7500 onePacked7500 checked7500 oneChecked7500 r hr hweight word hw he hoff
          · by_cases h33 : b < 33
            · by_cases h32 : b < 32
              · have heq : b = 31 := by omega
                subst b
                exact oneGroup_complete records7750 oneCovers7750 onePacked7750 checked7750 oneChecked7750 r hr hweight word hw he hoff
              · have heq : b = 32 := by omega
                subst b
                exact oneGroup_complete records8000 oneCovers8000 onePacked8000 checked8000 oneChecked8000 r hr hweight word hw he hoff
            · by_cases h34 : b < 34
              · have heq : b = 33 := by omega
                subst b
                exact oneGroup_complete records8250 oneCovers8250 onePacked8250 checked8250 oneChecked8250 r hr hweight word hw he hoff
              · have heq : b = 34 := by omega
                subst b
                exact oneGroup_complete records8500 oneCovers8500 onePacked8500 checked8500 oneChecked8500 r hr hweight word hw he hoff
        · by_cases h38 : b < 38
          · by_cases h36 : b < 36
            · have heq : b = 35 := by omega
              subst b
              exact oneGroup_complete records8750 oneCovers8750 onePacked8750 checked8750 oneChecked8750 r hr hweight word hw he hoff
            · by_cases h37 : b < 37
              · have heq : b = 36 := by omega
                subst b
                exact oneGroup_complete records9000 oneCovers9000 onePacked9000 checked9000 oneChecked9000 r hr hweight word hw he hoff
              · have heq : b = 37 := by omega
                subst b
                exact oneGroup_complete records9250 oneCovers9250 onePacked9250 checked9250 oneChecked9250 r hr hweight word hw he hoff
          · by_cases h40 : b < 40
            · by_cases h39 : b < 39
              · have heq : b = 38 := by omega
                subst b
                exact oneGroup_complete records9500 oneCovers9500 onePacked9500 checked9500 oneChecked9500 r hr hweight word hw he hoff
              · have heq : b = 39 := by omega
                subst b
                exact oneGroup_complete records9750 oneCovers9750 onePacked9750 checked9750 oneChecked9750 r hr hweight word hw he hoff
            · by_cases h41 : b < 41
              · have heq : b = 40 := by omega
                subst b
                exact oneGroup_complete records10000 oneCovers10000 onePacked10000 checked10000 oneChecked10000 r hr hweight word hw he hoff
              · have heq : b = 41 := by omega
                subst b
                exact oneGroup_complete records10250 oneCovers10250 onePacked10250 checked10250 oneChecked10250 r hr hweight word hw he hoff
      · by_cases h49 : b < 49
        · by_cases h45 : b < 45
          · by_cases h43 : b < 43
            · have heq : b = 42 := by omega
              subst b
              exact oneGroup_complete records10500 oneCovers10500 onePacked10500 checked10500 oneChecked10500 r hr hweight word hw he hoff
            · by_cases h44 : b < 44
              · have heq : b = 43 := by omega
                subst b
                exact oneGroup_complete records10750 oneCovers10750 onePacked10750 checked10750 oneChecked10750 r hr hweight word hw he hoff
              · have heq : b = 44 := by omega
                subst b
                exact oneGroup_complete records11000 oneCovers11000 onePacked11000 checked11000 oneChecked11000 r hr hweight word hw he hoff
          · by_cases h47 : b < 47
            · by_cases h46 : b < 46
              · have heq : b = 45 := by omega
                subst b
                exact oneGroup_complete records11250 oneCovers11250 onePacked11250 checked11250 oneChecked11250 r hr hweight word hw he hoff
              · have heq : b = 46 := by omega
                subst b
                exact oneGroup_complete records11500 oneCovers11500 onePacked11500 checked11500 oneChecked11500 r hr hweight word hw he hoff
            · by_cases h48 : b < 48
              · have heq : b = 47 := by omega
                subst b
                exact oneGroup_complete records11750 oneCovers11750 onePacked11750 checked11750 oneChecked11750 r hr hweight word hw he hoff
              · have heq : b = 48 := by omega
                subst b
                exact oneGroup_complete records12000 oneCovers12000 onePacked12000 checked12000 oneChecked12000 r hr hweight word hw he hoff
        · by_cases h52 : b < 52
          · by_cases h50 : b < 50
            · have heq : b = 49 := by omega
              subst b
              exact oneGroup_complete records12250 oneCovers12250 onePacked12250 checked12250 oneChecked12250 r hr hweight word hw he hoff
            · by_cases h51 : b < 51
              · have heq : b = 50 := by omega
                subst b
                exact oneGroup_complete records12500 oneCovers12500 onePacked12500 checked12500 oneChecked12500 r hr hweight word hw he hoff
              · have heq : b = 51 := by omega
                subst b
                exact oneGroup_complete records12750 oneCovers12750 onePacked12750 checked12750 oneChecked12750 r hr hweight word hw he hoff
          · by_cases h54 : b < 54
            · by_cases h53 : b < 53
              · have heq : b = 52 := by omega
                subst b
                exact oneGroup_complete records13000 oneCovers13000 onePacked13000 checked13000 oneChecked13000 r hr hweight word hw he hoff
              · have heq : b = 53 := by omega
                subst b
                exact oneGroup_complete records13250 oneCovers13250 onePacked13250 checked13250 oneChecked13250 r hr hweight word hw he hoff
            · by_cases h55 : b < 55
              · have heq : b = 54 := by omega
                subst b
                exact oneGroup_complete records13500 oneCovers13500 onePacked13500 checked13500 oneChecked13500 r hr hweight word hw he hoff
              · have heq : b = 55 := by omega
                subst b
                exact oneGroup_complete records13750 oneCovers13750 onePacked13750 checked13750 oneChecked13750 r hr hweight word hw he hoff
  · by_cases h84 : b < 84
    · by_cases h70 : b < 70
      · by_cases h63 : b < 63
        · by_cases h59 : b < 59
          · by_cases h57 : b < 57
            · have heq : b = 56 := by omega
              subst b
              exact oneGroup_complete records14000 oneCovers14000 onePacked14000 checked14000 oneChecked14000 r hr hweight word hw he hoff
            · by_cases h58 : b < 58
              · have heq : b = 57 := by omega
                subst b
                exact oneGroup_complete records14250 oneCovers14250 onePacked14250 checked14250 oneChecked14250 r hr hweight word hw he hoff
              · have heq : b = 58 := by omega
                subst b
                exact oneGroup_complete records14500 oneCovers14500 onePacked14500 checked14500 oneChecked14500 r hr hweight word hw he hoff
          · by_cases h61 : b < 61
            · by_cases h60 : b < 60
              · have heq : b = 59 := by omega
                subst b
                exact oneGroup_complete records14750 oneCovers14750 onePacked14750 checked14750 oneChecked14750 r hr hweight word hw he hoff
              · have heq : b = 60 := by omega
                subst b
                exact oneGroup_complete records15000 oneCovers15000 onePacked15000 checked15000 oneChecked15000 r hr hweight word hw he hoff
            · by_cases h62 : b < 62
              · have heq : b = 61 := by omega
                subst b
                exact oneGroup_complete records15250 oneCovers15250 onePacked15250 checked15250 oneChecked15250 r hr hweight word hw he hoff
              · have heq : b = 62 := by omega
                subst b
                exact oneGroup_complete records15500 oneCovers15500 onePacked15500 checked15500 oneChecked15500 r hr hweight word hw he hoff
        · by_cases h66 : b < 66
          · by_cases h64 : b < 64
            · have heq : b = 63 := by omega
              subst b
              exact oneGroup_complete records15750 oneCovers15750 onePacked15750 checked15750 oneChecked15750 r hr hweight word hw he hoff
            · by_cases h65 : b < 65
              · have heq : b = 64 := by omega
                subst b
                exact oneGroup_complete records16000 oneCovers16000 onePacked16000 checked16000 oneChecked16000 r hr hweight word hw he hoff
              · have heq : b = 65 := by omega
                subst b
                exact oneGroup_complete records16250 oneCovers16250 onePacked16250 checked16250 oneChecked16250 r hr hweight word hw he hoff
          · by_cases h68 : b < 68
            · by_cases h67 : b < 67
              · have heq : b = 66 := by omega
                subst b
                exact oneGroup_complete records16500 oneCovers16500 onePacked16500 checked16500 oneChecked16500 r hr hweight word hw he hoff
              · have heq : b = 67 := by omega
                subst b
                exact oneGroup_complete records16750 oneCovers16750 onePacked16750 checked16750 oneChecked16750 r hr hweight word hw he hoff
            · by_cases h69 : b < 69
              · have heq : b = 68 := by omega
                subst b
                exact oneGroup_complete records17000 oneCovers17000 onePacked17000 checked17000 oneChecked17000 r hr hweight word hw he hoff
              · have heq : b = 69 := by omega
                subst b
                exact oneGroup_complete records17250 oneCovers17250 onePacked17250 checked17250 oneChecked17250 r hr hweight word hw he hoff
      · by_cases h77 : b < 77
        · by_cases h73 : b < 73
          · by_cases h71 : b < 71
            · have heq : b = 70 := by omega
              subst b
              exact oneGroup_complete records17500 oneCovers17500 onePacked17500 checked17500 oneChecked17500 r hr hweight word hw he hoff
            · by_cases h72 : b < 72
              · have heq : b = 71 := by omega
                subst b
                exact oneGroup_complete records17750 oneCovers17750 onePacked17750 checked17750 oneChecked17750 r hr hweight word hw he hoff
              · have heq : b = 72 := by omega
                subst b
                exact oneGroup_complete records18000 oneCovers18000 onePacked18000 checked18000 oneChecked18000 r hr hweight word hw he hoff
          · by_cases h75 : b < 75
            · by_cases h74 : b < 74
              · have heq : b = 73 := by omega
                subst b
                exact oneGroup_complete records18250 oneCovers18250 onePacked18250 checked18250 oneChecked18250 r hr hweight word hw he hoff
              · have heq : b = 74 := by omega
                subst b
                exact oneGroup_complete records18500 oneCovers18500 onePacked18500 checked18500 oneChecked18500 r hr hweight word hw he hoff
            · by_cases h76 : b < 76
              · have heq : b = 75 := by omega
                subst b
                exact oneGroup_complete records18750 oneCovers18750 onePacked18750 checked18750 oneChecked18750 r hr hweight word hw he hoff
              · have heq : b = 76 := by omega
                subst b
                exact oneGroup_complete records19000 oneCovers19000 onePacked19000 checked19000 oneChecked19000 r hr hweight word hw he hoff
        · by_cases h80 : b < 80
          · by_cases h78 : b < 78
            · have heq : b = 77 := by omega
              subst b
              exact oneGroup_complete records19250 oneCovers19250 onePacked19250 checked19250 oneChecked19250 r hr hweight word hw he hoff
            · by_cases h79 : b < 79
              · have heq : b = 78 := by omega
                subst b
                exact oneGroup_complete records19500 oneCovers19500 onePacked19500 checked19500 oneChecked19500 r hr hweight word hw he hoff
              · have heq : b = 79 := by omega
                subst b
                exact oneGroup_complete records19750 oneCovers19750 onePacked19750 checked19750 oneChecked19750 r hr hweight word hw he hoff
          · by_cases h82 : b < 82
            · by_cases h81 : b < 81
              · have heq : b = 80 := by omega
                subst b
                exact oneGroup_complete records20000 oneCovers20000 onePacked20000 checked20000 oneChecked20000 r hr hweight word hw he hoff
              · have heq : b = 81 := by omega
                subst b
                exact oneGroup_complete records20250 oneCovers20250 onePacked20250 checked20250 oneChecked20250 r hr hweight word hw he hoff
            · by_cases h83 : b < 83
              · have heq : b = 82 := by omega
                subst b
                exact oneGroup_complete records20500 oneCovers20500 onePacked20500 checked20500 oneChecked20500 r hr hweight word hw he hoff
              · have heq : b = 83 := by omega
                subst b
                exact oneGroup_complete records20750 oneCovers20750 onePacked20750 checked20750 oneChecked20750 r hr hweight word hw he hoff
    · by_cases h98 : b < 98
      · by_cases h91 : b < 91
        · by_cases h87 : b < 87
          · by_cases h85 : b < 85
            · have heq : b = 84 := by omega
              subst b
              exact oneGroup_complete records21000 oneCovers21000 onePacked21000 checked21000 oneChecked21000 r hr hweight word hw he hoff
            · by_cases h86 : b < 86
              · have heq : b = 85 := by omega
                subst b
                exact oneGroup_complete records21250 oneCovers21250 onePacked21250 checked21250 oneChecked21250 r hr hweight word hw he hoff
              · have heq : b = 86 := by omega
                subst b
                exact oneGroup_complete records21500 oneCovers21500 onePacked21500 checked21500 oneChecked21500 r hr hweight word hw he hoff
          · by_cases h89 : b < 89
            · by_cases h88 : b < 88
              · have heq : b = 87 := by omega
                subst b
                exact oneGroup_complete records21750 oneCovers21750 onePacked21750 checked21750 oneChecked21750 r hr hweight word hw he hoff
              · have heq : b = 88 := by omega
                subst b
                exact oneGroup_complete records22000 oneCovers22000 onePacked22000 checked22000 oneChecked22000 r hr hweight word hw he hoff
            · by_cases h90 : b < 90
              · have heq : b = 89 := by omega
                subst b
                exact oneGroup_complete records22250 oneCovers22250 onePacked22250 checked22250 oneChecked22250 r hr hweight word hw he hoff
              · have heq : b = 90 := by omega
                subst b
                exact oneGroup_complete records22500 oneCovers22500 onePacked22500 checked22500 oneChecked22500 r hr hweight word hw he hoff
        · by_cases h94 : b < 94
          · by_cases h92 : b < 92
            · have heq : b = 91 := by omega
              subst b
              exact oneGroup_complete records22750 oneCovers22750 onePacked22750 checked22750 oneChecked22750 r hr hweight word hw he hoff
            · by_cases h93 : b < 93
              · have heq : b = 92 := by omega
                subst b
                exact oneGroup_complete records23000 oneCovers23000 onePacked23000 checked23000 oneChecked23000 r hr hweight word hw he hoff
              · have heq : b = 93 := by omega
                subst b
                exact oneGroup_complete records23250 oneCovers23250 onePacked23250 checked23250 oneChecked23250 r hr hweight word hw he hoff
          · by_cases h96 : b < 96
            · by_cases h95 : b < 95
              · have heq : b = 94 := by omega
                subst b
                exact oneGroup_complete records23500 oneCovers23500 onePacked23500 checked23500 oneChecked23500 r hr hweight word hw he hoff
              · have heq : b = 95 := by omega
                subst b
                exact oneGroup_complete records23750 oneCovers23750 onePacked23750 checked23750 oneChecked23750 r hr hweight word hw he hoff
            · by_cases h97 : b < 97
              · have heq : b = 96 := by omega
                subst b
                exact oneGroup_complete records24000 oneCovers24000 onePacked24000 checked24000 oneChecked24000 r hr hweight word hw he hoff
              · have heq : b = 97 := by omega
                subst b
                exact oneGroup_complete records24250 oneCovers24250 onePacked24250 checked24250 oneChecked24250 r hr hweight word hw he hoff
      · by_cases h105 : b < 105
        · by_cases h101 : b < 101
          · by_cases h99 : b < 99
            · have heq : b = 98 := by omega
              subst b
              exact oneGroup_complete records24500 oneCovers24500 onePacked24500 checked24500 oneChecked24500 r hr hweight word hw he hoff
            · by_cases h100 : b < 100
              · have heq : b = 99 := by omega
                subst b
                exact oneGroup_complete records24750 oneCovers24750 onePacked24750 checked24750 oneChecked24750 r hr hweight word hw he hoff
              · have heq : b = 100 := by omega
                subst b
                exact oneGroup_complete records25000 oneCovers25000 onePacked25000 checked25000 oneChecked25000 r hr hweight word hw he hoff
          · by_cases h103 : b < 103
            · by_cases h102 : b < 102
              · have heq : b = 101 := by omega
                subst b
                exact oneGroup_complete records25250 oneCovers25250 onePacked25250 checked25250 oneChecked25250 r hr hweight word hw he hoff
              · have heq : b = 102 := by omega
                subst b
                exact oneGroup_complete records25500 oneCovers25500 onePacked25500 checked25500 oneChecked25500 r hr hweight word hw he hoff
            · by_cases h104 : b < 104
              · have heq : b = 103 := by omega
                subst b
                exact oneGroup_complete records25750 oneCovers25750 onePacked25750 checked25750 oneChecked25750 r hr hweight word hw he hoff
              · have heq : b = 104 := by omega
                subst b
                exact oneGroup_complete records26000 oneCovers26000 onePacked26000 checked26000 oneChecked26000 r hr hweight word hw he hoff
        · by_cases h108 : b < 108
          · by_cases h106 : b < 106
            · have heq : b = 105 := by omega
              subst b
              exact oneGroup_complete records26250 oneCovers26250 onePacked26250 checked26250 oneChecked26250 r hr hweight word hw he hoff
            · by_cases h107 : b < 107
              · have heq : b = 106 := by omega
                subst b
                exact oneGroup_complete records26500 oneCovers26500 onePacked26500 checked26500 oneChecked26500 r hr hweight word hw he hoff
              · have heq : b = 107 := by omega
                subst b
                exact oneGroup_complete records26750 oneCovers26750 onePacked26750 checked26750 oneChecked26750 r hr hweight word hw he hoff
          · by_cases h110 : b < 110
            · by_cases h109 : b < 109
              · have heq : b = 108 := by omega
                subst b
                exact oneGroup_complete records27000 oneCovers27000 onePacked27000 checked27000 oneChecked27000 r hr hweight word hw he hoff
              · have heq : b = 109 := by omega
                subst b
                exact oneGroup_complete records27250 oneCovers27250 onePacked27250 checked27250 oneChecked27250 r hr hweight word hw he hoff
            · by_cases h111 : b < 111
              · have heq : b = 110 := by omega
                subst b
                exact oneGroup_complete records27500 oneCovers27500 onePacked27500 checked27500 oneChecked27500 r hr hweight word hw he hoff
              · have heq : b = 111 := by omega
                subst b
                exact oneGroup_complete records27750 oneCovers27750 onePacked27750 checked27750 oneChecked27750 r hr hweight word hw he hoff
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every cap-zero forest chunk lists the unique empty outside support. -/
theorem zero_records_complete (b : Nat) (hb : b < 112) (r : Fiber)
    (hr : r ∈ recordsAt b) (hweight : r.weight = 22)
    (word : Nat) (hw : word < 2^90)
    (hoff : bitCount 90 (outsideMask word r.beta) ≤ 0) :
    outsideMask word r.beta ∈ r.seeds.map Seed.off := by
  by_cases h56 : b < 56
  · by_cases h28 : b < 28
    · by_cases h14 : b < 14
      · by_cases h7 : b < 7
        · by_cases h3 : b < 3
          · by_cases h1 : b < 1
            · have heq : b = 0 := by omega
              subst b
              exact zeroGroup_complete records0 zeroChecked0 r hr hweight word hw hoff
            · by_cases h2 : b < 2
              · have heq : b = 1 := by omega
                subst b
                exact zeroGroup_complete records250 zeroChecked250 r hr hweight word hw hoff
              · have heq : b = 2 := by omega
                subst b
                exact zeroGroup_complete records500 zeroChecked500 r hr hweight word hw hoff
          · by_cases h5 : b < 5
            · by_cases h4 : b < 4
              · have heq : b = 3 := by omega
                subst b
                exact zeroGroup_complete records750 zeroChecked750 r hr hweight word hw hoff
              · have heq : b = 4 := by omega
                subst b
                exact zeroGroup_complete records1000 zeroChecked1000 r hr hweight word hw hoff
            · by_cases h6 : b < 6
              · have heq : b = 5 := by omega
                subst b
                exact zeroGroup_complete records1250 zeroChecked1250 r hr hweight word hw hoff
              · have heq : b = 6 := by omega
                subst b
                exact zeroGroup_complete records1500 zeroChecked1500 r hr hweight word hw hoff
        · by_cases h10 : b < 10
          · by_cases h8 : b < 8
            · have heq : b = 7 := by omega
              subst b
              exact zeroGroup_complete records1750 zeroChecked1750 r hr hweight word hw hoff
            · by_cases h9 : b < 9
              · have heq : b = 8 := by omega
                subst b
                exact zeroGroup_complete records2000 zeroChecked2000 r hr hweight word hw hoff
              · have heq : b = 9 := by omega
                subst b
                exact zeroGroup_complete records2250 zeroChecked2250 r hr hweight word hw hoff
          · by_cases h12 : b < 12
            · by_cases h11 : b < 11
              · have heq : b = 10 := by omega
                subst b
                exact zeroGroup_complete records2500 zeroChecked2500 r hr hweight word hw hoff
              · have heq : b = 11 := by omega
                subst b
                exact zeroGroup_complete records2750 zeroChecked2750 r hr hweight word hw hoff
            · by_cases h13 : b < 13
              · have heq : b = 12 := by omega
                subst b
                exact zeroGroup_complete records3000 zeroChecked3000 r hr hweight word hw hoff
              · have heq : b = 13 := by omega
                subst b
                exact zeroGroup_complete records3250 zeroChecked3250 r hr hweight word hw hoff
      · by_cases h21 : b < 21
        · by_cases h17 : b < 17
          · by_cases h15 : b < 15
            · have heq : b = 14 := by omega
              subst b
              exact zeroGroup_complete records3500 zeroChecked3500 r hr hweight word hw hoff
            · by_cases h16 : b < 16
              · have heq : b = 15 := by omega
                subst b
                exact zeroGroup_complete records3750 zeroChecked3750 r hr hweight word hw hoff
              · have heq : b = 16 := by omega
                subst b
                exact zeroGroup_complete records4000 zeroChecked4000 r hr hweight word hw hoff
          · by_cases h19 : b < 19
            · by_cases h18 : b < 18
              · have heq : b = 17 := by omega
                subst b
                exact zeroGroup_complete records4250 zeroChecked4250 r hr hweight word hw hoff
              · have heq : b = 18 := by omega
                subst b
                exact zeroGroup_complete records4500 zeroChecked4500 r hr hweight word hw hoff
            · by_cases h20 : b < 20
              · have heq : b = 19 := by omega
                subst b
                exact zeroGroup_complete records4750 zeroChecked4750 r hr hweight word hw hoff
              · have heq : b = 20 := by omega
                subst b
                exact zeroGroup_complete records5000 zeroChecked5000 r hr hweight word hw hoff
        · by_cases h24 : b < 24
          · by_cases h22 : b < 22
            · have heq : b = 21 := by omega
              subst b
              exact zeroGroup_complete records5250 zeroChecked5250 r hr hweight word hw hoff
            · by_cases h23 : b < 23
              · have heq : b = 22 := by omega
                subst b
                exact zeroGroup_complete records5500 zeroChecked5500 r hr hweight word hw hoff
              · have heq : b = 23 := by omega
                subst b
                exact zeroGroup_complete records5750 zeroChecked5750 r hr hweight word hw hoff
          · by_cases h26 : b < 26
            · by_cases h25 : b < 25
              · have heq : b = 24 := by omega
                subst b
                exact zeroGroup_complete records6000 zeroChecked6000 r hr hweight word hw hoff
              · have heq : b = 25 := by omega
                subst b
                exact zeroGroup_complete records6250 zeroChecked6250 r hr hweight word hw hoff
            · by_cases h27 : b < 27
              · have heq : b = 26 := by omega
                subst b
                exact zeroGroup_complete records6500 zeroChecked6500 r hr hweight word hw hoff
              · have heq : b = 27 := by omega
                subst b
                exact zeroGroup_complete records6750 zeroChecked6750 r hr hweight word hw hoff
    · by_cases h42 : b < 42
      · by_cases h35 : b < 35
        · by_cases h31 : b < 31
          · by_cases h29 : b < 29
            · have heq : b = 28 := by omega
              subst b
              exact zeroGroup_complete records7000 zeroChecked7000 r hr hweight word hw hoff
            · by_cases h30 : b < 30
              · have heq : b = 29 := by omega
                subst b
                exact zeroGroup_complete records7250 zeroChecked7250 r hr hweight word hw hoff
              · have heq : b = 30 := by omega
                subst b
                exact zeroGroup_complete records7500 zeroChecked7500 r hr hweight word hw hoff
          · by_cases h33 : b < 33
            · by_cases h32 : b < 32
              · have heq : b = 31 := by omega
                subst b
                exact zeroGroup_complete records7750 zeroChecked7750 r hr hweight word hw hoff
              · have heq : b = 32 := by omega
                subst b
                exact zeroGroup_complete records8000 zeroChecked8000 r hr hweight word hw hoff
            · by_cases h34 : b < 34
              · have heq : b = 33 := by omega
                subst b
                exact zeroGroup_complete records8250 zeroChecked8250 r hr hweight word hw hoff
              · have heq : b = 34 := by omega
                subst b
                exact zeroGroup_complete records8500 zeroChecked8500 r hr hweight word hw hoff
        · by_cases h38 : b < 38
          · by_cases h36 : b < 36
            · have heq : b = 35 := by omega
              subst b
              exact zeroGroup_complete records8750 zeroChecked8750 r hr hweight word hw hoff
            · by_cases h37 : b < 37
              · have heq : b = 36 := by omega
                subst b
                exact zeroGroup_complete records9000 zeroChecked9000 r hr hweight word hw hoff
              · have heq : b = 37 := by omega
                subst b
                exact zeroGroup_complete records9250 zeroChecked9250 r hr hweight word hw hoff
          · by_cases h40 : b < 40
            · by_cases h39 : b < 39
              · have heq : b = 38 := by omega
                subst b
                exact zeroGroup_complete records9500 zeroChecked9500 r hr hweight word hw hoff
              · have heq : b = 39 := by omega
                subst b
                exact zeroGroup_complete records9750 zeroChecked9750 r hr hweight word hw hoff
            · by_cases h41 : b < 41
              · have heq : b = 40 := by omega
                subst b
                exact zeroGroup_complete records10000 zeroChecked10000 r hr hweight word hw hoff
              · have heq : b = 41 := by omega
                subst b
                exact zeroGroup_complete records10250 zeroChecked10250 r hr hweight word hw hoff
      · by_cases h49 : b < 49
        · by_cases h45 : b < 45
          · by_cases h43 : b < 43
            · have heq : b = 42 := by omega
              subst b
              exact zeroGroup_complete records10500 zeroChecked10500 r hr hweight word hw hoff
            · by_cases h44 : b < 44
              · have heq : b = 43 := by omega
                subst b
                exact zeroGroup_complete records10750 zeroChecked10750 r hr hweight word hw hoff
              · have heq : b = 44 := by omega
                subst b
                exact zeroGroup_complete records11000 zeroChecked11000 r hr hweight word hw hoff
          · by_cases h47 : b < 47
            · by_cases h46 : b < 46
              · have heq : b = 45 := by omega
                subst b
                exact zeroGroup_complete records11250 zeroChecked11250 r hr hweight word hw hoff
              · have heq : b = 46 := by omega
                subst b
                exact zeroGroup_complete records11500 zeroChecked11500 r hr hweight word hw hoff
            · by_cases h48 : b < 48
              · have heq : b = 47 := by omega
                subst b
                exact zeroGroup_complete records11750 zeroChecked11750 r hr hweight word hw hoff
              · have heq : b = 48 := by omega
                subst b
                exact zeroGroup_complete records12000 zeroChecked12000 r hr hweight word hw hoff
        · by_cases h52 : b < 52
          · by_cases h50 : b < 50
            · have heq : b = 49 := by omega
              subst b
              exact zeroGroup_complete records12250 zeroChecked12250 r hr hweight word hw hoff
            · by_cases h51 : b < 51
              · have heq : b = 50 := by omega
                subst b
                exact zeroGroup_complete records12500 zeroChecked12500 r hr hweight word hw hoff
              · have heq : b = 51 := by omega
                subst b
                exact zeroGroup_complete records12750 zeroChecked12750 r hr hweight word hw hoff
          · by_cases h54 : b < 54
            · by_cases h53 : b < 53
              · have heq : b = 52 := by omega
                subst b
                exact zeroGroup_complete records13000 zeroChecked13000 r hr hweight word hw hoff
              · have heq : b = 53 := by omega
                subst b
                exact zeroGroup_complete records13250 zeroChecked13250 r hr hweight word hw hoff
            · by_cases h55 : b < 55
              · have heq : b = 54 := by omega
                subst b
                exact zeroGroup_complete records13500 zeroChecked13500 r hr hweight word hw hoff
              · have heq : b = 55 := by omega
                subst b
                exact zeroGroup_complete records13750 zeroChecked13750 r hr hweight word hw hoff
  · by_cases h84 : b < 84
    · by_cases h70 : b < 70
      · by_cases h63 : b < 63
        · by_cases h59 : b < 59
          · by_cases h57 : b < 57
            · have heq : b = 56 := by omega
              subst b
              exact zeroGroup_complete records14000 zeroChecked14000 r hr hweight word hw hoff
            · by_cases h58 : b < 58
              · have heq : b = 57 := by omega
                subst b
                exact zeroGroup_complete records14250 zeroChecked14250 r hr hweight word hw hoff
              · have heq : b = 58 := by omega
                subst b
                exact zeroGroup_complete records14500 zeroChecked14500 r hr hweight word hw hoff
          · by_cases h61 : b < 61
            · by_cases h60 : b < 60
              · have heq : b = 59 := by omega
                subst b
                exact zeroGroup_complete records14750 zeroChecked14750 r hr hweight word hw hoff
              · have heq : b = 60 := by omega
                subst b
                exact zeroGroup_complete records15000 zeroChecked15000 r hr hweight word hw hoff
            · by_cases h62 : b < 62
              · have heq : b = 61 := by omega
                subst b
                exact zeroGroup_complete records15250 zeroChecked15250 r hr hweight word hw hoff
              · have heq : b = 62 := by omega
                subst b
                exact zeroGroup_complete records15500 zeroChecked15500 r hr hweight word hw hoff
        · by_cases h66 : b < 66
          · by_cases h64 : b < 64
            · have heq : b = 63 := by omega
              subst b
              exact zeroGroup_complete records15750 zeroChecked15750 r hr hweight word hw hoff
            · by_cases h65 : b < 65
              · have heq : b = 64 := by omega
                subst b
                exact zeroGroup_complete records16000 zeroChecked16000 r hr hweight word hw hoff
              · have heq : b = 65 := by omega
                subst b
                exact zeroGroup_complete records16250 zeroChecked16250 r hr hweight word hw hoff
          · by_cases h68 : b < 68
            · by_cases h67 : b < 67
              · have heq : b = 66 := by omega
                subst b
                exact zeroGroup_complete records16500 zeroChecked16500 r hr hweight word hw hoff
              · have heq : b = 67 := by omega
                subst b
                exact zeroGroup_complete records16750 zeroChecked16750 r hr hweight word hw hoff
            · by_cases h69 : b < 69
              · have heq : b = 68 := by omega
                subst b
                exact zeroGroup_complete records17000 zeroChecked17000 r hr hweight word hw hoff
              · have heq : b = 69 := by omega
                subst b
                exact zeroGroup_complete records17250 zeroChecked17250 r hr hweight word hw hoff
      · by_cases h77 : b < 77
        · by_cases h73 : b < 73
          · by_cases h71 : b < 71
            · have heq : b = 70 := by omega
              subst b
              exact zeroGroup_complete records17500 zeroChecked17500 r hr hweight word hw hoff
            · by_cases h72 : b < 72
              · have heq : b = 71 := by omega
                subst b
                exact zeroGroup_complete records17750 zeroChecked17750 r hr hweight word hw hoff
              · have heq : b = 72 := by omega
                subst b
                exact zeroGroup_complete records18000 zeroChecked18000 r hr hweight word hw hoff
          · by_cases h75 : b < 75
            · by_cases h74 : b < 74
              · have heq : b = 73 := by omega
                subst b
                exact zeroGroup_complete records18250 zeroChecked18250 r hr hweight word hw hoff
              · have heq : b = 74 := by omega
                subst b
                exact zeroGroup_complete records18500 zeroChecked18500 r hr hweight word hw hoff
            · by_cases h76 : b < 76
              · have heq : b = 75 := by omega
                subst b
                exact zeroGroup_complete records18750 zeroChecked18750 r hr hweight word hw hoff
              · have heq : b = 76 := by omega
                subst b
                exact zeroGroup_complete records19000 zeroChecked19000 r hr hweight word hw hoff
        · by_cases h80 : b < 80
          · by_cases h78 : b < 78
            · have heq : b = 77 := by omega
              subst b
              exact zeroGroup_complete records19250 zeroChecked19250 r hr hweight word hw hoff
            · by_cases h79 : b < 79
              · have heq : b = 78 := by omega
                subst b
                exact zeroGroup_complete records19500 zeroChecked19500 r hr hweight word hw hoff
              · have heq : b = 79 := by omega
                subst b
                exact zeroGroup_complete records19750 zeroChecked19750 r hr hweight word hw hoff
          · by_cases h82 : b < 82
            · by_cases h81 : b < 81
              · have heq : b = 80 := by omega
                subst b
                exact zeroGroup_complete records20000 zeroChecked20000 r hr hweight word hw hoff
              · have heq : b = 81 := by omega
                subst b
                exact zeroGroup_complete records20250 zeroChecked20250 r hr hweight word hw hoff
            · by_cases h83 : b < 83
              · have heq : b = 82 := by omega
                subst b
                exact zeroGroup_complete records20500 zeroChecked20500 r hr hweight word hw hoff
              · have heq : b = 83 := by omega
                subst b
                exact zeroGroup_complete records20750 zeroChecked20750 r hr hweight word hw hoff
    · by_cases h98 : b < 98
      · by_cases h91 : b < 91
        · by_cases h87 : b < 87
          · by_cases h85 : b < 85
            · have heq : b = 84 := by omega
              subst b
              exact zeroGroup_complete records21000 zeroChecked21000 r hr hweight word hw hoff
            · by_cases h86 : b < 86
              · have heq : b = 85 := by omega
                subst b
                exact zeroGroup_complete records21250 zeroChecked21250 r hr hweight word hw hoff
              · have heq : b = 86 := by omega
                subst b
                exact zeroGroup_complete records21500 zeroChecked21500 r hr hweight word hw hoff
          · by_cases h89 : b < 89
            · by_cases h88 : b < 88
              · have heq : b = 87 := by omega
                subst b
                exact zeroGroup_complete records21750 zeroChecked21750 r hr hweight word hw hoff
              · have heq : b = 88 := by omega
                subst b
                exact zeroGroup_complete records22000 zeroChecked22000 r hr hweight word hw hoff
            · by_cases h90 : b < 90
              · have heq : b = 89 := by omega
                subst b
                exact zeroGroup_complete records22250 zeroChecked22250 r hr hweight word hw hoff
              · have heq : b = 90 := by omega
                subst b
                exact zeroGroup_complete records22500 zeroChecked22500 r hr hweight word hw hoff
        · by_cases h94 : b < 94
          · by_cases h92 : b < 92
            · have heq : b = 91 := by omega
              subst b
              exact zeroGroup_complete records22750 zeroChecked22750 r hr hweight word hw hoff
            · by_cases h93 : b < 93
              · have heq : b = 92 := by omega
                subst b
                exact zeroGroup_complete records23000 zeroChecked23000 r hr hweight word hw hoff
              · have heq : b = 93 := by omega
                subst b
                exact zeroGroup_complete records23250 zeroChecked23250 r hr hweight word hw hoff
          · by_cases h96 : b < 96
            · by_cases h95 : b < 95
              · have heq : b = 94 := by omega
                subst b
                exact zeroGroup_complete records23500 zeroChecked23500 r hr hweight word hw hoff
              · have heq : b = 95 := by omega
                subst b
                exact zeroGroup_complete records23750 zeroChecked23750 r hr hweight word hw hoff
            · by_cases h97 : b < 97
              · have heq : b = 96 := by omega
                subst b
                exact zeroGroup_complete records24000 zeroChecked24000 r hr hweight word hw hoff
              · have heq : b = 97 := by omega
                subst b
                exact zeroGroup_complete records24250 zeroChecked24250 r hr hweight word hw hoff
      · by_cases h105 : b < 105
        · by_cases h101 : b < 101
          · by_cases h99 : b < 99
            · have heq : b = 98 := by omega
              subst b
              exact zeroGroup_complete records24500 zeroChecked24500 r hr hweight word hw hoff
            · by_cases h100 : b < 100
              · have heq : b = 99 := by omega
                subst b
                exact zeroGroup_complete records24750 zeroChecked24750 r hr hweight word hw hoff
              · have heq : b = 100 := by omega
                subst b
                exact zeroGroup_complete records25000 zeroChecked25000 r hr hweight word hw hoff
          · by_cases h103 : b < 103
            · by_cases h102 : b < 102
              · have heq : b = 101 := by omega
                subst b
                exact zeroGroup_complete records25250 zeroChecked25250 r hr hweight word hw hoff
              · have heq : b = 102 := by omega
                subst b
                exact zeroGroup_complete records25500 zeroChecked25500 r hr hweight word hw hoff
            · by_cases h104 : b < 104
              · have heq : b = 103 := by omega
                subst b
                exact zeroGroup_complete records25750 zeroChecked25750 r hr hweight word hw hoff
              · have heq : b = 104 := by omega
                subst b
                exact zeroGroup_complete records26000 zeroChecked26000 r hr hweight word hw hoff
        · by_cases h108 : b < 108
          · by_cases h106 : b < 106
            · have heq : b = 105 := by omega
              subst b
              exact zeroGroup_complete records26250 zeroChecked26250 r hr hweight word hw hoff
            · by_cases h107 : b < 107
              · have heq : b = 106 := by omega
                subst b
                exact zeroGroup_complete records26500 zeroChecked26500 r hr hweight word hw hoff
              · have heq : b = 107 := by omega
                subst b
                exact zeroGroup_complete records26750 zeroChecked26750 r hr hweight word hw hoff
          · by_cases h110 : b < 110
            · by_cases h109 : b < 109
              · have heq : b = 108 := by omega
                subst b
                exact zeroGroup_complete records27000 zeroChecked27000 r hr hweight word hw hoff
              · have heq : b = 109 := by omega
                subst b
                exact zeroGroup_complete records27250 zeroChecked27250 r hr hweight word hw hoff
            · by_cases h111 : b < 111
              · have heq : b = 110 := by omega
                subst b
                exact zeroGroup_complete records27500 zeroChecked27500 r hr hweight word hw hoff
              · have heq : b = 111 := by omega
                subst b
                exact zeroGroup_complete records27750 zeroChecked27750 r hr hweight word hw hoff
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The five shallow positive shadow weights exhaust every forest chunk. -/
theorem records_weights (b : Nat) (hb : b < 112) (r : Fiber)
    (hr : r ∈ recordsAt b) : r.weight ∈ [14,16,18,20,22] := by
  by_cases h56 : b < 56
  · by_cases h28 : b < 28
    · by_cases h14 : b < 14
      · by_cases h7 : b < 7
        · by_cases h3 : b < 3
          · by_cases h1 : b < 1
            · have heq : b = 0 := by omega
              subst b
              have h := List.all_eq_true.mp weightChecked0 r hr
              simpa using h
            · by_cases h2 : b < 2
              · have heq : b = 1 := by omega
                subst b
                have h := List.all_eq_true.mp weightChecked250 r hr
                simpa using h
              · have heq : b = 2 := by omega
                subst b
                have h := List.all_eq_true.mp weightChecked500 r hr
                simpa using h
          · by_cases h5 : b < 5
            · by_cases h4 : b < 4
              · have heq : b = 3 := by omega
                subst b
                have h := List.all_eq_true.mp weightChecked750 r hr
                simpa using h
              · have heq : b = 4 := by omega
                subst b
                have h := List.all_eq_true.mp weightChecked1000 r hr
                simpa using h
            · by_cases h6 : b < 6
              · have heq : b = 5 := by omega
                subst b
                have h := List.all_eq_true.mp weightChecked1250 r hr
                simpa using h
              · have heq : b = 6 := by omega
                subst b
                have h := List.all_eq_true.mp weightChecked1500 r hr
                simpa using h
        · by_cases h10 : b < 10
          · by_cases h8 : b < 8
            · have heq : b = 7 := by omega
              subst b
              have h := List.all_eq_true.mp weightChecked1750 r hr
              simpa using h
            · by_cases h9 : b < 9
              · have heq : b = 8 := by omega
                subst b
                have h := List.all_eq_true.mp weightChecked2000 r hr
                simpa using h
              · have heq : b = 9 := by omega
                subst b
                have h := List.all_eq_true.mp weightChecked2250 r hr
                simpa using h
          · by_cases h12 : b < 12
            · by_cases h11 : b < 11
              · have heq : b = 10 := by omega
                subst b
                have h := List.all_eq_true.mp weightChecked2500 r hr
                simpa using h
              · have heq : b = 11 := by omega
                subst b
                have h := List.all_eq_true.mp weightChecked2750 r hr
                simpa using h
            · by_cases h13 : b < 13
              · have heq : b = 12 := by omega
                subst b
                have h := List.all_eq_true.mp weightChecked3000 r hr
                simpa using h
              · have heq : b = 13 := by omega
                subst b
                have h := List.all_eq_true.mp weightChecked3250 r hr
                simpa using h
      · by_cases h21 : b < 21
        · by_cases h17 : b < 17
          · by_cases h15 : b < 15
            · have heq : b = 14 := by omega
              subst b
              have h := List.all_eq_true.mp weightChecked3500 r hr
              simpa using h
            · by_cases h16 : b < 16
              · have heq : b = 15 := by omega
                subst b
                have h := List.all_eq_true.mp weightChecked3750 r hr
                simpa using h
              · have heq : b = 16 := by omega
                subst b
                have h := List.all_eq_true.mp weightChecked4000 r hr
                simpa using h
          · by_cases h19 : b < 19
            · by_cases h18 : b < 18
              · have heq : b = 17 := by omega
                subst b
                have h := List.all_eq_true.mp weightChecked4250 r hr
                simpa using h
              · have heq : b = 18 := by omega
                subst b
                have h := List.all_eq_true.mp weightChecked4500 r hr
                simpa using h
            · by_cases h20 : b < 20
              · have heq : b = 19 := by omega
                subst b
                have h := List.all_eq_true.mp weightChecked4750 r hr
                simpa using h
              · have heq : b = 20 := by omega
                subst b
                have h := List.all_eq_true.mp weightChecked5000 r hr
                simpa using h
        · by_cases h24 : b < 24
          · by_cases h22 : b < 22
            · have heq : b = 21 := by omega
              subst b
              have h := List.all_eq_true.mp weightChecked5250 r hr
              simpa using h
            · by_cases h23 : b < 23
              · have heq : b = 22 := by omega
                subst b
                have h := List.all_eq_true.mp weightChecked5500 r hr
                simpa using h
              · have heq : b = 23 := by omega
                subst b
                have h := List.all_eq_true.mp weightChecked5750 r hr
                simpa using h
          · by_cases h26 : b < 26
            · by_cases h25 : b < 25
              · have heq : b = 24 := by omega
                subst b
                have h := List.all_eq_true.mp weightChecked6000 r hr
                simpa using h
              · have heq : b = 25 := by omega
                subst b
                have h := List.all_eq_true.mp weightChecked6250 r hr
                simpa using h
            · by_cases h27 : b < 27
              · have heq : b = 26 := by omega
                subst b
                have h := List.all_eq_true.mp weightChecked6500 r hr
                simpa using h
              · have heq : b = 27 := by omega
                subst b
                have h := List.all_eq_true.mp weightChecked6750 r hr
                simpa using h
    · by_cases h42 : b < 42
      · by_cases h35 : b < 35
        · by_cases h31 : b < 31
          · by_cases h29 : b < 29
            · have heq : b = 28 := by omega
              subst b
              have h := List.all_eq_true.mp weightChecked7000 r hr
              simpa using h
            · by_cases h30 : b < 30
              · have heq : b = 29 := by omega
                subst b
                have h := List.all_eq_true.mp weightChecked7250 r hr
                simpa using h
              · have heq : b = 30 := by omega
                subst b
                have h := List.all_eq_true.mp weightChecked7500 r hr
                simpa using h
          · by_cases h33 : b < 33
            · by_cases h32 : b < 32
              · have heq : b = 31 := by omega
                subst b
                have h := List.all_eq_true.mp weightChecked7750 r hr
                simpa using h
              · have heq : b = 32 := by omega
                subst b
                have h := List.all_eq_true.mp weightChecked8000 r hr
                simpa using h
            · by_cases h34 : b < 34
              · have heq : b = 33 := by omega
                subst b
                have h := List.all_eq_true.mp weightChecked8250 r hr
                simpa using h
              · have heq : b = 34 := by omega
                subst b
                have h := List.all_eq_true.mp weightChecked8500 r hr
                simpa using h
        · by_cases h38 : b < 38
          · by_cases h36 : b < 36
            · have heq : b = 35 := by omega
              subst b
              have h := List.all_eq_true.mp weightChecked8750 r hr
              simpa using h
            · by_cases h37 : b < 37
              · have heq : b = 36 := by omega
                subst b
                have h := List.all_eq_true.mp weightChecked9000 r hr
                simpa using h
              · have heq : b = 37 := by omega
                subst b
                have h := List.all_eq_true.mp weightChecked9250 r hr
                simpa using h
          · by_cases h40 : b < 40
            · by_cases h39 : b < 39
              · have heq : b = 38 := by omega
                subst b
                have h := List.all_eq_true.mp weightChecked9500 r hr
                simpa using h
              · have heq : b = 39 := by omega
                subst b
                have h := List.all_eq_true.mp weightChecked9750 r hr
                simpa using h
            · by_cases h41 : b < 41
              · have heq : b = 40 := by omega
                subst b
                have h := List.all_eq_true.mp weightChecked10000 r hr
                simpa using h
              · have heq : b = 41 := by omega
                subst b
                have h := List.all_eq_true.mp weightChecked10250 r hr
                simpa using h
      · by_cases h49 : b < 49
        · by_cases h45 : b < 45
          · by_cases h43 : b < 43
            · have heq : b = 42 := by omega
              subst b
              have h := List.all_eq_true.mp weightChecked10500 r hr
              simpa using h
            · by_cases h44 : b < 44
              · have heq : b = 43 := by omega
                subst b
                have h := List.all_eq_true.mp weightChecked10750 r hr
                simpa using h
              · have heq : b = 44 := by omega
                subst b
                have h := List.all_eq_true.mp weightChecked11000 r hr
                simpa using h
          · by_cases h47 : b < 47
            · by_cases h46 : b < 46
              · have heq : b = 45 := by omega
                subst b
                have h := List.all_eq_true.mp weightChecked11250 r hr
                simpa using h
              · have heq : b = 46 := by omega
                subst b
                have h := List.all_eq_true.mp weightChecked11500 r hr
                simpa using h
            · by_cases h48 : b < 48
              · have heq : b = 47 := by omega
                subst b
                have h := List.all_eq_true.mp weightChecked11750 r hr
                simpa using h
              · have heq : b = 48 := by omega
                subst b
                have h := List.all_eq_true.mp weightChecked12000 r hr
                simpa using h
        · by_cases h52 : b < 52
          · by_cases h50 : b < 50
            · have heq : b = 49 := by omega
              subst b
              have h := List.all_eq_true.mp weightChecked12250 r hr
              simpa using h
            · by_cases h51 : b < 51
              · have heq : b = 50 := by omega
                subst b
                have h := List.all_eq_true.mp weightChecked12500 r hr
                simpa using h
              · have heq : b = 51 := by omega
                subst b
                have h := List.all_eq_true.mp weightChecked12750 r hr
                simpa using h
          · by_cases h54 : b < 54
            · by_cases h53 : b < 53
              · have heq : b = 52 := by omega
                subst b
                have h := List.all_eq_true.mp weightChecked13000 r hr
                simpa using h
              · have heq : b = 53 := by omega
                subst b
                have h := List.all_eq_true.mp weightChecked13250 r hr
                simpa using h
            · by_cases h55 : b < 55
              · have heq : b = 54 := by omega
                subst b
                have h := List.all_eq_true.mp weightChecked13500 r hr
                simpa using h
              · have heq : b = 55 := by omega
                subst b
                have h := List.all_eq_true.mp weightChecked13750 r hr
                simpa using h
  · by_cases h84 : b < 84
    · by_cases h70 : b < 70
      · by_cases h63 : b < 63
        · by_cases h59 : b < 59
          · by_cases h57 : b < 57
            · have heq : b = 56 := by omega
              subst b
              have h := List.all_eq_true.mp weightChecked14000 r hr
              simpa using h
            · by_cases h58 : b < 58
              · have heq : b = 57 := by omega
                subst b
                have h := List.all_eq_true.mp weightChecked14250 r hr
                simpa using h
              · have heq : b = 58 := by omega
                subst b
                have h := List.all_eq_true.mp weightChecked14500 r hr
                simpa using h
          · by_cases h61 : b < 61
            · by_cases h60 : b < 60
              · have heq : b = 59 := by omega
                subst b
                have h := List.all_eq_true.mp weightChecked14750 r hr
                simpa using h
              · have heq : b = 60 := by omega
                subst b
                have h := List.all_eq_true.mp weightChecked15000 r hr
                simpa using h
            · by_cases h62 : b < 62
              · have heq : b = 61 := by omega
                subst b
                have h := List.all_eq_true.mp weightChecked15250 r hr
                simpa using h
              · have heq : b = 62 := by omega
                subst b
                have h := List.all_eq_true.mp weightChecked15500 r hr
                simpa using h
        · by_cases h66 : b < 66
          · by_cases h64 : b < 64
            · have heq : b = 63 := by omega
              subst b
              have h := List.all_eq_true.mp weightChecked15750 r hr
              simpa using h
            · by_cases h65 : b < 65
              · have heq : b = 64 := by omega
                subst b
                have h := List.all_eq_true.mp weightChecked16000 r hr
                simpa using h
              · have heq : b = 65 := by omega
                subst b
                have h := List.all_eq_true.mp weightChecked16250 r hr
                simpa using h
          · by_cases h68 : b < 68
            · by_cases h67 : b < 67
              · have heq : b = 66 := by omega
                subst b
                have h := List.all_eq_true.mp weightChecked16500 r hr
                simpa using h
              · have heq : b = 67 := by omega
                subst b
                have h := List.all_eq_true.mp weightChecked16750 r hr
                simpa using h
            · by_cases h69 : b < 69
              · have heq : b = 68 := by omega
                subst b
                have h := List.all_eq_true.mp weightChecked17000 r hr
                simpa using h
              · have heq : b = 69 := by omega
                subst b
                have h := List.all_eq_true.mp weightChecked17250 r hr
                simpa using h
      · by_cases h77 : b < 77
        · by_cases h73 : b < 73
          · by_cases h71 : b < 71
            · have heq : b = 70 := by omega
              subst b
              have h := List.all_eq_true.mp weightChecked17500 r hr
              simpa using h
            · by_cases h72 : b < 72
              · have heq : b = 71 := by omega
                subst b
                have h := List.all_eq_true.mp weightChecked17750 r hr
                simpa using h
              · have heq : b = 72 := by omega
                subst b
                have h := List.all_eq_true.mp weightChecked18000 r hr
                simpa using h
          · by_cases h75 : b < 75
            · by_cases h74 : b < 74
              · have heq : b = 73 := by omega
                subst b
                have h := List.all_eq_true.mp weightChecked18250 r hr
                simpa using h
              · have heq : b = 74 := by omega
                subst b
                have h := List.all_eq_true.mp weightChecked18500 r hr
                simpa using h
            · by_cases h76 : b < 76
              · have heq : b = 75 := by omega
                subst b
                have h := List.all_eq_true.mp weightChecked18750 r hr
                simpa using h
              · have heq : b = 76 := by omega
                subst b
                have h := List.all_eq_true.mp weightChecked19000 r hr
                simpa using h
        · by_cases h80 : b < 80
          · by_cases h78 : b < 78
            · have heq : b = 77 := by omega
              subst b
              have h := List.all_eq_true.mp weightChecked19250 r hr
              simpa using h
            · by_cases h79 : b < 79
              · have heq : b = 78 := by omega
                subst b
                have h := List.all_eq_true.mp weightChecked19500 r hr
                simpa using h
              · have heq : b = 79 := by omega
                subst b
                have h := List.all_eq_true.mp weightChecked19750 r hr
                simpa using h
          · by_cases h82 : b < 82
            · by_cases h81 : b < 81
              · have heq : b = 80 := by omega
                subst b
                have h := List.all_eq_true.mp weightChecked20000 r hr
                simpa using h
              · have heq : b = 81 := by omega
                subst b
                have h := List.all_eq_true.mp weightChecked20250 r hr
                simpa using h
            · by_cases h83 : b < 83
              · have heq : b = 82 := by omega
                subst b
                have h := List.all_eq_true.mp weightChecked20500 r hr
                simpa using h
              · have heq : b = 83 := by omega
                subst b
                have h := List.all_eq_true.mp weightChecked20750 r hr
                simpa using h
    · by_cases h98 : b < 98
      · by_cases h91 : b < 91
        · by_cases h87 : b < 87
          · by_cases h85 : b < 85
            · have heq : b = 84 := by omega
              subst b
              have h := List.all_eq_true.mp weightChecked21000 r hr
              simpa using h
            · by_cases h86 : b < 86
              · have heq : b = 85 := by omega
                subst b
                have h := List.all_eq_true.mp weightChecked21250 r hr
                simpa using h
              · have heq : b = 86 := by omega
                subst b
                have h := List.all_eq_true.mp weightChecked21500 r hr
                simpa using h
          · by_cases h89 : b < 89
            · by_cases h88 : b < 88
              · have heq : b = 87 := by omega
                subst b
                have h := List.all_eq_true.mp weightChecked21750 r hr
                simpa using h
              · have heq : b = 88 := by omega
                subst b
                have h := List.all_eq_true.mp weightChecked22000 r hr
                simpa using h
            · by_cases h90 : b < 90
              · have heq : b = 89 := by omega
                subst b
                have h := List.all_eq_true.mp weightChecked22250 r hr
                simpa using h
              · have heq : b = 90 := by omega
                subst b
                have h := List.all_eq_true.mp weightChecked22500 r hr
                simpa using h
        · by_cases h94 : b < 94
          · by_cases h92 : b < 92
            · have heq : b = 91 := by omega
              subst b
              have h := List.all_eq_true.mp weightChecked22750 r hr
              simpa using h
            · by_cases h93 : b < 93
              · have heq : b = 92 := by omega
                subst b
                have h := List.all_eq_true.mp weightChecked23000 r hr
                simpa using h
              · have heq : b = 93 := by omega
                subst b
                have h := List.all_eq_true.mp weightChecked23250 r hr
                simpa using h
          · by_cases h96 : b < 96
            · by_cases h95 : b < 95
              · have heq : b = 94 := by omega
                subst b
                have h := List.all_eq_true.mp weightChecked23500 r hr
                simpa using h
              · have heq : b = 95 := by omega
                subst b
                have h := List.all_eq_true.mp weightChecked23750 r hr
                simpa using h
            · by_cases h97 : b < 97
              · have heq : b = 96 := by omega
                subst b
                have h := List.all_eq_true.mp weightChecked24000 r hr
                simpa using h
              · have heq : b = 97 := by omega
                subst b
                have h := List.all_eq_true.mp weightChecked24250 r hr
                simpa using h
      · by_cases h105 : b < 105
        · by_cases h101 : b < 101
          · by_cases h99 : b < 99
            · have heq : b = 98 := by omega
              subst b
              have h := List.all_eq_true.mp weightChecked24500 r hr
              simpa using h
            · by_cases h100 : b < 100
              · have heq : b = 99 := by omega
                subst b
                have h := List.all_eq_true.mp weightChecked24750 r hr
                simpa using h
              · have heq : b = 100 := by omega
                subst b
                have h := List.all_eq_true.mp weightChecked25000 r hr
                simpa using h
          · by_cases h103 : b < 103
            · by_cases h102 : b < 102
              · have heq : b = 101 := by omega
                subst b
                have h := List.all_eq_true.mp weightChecked25250 r hr
                simpa using h
              · have heq : b = 102 := by omega
                subst b
                have h := List.all_eq_true.mp weightChecked25500 r hr
                simpa using h
            · by_cases h104 : b < 104
              · have heq : b = 103 := by omega
                subst b
                have h := List.all_eq_true.mp weightChecked25750 r hr
                simpa using h
              · have heq : b = 104 := by omega
                subst b
                have h := List.all_eq_true.mp weightChecked26000 r hr
                simpa using h
        · by_cases h108 : b < 108
          · by_cases h106 : b < 106
            · have heq : b = 105 := by omega
              subst b
              have h := List.all_eq_true.mp weightChecked26250 r hr
              simpa using h
            · by_cases h107 : b < 107
              · have heq : b = 106 := by omega
                subst b
                have h := List.all_eq_true.mp weightChecked26500 r hr
                simpa using h
              · have heq : b = 107 := by omega
                subst b
                have h := List.all_eq_true.mp weightChecked26750 r hr
                simpa using h
          · by_cases h110 : b < 110
            · by_cases h109 : b < 109
              · have heq : b = 108 := by omega
                subst b
                have h := List.all_eq_true.mp weightChecked27000 r hr
                simpa using h
              · have heq : b = 109 := by omega
                subst b
                have h := List.all_eq_true.mp weightChecked27250 r hr
                simpa using h
            · by_cases h111 : b < 111
              · have heq : b = 110 := by omega
                subst b
                have h := List.all_eq_true.mp weightChecked27500 r hr
                simpa using h
              · have heq : b = 111 := by omega
                subst b
                have h := List.all_eq_true.mp weightChecked27750 r hr
                simpa using h
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical positive forest family has only the five shallow weights. -/
theorem fiberAt_weights (i : Fin 27867) : (fiberAt i.val).weight ∈ [14,16,18,20,22] :=
  records_weights _ (by omega) _ (fiberAt_mem i)
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Complete outside-support coverage for every positive cap-one fiber. -/
theorem oneFiberAt_complete (i : Fin 27867) (hweight : (fiberAt i.val).weight = 20)
    (word : Nat) (hw : word < 2^90)
    (he : reconX bottomEColumns word = reconX bottomRColumns (fiberAt i.val).beta)
    (hoff : bitCount 90 (outsideMask word (fiberAt i.val).beta) ≤ 1) :
    outsideMask word (fiberAt i.val).beta ∈ (fiberAt i.val).seeds.map Seed.off :=
  one_records_complete _ (by omega) _ (fiberAt_mem i) hweight word hw he hoff
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Complete outside-support coverage for every positive cap-zero fiber. -/
theorem zeroFiberAt_complete (i : Fin 27867) (hweight : (fiberAt i.val).weight = 22)
    (word : Nat) (hw : word < 2^90)
    (hoff : bitCount 90 (outsideMask word (fiberAt i.val).beta) ≤ 0) :
    outsideMask word (fiberAt i.val).beta ∈ (fiberAt i.val).seeds.map Seed.off :=
  zero_records_complete _ (by omega) _ (fiberAt_mem i) hweight word hw hoff
#print axioms oneFiberAt_complete
end Quantum.Stabilizer.Homological.BB.Bravyi360.BottomForest
