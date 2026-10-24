/-
GENERATED FILE — DO NOT HAND-EDIT
Generator: qec-lab:experiments/bb_lab/scripts/bravyi360_kernel/generate.py
Emitter, relative to generator directory:
  emitters/mark_research_noncomputable.py
Data and SHA-256 hashes: research_manifest.json
Regenerate:
  QECLEAN_ROOT=/path/to/QECLean \
    python3 experiments/bb_lab/scripts/bravyi360_kernel/generate.py --force
-/

import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.BottomForest
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.BottomPositiveTwoPart0
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.BottomPositiveTwoPart1
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.BottomPositiveTwoPart2
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.BottomPositiveTwoPart3
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.BottomPositiveTwoPart4
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.BottomPositiveTwoPart5
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.BottomPositiveTwoPart6
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.BottomPositiveTwoPart7
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.BottomPositiveTwoPart8
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.BottomPositiveTwoPart9
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.BottomPositiveTwoPart10
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.BottomPositiveTwoPart11
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.BottomPositiveTwoPart12
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.BottomPositiveTwoPart13

noncomputable section
namespace Quantum.Stabilizer.Homological.BB.Bravyi360.BottomForest
open F2Mask FiberData PackedDigits
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every cap-two record in any canonical chunk has a complete outside-support list. -/
theorem twoRecords_complete (b : Fin 112) (r : Fiber) (hr : r ∈ recordsAt b.val)
    (hweight : r.weight = 18) (word : Nat) (hw : word < 2^90)
    (he : reconX bottomEColumns word = reconX bottomRColumns r.beta)
    (hoff : bitCount 90 (outsideMask word r.beta) ≤ 2) :
    outsideMask word r.beta ∈ r.seeds.map Seed.off := by
  fin_cases b
  · change r ∈ records0 at hr
    exact twoGroup_complete bottomPairSpreadTable bottomPairRep bottomPair_lookup bottomPair_rep
      records0 twoCovers0 twoPacked0 checked0 twoChecked0 r hr hweight word hw he hoff
  · change r ∈ records250 at hr
    exact twoGroup_complete bottomPairSpreadTable bottomPairRep bottomPair_lookup bottomPair_rep
      records250 twoCovers250 twoPacked250 checked250 twoChecked250 r hr hweight word hw he hoff
  · change r ∈ records500 at hr
    exact twoGroup_complete bottomPairSpreadTable bottomPairRep bottomPair_lookup bottomPair_rep
      records500 twoCovers500 twoPacked500 checked500 twoChecked500 r hr hweight word hw he hoff
  · change r ∈ records750 at hr
    exact twoGroup_complete bottomPairSpreadTable bottomPairRep bottomPair_lookup bottomPair_rep
      records750 twoCovers750 twoPacked750 checked750 twoChecked750 r hr hweight word hw he hoff
  · change r ∈ records1000 at hr
    exact twoGroup_complete bottomPairSpreadTable bottomPairRep bottomPair_lookup bottomPair_rep
      records1000 twoCovers1000 twoPacked1000 checked1000 twoChecked1000 r hr hweight word hw he hoff
  · change r ∈ records1250 at hr
    exact twoGroup_complete bottomPairSpreadTable bottomPairRep bottomPair_lookup bottomPair_rep
      records1250 twoCovers1250 twoPacked1250 checked1250 twoChecked1250 r hr hweight word hw he hoff
  · change r ∈ records1500 at hr
    exact twoGroup_complete bottomPairSpreadTable bottomPairRep bottomPair_lookup bottomPair_rep
      records1500 twoCovers1500 twoPacked1500 checked1500 twoChecked1500 r hr hweight word hw he hoff
  · change r ∈ records1750 at hr
    exact twoGroup_complete bottomPairSpreadTable bottomPairRep bottomPair_lookup bottomPair_rep
      records1750 twoCovers1750 twoPacked1750 checked1750 twoChecked1750 r hr hweight word hw he hoff
  · change r ∈ records2000 at hr
    exact twoGroup_complete bottomPairSpreadTable bottomPairRep bottomPair_lookup bottomPair_rep
      records2000 twoCovers2000 twoPacked2000 checked2000 twoChecked2000 r hr hweight word hw he hoff
  · change r ∈ records2250 at hr
    exact twoGroup_complete bottomPairSpreadTable bottomPairRep bottomPair_lookup bottomPair_rep
      records2250 twoCovers2250 twoPacked2250 checked2250 twoChecked2250 r hr hweight word hw he hoff
  · change r ∈ records2500 at hr
    exact twoGroup_complete bottomPairSpreadTable bottomPairRep bottomPair_lookup bottomPair_rep
      records2500 twoCovers2500 twoPacked2500 checked2500 twoChecked2500 r hr hweight word hw he hoff
  · change r ∈ records2750 at hr
    exact twoGroup_complete bottomPairSpreadTable bottomPairRep bottomPair_lookup bottomPair_rep
      records2750 twoCovers2750 twoPacked2750 checked2750 twoChecked2750 r hr hweight word hw he hoff
  · change r ∈ records3000 at hr
    exact twoGroup_complete bottomPairSpreadTable bottomPairRep bottomPair_lookup bottomPair_rep
      records3000 twoCovers3000 twoPacked3000 checked3000 twoChecked3000 r hr hweight word hw he hoff
  · change r ∈ records3250 at hr
    exact twoGroup_complete bottomPairSpreadTable bottomPairRep bottomPair_lookup bottomPair_rep
      records3250 twoCovers3250 twoPacked3250 checked3250 twoChecked3250 r hr hweight word hw he hoff
  · change r ∈ records3500 at hr
    exact twoGroup_complete bottomPairSpreadTable bottomPairRep bottomPair_lookup bottomPair_rep
      records3500 twoCovers3500 twoPacked3500 checked3500 twoChecked3500 r hr hweight word hw he hoff
  · change r ∈ records3750 at hr
    exact twoGroup_complete bottomPairSpreadTable bottomPairRep bottomPair_lookup bottomPair_rep
      records3750 twoCovers3750 twoPacked3750 checked3750 twoChecked3750 r hr hweight word hw he hoff
  · change r ∈ records4000 at hr
    exact twoGroup_complete bottomPairSpreadTable bottomPairRep bottomPair_lookup bottomPair_rep
      records4000 twoCovers4000 twoPacked4000 checked4000 twoChecked4000 r hr hweight word hw he hoff
  · change r ∈ records4250 at hr
    exact twoGroup_complete bottomPairSpreadTable bottomPairRep bottomPair_lookup bottomPair_rep
      records4250 twoCovers4250 twoPacked4250 checked4250 twoChecked4250 r hr hweight word hw he hoff
  · change r ∈ records4500 at hr
    exact twoGroup_complete bottomPairSpreadTable bottomPairRep bottomPair_lookup bottomPair_rep
      records4500 twoCovers4500 twoPacked4500 checked4500 twoChecked4500 r hr hweight word hw he hoff
  · change r ∈ records4750 at hr
    exact twoGroup_complete bottomPairSpreadTable bottomPairRep bottomPair_lookup bottomPair_rep
      records4750 twoCovers4750 twoPacked4750 checked4750 twoChecked4750 r hr hweight word hw he hoff
  · change r ∈ records5000 at hr
    exact twoGroup_complete bottomPairSpreadTable bottomPairRep bottomPair_lookup bottomPair_rep
      records5000 twoCovers5000 twoPacked5000 checked5000 twoChecked5000 r hr hweight word hw he hoff
  · change r ∈ records5250 at hr
    exact twoGroup_complete bottomPairSpreadTable bottomPairRep bottomPair_lookup bottomPair_rep
      records5250 twoCovers5250 twoPacked5250 checked5250 twoChecked5250 r hr hweight word hw he hoff
  · change r ∈ records5500 at hr
    exact twoGroup_complete bottomPairSpreadTable bottomPairRep bottomPair_lookup bottomPair_rep
      records5500 twoCovers5500 twoPacked5500 checked5500 twoChecked5500 r hr hweight word hw he hoff
  · change r ∈ records5750 at hr
    exact twoGroup_complete bottomPairSpreadTable bottomPairRep bottomPair_lookup bottomPair_rep
      records5750 twoCovers5750 twoPacked5750 checked5750 twoChecked5750 r hr hweight word hw he hoff
  · change r ∈ records6000 at hr
    exact twoGroup_complete bottomPairSpreadTable bottomPairRep bottomPair_lookup bottomPair_rep
      records6000 twoCovers6000 twoPacked6000 checked6000 twoChecked6000 r hr hweight word hw he hoff
  · change r ∈ records6250 at hr
    exact twoGroup_complete bottomPairSpreadTable bottomPairRep bottomPair_lookup bottomPair_rep
      records6250 twoCovers6250 twoPacked6250 checked6250 twoChecked6250 r hr hweight word hw he hoff
  · change r ∈ records6500 at hr
    exact twoGroup_complete bottomPairSpreadTable bottomPairRep bottomPair_lookup bottomPair_rep
      records6500 twoCovers6500 twoPacked6500 checked6500 twoChecked6500 r hr hweight word hw he hoff
  · change r ∈ records6750 at hr
    exact twoGroup_complete bottomPairSpreadTable bottomPairRep bottomPair_lookup bottomPair_rep
      records6750 twoCovers6750 twoPacked6750 checked6750 twoChecked6750 r hr hweight word hw he hoff
  · change r ∈ records7000 at hr
    exact twoGroup_complete bottomPairSpreadTable bottomPairRep bottomPair_lookup bottomPair_rep
      records7000 twoCovers7000 twoPacked7000 checked7000 twoChecked7000 r hr hweight word hw he hoff
  · change r ∈ records7250 at hr
    exact twoGroup_complete bottomPairSpreadTable bottomPairRep bottomPair_lookup bottomPair_rep
      records7250 twoCovers7250 twoPacked7250 checked7250 twoChecked7250 r hr hweight word hw he hoff
  · change r ∈ records7500 at hr
    exact twoGroup_complete bottomPairSpreadTable bottomPairRep bottomPair_lookup bottomPair_rep
      records7500 twoCovers7500 twoPacked7500 checked7500 twoChecked7500 r hr hweight word hw he hoff
  · change r ∈ records7750 at hr
    exact twoGroup_complete bottomPairSpreadTable bottomPairRep bottomPair_lookup bottomPair_rep
      records7750 twoCovers7750 twoPacked7750 checked7750 twoChecked7750 r hr hweight word hw he hoff
  · change r ∈ records8000 at hr
    exact twoGroup_complete bottomPairSpreadTable bottomPairRep bottomPair_lookup bottomPair_rep
      records8000 twoCovers8000 twoPacked8000 checked8000 twoChecked8000 r hr hweight word hw he hoff
  · change r ∈ records8250 at hr
    exact twoGroup_complete bottomPairSpreadTable bottomPairRep bottomPair_lookup bottomPair_rep
      records8250 twoCovers8250 twoPacked8250 checked8250 twoChecked8250 r hr hweight word hw he hoff
  · change r ∈ records8500 at hr
    exact twoGroup_complete bottomPairSpreadTable bottomPairRep bottomPair_lookup bottomPair_rep
      records8500 twoCovers8500 twoPacked8500 checked8500 twoChecked8500 r hr hweight word hw he hoff
  · change r ∈ records8750 at hr
    exact twoGroup_complete bottomPairSpreadTable bottomPairRep bottomPair_lookup bottomPair_rep
      records8750 twoCovers8750 twoPacked8750 checked8750 twoChecked8750 r hr hweight word hw he hoff
  · change r ∈ records9000 at hr
    exact twoGroup_complete bottomPairSpreadTable bottomPairRep bottomPair_lookup bottomPair_rep
      records9000 twoCovers9000 twoPacked9000 checked9000 twoChecked9000 r hr hweight word hw he hoff
  · change r ∈ records9250 at hr
    exact twoGroup_complete bottomPairSpreadTable bottomPairRep bottomPair_lookup bottomPair_rep
      records9250 twoCovers9250 twoPacked9250 checked9250 twoChecked9250 r hr hweight word hw he hoff
  · change r ∈ records9500 at hr
    exact twoGroup_complete bottomPairSpreadTable bottomPairRep bottomPair_lookup bottomPair_rep
      records9500 twoCovers9500 twoPacked9500 checked9500 twoChecked9500 r hr hweight word hw he hoff
  · change r ∈ records9750 at hr
    exact twoGroup_complete bottomPairSpreadTable bottomPairRep bottomPair_lookup bottomPair_rep
      records9750 twoCovers9750 twoPacked9750 checked9750 twoChecked9750 r hr hweight word hw he hoff
  · change r ∈ records10000 at hr
    exact twoGroup_complete bottomPairSpreadTable bottomPairRep bottomPair_lookup bottomPair_rep
      records10000 twoCovers10000 twoPacked10000 checked10000 twoChecked10000 r hr hweight word hw he hoff
  · change r ∈ records10250 at hr
    exact twoGroup_complete bottomPairSpreadTable bottomPairRep bottomPair_lookup bottomPair_rep
      records10250 twoCovers10250 twoPacked10250 checked10250 twoChecked10250 r hr hweight word hw he hoff
  · change r ∈ records10500 at hr
    exact twoGroup_complete bottomPairSpreadTable bottomPairRep bottomPair_lookup bottomPair_rep
      records10500 twoCovers10500 twoPacked10500 checked10500 twoChecked10500 r hr hweight word hw he hoff
  · change r ∈ records10750 at hr
    exact twoGroup_complete bottomPairSpreadTable bottomPairRep bottomPair_lookup bottomPair_rep
      records10750 twoCovers10750 twoPacked10750 checked10750 twoChecked10750 r hr hweight word hw he hoff
  · change r ∈ records11000 at hr
    exact twoGroup_complete bottomPairSpreadTable bottomPairRep bottomPair_lookup bottomPair_rep
      records11000 twoCovers11000 twoPacked11000 checked11000 twoChecked11000 r hr hweight word hw he hoff
  · change r ∈ records11250 at hr
    exact twoGroup_complete bottomPairSpreadTable bottomPairRep bottomPair_lookup bottomPair_rep
      records11250 twoCovers11250 twoPacked11250 checked11250 twoChecked11250 r hr hweight word hw he hoff
  · change r ∈ records11500 at hr
    exact twoGroup_complete bottomPairSpreadTable bottomPairRep bottomPair_lookup bottomPair_rep
      records11500 twoCovers11500 twoPacked11500 checked11500 twoChecked11500 r hr hweight word hw he hoff
  · change r ∈ records11750 at hr
    exact twoGroup_complete bottomPairSpreadTable bottomPairRep bottomPair_lookup bottomPair_rep
      records11750 twoCovers11750 twoPacked11750 checked11750 twoChecked11750 r hr hweight word hw he hoff
  · change r ∈ records12000 at hr
    exact twoGroup_complete bottomPairSpreadTable bottomPairRep bottomPair_lookup bottomPair_rep
      records12000 twoCovers12000 twoPacked12000 checked12000 twoChecked12000 r hr hweight word hw he hoff
  · change r ∈ records12250 at hr
    exact twoGroup_complete bottomPairSpreadTable bottomPairRep bottomPair_lookup bottomPair_rep
      records12250 twoCovers12250 twoPacked12250 checked12250 twoChecked12250 r hr hweight word hw he hoff
  · change r ∈ records12500 at hr
    exact twoGroup_complete bottomPairSpreadTable bottomPairRep bottomPair_lookup bottomPair_rep
      records12500 twoCovers12500 twoPacked12500 checked12500 twoChecked12500 r hr hweight word hw he hoff
  · change r ∈ records12750 at hr
    exact twoGroup_complete bottomPairSpreadTable bottomPairRep bottomPair_lookup bottomPair_rep
      records12750 twoCovers12750 twoPacked12750 checked12750 twoChecked12750 r hr hweight word hw he hoff
  · change r ∈ records13000 at hr
    exact twoGroup_complete bottomPairSpreadTable bottomPairRep bottomPair_lookup bottomPair_rep
      records13000 twoCovers13000 twoPacked13000 checked13000 twoChecked13000 r hr hweight word hw he hoff
  · change r ∈ records13250 at hr
    exact twoGroup_complete bottomPairSpreadTable bottomPairRep bottomPair_lookup bottomPair_rep
      records13250 twoCovers13250 twoPacked13250 checked13250 twoChecked13250 r hr hweight word hw he hoff
  · change r ∈ records13500 at hr
    exact twoGroup_complete bottomPairSpreadTable bottomPairRep bottomPair_lookup bottomPair_rep
      records13500 twoCovers13500 twoPacked13500 checked13500 twoChecked13500 r hr hweight word hw he hoff
  · change r ∈ records13750 at hr
    exact twoGroup_complete bottomPairSpreadTable bottomPairRep bottomPair_lookup bottomPair_rep
      records13750 twoCovers13750 twoPacked13750 checked13750 twoChecked13750 r hr hweight word hw he hoff
  · change r ∈ records14000 at hr
    exact twoGroup_complete bottomPairSpreadTable bottomPairRep bottomPair_lookup bottomPair_rep
      records14000 twoCovers14000 twoPacked14000 checked14000 twoChecked14000 r hr hweight word hw he hoff
  · change r ∈ records14250 at hr
    exact twoGroup_complete bottomPairSpreadTable bottomPairRep bottomPair_lookup bottomPair_rep
      records14250 twoCovers14250 twoPacked14250 checked14250 twoChecked14250 r hr hweight word hw he hoff
  · change r ∈ records14500 at hr
    exact twoGroup_complete bottomPairSpreadTable bottomPairRep bottomPair_lookup bottomPair_rep
      records14500 twoCovers14500 twoPacked14500 checked14500 twoChecked14500 r hr hweight word hw he hoff
  · change r ∈ records14750 at hr
    exact twoGroup_complete bottomPairSpreadTable bottomPairRep bottomPair_lookup bottomPair_rep
      records14750 twoCovers14750 twoPacked14750 checked14750 twoChecked14750 r hr hweight word hw he hoff
  · change r ∈ records15000 at hr
    exact twoGroup_complete bottomPairSpreadTable bottomPairRep bottomPair_lookup bottomPair_rep
      records15000 twoCovers15000 twoPacked15000 checked15000 twoChecked15000 r hr hweight word hw he hoff
  · change r ∈ records15250 at hr
    exact twoGroup_complete bottomPairSpreadTable bottomPairRep bottomPair_lookup bottomPair_rep
      records15250 twoCovers15250 twoPacked15250 checked15250 twoChecked15250 r hr hweight word hw he hoff
  · change r ∈ records15500 at hr
    exact twoGroup_complete bottomPairSpreadTable bottomPairRep bottomPair_lookup bottomPair_rep
      records15500 twoCovers15500 twoPacked15500 checked15500 twoChecked15500 r hr hweight word hw he hoff
  · change r ∈ records15750 at hr
    exact twoGroup_complete bottomPairSpreadTable bottomPairRep bottomPair_lookup bottomPair_rep
      records15750 twoCovers15750 twoPacked15750 checked15750 twoChecked15750 r hr hweight word hw he hoff
  · change r ∈ records16000 at hr
    exact twoGroup_complete bottomPairSpreadTable bottomPairRep bottomPair_lookup bottomPair_rep
      records16000 twoCovers16000 twoPacked16000 checked16000 twoChecked16000 r hr hweight word hw he hoff
  · change r ∈ records16250 at hr
    exact twoGroup_complete bottomPairSpreadTable bottomPairRep bottomPair_lookup bottomPair_rep
      records16250 twoCovers16250 twoPacked16250 checked16250 twoChecked16250 r hr hweight word hw he hoff
  · change r ∈ records16500 at hr
    exact twoGroup_complete bottomPairSpreadTable bottomPairRep bottomPair_lookup bottomPair_rep
      records16500 twoCovers16500 twoPacked16500 checked16500 twoChecked16500 r hr hweight word hw he hoff
  · change r ∈ records16750 at hr
    exact twoGroup_complete bottomPairSpreadTable bottomPairRep bottomPair_lookup bottomPair_rep
      records16750 twoCovers16750 twoPacked16750 checked16750 twoChecked16750 r hr hweight word hw he hoff
  · change r ∈ records17000 at hr
    exact twoGroup_complete bottomPairSpreadTable bottomPairRep bottomPair_lookup bottomPair_rep
      records17000 twoCovers17000 twoPacked17000 checked17000 twoChecked17000 r hr hweight word hw he hoff
  · change r ∈ records17250 at hr
    exact twoGroup_complete bottomPairSpreadTable bottomPairRep bottomPair_lookup bottomPair_rep
      records17250 twoCovers17250 twoPacked17250 checked17250 twoChecked17250 r hr hweight word hw he hoff
  · change r ∈ records17500 at hr
    exact twoGroup_complete bottomPairSpreadTable bottomPairRep bottomPair_lookup bottomPair_rep
      records17500 twoCovers17500 twoPacked17500 checked17500 twoChecked17500 r hr hweight word hw he hoff
  · change r ∈ records17750 at hr
    exact twoGroup_complete bottomPairSpreadTable bottomPairRep bottomPair_lookup bottomPair_rep
      records17750 twoCovers17750 twoPacked17750 checked17750 twoChecked17750 r hr hweight word hw he hoff
  · change r ∈ records18000 at hr
    exact twoGroup_complete bottomPairSpreadTable bottomPairRep bottomPair_lookup bottomPair_rep
      records18000 twoCovers18000 twoPacked18000 checked18000 twoChecked18000 r hr hweight word hw he hoff
  · change r ∈ records18250 at hr
    exact twoGroup_complete bottomPairSpreadTable bottomPairRep bottomPair_lookup bottomPair_rep
      records18250 twoCovers18250 twoPacked18250 checked18250 twoChecked18250 r hr hweight word hw he hoff
  · change r ∈ records18500 at hr
    exact twoGroup_complete bottomPairSpreadTable bottomPairRep bottomPair_lookup bottomPair_rep
      records18500 twoCovers18500 twoPacked18500 checked18500 twoChecked18500 r hr hweight word hw he hoff
  · change r ∈ records18750 at hr
    exact twoGroup_complete bottomPairSpreadTable bottomPairRep bottomPair_lookup bottomPair_rep
      records18750 twoCovers18750 twoPacked18750 checked18750 twoChecked18750 r hr hweight word hw he hoff
  · change r ∈ records19000 at hr
    exact twoGroup_complete bottomPairSpreadTable bottomPairRep bottomPair_lookup bottomPair_rep
      records19000 twoCovers19000 twoPacked19000 checked19000 twoChecked19000 r hr hweight word hw he hoff
  · change r ∈ records19250 at hr
    exact twoGroup_complete bottomPairSpreadTable bottomPairRep bottomPair_lookup bottomPair_rep
      records19250 twoCovers19250 twoPacked19250 checked19250 twoChecked19250 r hr hweight word hw he hoff
  · change r ∈ records19500 at hr
    exact twoGroup_complete bottomPairSpreadTable bottomPairRep bottomPair_lookup bottomPair_rep
      records19500 twoCovers19500 twoPacked19500 checked19500 twoChecked19500 r hr hweight word hw he hoff
  · change r ∈ records19750 at hr
    exact twoGroup_complete bottomPairSpreadTable bottomPairRep bottomPair_lookup bottomPair_rep
      records19750 twoCovers19750 twoPacked19750 checked19750 twoChecked19750 r hr hweight word hw he hoff
  · change r ∈ records20000 at hr
    exact twoGroup_complete bottomPairSpreadTable bottomPairRep bottomPair_lookup bottomPair_rep
      records20000 twoCovers20000 twoPacked20000 checked20000 twoChecked20000 r hr hweight word hw he hoff
  · change r ∈ records20250 at hr
    exact twoGroup_complete bottomPairSpreadTable bottomPairRep bottomPair_lookup bottomPair_rep
      records20250 twoCovers20250 twoPacked20250 checked20250 twoChecked20250 r hr hweight word hw he hoff
  · change r ∈ records20500 at hr
    exact twoGroup_complete bottomPairSpreadTable bottomPairRep bottomPair_lookup bottomPair_rep
      records20500 twoCovers20500 twoPacked20500 checked20500 twoChecked20500 r hr hweight word hw he hoff
  · change r ∈ records20750 at hr
    exact twoGroup_complete bottomPairSpreadTable bottomPairRep bottomPair_lookup bottomPair_rep
      records20750 twoCovers20750 twoPacked20750 checked20750 twoChecked20750 r hr hweight word hw he hoff
  · change r ∈ records21000 at hr
    exact twoGroup_complete bottomPairSpreadTable bottomPairRep bottomPair_lookup bottomPair_rep
      records21000 twoCovers21000 twoPacked21000 checked21000 twoChecked21000 r hr hweight word hw he hoff
  · change r ∈ records21250 at hr
    exact twoGroup_complete bottomPairSpreadTable bottomPairRep bottomPair_lookup bottomPair_rep
      records21250 twoCovers21250 twoPacked21250 checked21250 twoChecked21250 r hr hweight word hw he hoff
  · change r ∈ records21500 at hr
    exact twoGroup_complete bottomPairSpreadTable bottomPairRep bottomPair_lookup bottomPair_rep
      records21500 twoCovers21500 twoPacked21500 checked21500 twoChecked21500 r hr hweight word hw he hoff
  · change r ∈ records21750 at hr
    exact twoGroup_complete bottomPairSpreadTable bottomPairRep bottomPair_lookup bottomPair_rep
      records21750 twoCovers21750 twoPacked21750 checked21750 twoChecked21750 r hr hweight word hw he hoff
  · change r ∈ records22000 at hr
    exact twoGroup_complete bottomPairSpreadTable bottomPairRep bottomPair_lookup bottomPair_rep
      records22000 twoCovers22000 twoPacked22000 checked22000 twoChecked22000 r hr hweight word hw he hoff
  · change r ∈ records22250 at hr
    exact twoGroup_complete bottomPairSpreadTable bottomPairRep bottomPair_lookup bottomPair_rep
      records22250 twoCovers22250 twoPacked22250 checked22250 twoChecked22250 r hr hweight word hw he hoff
  · change r ∈ records22500 at hr
    exact twoGroup_complete bottomPairSpreadTable bottomPairRep bottomPair_lookup bottomPair_rep
      records22500 twoCovers22500 twoPacked22500 checked22500 twoChecked22500 r hr hweight word hw he hoff
  · change r ∈ records22750 at hr
    exact twoGroup_complete bottomPairSpreadTable bottomPairRep bottomPair_lookup bottomPair_rep
      records22750 twoCovers22750 twoPacked22750 checked22750 twoChecked22750 r hr hweight word hw he hoff
  · change r ∈ records23000 at hr
    exact twoGroup_complete bottomPairSpreadTable bottomPairRep bottomPair_lookup bottomPair_rep
      records23000 twoCovers23000 twoPacked23000 checked23000 twoChecked23000 r hr hweight word hw he hoff
  · change r ∈ records23250 at hr
    exact twoGroup_complete bottomPairSpreadTable bottomPairRep bottomPair_lookup bottomPair_rep
      records23250 twoCovers23250 twoPacked23250 checked23250 twoChecked23250 r hr hweight word hw he hoff
  · change r ∈ records23500 at hr
    exact twoGroup_complete bottomPairSpreadTable bottomPairRep bottomPair_lookup bottomPair_rep
      records23500 twoCovers23500 twoPacked23500 checked23500 twoChecked23500 r hr hweight word hw he hoff
  · change r ∈ records23750 at hr
    exact twoGroup_complete bottomPairSpreadTable bottomPairRep bottomPair_lookup bottomPair_rep
      records23750 twoCovers23750 twoPacked23750 checked23750 twoChecked23750 r hr hweight word hw he hoff
  · change r ∈ records24000 at hr
    exact twoGroup_complete bottomPairSpreadTable bottomPairRep bottomPair_lookup bottomPair_rep
      records24000 twoCovers24000 twoPacked24000 checked24000 twoChecked24000 r hr hweight word hw he hoff
  · change r ∈ records24250 at hr
    exact twoGroup_complete bottomPairSpreadTable bottomPairRep bottomPair_lookup bottomPair_rep
      records24250 twoCovers24250 twoPacked24250 checked24250 twoChecked24250 r hr hweight word hw he hoff
  · change r ∈ records24500 at hr
    exact twoGroup_complete bottomPairSpreadTable bottomPairRep bottomPair_lookup bottomPair_rep
      records24500 twoCovers24500 twoPacked24500 checked24500 twoChecked24500 r hr hweight word hw he hoff
  · change r ∈ records24750 at hr
    exact twoGroup_complete bottomPairSpreadTable bottomPairRep bottomPair_lookup bottomPair_rep
      records24750 twoCovers24750 twoPacked24750 checked24750 twoChecked24750 r hr hweight word hw he hoff
  · change r ∈ records25000 at hr
    exact twoGroup_complete bottomPairSpreadTable bottomPairRep bottomPair_lookup bottomPair_rep
      records25000 twoCovers25000 twoPacked25000 checked25000 twoChecked25000 r hr hweight word hw he hoff
  · change r ∈ records25250 at hr
    exact twoGroup_complete bottomPairSpreadTable bottomPairRep bottomPair_lookup bottomPair_rep
      records25250 twoCovers25250 twoPacked25250 checked25250 twoChecked25250 r hr hweight word hw he hoff
  · change r ∈ records25500 at hr
    exact twoGroup_complete bottomPairSpreadTable bottomPairRep bottomPair_lookup bottomPair_rep
      records25500 twoCovers25500 twoPacked25500 checked25500 twoChecked25500 r hr hweight word hw he hoff
  · change r ∈ records25750 at hr
    exact twoGroup_complete bottomPairSpreadTable bottomPairRep bottomPair_lookup bottomPair_rep
      records25750 twoCovers25750 twoPacked25750 checked25750 twoChecked25750 r hr hweight word hw he hoff
  · change r ∈ records26000 at hr
    exact twoGroup_complete bottomPairSpreadTable bottomPairRep bottomPair_lookup bottomPair_rep
      records26000 twoCovers26000 twoPacked26000 checked26000 twoChecked26000 r hr hweight word hw he hoff
  · change r ∈ records26250 at hr
    exact twoGroup_complete bottomPairSpreadTable bottomPairRep bottomPair_lookup bottomPair_rep
      records26250 twoCovers26250 twoPacked26250 checked26250 twoChecked26250 r hr hweight word hw he hoff
  · change r ∈ records26500 at hr
    exact twoGroup_complete bottomPairSpreadTable bottomPairRep bottomPair_lookup bottomPair_rep
      records26500 twoCovers26500 twoPacked26500 checked26500 twoChecked26500 r hr hweight word hw he hoff
  · change r ∈ records26750 at hr
    exact twoGroup_complete bottomPairSpreadTable bottomPairRep bottomPair_lookup bottomPair_rep
      records26750 twoCovers26750 twoPacked26750 checked26750 twoChecked26750 r hr hweight word hw he hoff
  · change r ∈ records27000 at hr
    exact twoGroup_complete bottomPairSpreadTable bottomPairRep bottomPair_lookup bottomPair_rep
      records27000 twoCovers27000 twoPacked27000 checked27000 twoChecked27000 r hr hweight word hw he hoff
  · change r ∈ records27250 at hr
    exact twoGroup_complete bottomPairSpreadTable bottomPairRep bottomPair_lookup bottomPair_rep
      records27250 twoCovers27250 twoPacked27250 checked27250 twoChecked27250 r hr hweight word hw he hoff
  · change r ∈ records27500 at hr
    exact twoGroup_complete bottomPairSpreadTable bottomPairRep bottomPair_lookup bottomPair_rep
      records27500 twoCovers27500 twoPacked27500 checked27500 twoChecked27500 r hr hweight word hw he hoff
  · change r ∈ records27750 at hr
    exact twoGroup_complete bottomPairSpreadTable bottomPairRep bottomPair_lookup bottomPair_rep
      records27750 twoCovers27750 twoPacked27750 checked27750 twoChecked27750 r hr hweight word hw he hoff
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every canonical cap-two fiber contains the outside support of each actual solution. -/
theorem twoFiberAt_complete (j : Fin 27867) (hweight : (fiberAt j.val).weight = 18)
    (word : Nat) (hw : word < 2^90)
    (he : reconX bottomEColumns word = reconX bottomRColumns (fiberAt j.val).beta)
    (hoff : bitCount 90 (outsideMask word (fiberAt j.val).beta) ≤ 2) :
    outsideMask word (fiberAt j.val).beta ∈ (fiberAt j.val).seeds.map Seed.off :=
  twoRecords_complete ⟨j.val/250,by omega⟩ (fiberAt j.val) (fiberAt_mem j)
    hweight word hw he hoff
#print axioms twoFiberAt_complete
end Quantum.Stabilizer.Homological.BB.Bravyi360.BottomForest
