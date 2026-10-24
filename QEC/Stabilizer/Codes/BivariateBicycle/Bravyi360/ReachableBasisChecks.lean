/-
GENERATED FILE — DO NOT HAND-EDIT
Generator: qec-lab:experiments/bb_lab/scripts/bravyi360_kernel/generate.py
Emitter, relative to generator directory:
  emitters/generate_trellis_bridges.py
Data and SHA-256 hashes: audit_manifest.json
Regenerate:
  QECLEAN_ROOT=/path/to/QECLean \
    python3 experiments/bb_lab/scripts/bravyi360_kernel/generate.py --force
-/

import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.TrellisBasisBridge

noncomputable section

namespace Quantum.Stabilizer.Homological.F2Mask.Trellis.Bravyi90

/-- The reachable frame's first forty-one directions and their stabilizer-span coefficients. -/
noncomputable def reachableStableChecks : List (Nat × Nat) := [
  (362652796765767564181635074, 76411879300),
  (188601134846371394278653953, 314340196320),
  (531225771639640345075253248, 382162047402),
  (679885732332369156843241488, 382162142215),
  (690766349480233181353345032, 327315137610),
  (16321013922683676493086720, 89374580815),
  (487325701517572892637790336, 317620728469),
  (574370638700485088718618688, 286044846465),
  (130568111381469411944693760, 113455659796),
  (7215840554495762889704448, 460361080580),
  (2417851641762945456669184, 67805024),
  (14507773951376663343267840, 873759686624),
  (57726724435966103117635584, 378242359296),
  (19342813134103563653353472, 17179869184),
  (116062191611013306746142720, 120804343808),
  (461813795487728824941084672, 289910292480),
  (154742505072828509226827776, 68996300800),
  (928497532888106453969141760, 10872684544),
  (529865693199085464956960768, 382162047370),
  (531905810859917510257410048, 382162047406),
  (2380137270971040207470592, 100),
  (5440386398244635546746880, 49231),
  (10880700160464156025159680, 89374531663),
  (19041098167768321659764736, 1477753987072),
  (43523091185957084373975040, 388333566740),
  (87045601283713248201277440, 49031150356),
  (152328785342146573278117888, 279172874240),
  (705995846062619472840097796, 39218970724),
  (9636348599462642218696704, 322854584420),
  (14470723681385466684243968, 10125098884),
  (696206611359575420612640800, 327315121152),
  (77090788795701137749573632, 395959099392),
  (115765789451083733473951744, 343949729792),
  (617892733735223002792984832, 358907660673),
  (616726310365609101996589056, 358908237514),
  (926126315608669867791613952, 348303673601),
  (12051543838020966608275456, 139041841380),
  (884242885203817921805025280, 275171550794),
  (1061091462244581506166030336, 107024147551),
  (96412350704167732866203648, 361062490112),
  (771298805633341862929629184, 279307091968)]

/-- The stabilizer part of the reachable frame lies in the counted stabilizer span. -/
theorem reachable_stable_checks : reachableStableChecks.all (fun gc =>
    decide (reconX stabPermutation gc.1 = reconX stabWindow gc.2)) = true := by
  decide +kernel

/-- Every combination of the reachable frame's stabilizer directions is counted. -/
theorem reachable_stable_span {word : Nat}
    (hword : XorSpan (reachableStableChecks.map Prod.fst) word) :
    XorSpan stabGenerators (reconX stabPermutation word) := by
  rw [← stab_window_generators]
  exact reconX_span_of_checks reachableStableChecks stabWindow stabPermutation
    reachable_stable_checks hword

/-- Reachable nonzero affine class 1 is exactly a counted coset offset. -/
theorem reachable_offset_1 : reconX stabPermutation 1065874952622347 = 154747230380280876349985376 := by decide +kernel

/-- Reachable nonzero affine class 2 is exactly a counted coset offset. -/
theorem reachable_offset_2 : reconX stabPermutation 1518104189649061 = 773714314175997197296277888 := by decide +kernel

/-- Reachable nonzero affine class 3 is exactly a counted coset offset. -/
theorem reachable_offset_3 : reconX stabPermutation 1880016524267950 = 618976534734651495043042272 := by decide +kernel

#print axioms reachable_stable_span
end Quantum.Stabilizer.Homological.F2Mask.Trellis.Bravyi90
