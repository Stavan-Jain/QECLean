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

import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.TopEmpty2Data
import Mathlib.Tactic.FinCases

noncomputable section

namespace Quantum.Stabilizer.Homological.BB.Bravyi360.TopEmpty
open F2Mask FiberData PackedDigits

/-- A checked matrix-dual pair census excludes the corresponding physical top fiber. -/
theorem cap2_impossible_of_data (beta target word : Nat) (planes : List (Nat × Nat))
    (hb : beta < 2^180) (hw : word < 2^180)
    (hduals : dualPlaneCertificate 180 8 topDualColumns beta planes target)
    (hpairs : filterPlanes ((planes.map Prod.snd).map
      (fastPairPlane 256 7 26 cap2SpreadTable cap2Rep)) target
      (fastPairDomain 256 7 26 cap2SpreadTable cap2Rep beta) = 0)
    (he : reconX topEColumns word = reconX topRColumns beta)
    (hoff : bitCount 180 (outsideMask word beta) ≤ 2) : False := by
  obtain ⟨hbound,hdisjoint⟩ := outsideMask_bounded_disjoint 180 word beta hw
  have hconstraints := dualPlaneCertificate_constraints 180 8 topDualColumns beta
    (outsideMask word beta) planes target hbound
    (fun coeff hann => topDual_constraint coeff beta word hw hann he) hduals
  have hcheck := hpairs
  rw [fastPairFilter_eq 256 7 26 cap2SpreadTable cap2Rep (by decide) cap2_lookup cap2_rep] at hcheck
  exact cap_two_impossible 180 8 256 182 beta (outsideMask word beta) target
    (planes.map Prod.snd) (by decide) (by decide) (by decide) (by decide) hb hbound hoff hdisjoint
    (dualPlaneCertificate_bounded 180 8 topDualColumns beta planes target hduals) hconstraints hcheck
/-- Every listed top cap-two fiber is impossible with at most two outside coordinates. -/
theorem cap2_impossible (i : Fin 143) (word : Nat) (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns (beta2 i.val))
    (hoff : bitCount 180 (outsideMask word (beta2 i.val)) ≤ 2) : False := by
  fin_cases i
  · exact cap2_impossible_of_data (beta2 0) 1023 word planes2_0 (by decide +kernel) hw duals2_0 empty2_0 he hoff
  · exact cap2_impossible_of_data (beta2 1) 1023 word planes2_1 (by decide +kernel) hw duals2_1 empty2_1 he hoff
  · exact cap2_impossible_of_data (beta2 2) 1023 word planes2_2 (by decide +kernel) hw duals2_2 empty2_2 he hoff
  · exact cap2_impossible_of_data (beta2 3) 2047 word planes2_3 (by decide +kernel) hw duals2_3 empty2_3 he hoff
  · exact cap2_impossible_of_data (beta2 4) 2047 word planes2_4 (by decide +kernel) hw duals2_4 empty2_4 he hoff
  · exact cap2_impossible_of_data (beta2 5) 1023 word planes2_5 (by decide +kernel) hw duals2_5 empty2_5 he hoff
  · exact cap2_impossible_of_data (beta2 6) 2047 word planes2_6 (by decide +kernel) hw duals2_6 empty2_6 he hoff
  · exact cap2_impossible_of_data (beta2 7) 2047 word planes2_7 (by decide +kernel) hw duals2_7 empty2_7 he hoff
  · exact cap2_impossible_of_data (beta2 8) 2047 word planes2_8 (by decide +kernel) hw duals2_8 empty2_8 he hoff
  · exact cap2_impossible_of_data (beta2 9) 2047 word planes2_9 (by decide +kernel) hw duals2_9 empty2_9 he hoff
  · exact cap2_impossible_of_data (beta2 10) 1023 word planes2_10 (by decide +kernel) hw duals2_10 empty2_10 he hoff
  · exact cap2_impossible_of_data (beta2 11) 2047 word planes2_11 (by decide +kernel) hw duals2_11 empty2_11 he hoff
  · exact cap2_impossible_of_data (beta2 12) 1023 word planes2_12 (by decide +kernel) hw duals2_12 empty2_12 he hoff
  · exact cap2_impossible_of_data (beta2 13) 2047 word planes2_13 (by decide +kernel) hw duals2_13 empty2_13 he hoff
  · exact cap2_impossible_of_data (beta2 14) 2047 word planes2_14 (by decide +kernel) hw duals2_14 empty2_14 he hoff
  · exact cap2_impossible_of_data (beta2 15) 1023 word planes2_15 (by decide +kernel) hw duals2_15 empty2_15 he hoff
  · exact cap2_impossible_of_data (beta2 16) 2047 word planes2_16 (by decide +kernel) hw duals2_16 empty2_16 he hoff
  · exact cap2_impossible_of_data (beta2 17) 1023 word planes2_17 (by decide +kernel) hw duals2_17 empty2_17 he hoff
  · exact cap2_impossible_of_data (beta2 18) 1023 word planes2_18 (by decide +kernel) hw duals2_18 empty2_18 he hoff
  · exact cap2_impossible_of_data (beta2 19) 2047 word planes2_19 (by decide +kernel) hw duals2_19 empty2_19 he hoff
  · exact cap2_impossible_of_data (beta2 20) 1023 word planes2_20 (by decide +kernel) hw duals2_20 empty2_20 he hoff
  · exact cap2_impossible_of_data (beta2 21) 2047 word planes2_21 (by decide +kernel) hw duals2_21 empty2_21 he hoff
  · exact cap2_impossible_of_data (beta2 22) 2047 word planes2_22 (by decide +kernel) hw duals2_22 empty2_22 he hoff
  · exact cap2_impossible_of_data (beta2 23) 2047 word planes2_23 (by decide +kernel) hw duals2_23 empty2_23 he hoff
  · exact cap2_impossible_of_data (beta2 24) 1023 word planes2_24 (by decide +kernel) hw duals2_24 empty2_24 he hoff
  · exact cap2_impossible_of_data (beta2 25) 2047 word planes2_25 (by decide +kernel) hw duals2_25 empty2_25 he hoff
  · exact cap2_impossible_of_data (beta2 26) 1023 word planes2_26 (by decide +kernel) hw duals2_26 empty2_26 he hoff
  · exact cap2_impossible_of_data (beta2 27) 1023 word planes2_27 (by decide +kernel) hw duals2_27 empty2_27 he hoff
  · exact cap2_impossible_of_data (beta2 28) 2047 word planes2_28 (by decide +kernel) hw duals2_28 empty2_28 he hoff
  · exact cap2_impossible_of_data (beta2 29) 2047 word planes2_29 (by decide +kernel) hw duals2_29 empty2_29 he hoff
  · exact cap2_impossible_of_data (beta2 30) 2047 word planes2_30 (by decide +kernel) hw duals2_30 empty2_30 he hoff
  · exact cap2_impossible_of_data (beta2 31) 1023 word planes2_31 (by decide +kernel) hw duals2_31 empty2_31 he hoff
  · exact cap2_impossible_of_data (beta2 32) 1023 word planes2_32 (by decide +kernel) hw duals2_32 empty2_32 he hoff
  · exact cap2_impossible_of_data (beta2 33) 1023 word planes2_33 (by decide +kernel) hw duals2_33 empty2_33 he hoff
  · exact cap2_impossible_of_data (beta2 34) 1023 word planes2_34 (by decide +kernel) hw duals2_34 empty2_34 he hoff
  · exact cap2_impossible_of_data (beta2 35) 2047 word planes2_35 (by decide +kernel) hw duals2_35 empty2_35 he hoff
  · exact cap2_impossible_of_data (beta2 36) 2047 word planes2_36 (by decide +kernel) hw duals2_36 empty2_36 he hoff
  · exact cap2_impossible_of_data (beta2 37) 2047 word planes2_37 (by decide +kernel) hw duals2_37 empty2_37 he hoff
  · exact cap2_impossible_of_data (beta2 38) 1023 word planes2_38 (by decide +kernel) hw duals2_38 empty2_38 he hoff
  · exact cap2_impossible_of_data (beta2 39) 1023 word planes2_39 (by decide +kernel) hw duals2_39 empty2_39 he hoff
  · exact cap2_impossible_of_data (beta2 40) 1023 word planes2_40 (by decide +kernel) hw duals2_40 empty2_40 he hoff
  · exact cap2_impossible_of_data (beta2 41) 2047 word planes2_41 (by decide +kernel) hw duals2_41 empty2_41 he hoff
  · exact cap2_impossible_of_data (beta2 42) 2047 word planes2_42 (by decide +kernel) hw duals2_42 empty2_42 he hoff
  · exact cap2_impossible_of_data (beta2 43) 1023 word planes2_43 (by decide +kernel) hw duals2_43 empty2_43 he hoff
  · exact cap2_impossible_of_data (beta2 44) 2047 word planes2_44 (by decide +kernel) hw duals2_44 empty2_44 he hoff
  · exact cap2_impossible_of_data (beta2 45) 1023 word planes2_45 (by decide +kernel) hw duals2_45 empty2_45 he hoff
  · exact cap2_impossible_of_data (beta2 46) 2047 word planes2_46 (by decide +kernel) hw duals2_46 empty2_46 he hoff
  · exact cap2_impossible_of_data (beta2 47) 1023 word planes2_47 (by decide +kernel) hw duals2_47 empty2_47 he hoff
  · exact cap2_impossible_of_data (beta2 48) 1023 word planes2_48 (by decide +kernel) hw duals2_48 empty2_48 he hoff
  · exact cap2_impossible_of_data (beta2 49) 1023 word planes2_49 (by decide +kernel) hw duals2_49 empty2_49 he hoff
  · exact cap2_impossible_of_data (beta2 50) 1023 word planes2_50 (by decide +kernel) hw duals2_50 empty2_50 he hoff
  · exact cap2_impossible_of_data (beta2 51) 1023 word planes2_51 (by decide +kernel) hw duals2_51 empty2_51 he hoff
  · exact cap2_impossible_of_data (beta2 52) 1023 word planes2_52 (by decide +kernel) hw duals2_52 empty2_52 he hoff
  · exact cap2_impossible_of_data (beta2 53) 1023 word planes2_53 (by decide +kernel) hw duals2_53 empty2_53 he hoff
  · exact cap2_impossible_of_data (beta2 54) 1023 word planes2_54 (by decide +kernel) hw duals2_54 empty2_54 he hoff
  · exact cap2_impossible_of_data (beta2 55) 1023 word planes2_55 (by decide +kernel) hw duals2_55 empty2_55 he hoff
  · exact cap2_impossible_of_data (beta2 56) 2047 word planes2_56 (by decide +kernel) hw duals2_56 empty2_56 he hoff
  · exact cap2_impossible_of_data (beta2 57) 2047 word planes2_57 (by decide +kernel) hw duals2_57 empty2_57 he hoff
  · exact cap2_impossible_of_data (beta2 58) 2047 word planes2_58 (by decide +kernel) hw duals2_58 empty2_58 he hoff
  · exact cap2_impossible_of_data (beta2 59) 2047 word planes2_59 (by decide +kernel) hw duals2_59 empty2_59 he hoff
  · exact cap2_impossible_of_data (beta2 60) 2047 word planes2_60 (by decide +kernel) hw duals2_60 empty2_60 he hoff
  · exact cap2_impossible_of_data (beta2 61) 1023 word planes2_61 (by decide +kernel) hw duals2_61 empty2_61 he hoff
  · exact cap2_impossible_of_data (beta2 62) 1023 word planes2_62 (by decide +kernel) hw duals2_62 empty2_62 he hoff
  · exact cap2_impossible_of_data (beta2 63) 2047 word planes2_63 (by decide +kernel) hw duals2_63 empty2_63 he hoff
  · exact cap2_impossible_of_data (beta2 64) 1023 word planes2_64 (by decide +kernel) hw duals2_64 empty2_64 he hoff
  · exact cap2_impossible_of_data (beta2 65) 2047 word planes2_65 (by decide +kernel) hw duals2_65 empty2_65 he hoff
  · exact cap2_impossible_of_data (beta2 66) 2047 word planes2_66 (by decide +kernel) hw duals2_66 empty2_66 he hoff
  · exact cap2_impossible_of_data (beta2 67) 1023 word planes2_67 (by decide +kernel) hw duals2_67 empty2_67 he hoff
  · exact cap2_impossible_of_data (beta2 68) 1023 word planes2_68 (by decide +kernel) hw duals2_68 empty2_68 he hoff
  · exact cap2_impossible_of_data (beta2 69) 2047 word planes2_69 (by decide +kernel) hw duals2_69 empty2_69 he hoff
  · exact cap2_impossible_of_data (beta2 70) 2047 word planes2_70 (by decide +kernel) hw duals2_70 empty2_70 he hoff
  · exact cap2_impossible_of_data (beta2 71) 2047 word planes2_71 (by decide +kernel) hw duals2_71 empty2_71 he hoff
  · exact cap2_impossible_of_data (beta2 72) 1023 word planes2_72 (by decide +kernel) hw duals2_72 empty2_72 he hoff
  · exact cap2_impossible_of_data (beta2 73) 2047 word planes2_73 (by decide +kernel) hw duals2_73 empty2_73 he hoff
  · exact cap2_impossible_of_data (beta2 74) 1023 word planes2_74 (by decide +kernel) hw duals2_74 empty2_74 he hoff
  · exact cap2_impossible_of_data (beta2 75) 2047 word planes2_75 (by decide +kernel) hw duals2_75 empty2_75 he hoff
  · exact cap2_impossible_of_data (beta2 76) 2047 word planes2_76 (by decide +kernel) hw duals2_76 empty2_76 he hoff
  · exact cap2_impossible_of_data (beta2 77) 1023 word planes2_77 (by decide +kernel) hw duals2_77 empty2_77 he hoff
  · exact cap2_impossible_of_data (beta2 78) 2047 word planes2_78 (by decide +kernel) hw duals2_78 empty2_78 he hoff
  · exact cap2_impossible_of_data (beta2 79) 2047 word planes2_79 (by decide +kernel) hw duals2_79 empty2_79 he hoff
  · exact cap2_impossible_of_data (beta2 80) 1023 word planes2_80 (by decide +kernel) hw duals2_80 empty2_80 he hoff
  · exact cap2_impossible_of_data (beta2 81) 1023 word planes2_81 (by decide +kernel) hw duals2_81 empty2_81 he hoff
  · exact cap2_impossible_of_data (beta2 82) 2047 word planes2_82 (by decide +kernel) hw duals2_82 empty2_82 he hoff
  · exact cap2_impossible_of_data (beta2 83) 1023 word planes2_83 (by decide +kernel) hw duals2_83 empty2_83 he hoff
  · exact cap2_impossible_of_data (beta2 84) 2047 word planes2_84 (by decide +kernel) hw duals2_84 empty2_84 he hoff
  · exact cap2_impossible_of_data (beta2 85) 1023 word planes2_85 (by decide +kernel) hw duals2_85 empty2_85 he hoff
  · exact cap2_impossible_of_data (beta2 86) 1023 word planes2_86 (by decide +kernel) hw duals2_86 empty2_86 he hoff
  · exact cap2_impossible_of_data (beta2 87) 1023 word planes2_87 (by decide +kernel) hw duals2_87 empty2_87 he hoff
  · exact cap2_impossible_of_data (beta2 88) 1023 word planes2_88 (by decide +kernel) hw duals2_88 empty2_88 he hoff
  · exact cap2_impossible_of_data (beta2 89) 2047 word planes2_89 (by decide +kernel) hw duals2_89 empty2_89 he hoff
  · exact cap2_impossible_of_data (beta2 90) 1023 word planes2_90 (by decide +kernel) hw duals2_90 empty2_90 he hoff
  · exact cap2_impossible_of_data (beta2 91) 2047 word planes2_91 (by decide +kernel) hw duals2_91 empty2_91 he hoff
  · exact cap2_impossible_of_data (beta2 92) 2047 word planes2_92 (by decide +kernel) hw duals2_92 empty2_92 he hoff
  · exact cap2_impossible_of_data (beta2 93) 1023 word planes2_93 (by decide +kernel) hw duals2_93 empty2_93 he hoff
  · exact cap2_impossible_of_data (beta2 94) 1023 word planes2_94 (by decide +kernel) hw duals2_94 empty2_94 he hoff
  · exact cap2_impossible_of_data (beta2 95) 1023 word planes2_95 (by decide +kernel) hw duals2_95 empty2_95 he hoff
  · exact cap2_impossible_of_data (beta2 96) 1023 word planes2_96 (by decide +kernel) hw duals2_96 empty2_96 he hoff
  · exact cap2_impossible_of_data (beta2 97) 2047 word planes2_97 (by decide +kernel) hw duals2_97 empty2_97 he hoff
  · exact cap2_impossible_of_data (beta2 98) 2047 word planes2_98 (by decide +kernel) hw duals2_98 empty2_98 he hoff
  · exact cap2_impossible_of_data (beta2 99) 2047 word planes2_99 (by decide +kernel) hw duals2_99 empty2_99 he hoff
  · exact cap2_impossible_of_data (beta2 100) 2047 word planes2_100 (by decide +kernel) hw duals2_100 empty2_100 he hoff
  · exact cap2_impossible_of_data (beta2 101) 2047 word planes2_101 (by decide +kernel) hw duals2_101 empty2_101 he hoff
  · exact cap2_impossible_of_data (beta2 102) 1023 word planes2_102 (by decide +kernel) hw duals2_102 empty2_102 he hoff
  · exact cap2_impossible_of_data (beta2 103) 1023 word planes2_103 (by decide +kernel) hw duals2_103 empty2_103 he hoff
  · exact cap2_impossible_of_data (beta2 104) 2047 word planes2_104 (by decide +kernel) hw duals2_104 empty2_104 he hoff
  · exact cap2_impossible_of_data (beta2 105) 2047 word planes2_105 (by decide +kernel) hw duals2_105 empty2_105 he hoff
  · exact cap2_impossible_of_data (beta2 106) 1023 word planes2_106 (by decide +kernel) hw duals2_106 empty2_106 he hoff
  · exact cap2_impossible_of_data (beta2 107) 1023 word planes2_107 (by decide +kernel) hw duals2_107 empty2_107 he hoff
  · exact cap2_impossible_of_data (beta2 108) 2047 word planes2_108 (by decide +kernel) hw duals2_108 empty2_108 he hoff
  · exact cap2_impossible_of_data (beta2 109) 2047 word planes2_109 (by decide +kernel) hw duals2_109 empty2_109 he hoff
  · exact cap2_impossible_of_data (beta2 110) 2047 word planes2_110 (by decide +kernel) hw duals2_110 empty2_110 he hoff
  · exact cap2_impossible_of_data (beta2 111) 1023 word planes2_111 (by decide +kernel) hw duals2_111 empty2_111 he hoff
  · exact cap2_impossible_of_data (beta2 112) 1023 word planes2_112 (by decide +kernel) hw duals2_112 empty2_112 he hoff
  · exact cap2_impossible_of_data (beta2 113) 2047 word planes2_113 (by decide +kernel) hw duals2_113 empty2_113 he hoff
  · exact cap2_impossible_of_data (beta2 114) 1023 word planes2_114 (by decide +kernel) hw duals2_114 empty2_114 he hoff
  · exact cap2_impossible_of_data (beta2 115) 2047 word planes2_115 (by decide +kernel) hw duals2_115 empty2_115 he hoff
  · exact cap2_impossible_of_data (beta2 116) 1023 word planes2_116 (by decide +kernel) hw duals2_116 empty2_116 he hoff
  · exact cap2_impossible_of_data (beta2 117) 2047 word planes2_117 (by decide +kernel) hw duals2_117 empty2_117 he hoff
  · exact cap2_impossible_of_data (beta2 118) 2047 word planes2_118 (by decide +kernel) hw duals2_118 empty2_118 he hoff
  · exact cap2_impossible_of_data (beta2 119) 2047 word planes2_119 (by decide +kernel) hw duals2_119 empty2_119 he hoff
  · exact cap2_impossible_of_data (beta2 120) 1023 word planes2_120 (by decide +kernel) hw duals2_120 empty2_120 he hoff
  · exact cap2_impossible_of_data (beta2 121) 2047 word planes2_121 (by decide +kernel) hw duals2_121 empty2_121 he hoff
  · exact cap2_impossible_of_data (beta2 122) 2047 word planes2_122 (by decide +kernel) hw duals2_122 empty2_122 he hoff
  · exact cap2_impossible_of_data (beta2 123) 1023 word planes2_123 (by decide +kernel) hw duals2_123 empty2_123 he hoff
  · exact cap2_impossible_of_data (beta2 124) 2047 word planes2_124 (by decide +kernel) hw duals2_124 empty2_124 he hoff
  · exact cap2_impossible_of_data (beta2 125) 1023 word planes2_125 (by decide +kernel) hw duals2_125 empty2_125 he hoff
  · exact cap2_impossible_of_data (beta2 126) 2047 word planes2_126 (by decide +kernel) hw duals2_126 empty2_126 he hoff
  · exact cap2_impossible_of_data (beta2 127) 1023 word planes2_127 (by decide +kernel) hw duals2_127 empty2_127 he hoff
  · exact cap2_impossible_of_data (beta2 128) 2047 word planes2_128 (by decide +kernel) hw duals2_128 empty2_128 he hoff
  · exact cap2_impossible_of_data (beta2 129) 1023 word planes2_129 (by decide +kernel) hw duals2_129 empty2_129 he hoff
  · exact cap2_impossible_of_data (beta2 130) 2047 word planes2_130 (by decide +kernel) hw duals2_130 empty2_130 he hoff
  · exact cap2_impossible_of_data (beta2 131) 2047 word planes2_131 (by decide +kernel) hw duals2_131 empty2_131 he hoff
  · exact cap2_impossible_of_data (beta2 132) 1023 word planes2_132 (by decide +kernel) hw duals2_132 empty2_132 he hoff
  · exact cap2_impossible_of_data (beta2 133) 1023 word planes2_133 (by decide +kernel) hw duals2_133 empty2_133 he hoff
  · exact cap2_impossible_of_data (beta2 134) 2047 word planes2_134 (by decide +kernel) hw duals2_134 empty2_134 he hoff
  · exact cap2_impossible_of_data (beta2 135) 2047 word planes2_135 (by decide +kernel) hw duals2_135 empty2_135 he hoff
  · exact cap2_impossible_of_data (beta2 136) 1023 word planes2_136 (by decide +kernel) hw duals2_136 empty2_136 he hoff
  · exact cap2_impossible_of_data (beta2 137) 2047 word planes2_137 (by decide +kernel) hw duals2_137 empty2_137 he hoff
  · exact cap2_impossible_of_data (beta2 138) 2047 word planes2_138 (by decide +kernel) hw duals2_138 empty2_138 he hoff
  · exact cap2_impossible_of_data (beta2 139) 1023 word planes2_139 (by decide +kernel) hw duals2_139 empty2_139 he hoff
  · exact cap2_impossible_of_data (beta2 140) 1023 word planes2_140 (by decide +kernel) hw duals2_140 empty2_140 he hoff
  · exact cap2_impossible_of_data (beta2 141) 1023 word planes2_141 (by decide +kernel) hw duals2_141 empty2_141 he hoff
  · exact cap2_impossible_of_data (beta2 142) 2047 word planes2_142 (by decide +kernel) hw duals2_142 empty2_142 he hoff

#print axioms cap2_impossible
end Quantum.Stabilizer.Homological.BB.Bravyi360.TopEmpty
