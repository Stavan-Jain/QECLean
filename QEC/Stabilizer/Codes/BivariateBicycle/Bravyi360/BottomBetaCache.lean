/-
GENERATED FILE — DO NOT HAND-EDIT
Generator: qec-lab:experiments/bb_lab/scripts/bravyi360_kernel/generate.py
Emitter, relative to generator directory:
  emitters/compression_forest_beta_cache.py
Data and SHA-256 hashes: compression_manifest.json
Regenerate:
  QECLEAN_ROOT=/path/to/QECLean \
    python3 experiments/bb_lab/scripts/bravyi360_kernel/generate.py --force
-/

import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.BottomForest
import QEC.Stabilizer.Framework.Homological.Certificate.PackedListLookup

noncomputable section
set_option maxRecDepth 100000
namespace Quantum.Stabilizer.Homological.BB.Bravyi360.BottomForest
open F2Mask PackedDigits
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The existing packed matrix input is also an exact cache of the shadow field. -/
theorem packedGroupCheck_beta (rs : List Fiber) (p : PackedGroup)
    (h : packedGroupCheck rs p = true) : packList 256 (rs.map Fiber.beta) = p.rInput := by
  simp only [packedGroupCheck,Bool.and_eq_true,Nat.beq_eq,and_assoc] at h
  rcases h with ⟨_,_,_,_,_,_,hrI,_,_,_,_,_,_,_⟩
  simpa only [rPairs,List.map_map,Function.comp_def] using hrI
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Existing checked packed tables, addressed by their short forest chunk. -/
noncomputable def packedAt (b : Nat) : PackedGroup := (if Nat.blt b 56 then (if Nat.blt b 28 then (if Nat.blt b 14 then (if Nat.blt b 7 then (if Nat.blt b 3 then (if Nat.blt b 1 then packed0 else (if Nat.blt b 2 then packed250 else packed500)) else (if Nat.blt b 5 then (if Nat.blt b 4 then packed750 else packed1000) else (if Nat.blt b 6 then packed1250 else packed1500))) else (if Nat.blt b 10 then (if Nat.blt b 8 then packed1750 else (if Nat.blt b 9 then packed2000 else packed2250)) else (if Nat.blt b 12 then (if Nat.blt b 11 then packed2500 else packed2750) else (if Nat.blt b 13 then packed3000 else packed3250)))) else (if Nat.blt b 21 then (if Nat.blt b 17 then (if Nat.blt b 15 then packed3500 else (if Nat.blt b 16 then packed3750 else packed4000)) else (if Nat.blt b 19 then (if Nat.blt b 18 then packed4250 else packed4500) else (if Nat.blt b 20 then packed4750 else packed5000))) else (if Nat.blt b 24 then (if Nat.blt b 22 then packed5250 else (if Nat.blt b 23 then packed5500 else packed5750)) else (if Nat.blt b 26 then (if Nat.blt b 25 then packed6000 else packed6250) else (if Nat.blt b 27 then packed6500 else packed6750))))) else (if Nat.blt b 42 then (if Nat.blt b 35 then (if Nat.blt b 31 then (if Nat.blt b 29 then packed7000 else (if Nat.blt b 30 then packed7250 else packed7500)) else (if Nat.blt b 33 then (if Nat.blt b 32 then packed7750 else packed8000) else (if Nat.blt b 34 then packed8250 else packed8500))) else (if Nat.blt b 38 then (if Nat.blt b 36 then packed8750 else (if Nat.blt b 37 then packed9000 else packed9250)) else (if Nat.blt b 40 then (if Nat.blt b 39 then packed9500 else packed9750) else (if Nat.blt b 41 then packed10000 else packed10250)))) else (if Nat.blt b 49 then (if Nat.blt b 45 then (if Nat.blt b 43 then packed10500 else (if Nat.blt b 44 then packed10750 else packed11000)) else (if Nat.blt b 47 then (if Nat.blt b 46 then packed11250 else packed11500) else (if Nat.blt b 48 then packed11750 else packed12000))) else (if Nat.blt b 52 then (if Nat.blt b 50 then packed12250 else (if Nat.blt b 51 then packed12500 else packed12750)) else (if Nat.blt b 54 then (if Nat.blt b 53 then packed13000 else packed13250) else (if Nat.blt b 55 then packed13500 else packed13750)))))) else (if Nat.blt b 84 then (if Nat.blt b 70 then (if Nat.blt b 63 then (if Nat.blt b 59 then (if Nat.blt b 57 then packed14000 else (if Nat.blt b 58 then packed14250 else packed14500)) else (if Nat.blt b 61 then (if Nat.blt b 60 then packed14750 else packed15000) else (if Nat.blt b 62 then packed15250 else packed15500))) else (if Nat.blt b 66 then (if Nat.blt b 64 then packed15750 else (if Nat.blt b 65 then packed16000 else packed16250)) else (if Nat.blt b 68 then (if Nat.blt b 67 then packed16500 else packed16750) else (if Nat.blt b 69 then packed17000 else packed17250)))) else (if Nat.blt b 77 then (if Nat.blt b 73 then (if Nat.blt b 71 then packed17500 else (if Nat.blt b 72 then packed17750 else packed18000)) else (if Nat.blt b 75 then (if Nat.blt b 74 then packed18250 else packed18500) else (if Nat.blt b 76 then packed18750 else packed19000))) else (if Nat.blt b 80 then (if Nat.blt b 78 then packed19250 else (if Nat.blt b 79 then packed19500 else packed19750)) else (if Nat.blt b 82 then (if Nat.blt b 81 then packed20000 else packed20250) else (if Nat.blt b 83 then packed20500 else packed20750))))) else (if Nat.blt b 98 then (if Nat.blt b 91 then (if Nat.blt b 87 then (if Nat.blt b 85 then packed21000 else (if Nat.blt b 86 then packed21250 else packed21500)) else (if Nat.blt b 89 then (if Nat.blt b 88 then packed21750 else packed22000) else (if Nat.blt b 90 then packed22250 else packed22500))) else (if Nat.blt b 94 then (if Nat.blt b 92 then packed22750 else (if Nat.blt b 93 then packed23000 else packed23250)) else (if Nat.blt b 96 then (if Nat.blt b 95 then packed23500 else packed23750) else (if Nat.blt b 97 then packed24000 else packed24250)))) else (if Nat.blt b 105 then (if Nat.blt b 101 then (if Nat.blt b 99 then packed24500 else (if Nat.blt b 100 then packed24750 else packed25000)) else (if Nat.blt b 103 then (if Nat.blt b 102 then packed25250 else packed25500) else (if Nat.blt b 104 then packed25750 else packed26000))) else (if Nat.blt b 108 then (if Nat.blt b 106 then packed26250 else (if Nat.blt b 107 then packed26500 else packed26750)) else (if Nat.blt b 110 then (if Nat.blt b 109 then packed27000 else packed27250) else (if Nat.blt b 111 then packed27500 else packed27750)))))))
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every packed forest chunk retains its existing numerical certificate. -/
theorem packedAt_checked (b : Nat) (hb : b < 112) : packedGroupCheck (recordsAt b) (packedAt b) = true := by
  by_cases h56 : b < 56
  · by_cases h28 : b < 28
    · by_cases h14 : b < 14
      · by_cases h7 : b < 7
        · by_cases h3 : b < 3
          · by_cases h1 : b < 1
            · have heq : b = 0 := by omega
              subst b
              exact packed_checked0
            · by_cases h2 : b < 2
              · have heq : b = 1 := by omega
                subst b
                exact packed_checked250
              · have heq : b = 2 := by omega
                subst b
                exact packed_checked500
          · by_cases h5 : b < 5
            · by_cases h4 : b < 4
              · have heq : b = 3 := by omega
                subst b
                exact packed_checked750
              · have heq : b = 4 := by omega
                subst b
                exact packed_checked1000
            · by_cases h6 : b < 6
              · have heq : b = 5 := by omega
                subst b
                exact packed_checked1250
              · have heq : b = 6 := by omega
                subst b
                exact packed_checked1500
        · by_cases h10 : b < 10
          · by_cases h8 : b < 8
            · have heq : b = 7 := by omega
              subst b
              exact packed_checked1750
            · by_cases h9 : b < 9
              · have heq : b = 8 := by omega
                subst b
                exact packed_checked2000
              · have heq : b = 9 := by omega
                subst b
                exact packed_checked2250
          · by_cases h12 : b < 12
            · by_cases h11 : b < 11
              · have heq : b = 10 := by omega
                subst b
                exact packed_checked2500
              · have heq : b = 11 := by omega
                subst b
                exact packed_checked2750
            · by_cases h13 : b < 13
              · have heq : b = 12 := by omega
                subst b
                exact packed_checked3000
              · have heq : b = 13 := by omega
                subst b
                exact packed_checked3250
      · by_cases h21 : b < 21
        · by_cases h17 : b < 17
          · by_cases h15 : b < 15
            · have heq : b = 14 := by omega
              subst b
              exact packed_checked3500
            · by_cases h16 : b < 16
              · have heq : b = 15 := by omega
                subst b
                exact packed_checked3750
              · have heq : b = 16 := by omega
                subst b
                exact packed_checked4000
          · by_cases h19 : b < 19
            · by_cases h18 : b < 18
              · have heq : b = 17 := by omega
                subst b
                exact packed_checked4250
              · have heq : b = 18 := by omega
                subst b
                exact packed_checked4500
            · by_cases h20 : b < 20
              · have heq : b = 19 := by omega
                subst b
                exact packed_checked4750
              · have heq : b = 20 := by omega
                subst b
                exact packed_checked5000
        · by_cases h24 : b < 24
          · by_cases h22 : b < 22
            · have heq : b = 21 := by omega
              subst b
              exact packed_checked5250
            · by_cases h23 : b < 23
              · have heq : b = 22 := by omega
                subst b
                exact packed_checked5500
              · have heq : b = 23 := by omega
                subst b
                exact packed_checked5750
          · by_cases h26 : b < 26
            · by_cases h25 : b < 25
              · have heq : b = 24 := by omega
                subst b
                exact packed_checked6000
              · have heq : b = 25 := by omega
                subst b
                exact packed_checked6250
            · by_cases h27 : b < 27
              · have heq : b = 26 := by omega
                subst b
                exact packed_checked6500
              · have heq : b = 27 := by omega
                subst b
                exact packed_checked6750
    · by_cases h42 : b < 42
      · by_cases h35 : b < 35
        · by_cases h31 : b < 31
          · by_cases h29 : b < 29
            · have heq : b = 28 := by omega
              subst b
              exact packed_checked7000
            · by_cases h30 : b < 30
              · have heq : b = 29 := by omega
                subst b
                exact packed_checked7250
              · have heq : b = 30 := by omega
                subst b
                exact packed_checked7500
          · by_cases h33 : b < 33
            · by_cases h32 : b < 32
              · have heq : b = 31 := by omega
                subst b
                exact packed_checked7750
              · have heq : b = 32 := by omega
                subst b
                exact packed_checked8000
            · by_cases h34 : b < 34
              · have heq : b = 33 := by omega
                subst b
                exact packed_checked8250
              · have heq : b = 34 := by omega
                subst b
                exact packed_checked8500
        · by_cases h38 : b < 38
          · by_cases h36 : b < 36
            · have heq : b = 35 := by omega
              subst b
              exact packed_checked8750
            · by_cases h37 : b < 37
              · have heq : b = 36 := by omega
                subst b
                exact packed_checked9000
              · have heq : b = 37 := by omega
                subst b
                exact packed_checked9250
          · by_cases h40 : b < 40
            · by_cases h39 : b < 39
              · have heq : b = 38 := by omega
                subst b
                exact packed_checked9500
              · have heq : b = 39 := by omega
                subst b
                exact packed_checked9750
            · by_cases h41 : b < 41
              · have heq : b = 40 := by omega
                subst b
                exact packed_checked10000
              · have heq : b = 41 := by omega
                subst b
                exact packed_checked10250
      · by_cases h49 : b < 49
        · by_cases h45 : b < 45
          · by_cases h43 : b < 43
            · have heq : b = 42 := by omega
              subst b
              exact packed_checked10500
            · by_cases h44 : b < 44
              · have heq : b = 43 := by omega
                subst b
                exact packed_checked10750
              · have heq : b = 44 := by omega
                subst b
                exact packed_checked11000
          · by_cases h47 : b < 47
            · by_cases h46 : b < 46
              · have heq : b = 45 := by omega
                subst b
                exact packed_checked11250
              · have heq : b = 46 := by omega
                subst b
                exact packed_checked11500
            · by_cases h48 : b < 48
              · have heq : b = 47 := by omega
                subst b
                exact packed_checked11750
              · have heq : b = 48 := by omega
                subst b
                exact packed_checked12000
        · by_cases h52 : b < 52
          · by_cases h50 : b < 50
            · have heq : b = 49 := by omega
              subst b
              exact packed_checked12250
            · by_cases h51 : b < 51
              · have heq : b = 50 := by omega
                subst b
                exact packed_checked12500
              · have heq : b = 51 := by omega
                subst b
                exact packed_checked12750
          · by_cases h54 : b < 54
            · by_cases h53 : b < 53
              · have heq : b = 52 := by omega
                subst b
                exact packed_checked13000
              · have heq : b = 53 := by omega
                subst b
                exact packed_checked13250
            · by_cases h55 : b < 55
              · have heq : b = 54 := by omega
                subst b
                exact packed_checked13500
              · have heq : b = 55 := by omega
                subst b
                exact packed_checked13750
  · by_cases h84 : b < 84
    · by_cases h70 : b < 70
      · by_cases h63 : b < 63
        · by_cases h59 : b < 59
          · by_cases h57 : b < 57
            · have heq : b = 56 := by omega
              subst b
              exact packed_checked14000
            · by_cases h58 : b < 58
              · have heq : b = 57 := by omega
                subst b
                exact packed_checked14250
              · have heq : b = 58 := by omega
                subst b
                exact packed_checked14500
          · by_cases h61 : b < 61
            · by_cases h60 : b < 60
              · have heq : b = 59 := by omega
                subst b
                exact packed_checked14750
              · have heq : b = 60 := by omega
                subst b
                exact packed_checked15000
            · by_cases h62 : b < 62
              · have heq : b = 61 := by omega
                subst b
                exact packed_checked15250
              · have heq : b = 62 := by omega
                subst b
                exact packed_checked15500
        · by_cases h66 : b < 66
          · by_cases h64 : b < 64
            · have heq : b = 63 := by omega
              subst b
              exact packed_checked15750
            · by_cases h65 : b < 65
              · have heq : b = 64 := by omega
                subst b
                exact packed_checked16000
              · have heq : b = 65 := by omega
                subst b
                exact packed_checked16250
          · by_cases h68 : b < 68
            · by_cases h67 : b < 67
              · have heq : b = 66 := by omega
                subst b
                exact packed_checked16500
              · have heq : b = 67 := by omega
                subst b
                exact packed_checked16750
            · by_cases h69 : b < 69
              · have heq : b = 68 := by omega
                subst b
                exact packed_checked17000
              · have heq : b = 69 := by omega
                subst b
                exact packed_checked17250
      · by_cases h77 : b < 77
        · by_cases h73 : b < 73
          · by_cases h71 : b < 71
            · have heq : b = 70 := by omega
              subst b
              exact packed_checked17500
            · by_cases h72 : b < 72
              · have heq : b = 71 := by omega
                subst b
                exact packed_checked17750
              · have heq : b = 72 := by omega
                subst b
                exact packed_checked18000
          · by_cases h75 : b < 75
            · by_cases h74 : b < 74
              · have heq : b = 73 := by omega
                subst b
                exact packed_checked18250
              · have heq : b = 74 := by omega
                subst b
                exact packed_checked18500
            · by_cases h76 : b < 76
              · have heq : b = 75 := by omega
                subst b
                exact packed_checked18750
              · have heq : b = 76 := by omega
                subst b
                exact packed_checked19000
        · by_cases h80 : b < 80
          · by_cases h78 : b < 78
            · have heq : b = 77 := by omega
              subst b
              exact packed_checked19250
            · by_cases h79 : b < 79
              · have heq : b = 78 := by omega
                subst b
                exact packed_checked19500
              · have heq : b = 79 := by omega
                subst b
                exact packed_checked19750
          · by_cases h82 : b < 82
            · by_cases h81 : b < 81
              · have heq : b = 80 := by omega
                subst b
                exact packed_checked20000
              · have heq : b = 81 := by omega
                subst b
                exact packed_checked20250
            · by_cases h83 : b < 83
              · have heq : b = 82 := by omega
                subst b
                exact packed_checked20500
              · have heq : b = 83 := by omega
                subst b
                exact packed_checked20750
    · by_cases h98 : b < 98
      · by_cases h91 : b < 91
        · by_cases h87 : b < 87
          · by_cases h85 : b < 85
            · have heq : b = 84 := by omega
              subst b
              exact packed_checked21000
            · by_cases h86 : b < 86
              · have heq : b = 85 := by omega
                subst b
                exact packed_checked21250
              · have heq : b = 86 := by omega
                subst b
                exact packed_checked21500
          · by_cases h89 : b < 89
            · by_cases h88 : b < 88
              · have heq : b = 87 := by omega
                subst b
                exact packed_checked21750
              · have heq : b = 88 := by omega
                subst b
                exact packed_checked22000
            · by_cases h90 : b < 90
              · have heq : b = 89 := by omega
                subst b
                exact packed_checked22250
              · have heq : b = 90 := by omega
                subst b
                exact packed_checked22500
        · by_cases h94 : b < 94
          · by_cases h92 : b < 92
            · have heq : b = 91 := by omega
              subst b
              exact packed_checked22750
            · by_cases h93 : b < 93
              · have heq : b = 92 := by omega
                subst b
                exact packed_checked23000
              · have heq : b = 93 := by omega
                subst b
                exact packed_checked23250
          · by_cases h96 : b < 96
            · by_cases h95 : b < 95
              · have heq : b = 94 := by omega
                subst b
                exact packed_checked23500
              · have heq : b = 95 := by omega
                subst b
                exact packed_checked23750
            · by_cases h97 : b < 97
              · have heq : b = 96 := by omega
                subst b
                exact packed_checked24000
              · have heq : b = 97 := by omega
                subst b
                exact packed_checked24250
      · by_cases h105 : b < 105
        · by_cases h101 : b < 101
          · by_cases h99 : b < 99
            · have heq : b = 98 := by omega
              subst b
              exact packed_checked24500
            · by_cases h100 : b < 100
              · have heq : b = 99 := by omega
                subst b
                exact packed_checked24750
              · have heq : b = 100 := by omega
                subst b
                exact packed_checked25000
          · by_cases h103 : b < 103
            · by_cases h102 : b < 102
              · have heq : b = 101 := by omega
                subst b
                exact packed_checked25250
              · have heq : b = 102 := by omega
                subst b
                exact packed_checked25500
            · by_cases h104 : b < 104
              · have heq : b = 103 := by omega
                subst b
                exact packed_checked25750
              · have heq : b = 104 := by omega
                subst b
                exact packed_checked26000
        · by_cases h108 : b < 108
          · by_cases h106 : b < 106
            · have heq : b = 105 := by omega
              subst b
              exact packed_checked26250
            · by_cases h107 : b < 107
              · have heq : b = 106 := by omega
                subst b
                exact packed_checked26500
              · have heq : b = 107 := by omega
                subst b
                exact packed_checked26750
          · by_cases h110 : b < 110
            · by_cases h109 : b < 109
              · have heq : b = 108 := by omega
                subst b
                exact packed_checked27000
              · have heq : b = 109 := by omega
                subst b
                exact packed_checked27250
            · by_cases h111 : b < 111
              · have heq : b = 110 := by omega
                subst b
                exact packed_checked27500
              · have heq : b = 111 := by omega
                subst b
                exact packed_checked27750
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Read a shadow directly from its already checked packed cache. -/
noncomputable def betaAtFast (i : Nat) : Nat := lane 256 (i%250) (packedAt (i/250)).rInput
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The packed shadow accessor is exactly the field of the canonical forest record. -/
theorem betaAtFast_eq (i : Fin 27867) : betaAtFast i.val = (fiberAt i.val).beta := by
  have hm := Nat.mod_lt i.val (by decide : 0 < 250)
  have he := Nat.mod_add_div i.val 250
  have hb : i.val/250 < 112 := by omega
  have hi : i.val%250 < (recordsAt (i.val/250)).length := by
    rw [recordsAt_length _ hb]
    split_ifs <;> omega
  symm
  apply getD_field_eq_lane 256 (recordsAt (i.val/250)) Fiber.beta default
    (packedAt (i.val/250)).rInput
  · intro r hr
    exact lt_trans (fiberCheck_beta r (groupCheck_member _ (recordsAt_checked _ hb) r hr))
      (by decide : 2^90 < 2^256)
  · exact packedGroupCheck_beta _ _ (packedAt_checked _ hb)
  · exact hi
#print axioms betaAtFast_eq
end Quantum.Stabilizer.Homological.BB.Bravyi360.BottomForest
