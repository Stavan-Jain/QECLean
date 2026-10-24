/-
GENERATED FILE — DO NOT HAND-EDIT
Generator: qec-lab:experiments/bb_lab/scripts/bravyi360_kernel/generate.py
Emitter, relative to generator directory:
  emitters/compression_shallow_links.py
Data and SHA-256 hashes: compression_manifest.json
Regenerate:
  QECLEAN_ROOT=/path/to/QECLean \
    python3 experiments/bb_lab/scripts/bravyi360_kernel/generate.py --force
-/

import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.BottomShallowLinkPart0
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.BottomShallowLinkPart1
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.BottomShallowLinkPart2
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.BottomShallowLinkPart3
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.BottomShallowLinkPart4
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.BottomShallowLinkPart5
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.BottomShallowLinkPart6
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.BottomShallowLinkPart7
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.BottomShallowLinkPart8

noncomputable section
namespace Quantum.Stabilizer.Homological.BB.Bravyi360.BottomShallow
set_option maxRecDepth 100000
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every valid census entry has its exact checked shallow-family association. -/
theorem link_checked (i : Fin 274011) : linkCheck i.val = true := by
  have hm := Nat.mod_lt i.val (by decide : 0 < 1024)
  have he := Nat.mod_add_div i.val 1024
  have hb : i.val / 1024 < 268 := by omega
  generalize hn : i.val / 1024 = b at hb
  by_cases h134 : b < 134
  · by_cases h67 : b < 67
    · by_cases h33 : b < 33
      · by_cases h16 : b < 16
        · by_cases h8 : b < 8
          · by_cases h4 : b < 4
            · by_cases h2 : b < 2
              · by_cases h1 : b < 1
                · have heq : b = 0 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked0 _ hj
                  have heq : 0+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
                · have heq : b = 1 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked1 _ hj
                  have heq : 1024+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
              · by_cases h3 : b < 3
                · have heq : b = 2 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked2 _ hj
                  have heq : 2048+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
                · have heq : b = 3 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked3 _ hj
                  have heq : 3072+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
            · by_cases h6 : b < 6
              · by_cases h5 : b < 5
                · have heq : b = 4 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked4 _ hj
                  have heq : 4096+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
                · have heq : b = 5 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked5 _ hj
                  have heq : 5120+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
              · by_cases h7 : b < 7
                · have heq : b = 6 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked6 _ hj
                  have heq : 6144+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
                · have heq : b = 7 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked7 _ hj
                  have heq : 7168+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
          · by_cases h12 : b < 12
            · by_cases h10 : b < 10
              · by_cases h9 : b < 9
                · have heq : b = 8 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked8 _ hj
                  have heq : 8192+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
                · have heq : b = 9 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked9 _ hj
                  have heq : 9216+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
              · by_cases h11 : b < 11
                · have heq : b = 10 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked10 _ hj
                  have heq : 10240+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
                · have heq : b = 11 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked11 _ hj
                  have heq : 11264+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
            · by_cases h14 : b < 14
              · by_cases h13 : b < 13
                · have heq : b = 12 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked12 _ hj
                  have heq : 12288+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
                · have heq : b = 13 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked13 _ hj
                  have heq : 13312+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
              · by_cases h15 : b < 15
                · have heq : b = 14 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked14 _ hj
                  have heq : 14336+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
                · have heq : b = 15 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked15 _ hj
                  have heq : 15360+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
        · by_cases h24 : b < 24
          · by_cases h20 : b < 20
            · by_cases h18 : b < 18
              · by_cases h17 : b < 17
                · have heq : b = 16 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked16 _ hj
                  have heq : 16384+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
                · have heq : b = 17 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked17 _ hj
                  have heq : 17408+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
              · by_cases h19 : b < 19
                · have heq : b = 18 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked18 _ hj
                  have heq : 18432+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
                · have heq : b = 19 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked19 _ hj
                  have heq : 19456+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
            · by_cases h22 : b < 22
              · by_cases h21 : b < 21
                · have heq : b = 20 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked20 _ hj
                  have heq : 20480+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
                · have heq : b = 21 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked21 _ hj
                  have heq : 21504+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
              · by_cases h23 : b < 23
                · have heq : b = 22 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked22 _ hj
                  have heq : 22528+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
                · have heq : b = 23 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked23 _ hj
                  have heq : 23552+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
          · by_cases h28 : b < 28
            · by_cases h26 : b < 26
              · by_cases h25 : b < 25
                · have heq : b = 24 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked24 _ hj
                  have heq : 24576+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
                · have heq : b = 25 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked25 _ hj
                  have heq : 25600+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
              · by_cases h27 : b < 27
                · have heq : b = 26 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked26 _ hj
                  have heq : 26624+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
                · have heq : b = 27 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked27 _ hj
                  have heq : 27648+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
            · by_cases h30 : b < 30
              · by_cases h29 : b < 29
                · have heq : b = 28 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked28 _ hj
                  have heq : 28672+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
                · have heq : b = 29 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked29 _ hj
                  have heq : 29696+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
              · by_cases h31 : b < 31
                · have heq : b = 30 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked30 _ hj
                  have heq : 30720+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
                · by_cases h32 : b < 32
                  · have heq : b = 31 := by omega
                    subst b
                    have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                    have h := List.all_eq_true.mp linkChecked31 _ hj
                    have heq : 31744+i.val%1024 = i.val := by omega
                    simpa only [heq] using h
                  · have heq : b = 32 := by omega
                    subst b
                    have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                    have h := List.all_eq_true.mp linkChecked32 _ hj
                    have heq : 32768+i.val%1024 = i.val := by omega
                    simpa only [heq] using h
      · by_cases h50 : b < 50
        · by_cases h41 : b < 41
          · by_cases h37 : b < 37
            · by_cases h35 : b < 35
              · by_cases h34 : b < 34
                · have heq : b = 33 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked33 _ hj
                  have heq : 33792+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
                · have heq : b = 34 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked34 _ hj
                  have heq : 34816+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
              · by_cases h36 : b < 36
                · have heq : b = 35 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked35 _ hj
                  have heq : 35840+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
                · have heq : b = 36 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked36 _ hj
                  have heq : 36864+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
            · by_cases h39 : b < 39
              · by_cases h38 : b < 38
                · have heq : b = 37 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked37 _ hj
                  have heq : 37888+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
                · have heq : b = 38 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked38 _ hj
                  have heq : 38912+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
              · by_cases h40 : b < 40
                · have heq : b = 39 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked39 _ hj
                  have heq : 39936+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
                · have heq : b = 40 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked40 _ hj
                  have heq : 40960+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
          · by_cases h45 : b < 45
            · by_cases h43 : b < 43
              · by_cases h42 : b < 42
                · have heq : b = 41 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked41 _ hj
                  have heq : 41984+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
                · have heq : b = 42 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked42 _ hj
                  have heq : 43008+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
              · by_cases h44 : b < 44
                · have heq : b = 43 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked43 _ hj
                  have heq : 44032+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
                · have heq : b = 44 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked44 _ hj
                  have heq : 45056+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
            · by_cases h47 : b < 47
              · by_cases h46 : b < 46
                · have heq : b = 45 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked45 _ hj
                  have heq : 46080+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
                · have heq : b = 46 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked46 _ hj
                  have heq : 47104+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
              · by_cases h48 : b < 48
                · have heq : b = 47 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked47 _ hj
                  have heq : 48128+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
                · by_cases h49 : b < 49
                  · have heq : b = 48 := by omega
                    subst b
                    have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                    have h := List.all_eq_true.mp linkChecked48 _ hj
                    have heq : 49152+i.val%1024 = i.val := by omega
                    simpa only [heq] using h
                  · have heq : b = 49 := by omega
                    subst b
                    have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                    have h := List.all_eq_true.mp linkChecked49 _ hj
                    have heq : 50176+i.val%1024 = i.val := by omega
                    simpa only [heq] using h
        · by_cases h58 : b < 58
          · by_cases h54 : b < 54
            · by_cases h52 : b < 52
              · by_cases h51 : b < 51
                · have heq : b = 50 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked50 _ hj
                  have heq : 51200+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
                · have heq : b = 51 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked51 _ hj
                  have heq : 52224+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
              · by_cases h53 : b < 53
                · have heq : b = 52 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked52 _ hj
                  have heq : 53248+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
                · have heq : b = 53 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked53 _ hj
                  have heq : 54272+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
            · by_cases h56 : b < 56
              · by_cases h55 : b < 55
                · have heq : b = 54 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked54 _ hj
                  have heq : 55296+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
                · have heq : b = 55 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked55 _ hj
                  have heq : 56320+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
              · by_cases h57 : b < 57
                · have heq : b = 56 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked56 _ hj
                  have heq : 57344+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
                · have heq : b = 57 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked57 _ hj
                  have heq : 58368+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
          · by_cases h62 : b < 62
            · by_cases h60 : b < 60
              · by_cases h59 : b < 59
                · have heq : b = 58 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked58 _ hj
                  have heq : 59392+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
                · have heq : b = 59 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked59 _ hj
                  have heq : 60416+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
              · by_cases h61 : b < 61
                · have heq : b = 60 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked60 _ hj
                  have heq : 61440+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
                · have heq : b = 61 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked61 _ hj
                  have heq : 62464+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
            · by_cases h64 : b < 64
              · by_cases h63 : b < 63
                · have heq : b = 62 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked62 _ hj
                  have heq : 63488+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
                · have heq : b = 63 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked63 _ hj
                  have heq : 64512+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
              · by_cases h65 : b < 65
                · have heq : b = 64 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked64 _ hj
                  have heq : 65536+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
                · by_cases h66 : b < 66
                  · have heq : b = 65 := by omega
                    subst b
                    have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                    have h := List.all_eq_true.mp linkChecked65 _ hj
                    have heq : 66560+i.val%1024 = i.val := by omega
                    simpa only [heq] using h
                  · have heq : b = 66 := by omega
                    subst b
                    have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                    have h := List.all_eq_true.mp linkChecked66 _ hj
                    have heq : 67584+i.val%1024 = i.val := by omega
                    simpa only [heq] using h
    · by_cases h100 : b < 100
      · by_cases h83 : b < 83
        · by_cases h75 : b < 75
          · by_cases h71 : b < 71
            · by_cases h69 : b < 69
              · by_cases h68 : b < 68
                · have heq : b = 67 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked67 _ hj
                  have heq : 68608+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
                · have heq : b = 68 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked68 _ hj
                  have heq : 69632+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
              · by_cases h70 : b < 70
                · have heq : b = 69 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked69 _ hj
                  have heq : 70656+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
                · have heq : b = 70 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked70 _ hj
                  have heq : 71680+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
            · by_cases h73 : b < 73
              · by_cases h72 : b < 72
                · have heq : b = 71 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked71 _ hj
                  have heq : 72704+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
                · have heq : b = 72 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked72 _ hj
                  have heq : 73728+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
              · by_cases h74 : b < 74
                · have heq : b = 73 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked73 _ hj
                  have heq : 74752+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
                · have heq : b = 74 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked74 _ hj
                  have heq : 75776+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
          · by_cases h79 : b < 79
            · by_cases h77 : b < 77
              · by_cases h76 : b < 76
                · have heq : b = 75 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked75 _ hj
                  have heq : 76800+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
                · have heq : b = 76 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked76 _ hj
                  have heq : 77824+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
              · by_cases h78 : b < 78
                · have heq : b = 77 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked77 _ hj
                  have heq : 78848+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
                · have heq : b = 78 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked78 _ hj
                  have heq : 79872+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
            · by_cases h81 : b < 81
              · by_cases h80 : b < 80
                · have heq : b = 79 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked79 _ hj
                  have heq : 80896+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
                · have heq : b = 80 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked80 _ hj
                  have heq : 81920+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
              · by_cases h82 : b < 82
                · have heq : b = 81 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked81 _ hj
                  have heq : 82944+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
                · have heq : b = 82 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked82 _ hj
                  have heq : 83968+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
        · by_cases h91 : b < 91
          · by_cases h87 : b < 87
            · by_cases h85 : b < 85
              · by_cases h84 : b < 84
                · have heq : b = 83 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked83 _ hj
                  have heq : 84992+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
                · have heq : b = 84 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked84 _ hj
                  have heq : 86016+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
              · by_cases h86 : b < 86
                · have heq : b = 85 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked85 _ hj
                  have heq : 87040+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
                · have heq : b = 86 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked86 _ hj
                  have heq : 88064+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
            · by_cases h89 : b < 89
              · by_cases h88 : b < 88
                · have heq : b = 87 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked87 _ hj
                  have heq : 89088+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
                · have heq : b = 88 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked88 _ hj
                  have heq : 90112+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
              · by_cases h90 : b < 90
                · have heq : b = 89 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked89 _ hj
                  have heq : 91136+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
                · have heq : b = 90 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked90 _ hj
                  have heq : 92160+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
          · by_cases h95 : b < 95
            · by_cases h93 : b < 93
              · by_cases h92 : b < 92
                · have heq : b = 91 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked91 _ hj
                  have heq : 93184+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
                · have heq : b = 92 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked92 _ hj
                  have heq : 94208+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
              · by_cases h94 : b < 94
                · have heq : b = 93 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked93 _ hj
                  have heq : 95232+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
                · have heq : b = 94 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked94 _ hj
                  have heq : 96256+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
            · by_cases h97 : b < 97
              · by_cases h96 : b < 96
                · have heq : b = 95 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked95 _ hj
                  have heq : 97280+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
                · have heq : b = 96 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked96 _ hj
                  have heq : 98304+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
              · by_cases h98 : b < 98
                · have heq : b = 97 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked97 _ hj
                  have heq : 99328+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
                · by_cases h99 : b < 99
                  · have heq : b = 98 := by omega
                    subst b
                    have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                    have h := List.all_eq_true.mp linkChecked98 _ hj
                    have heq : 100352+i.val%1024 = i.val := by omega
                    simpa only [heq] using h
                  · have heq : b = 99 := by omega
                    subst b
                    have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                    have h := List.all_eq_true.mp linkChecked99 _ hj
                    have heq : 101376+i.val%1024 = i.val := by omega
                    simpa only [heq] using h
      · by_cases h117 : b < 117
        · by_cases h108 : b < 108
          · by_cases h104 : b < 104
            · by_cases h102 : b < 102
              · by_cases h101 : b < 101
                · have heq : b = 100 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked100 _ hj
                  have heq : 102400+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
                · have heq : b = 101 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked101 _ hj
                  have heq : 103424+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
              · by_cases h103 : b < 103
                · have heq : b = 102 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked102 _ hj
                  have heq : 104448+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
                · have heq : b = 103 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked103 _ hj
                  have heq : 105472+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
            · by_cases h106 : b < 106
              · by_cases h105 : b < 105
                · have heq : b = 104 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked104 _ hj
                  have heq : 106496+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
                · have heq : b = 105 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked105 _ hj
                  have heq : 107520+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
              · by_cases h107 : b < 107
                · have heq : b = 106 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked106 _ hj
                  have heq : 108544+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
                · have heq : b = 107 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked107 _ hj
                  have heq : 109568+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
          · by_cases h112 : b < 112
            · by_cases h110 : b < 110
              · by_cases h109 : b < 109
                · have heq : b = 108 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked108 _ hj
                  have heq : 110592+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
                · have heq : b = 109 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked109 _ hj
                  have heq : 111616+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
              · by_cases h111 : b < 111
                · have heq : b = 110 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked110 _ hj
                  have heq : 112640+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
                · have heq : b = 111 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked111 _ hj
                  have heq : 113664+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
            · by_cases h114 : b < 114
              · by_cases h113 : b < 113
                · have heq : b = 112 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked112 _ hj
                  have heq : 114688+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
                · have heq : b = 113 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked113 _ hj
                  have heq : 115712+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
              · by_cases h115 : b < 115
                · have heq : b = 114 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked114 _ hj
                  have heq : 116736+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
                · by_cases h116 : b < 116
                  · have heq : b = 115 := by omega
                    subst b
                    have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                    have h := List.all_eq_true.mp linkChecked115 _ hj
                    have heq : 117760+i.val%1024 = i.val := by omega
                    simpa only [heq] using h
                  · have heq : b = 116 := by omega
                    subst b
                    have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                    have h := List.all_eq_true.mp linkChecked116 _ hj
                    have heq : 118784+i.val%1024 = i.val := by omega
                    simpa only [heq] using h
        · by_cases h125 : b < 125
          · by_cases h121 : b < 121
            · by_cases h119 : b < 119
              · by_cases h118 : b < 118
                · have heq : b = 117 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked117 _ hj
                  have heq : 119808+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
                · have heq : b = 118 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked118 _ hj
                  have heq : 120832+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
              · by_cases h120 : b < 120
                · have heq : b = 119 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked119 _ hj
                  have heq : 121856+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
                · have heq : b = 120 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked120 _ hj
                  have heq : 122880+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
            · by_cases h123 : b < 123
              · by_cases h122 : b < 122
                · have heq : b = 121 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked121 _ hj
                  have heq : 123904+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
                · have heq : b = 122 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked122 _ hj
                  have heq : 124928+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
              · by_cases h124 : b < 124
                · have heq : b = 123 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked123 _ hj
                  have heq : 125952+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
                · have heq : b = 124 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked124 _ hj
                  have heq : 126976+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
          · by_cases h129 : b < 129
            · by_cases h127 : b < 127
              · by_cases h126 : b < 126
                · have heq : b = 125 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked125 _ hj
                  have heq : 128000+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
                · have heq : b = 126 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked126 _ hj
                  have heq : 129024+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
              · by_cases h128 : b < 128
                · have heq : b = 127 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked127 _ hj
                  have heq : 130048+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
                · have heq : b = 128 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked128 _ hj
                  have heq : 131072+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
            · by_cases h131 : b < 131
              · by_cases h130 : b < 130
                · have heq : b = 129 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked129 _ hj
                  have heq : 132096+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
                · have heq : b = 130 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked130 _ hj
                  have heq : 133120+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
              · by_cases h132 : b < 132
                · have heq : b = 131 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked131 _ hj
                  have heq : 134144+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
                · by_cases h133 : b < 133
                  · have heq : b = 132 := by omega
                    subst b
                    have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                    have h := List.all_eq_true.mp linkChecked132 _ hj
                    have heq : 135168+i.val%1024 = i.val := by omega
                    simpa only [heq] using h
                  · have heq : b = 133 := by omega
                    subst b
                    have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                    have h := List.all_eq_true.mp linkChecked133 _ hj
                    have heq : 136192+i.val%1024 = i.val := by omega
                    simpa only [heq] using h
  · by_cases h201 : b < 201
    · by_cases h167 : b < 167
      · by_cases h150 : b < 150
        · by_cases h142 : b < 142
          · by_cases h138 : b < 138
            · by_cases h136 : b < 136
              · by_cases h135 : b < 135
                · have heq : b = 134 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked134 _ hj
                  have heq : 137216+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
                · have heq : b = 135 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked135 _ hj
                  have heq : 138240+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
              · by_cases h137 : b < 137
                · have heq : b = 136 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked136 _ hj
                  have heq : 139264+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
                · have heq : b = 137 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked137 _ hj
                  have heq : 140288+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
            · by_cases h140 : b < 140
              · by_cases h139 : b < 139
                · have heq : b = 138 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked138 _ hj
                  have heq : 141312+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
                · have heq : b = 139 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked139 _ hj
                  have heq : 142336+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
              · by_cases h141 : b < 141
                · have heq : b = 140 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked140 _ hj
                  have heq : 143360+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
                · have heq : b = 141 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked141 _ hj
                  have heq : 144384+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
          · by_cases h146 : b < 146
            · by_cases h144 : b < 144
              · by_cases h143 : b < 143
                · have heq : b = 142 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked142 _ hj
                  have heq : 145408+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
                · have heq : b = 143 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked143 _ hj
                  have heq : 146432+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
              · by_cases h145 : b < 145
                · have heq : b = 144 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked144 _ hj
                  have heq : 147456+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
                · have heq : b = 145 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked145 _ hj
                  have heq : 148480+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
            · by_cases h148 : b < 148
              · by_cases h147 : b < 147
                · have heq : b = 146 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked146 _ hj
                  have heq : 149504+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
                · have heq : b = 147 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked147 _ hj
                  have heq : 150528+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
              · by_cases h149 : b < 149
                · have heq : b = 148 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked148 _ hj
                  have heq : 151552+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
                · have heq : b = 149 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked149 _ hj
                  have heq : 152576+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
        · by_cases h158 : b < 158
          · by_cases h154 : b < 154
            · by_cases h152 : b < 152
              · by_cases h151 : b < 151
                · have heq : b = 150 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked150 _ hj
                  have heq : 153600+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
                · have heq : b = 151 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked151 _ hj
                  have heq : 154624+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
              · by_cases h153 : b < 153
                · have heq : b = 152 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked152 _ hj
                  have heq : 155648+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
                · have heq : b = 153 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked153 _ hj
                  have heq : 156672+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
            · by_cases h156 : b < 156
              · by_cases h155 : b < 155
                · have heq : b = 154 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked154 _ hj
                  have heq : 157696+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
                · have heq : b = 155 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked155 _ hj
                  have heq : 158720+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
              · by_cases h157 : b < 157
                · have heq : b = 156 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked156 _ hj
                  have heq : 159744+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
                · have heq : b = 157 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked157 _ hj
                  have heq : 160768+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
          · by_cases h162 : b < 162
            · by_cases h160 : b < 160
              · by_cases h159 : b < 159
                · have heq : b = 158 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked158 _ hj
                  have heq : 161792+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
                · have heq : b = 159 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked159 _ hj
                  have heq : 162816+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
              · by_cases h161 : b < 161
                · have heq : b = 160 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked160 _ hj
                  have heq : 163840+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
                · have heq : b = 161 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked161 _ hj
                  have heq : 164864+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
            · by_cases h164 : b < 164
              · by_cases h163 : b < 163
                · have heq : b = 162 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked162 _ hj
                  have heq : 165888+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
                · have heq : b = 163 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked163 _ hj
                  have heq : 166912+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
              · by_cases h165 : b < 165
                · have heq : b = 164 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked164 _ hj
                  have heq : 167936+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
                · by_cases h166 : b < 166
                  · have heq : b = 165 := by omega
                    subst b
                    have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                    have h := List.all_eq_true.mp linkChecked165 _ hj
                    have heq : 168960+i.val%1024 = i.val := by omega
                    simpa only [heq] using h
                  · have heq : b = 166 := by omega
                    subst b
                    have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                    have h := List.all_eq_true.mp linkChecked166 _ hj
                    have heq : 169984+i.val%1024 = i.val := by omega
                    simpa only [heq] using h
      · by_cases h184 : b < 184
        · by_cases h175 : b < 175
          · by_cases h171 : b < 171
            · by_cases h169 : b < 169
              · by_cases h168 : b < 168
                · have heq : b = 167 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked167 _ hj
                  have heq : 171008+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
                · have heq : b = 168 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked168 _ hj
                  have heq : 172032+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
              · by_cases h170 : b < 170
                · have heq : b = 169 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked169 _ hj
                  have heq : 173056+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
                · have heq : b = 170 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked170 _ hj
                  have heq : 174080+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
            · by_cases h173 : b < 173
              · by_cases h172 : b < 172
                · have heq : b = 171 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked171 _ hj
                  have heq : 175104+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
                · have heq : b = 172 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked172 _ hj
                  have heq : 176128+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
              · by_cases h174 : b < 174
                · have heq : b = 173 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked173 _ hj
                  have heq : 177152+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
                · have heq : b = 174 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked174 _ hj
                  have heq : 178176+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
          · by_cases h179 : b < 179
            · by_cases h177 : b < 177
              · by_cases h176 : b < 176
                · have heq : b = 175 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked175 _ hj
                  have heq : 179200+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
                · have heq : b = 176 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked176 _ hj
                  have heq : 180224+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
              · by_cases h178 : b < 178
                · have heq : b = 177 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked177 _ hj
                  have heq : 181248+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
                · have heq : b = 178 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked178 _ hj
                  have heq : 182272+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
            · by_cases h181 : b < 181
              · by_cases h180 : b < 180
                · have heq : b = 179 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked179 _ hj
                  have heq : 183296+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
                · have heq : b = 180 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked180 _ hj
                  have heq : 184320+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
              · by_cases h182 : b < 182
                · have heq : b = 181 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked181 _ hj
                  have heq : 185344+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
                · by_cases h183 : b < 183
                  · have heq : b = 182 := by omega
                    subst b
                    have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                    have h := List.all_eq_true.mp linkChecked182 _ hj
                    have heq : 186368+i.val%1024 = i.val := by omega
                    simpa only [heq] using h
                  · have heq : b = 183 := by omega
                    subst b
                    have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                    have h := List.all_eq_true.mp linkChecked183 _ hj
                    have heq : 187392+i.val%1024 = i.val := by omega
                    simpa only [heq] using h
        · by_cases h192 : b < 192
          · by_cases h188 : b < 188
            · by_cases h186 : b < 186
              · by_cases h185 : b < 185
                · have heq : b = 184 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked184 _ hj
                  have heq : 188416+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
                · have heq : b = 185 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked185 _ hj
                  have heq : 189440+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
              · by_cases h187 : b < 187
                · have heq : b = 186 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked186 _ hj
                  have heq : 190464+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
                · have heq : b = 187 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked187 _ hj
                  have heq : 191488+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
            · by_cases h190 : b < 190
              · by_cases h189 : b < 189
                · have heq : b = 188 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked188 _ hj
                  have heq : 192512+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
                · have heq : b = 189 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked189 _ hj
                  have heq : 193536+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
              · by_cases h191 : b < 191
                · have heq : b = 190 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked190 _ hj
                  have heq : 194560+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
                · have heq : b = 191 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked191 _ hj
                  have heq : 195584+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
          · by_cases h196 : b < 196
            · by_cases h194 : b < 194
              · by_cases h193 : b < 193
                · have heq : b = 192 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked192 _ hj
                  have heq : 196608+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
                · have heq : b = 193 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked193 _ hj
                  have heq : 197632+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
              · by_cases h195 : b < 195
                · have heq : b = 194 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked194 _ hj
                  have heq : 198656+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
                · have heq : b = 195 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked195 _ hj
                  have heq : 199680+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
            · by_cases h198 : b < 198
              · by_cases h197 : b < 197
                · have heq : b = 196 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked196 _ hj
                  have heq : 200704+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
                · have heq : b = 197 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked197 _ hj
                  have heq : 201728+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
              · by_cases h199 : b < 199
                · have heq : b = 198 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked198 _ hj
                  have heq : 202752+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
                · by_cases h200 : b < 200
                  · have heq : b = 199 := by omega
                    subst b
                    have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                    have h := List.all_eq_true.mp linkChecked199 _ hj
                    have heq : 203776+i.val%1024 = i.val := by omega
                    simpa only [heq] using h
                  · have heq : b = 200 := by omega
                    subst b
                    have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                    have h := List.all_eq_true.mp linkChecked200 _ hj
                    have heq : 204800+i.val%1024 = i.val := by omega
                    simpa only [heq] using h
    · by_cases h234 : b < 234
      · by_cases h217 : b < 217
        · by_cases h209 : b < 209
          · by_cases h205 : b < 205
            · by_cases h203 : b < 203
              · by_cases h202 : b < 202
                · have heq : b = 201 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked201 _ hj
                  have heq : 205824+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
                · have heq : b = 202 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked202 _ hj
                  have heq : 206848+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
              · by_cases h204 : b < 204
                · have heq : b = 203 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked203 _ hj
                  have heq : 207872+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
                · have heq : b = 204 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked204 _ hj
                  have heq : 208896+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
            · by_cases h207 : b < 207
              · by_cases h206 : b < 206
                · have heq : b = 205 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked205 _ hj
                  have heq : 209920+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
                · have heq : b = 206 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked206 _ hj
                  have heq : 210944+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
              · by_cases h208 : b < 208
                · have heq : b = 207 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked207 _ hj
                  have heq : 211968+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
                · have heq : b = 208 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked208 _ hj
                  have heq : 212992+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
          · by_cases h213 : b < 213
            · by_cases h211 : b < 211
              · by_cases h210 : b < 210
                · have heq : b = 209 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked209 _ hj
                  have heq : 214016+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
                · have heq : b = 210 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked210 _ hj
                  have heq : 215040+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
              · by_cases h212 : b < 212
                · have heq : b = 211 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked211 _ hj
                  have heq : 216064+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
                · have heq : b = 212 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked212 _ hj
                  have heq : 217088+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
            · by_cases h215 : b < 215
              · by_cases h214 : b < 214
                · have heq : b = 213 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked213 _ hj
                  have heq : 218112+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
                · have heq : b = 214 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked214 _ hj
                  have heq : 219136+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
              · by_cases h216 : b < 216
                · have heq : b = 215 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked215 _ hj
                  have heq : 220160+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
                · have heq : b = 216 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked216 _ hj
                  have heq : 221184+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
        · by_cases h225 : b < 225
          · by_cases h221 : b < 221
            · by_cases h219 : b < 219
              · by_cases h218 : b < 218
                · have heq : b = 217 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked217 _ hj
                  have heq : 222208+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
                · have heq : b = 218 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked218 _ hj
                  have heq : 223232+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
              · by_cases h220 : b < 220
                · have heq : b = 219 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked219 _ hj
                  have heq : 224256+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
                · have heq : b = 220 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked220 _ hj
                  have heq : 225280+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
            · by_cases h223 : b < 223
              · by_cases h222 : b < 222
                · have heq : b = 221 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked221 _ hj
                  have heq : 226304+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
                · have heq : b = 222 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked222 _ hj
                  have heq : 227328+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
              · by_cases h224 : b < 224
                · have heq : b = 223 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked223 _ hj
                  have heq : 228352+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
                · have heq : b = 224 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked224 _ hj
                  have heq : 229376+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
          · by_cases h229 : b < 229
            · by_cases h227 : b < 227
              · by_cases h226 : b < 226
                · have heq : b = 225 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked225 _ hj
                  have heq : 230400+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
                · have heq : b = 226 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked226 _ hj
                  have heq : 231424+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
              · by_cases h228 : b < 228
                · have heq : b = 227 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked227 _ hj
                  have heq : 232448+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
                · have heq : b = 228 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked228 _ hj
                  have heq : 233472+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
            · by_cases h231 : b < 231
              · by_cases h230 : b < 230
                · have heq : b = 229 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked229 _ hj
                  have heq : 234496+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
                · have heq : b = 230 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked230 _ hj
                  have heq : 235520+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
              · by_cases h232 : b < 232
                · have heq : b = 231 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked231 _ hj
                  have heq : 236544+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
                · by_cases h233 : b < 233
                  · have heq : b = 232 := by omega
                    subst b
                    have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                    have h := List.all_eq_true.mp linkChecked232 _ hj
                    have heq : 237568+i.val%1024 = i.val := by omega
                    simpa only [heq] using h
                  · have heq : b = 233 := by omega
                    subst b
                    have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                    have h := List.all_eq_true.mp linkChecked233 _ hj
                    have heq : 238592+i.val%1024 = i.val := by omega
                    simpa only [heq] using h
      · by_cases h251 : b < 251
        · by_cases h242 : b < 242
          · by_cases h238 : b < 238
            · by_cases h236 : b < 236
              · by_cases h235 : b < 235
                · have heq : b = 234 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked234 _ hj
                  have heq : 239616+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
                · have heq : b = 235 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked235 _ hj
                  have heq : 240640+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
              · by_cases h237 : b < 237
                · have heq : b = 236 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked236 _ hj
                  have heq : 241664+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
                · have heq : b = 237 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked237 _ hj
                  have heq : 242688+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
            · by_cases h240 : b < 240
              · by_cases h239 : b < 239
                · have heq : b = 238 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked238 _ hj
                  have heq : 243712+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
                · have heq : b = 239 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked239 _ hj
                  have heq : 244736+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
              · by_cases h241 : b < 241
                · have heq : b = 240 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked240 _ hj
                  have heq : 245760+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
                · have heq : b = 241 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked241 _ hj
                  have heq : 246784+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
          · by_cases h246 : b < 246
            · by_cases h244 : b < 244
              · by_cases h243 : b < 243
                · have heq : b = 242 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked242 _ hj
                  have heq : 247808+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
                · have heq : b = 243 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked243 _ hj
                  have heq : 248832+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
              · by_cases h245 : b < 245
                · have heq : b = 244 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked244 _ hj
                  have heq : 249856+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
                · have heq : b = 245 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked245 _ hj
                  have heq : 250880+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
            · by_cases h248 : b < 248
              · by_cases h247 : b < 247
                · have heq : b = 246 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked246 _ hj
                  have heq : 251904+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
                · have heq : b = 247 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked247 _ hj
                  have heq : 252928+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
              · by_cases h249 : b < 249
                · have heq : b = 248 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked248 _ hj
                  have heq : 253952+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
                · by_cases h250 : b < 250
                  · have heq : b = 249 := by omega
                    subst b
                    have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                    have h := List.all_eq_true.mp linkChecked249 _ hj
                    have heq : 254976+i.val%1024 = i.val := by omega
                    simpa only [heq] using h
                  · have heq : b = 250 := by omega
                    subst b
                    have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                    have h := List.all_eq_true.mp linkChecked250 _ hj
                    have heq : 256000+i.val%1024 = i.val := by omega
                    simpa only [heq] using h
        · by_cases h259 : b < 259
          · by_cases h255 : b < 255
            · by_cases h253 : b < 253
              · by_cases h252 : b < 252
                · have heq : b = 251 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked251 _ hj
                  have heq : 257024+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
                · have heq : b = 252 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked252 _ hj
                  have heq : 258048+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
              · by_cases h254 : b < 254
                · have heq : b = 253 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked253 _ hj
                  have heq : 259072+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
                · have heq : b = 254 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked254 _ hj
                  have heq : 260096+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
            · by_cases h257 : b < 257
              · by_cases h256 : b < 256
                · have heq : b = 255 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked255 _ hj
                  have heq : 261120+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
                · have heq : b = 256 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked256 _ hj
                  have heq : 262144+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
              · by_cases h258 : b < 258
                · have heq : b = 257 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked257 _ hj
                  have heq : 263168+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
                · have heq : b = 258 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked258 _ hj
                  have heq : 264192+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
          · by_cases h263 : b < 263
            · by_cases h261 : b < 261
              · by_cases h260 : b < 260
                · have heq : b = 259 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked259 _ hj
                  have heq : 265216+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
                · have heq : b = 260 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked260 _ hj
                  have heq : 266240+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
              · by_cases h262 : b < 262
                · have heq : b = 261 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked261 _ hj
                  have heq : 267264+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
                · have heq : b = 262 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked262 _ hj
                  have heq : 268288+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
            · by_cases h265 : b < 265
              · by_cases h264 : b < 264
                · have heq : b = 263 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked263 _ hj
                  have heq : 269312+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
                · have heq : b = 264 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked264 _ hj
                  have heq : 270336+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
              · by_cases h266 : b < 266
                · have heq : b = 265 := by omega
                  subst b
                  have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                  have h := List.all_eq_true.mp linkChecked265 _ hj
                  have heq : 271360+i.val%1024 = i.val := by omega
                  simpa only [heq] using h
                · by_cases h267 : b < 267
                  · have heq : b = 266 := by omega
                    subst b
                    have hj : i.val%1024 ∈ List.range 1024 := List.mem_range.mpr (by omega)
                    have h := List.all_eq_true.mp linkChecked266 _ hj
                    have heq : 272384+i.val%1024 = i.val := by omega
                    simpa only [heq] using h
                  · have heq : b = 267 := by omega
                    subst b
                    have hj : i.val%1024 ∈ List.range 603 := List.mem_range.mpr (by omega)
                    have h := List.all_eq_true.mp linkChecked267 _ hj
                    have heq : 273408+i.val%1024 = i.val := by omega
                    simpa only [heq] using h
#print axioms link_checked
end Quantum.Stabilizer.Homological.BB.Bravyi360.BottomShallow
