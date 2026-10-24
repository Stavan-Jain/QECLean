/-
GENERATED FILE — DO NOT HAND-EDIT
Generator: qec-lab:experiments/bb_lab/scripts/bravyi360_kernel/generate.py
Emitter, relative to generator directory:
  emitters/generate_affine_boundaries.py
Data and SHA-256 hashes: audit_manifest.json
Regenerate:
  QECLEAN_ROOT=/path/to/QECLean \
    python3 experiments/bb_lab/scripts/bravyi360_kernel/generate.py --force
-/

import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.AffineInitialPart2
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.AffineBoundaryCachedPart2
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.TopFiberBoundary

noncomputable section

namespace Quantum.Stabilizer.Homological.BB.Bravyi360.TopNonempty
open F2Mask FiberData

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census204 : (AffineBoundaryCached.cert204).seeds.map Prod.fst = AffineSearchData.allowed204 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 204 is a boundary. -/
theorem boundary204 : TopFiberBoundary 0x205800a000000004802c0180020020001005000005 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x205800a000000004802c0180020020001005000005)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete204 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert204).beta ∈
      (AffineBoundaryCached.cert204).seeds.map Prod.fst := by
    rw [census204]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert204) 180 512
    8 AffineBoundaryCached.sheets204 AffineBoundaryCached.shadows204
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt204
    (AffineBoundaryCached.checked204) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census205 : (AffineBoundaryCached.cert205).seeds.map Prod.fst = AffineSearchData.allowed205 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 205 is a boundary. -/
theorem boundary205 : TopFiberBoundary 0x205800a00000000900340180010020001005000003 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x205800a00000000900340180010020001005000003)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete205 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert205).beta ∈
      (AffineBoundaryCached.cert205).seeds.map Prod.fst := by
    rw [census205]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert205) 180 512
    8 AffineBoundaryCached.sheets205 AffineBoundaryCached.shadows205
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt205
    (AffineBoundaryCached.checked205) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census206 : (AffineBoundaryCached.cert206).seeds.map Prod.fst = AffineSearchData.allowed206 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 206 is a boundary. -/
theorem boundary206 : TopFiberBoundary 0x205800a00000001200040180070020001005000030 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x205800a00000001200040180070020001005000030)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete206 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert206).beta ∈
      (AffineBoundaryCached.cert206).seeds.map Prod.fst := by
    rw [census206]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert206) 180 512
    8 AffineBoundaryCached.sheets206 AffineBoundaryCached.shadows206
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt206
    (AffineBoundaryCached.checked206) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census207 : (AffineBoundaryCached.cert207).seeds.map Prod.fst = AffineSearchData.allowed207 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 207 is a boundary. -/
theorem boundary207 : TopFiberBoundary 0x20c801a000000000002401800301a000100d000000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x20c801a000000000002401800301a000100d000000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete207 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert207).beta ∈
      (AffineBoundaryCached.cert207).seeds.map Prod.fst := by
    rw [census207]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert207) 180 512
    8 AffineBoundaryCached.sheets207 AffineBoundaryCached.shadows207
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt207
    (AffineBoundaryCached.checked207) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census208 : (AffineBoundaryCached.cert208).seeds.map Prod.fst = AffineSearchData.allowed208 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 208 is a boundary. -/
theorem boundary208 : TopFiberBoundary 0x221804a000000000002401800300e0001025000000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x221804a000000000002401800300e0001025000000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete208 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert208).beta ∈
      (AffineBoundaryCached.cert208).seeds.map Prod.fst := by
    rw [census208]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert208) 180 512
    8 AffineBoundaryCached.sheets208 AffineBoundaryCached.shadows208
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt208
    (AffineBoundaryCached.checked208) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census209 : (AffineBoundaryCached.cert209).seeds.map Prod.fst = AffineSearchData.allowed209 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 209 is a boundary. -/
theorem boundary209 : TopFiberBoundary 0x2400000000000d8011046035000201200000000600 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x2400000000000d8011046035000201200000000600)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete209 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert209).beta ∈
      (AffineBoundaryCached.cert209).seeds.map Prod.fst := by
    rw [census209]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert209) 180 512
    8 AffineBoundaryCached.sheets209 AffineBoundaryCached.shadows209
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt209
    (AffineBoundaryCached.checked209) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census210 : (AffineBoundaryCached.cert210).seeds.map Prod.fst = AffineSearchData.allowed210 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 210 is a boundary. -/
theorem boundary210 : TopFiberBoundary 0x2400000000001f8031046031000201200000000000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x2400000000001f8031046031000201200000000000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete210 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert210).beta ∈
      (AffineBoundaryCached.cert210).seeds.map Prod.fst := by
    rw [census210]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert210) 180 512
    2 AffineBoundaryCached.sheets210 AffineBoundaryCached.shadows210
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt210
    (AffineBoundaryCached.checked210) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census211 : (AffineBoundaryCached.cert211).seeds.map Prod.fst = AffineSearchData.allowed211 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 211 is a boundary. -/
theorem boundary211 : TopFiberBoundary 0x240098050001001000000200006000600e00140040 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x240098050001001000000200006000600e00140040)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete211 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert211).beta ∈
      (AffineBoundaryCached.cert211).seeds.map Prod.fst := by
    rw [census211]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert211) 180 512
    8 AffineBoundaryCached.sheets211 AffineBoundaryCached.shadows211
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt211
    (AffineBoundaryCached.checked211) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census212 : (AffineBoundaryCached.cert212).seeds.map Prod.fst = AffineSearchData.allowed212 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 212 is a boundary. -/
theorem boundary212 : TopFiberBoundary 0x2401b8070001001000000200006000000e00040040 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x2401b8070001001000000200006000000e00040040)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete212 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert212).beta ∈
      (AffineBoundaryCached.cert212).seeds.map Prod.fst := by
    rw [census212]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert212) 180 512
    2 AffineBoundaryCached.sheets212 AffineBoundaryCached.shadows212
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt212
    (AffineBoundaryCached.checked212) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census213 : (AffineBoundaryCached.cert213).seeds.map Prod.fst = AffineSearchData.allowed213 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 213 is a boundary. -/
theorem boundary213 : TopFiberBoundary 0x2405380b80000000000000000060050002005c0000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x2405380b80000000000000000060050002005c0000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete213 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert213).beta ∈
      (AffineBoundaryCached.cert213).seeds.map Prod.fst := by
    rw [census213]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert213) 180 512
    6 AffineBoundaryCached.sheets213 AffineBoundaryCached.shadows213
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt213
    (AffineBoundaryCached.checked213) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census214 : (AffineBoundaryCached.cert214).seeds.map Prod.fst = AffineSearchData.allowed214 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 214 is a boundary. -/
theorem boundary214 : TopFiberBoundary 0x2408b81380000000000000000060030002009c0000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x2408b81380000000000000000060030002009c0000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete214 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert214).beta ∈
      (AffineBoundaryCached.cert214).seeds.map Prod.fst := by
    rw [census214]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert214) 180 512
    6 AffineBoundaryCached.sheets214 AffineBoundaryCached.shadows214
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt214
    (AffineBoundaryCached.checked214) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census215 : (AffineBoundaryCached.cert215).seeds.map Prod.fst = AffineSearchData.allowed215 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 215 is a boundary. -/
theorem boundary215 : TopFiberBoundary 0x240ea01e0000000000000000006000600200f00000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x240ea01e0000000000000000006000600200f00000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete215 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert215).beta ∈
      (AffineBoundaryCached.cert215).seeds.map Prod.fst := by
    rw [census215]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert215) 180 512
    6 AffineBoundaryCached.sheets215 AffineBoundaryCached.shadows215
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt215
    (AffineBoundaryCached.checked215) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census216 : (AffineBoundaryCached.cert216).seeds.map Prod.fst = AffineSearchData.allowed216 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 216 is a boundary. -/
theorem boundary216 : TopFiberBoundary 0x240f101d0000000000000000006000a00200e80000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x240f101d0000000000000000006000a00200e80000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete216 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert216).beta ∈
      (AffineBoundaryCached.cert216).seeds.map Prod.fst := by
    rw [census216]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert216) 180 512
    6 AffineBoundaryCached.sheets216 AffineBoundaryCached.shadows216
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt216
    (AffineBoundaryCached.checked216) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census217 : (AffineBoundaryCached.cert217).seeds.map Prod.fst = AffineSearchData.allowed217 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 217 is a boundary. -/
theorem boundary217 : TopFiberBoundary 0x2500d00000000000900a8028001a02000680000000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x2500d00000000000900a8028001a02000680000000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete217 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert217).beta ∈
      (AffineBoundaryCached.cert217).seeds.map Prod.fst := by
    rw [census217]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert217) 180 512
    8 AffineBoundaryCached.sheets217 AffineBoundaryCached.shadows217
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt217
    (AffineBoundaryCached.checked217) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census218 : (AffineBoundaryCached.cert218).seeds.map Prod.fst = AffineSearchData.allowed218 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 218 is a boundary. -/
theorem boundary218 : TopFiberBoundary 0x2800800000004800580d8008006003000400005000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x2800800000004800580d8008006003000400005000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete218 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert218).beta ∈
      (AffineBoundaryCached.cert218).seeds.map Prod.fst := by
    rw [census218]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert218) 180 512
    4 AffineBoundaryCached.sheets218 AffineBoundaryCached.shadows218
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt218
    (AffineBoundaryCached.checked218) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census219 : (AffineBoundaryCached.cert219).seeds.map Prod.fst = AffineSearchData.allowed219 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 219 is a boundary. -/
theorem boundary219 : TopFiberBoundary 0x2800800000006c00180d8000006003000400003000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x2800800000006c00180d8000006003000400003000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete219 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert219).beta ∈
      (AffineBoundaryCached.cert219).seeds.map Prod.fst := by
    rw [census219]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert219) 180 512
    2 AffineBoundaryCached.sheets219 AffineBoundaryCached.shadows219
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt219
    (AffineBoundaryCached.checked219) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census220 : (AffineBoundaryCached.cert220).seeds.map Prod.fst = AffineSearchData.allowed220 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 220 is a boundary. -/
theorem boundary220 : TopFiberBoundary 0x2880c80000000000900a8028001c02000640000000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x2880c80000000000900a8028001c02000640000000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete220 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert220).beta ∈
      (AffineBoundaryCached.cert220).seeds.map Prod.fst := by
    rw [census220]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert220) 180 512
    8 AffineBoundaryCached.sheets220 AffineBoundaryCached.shadows220
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt220
    (AffineBoundaryCached.checked220) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census221 : (AffineBoundaryCached.cert221).seeds.map Prod.fst = AffineSearchData.allowed221 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 221 is a boundary. -/
theorem boundary221 : TopFiberBoundary 0x2981a00380000000000000000066000002c01c0000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x2981a00380000000000000000066000002c01c0000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete221 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert221).beta ∈
      (AffineBoundaryCached.cert221).seeds.map Prod.fst := by
    rw [census221]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert221) 180 512
    4 AffineBoundaryCached.sheets221 AffineBoundaryCached.shadows221
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt221
    (AffineBoundaryCached.checked221) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census222 : (AffineBoundaryCached.cert222).seeds.map Prod.fst = AffineSearchData.allowed222 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 222 is a boundary. -/
theorem boundary222 : TopFiberBoundary 0x2c00880080000000900a8028001002c00600040000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x2c00880080000000900a8028001002c00600040000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete222 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert222).beta ∈
      (AffineBoundaryCached.cert222).seeds.map Prod.fst := by
    rw [census222]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert222) 180 512
    8 AffineBoundaryCached.sheets222 AffineBoundaryCached.shadows222
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt222
    (AffineBoundaryCached.checked222) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census223 : (AffineBoundaryCached.cert223).seeds.map Prod.fst = AffineSearchData.allowed223 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 223 is a boundary. -/
theorem boundary223 : TopFiberBoundary 0x2c00c00000000900800a802a001002000600000a00 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x2c00c00000000900800a802a001002000600000a00)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete223 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert223).beta ∈
      (AffineBoundaryCached.cert223).seeds.map Prod.fst := by
    rw [census223]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert223) 180 512
    8 AffineBoundaryCached.sheets223 AffineBoundaryCached.shadows223
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt223
    (AffineBoundaryCached.checked223) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census224 : (AffineBoundaryCached.cert224).seeds.map Prod.fst = AffineSearchData.allowed224 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 224 is a boundary. -/
theorem boundary224 : TopFiberBoundary 0x2c00c00000002400d00a8020001002000600006000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x2c00c00000002400d00a8020001002000600006000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete224 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert224).beta ∈
      (AffineBoundaryCached.cert224).seeds.map Prod.fst := by
    rw [census224]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert224) 180 512
    8 AffineBoundaryCached.sheets224 AffineBoundaryCached.shadows224
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt224
    (AffineBoundaryCached.checked224) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census225 : (AffineBoundaryCached.cert225).seeds.map Prod.fst = AffineSearchData.allowed225 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 225 is a boundary. -/
theorem boundary225 : TopFiberBoundary 0x2c00c00000004800100a8038001002000600005000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x2c00c00000004800100a8038001002000600005000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete225 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert225).beta ∈
      (AffineBoundaryCached.cert225).seeds.map Prod.fst := by
    rw [census225]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert225) 180 512
    8 AffineBoundaryCached.sheets225 AffineBoundaryCached.shadows225
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt225
    (AffineBoundaryCached.checked225) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census226 : (AffineBoundaryCached.cert226).seeds.map Prod.fst = AffineSearchData.allowed226 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 226 is a boundary. -/
theorem boundary226 : TopFiberBoundary 0x2c00c00000009001900a8008001002000600003000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x2c00c00000009001900a8008001002000600003000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete226 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert226).beta ∈
      (AffineBoundaryCached.cert226).seeds.map Prod.fst := by
    rw [census226]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert226) 180 512
    8 AffineBoundaryCached.sheets226 AffineBoundaryCached.shadows226
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt226
    (AffineBoundaryCached.checked226) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census227 : (AffineBoundaryCached.cert227).seeds.map Prod.fst = AffineSearchData.allowed227 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 227 is a boundary. -/
theorem boundary227 : TopFiberBoundary 0x2c04400800000000900a8028001007000600400000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x2c04400800000000900a8028001007000600400000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete227 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert227).beta ∈
      (AffineBoundaryCached.cert227).seeds.map Prod.fst := by
    rw [census227]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert227) 180 512
    8 AffineBoundaryCached.sheets227 AffineBoundaryCached.shadows227
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt227
    (AffineBoundaryCached.checked227) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census228 : (AffineBoundaryCached.cert228).seeds.map Prod.fst = AffineSearchData.allowed228 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 228 is a boundary. -/
theorem boundary228 : TopFiberBoundary 0x2c06000c00000000900a8028001001000600600000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x2c06000c00000000900a8028001001000600600000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete228 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert228).beta ∈
      (AffineBoundaryCached.cert228).seeds.map Prod.fst := by
    rw [census228]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert228) 180 512
    2 AffineBoundaryCached.sheets228 AffineBoundaryCached.shadows228
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt228
    (AffineBoundaryCached.checked228) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census229 : (AffineBoundaryCached.cert229).seeds.map Prod.fst = AffineSearchData.allowed229 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 229 is a boundary. -/
theorem boundary229 : TopFiberBoundary 0x2c09c01000000000900a8028001001000600800000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x2c09c01000000000900a8028001001000600800000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete229 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert229).beta ∈
      (AffineBoundaryCached.cert229).seeds.map Prod.fst := by
    rw [census229]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert229) 180 512
    8 AffineBoundaryCached.sheets229 AffineBoundaryCached.shadows229
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt229
    (AffineBoundaryCached.checked229) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census230 : (AffineBoundaryCached.cert230).seeds.map Prod.fst = AffineSearchData.allowed230 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 230 is a boundary. -/
theorem boundary230 : TopFiberBoundary 0x2d01a8038000000000000000006a000002801c0000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x2d01a8038000000000000000006a000002801c0000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete230 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert230).beta ∈
      (AffineBoundaryCached.cert230).seeds.map Prod.fst := by
    rw [census230]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert230) 180 512
    6 AffineBoundaryCached.sheets230 AffineBoundaryCached.shadows230
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt230
    (AffineBoundaryCached.checked230) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census231 : (AffineBoundaryCached.cert231).seeds.map Prod.fst = AffineSearchData.allowed231 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 231 is a boundary. -/
theorem boundary231 : TopFiberBoundary 0x30010000000000032812802800e005000800000006 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x30010000000000032812802800e005000800000006)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete231 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert231).beta ∈
      (AffineBoundaryCached.cert231).seeds.map Prod.fst := by
    rw [census231]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert231) 180 512
    4 AffineBoundaryCached.sheets231 AffineBoundaryCached.shadows231
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt231
    (AffineBoundaryCached.checked231) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census232 : (AffineBoundaryCached.cert232).seeds.map Prod.fst = AffineSearchData.allowed232 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 232 is a boundary. -/
theorem boundary232 : TopFiberBoundary 0x300100000000000868068028026005000800000003 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x300100000000000868068028026005000800000003)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete232 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert232).beta ∈
      (AffineBoundaryCached.cert232).seeds.map Prod.fst := by
    rw [census232]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert232) 180 512
    4 AffineBoundaryCached.sheets232 AffineBoundaryCached.shadows232
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt232
    (AffineBoundaryCached.checked232) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census233 : (AffineBoundaryCached.cert233).seeds.map Prod.fst = AffineSearchData.allowed233 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 233 is a boundary. -/
theorem boundary233 : TopFiberBoundary 0x300100000000900068168008006005000800003000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x300100000000900068168008006005000800003000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete233 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert233).beta ∈
      (AffineBoundaryCached.cert233).seeds.map Prod.fst := by
    rw [census233]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert233) 180 512
    4 AffineBoundaryCached.sheets233 AffineBoundaryCached.shadows233
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt233
    (AffineBoundaryCached.checked233) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census234 : (AffineBoundaryCached.cert234).seeds.map Prod.fst = AffineSearchData.allowed234 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 234 is a boundary. -/
theorem boundary234 : TopFiberBoundary 0x300580080000000168168028006000000800400000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x300580080000000168168028006000000800400000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete234 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert234).beta ∈
      (AffineBoundaryCached.cert234).seeds.map Prod.fst := by
    rw [census234]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert234) 180 512
    4 AffineBoundaryCached.sheets234 AffineBoundaryCached.shadows234
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt234
    (AffineBoundaryCached.checked234) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census235 : (AffineBoundaryCached.cert235).seeds.map Prod.fst = AffineSearchData.allowed235 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 235 is a boundary. -/
theorem boundary235 : TopFiberBoundary 0x300800100000000168168028006006000800800000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x300800100000000168168028006006000800800000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete235 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert235).beta ∈
      (AffineBoundaryCached.cert235).seeds.map Prod.fst := by
    rw [census235]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert235) 180 512
    2 AffineBoundaryCached.sheets235 AffineBoundaryCached.shadows235
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt235
    (AffineBoundaryCached.checked235) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census236 : (AffineBoundaryCached.cert236).seeds.map Prod.fst = AffineSearchData.allowed236 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 236 is a boundary. -/
theorem boundary236 : TopFiberBoundary 0x328028000000000009046036000801200140000000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x328028000000000009046036000801200140000000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete236 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert236).beta ∈
      (AffineBoundaryCached.cert236).seeds.map Prod.fst := by
    rw [census236]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert236) 180 512
    8 AffineBoundaryCached.sheets236 AffineBoundaryCached.shadows236
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt236
    (AffineBoundaryCached.checked236) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census237 : (AffineBoundaryCached.cert237).seeds.map Prod.fst = AffineSearchData.allowed237 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 237 is a boundary. -/
theorem boundary237 : TopFiberBoundary 0x328190038000000000000000006a000003401c0000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x328190038000000000000000006a000003401c0000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete237 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert237).beta ∈
      (AffineBoundaryCached.cert237).seeds.map Prod.fst := by
    rw [census237]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert237) 180 512
    4 AffineBoundaryCached.sheets237 AffineBoundaryCached.shadows237
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt237
    (AffineBoundaryCached.checked237) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census238 : (AffineBoundaryCached.cert238).seeds.map Prod.fst = AffineSearchData.allowed238 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 238 is a boundary. -/
theorem boundary238 : TopFiberBoundary 0x3601980380000000000000000066000003001c0000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x3601980380000000000000000066000003001c0000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete238 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert238).beta ∈
      (AffineBoundaryCached.cert238).seeds.map Prod.fst := by
    rw [census238]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert238) 180 512
    6 AffineBoundaryCached.sheets238 AffineBoundaryCached.shadows238
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt238
    (AffineBoundaryCached.checked238) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census239 : (AffineBoundaryCached.cert239).seeds.map Prod.fst = AffineSearchData.allowed239 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 239 is a boundary. -/
theorem boundary239 : TopFiberBoundary 0x3b80a00180000000000000000060006003c00c0000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x3b80a00180000000000000000060006003c00c0000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete239 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert239).beta ∈
      (AffineBoundaryCached.cert239).seeds.map Prod.fst := by
    rw [census239]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert239) 180 512
    4 AffineBoundaryCached.sheets239 AffineBoundaryCached.shadows239
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt239
    (AffineBoundaryCached.checked239) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census240 : (AffineBoundaryCached.cert240).seeds.map Prod.fst = AffineSearchData.allowed240 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 240 is a boundary. -/
theorem boundary240 : TopFiberBoundary 0x3b80e8010000000000000000006000a003c0080000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x3b80e8010000000000000000006000a003c0080000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete240 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert240).beta ∈
      (AffineBoundaryCached.cert240).seeds.map Prod.fst := by
    rw [census240]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert240) 180 512
    6 AffineBoundaryCached.sheets240 AffineBoundaryCached.shadows240
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt240
    (AffineBoundaryCached.checked240) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census241 : (AffineBoundaryCached.cert241).seeds.map Prod.fst = AffineSearchData.allowed241 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 241 is a boundary. -/
theorem boundary241 : TopFiberBoundary 0x3b8110028000000000000000006000a003c0140000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x3b8110028000000000000000006000a003c0140000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete241 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert241).beta ∈
      (AffineBoundaryCached.cert241).seeds.map Prod.fst := by
    rw [census241]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert241) 180 512
    4 AffineBoundaryCached.sheets241 AffineBoundaryCached.shadows241
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt241
    (AffineBoundaryCached.checked241) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census242 : (AffineBoundaryCached.cert242).seeds.map Prod.fst = AffineSearchData.allowed242 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 242 is a boundary. -/
theorem boundary242 : TopFiberBoundary 0x3b81580200000000000000000060006003c0100000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x3b81580200000000000000000060006003c0100000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete242 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert242).beta ∈
      (AffineBoundaryCached.cert242).seeds.map Prod.fst := by
    rw [census242]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert242) 180 512
    6 AffineBoundaryCached.sheets242 AffineBoundaryCached.shadows242
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt242
    (AffineBoundaryCached.checked242) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census243 : (AffineBoundaryCached.cert243).seeds.map Prod.fst = AffineSearchData.allowed243 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 243 is a boundary. -/
theorem boundary243 : TopFiberBoundary 0x400000000001dc03500a8050002002000000030000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x400000000001dc03500a8050002002000000030000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete243 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert243).beta ∈
      (AffineBoundaryCached.cert243).seeds.map Prod.fst := by
    rw [census243]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert243) 180 512
    2 AffineBoundaryCached.sheets243 AffineBoundaryCached.shadows243
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt243
    (AffineBoundaryCached.checked243) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census244 : (AffineBoundaryCached.cert244).seeds.map Prod.fst = AffineSearchData.allowed244 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 244 is a boundary. -/
theorem boundary244 : TopFiberBoundary 0x400400000001040d80540108010010002000036000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x400400000001040d80540108010010002000036000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete244 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert244).beta ∈
      (AffineBoundaryCached.cert244).seeds.map Prod.fst := by
    rw [census244]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert244) 180 512
    2 AffineBoundaryCached.sheets244 AffineBoundaryCached.shadows244
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt244
    (AffineBoundaryCached.checked244) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census245 : (AffineBoundaryCached.cert245).seeds.map Prod.fst = AffineSearchData.allowed245 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 245 is a boundary. -/
theorem boundary245 : TopFiberBoundary 0x400400000001200f80500100018010002000030006 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x400400000001200f80500100018010002000030006)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete245 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert245).beta ∈
      (AffineBoundaryCached.cert245).seeds.map Prod.fst := by
    rw [census245]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert245) 180 512
    8 AffineBoundaryCached.sheets245 AffineBoundaryCached.shadows245
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt245
    (AffineBoundaryCached.checked245) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census246 : (AffineBoundaryCached.cert246).seeds.map Prod.fst = AffineSearchData.allowed246 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 246 is a boundary. -/
theorem boundary246 : TopFiberBoundary 0x4004000000012029c0140100090010002000030028 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x4004000000012029c0140100090010002000030028)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete246 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert246).beta ∈
      (AffineBoundaryCached.cert246).seeds.map Prod.fst := by
    rw [census246]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert246) 180 512
    2 AffineBoundaryCached.sheets246 AffineBoundaryCached.shadows246
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt246
    (AffineBoundaryCached.checked246) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census247 : (AffineBoundaryCached.cert247).seeds.map Prod.fst = AffineSearchData.allowed247 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 247 is a boundary. -/
theorem boundary247 : TopFiberBoundary 0x403200600001200200480100028008002003030000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x403200600001200200480100028008002003030000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete247 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert247).beta ∈
      (AffineBoundaryCached.cert247).seeds.map Prod.fst := by
    rw [census247]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert247) 180 512
    8 AffineBoundaryCached.sheets247 AffineBoundaryCached.shadows247
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt247
    (AffineBoundaryCached.checked247) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census248 : (AffineBoundaryCached.cert248).seeds.map Prod.fst = AffineSearchData.allowed248 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 248 is a boundary. -/
theorem boundary248 : TopFiberBoundary 0x410041010001000000000000005a007805000c8008 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x410041010001000000000000005a007805000c8008)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete248 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert248).beta ∈
      (AffineBoundaryCached.cert248).seeds.map Prod.fst := by
    rw [census248]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert248) 180 512
    4 AffineBoundaryCached.sheets248 AffineBoundaryCached.shadows248
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt248
    (AffineBoundaryCached.checked248) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census249 : (AffineBoundaryCached.cert249).seeds.map Prod.fst = AffineSearchData.allowed249 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 249 is a boundary. -/
theorem boundary249 : TopFiberBoundary 0x410048050001001000000200005a00600880140040 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x410048050001001000000200005a00600880140040)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete249 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert249).beta ∈
      (AffineBoundaryCached.cert249).seeds.map Prod.fst := by
    rw [census249]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert249) 180 512
    4 AffineBoundaryCached.sheets249 AffineBoundaryCached.shadows249
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt249
    (AffineBoundaryCached.checked249) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census250 : (AffineBoundaryCached.cert250).seeds.map Prod.fst = AffineSearchData.allowed250 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 250 is a boundary. -/
theorem boundary250 : TopFiberBoundary 0x410168070001001000000200005a00000880040040 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x410168070001001000000200005a00000880040040)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete250 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert250).beta ∈
      (AffineBoundaryCached.cert250).seeds.map Prod.fst := by
    rw [census250]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert250) 180 512
    2 AffineBoundaryCached.sheets250 AffineBoundaryCached.shadows250
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt250
    (AffineBoundaryCached.checked250) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census251 : (AffineBoundaryCached.cert251).seeds.map Prod.fst = AffineSearchData.allowed251 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 251 is a boundary. -/
theorem boundary251 : TopFiberBoundary 0x458091008001000000000000005600180540008008 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x458091008001000000000000005600180540008008)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete251 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert251).beta ∈
      (AffineBoundaryCached.cert251).seeds.map Prod.fst := by
    rw [census251]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert251) 180 512
    8 AffineBoundaryCached.sheets251 AffineBoundaryCached.shadows251
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt251
    (AffineBoundaryCached.checked251) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census252 : (AffineBoundaryCached.cert252).seeds.map Prod.fst = AffineSearchData.allowed252 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 252 is a boundary. -/
theorem boundary252 : TopFiberBoundary 0x48008004800102c005000200a05000000800180100 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x48008004800102c005000200a05000000800180100)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete252 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert252).beta ∈
      (AffineBoundaryCached.cert252).seeds.map Prod.fst := by
    rw [census252]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert252) 180 512
    8 AffineBoundaryCached.sheets252 AffineBoundaryCached.shadows252
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt252
    (AffineBoundaryCached.checked252) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census253 : (AffineBoundaryCached.cert253).seeds.map Prod.fst = AffineSearchData.allowed253 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 253 is a boundary. -/
theorem boundary253 : TopFiberBoundary 0x480338030001001000000200005006000800240040 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x480338030001001000000200005006000800240040)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete253 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert253).beta ∈
      (AffineBoundaryCached.cert253).seeds.map Prod.fst := by
    rw [census253]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert253) 180 512
    2 AffineBoundaryCached.sheets253 AffineBoundaryCached.shadows253
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt253
    (AffineBoundaryCached.checked253) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census254 : (AffineBoundaryCached.cert254).seeds.map Prod.fst = AffineSearchData.allowed254 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 254 is a boundary. -/
theorem boundary254 : TopFiberBoundary 0x480640088001001000000200005003000800780040 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x480640088001001000000200005003000800780040)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete254 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert254).beta ∈
      (AffineBoundaryCached.cert254).seeds.map Prod.fst := by
    rw [census254]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert254) 180 512
    8 AffineBoundaryCached.sheets254 AffineBoundaryCached.shadows254
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt254
    (AffineBoundaryCached.checked254) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census255 : (AffineBoundaryCached.cert255).seeds.map Prod.fst = AffineSearchData.allowed255 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 255 is a boundary. -/
theorem boundary255 : TopFiberBoundary 0x5780b1008001000000000000005000180440008008 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x5780b1008001000000000000005000180440008008)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete255 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert255).beta ∈
      (AffineBoundaryCached.cert255).seeds.map Prod.fst := by
    rw [census255]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert255) 180 512
    2 AffineBoundaryCached.sheets255 AffineBoundaryCached.shadows255
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt255
    (AffineBoundaryCached.checked255) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census256 : (AffineBoundaryCached.cert256).seeds.map Prod.fst = AffineSearchData.allowed256 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 256 is a boundary. -/
theorem boundary256 : TopFiberBoundary 0x600000000000000f1811801803b003000000000000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x600000000000000f1811801803b003000000000000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete256 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert256).beta ∈
      (AffineBoundaryCached.cert256).seeds.map Prod.fst := by
    rw [census256]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert256) 180 512
    4 AffineBoundaryCached.sheets256 AffineBoundaryCached.shadows256
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt256
    (AffineBoundaryCached.checked256) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census257 : (AffineBoundaryCached.cert257).seeds.map Prod.fst = AffineSearchData.allowed257 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 257 is a boundary. -/
theorem boundary257 : TopFiberBoundary 0x6000000000004100480d800a003003000000005a00 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x6000000000004100480d800a003003000000005a00)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete257 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert257).beta ∈
      (AffineBoundaryCached.cert257).seeds.map Prod.fst := by
    rw [census257]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert257) 180 512
    2 AffineBoundaryCached.sheets257 AffineBoundaryCached.shadows257
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt257
    (AffineBoundaryCached.checked257) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census258 : (AffineBoundaryCached.cert258).seeds.map Prod.fst = AffineSearchData.allowed258 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 258 is a boundary. -/
theorem boundary258 : TopFiberBoundary 0x60000000000048021809800800b003000000005006 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x60000000000048021809800800b003000000005006)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete258 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert258).beta ∈
      (AffineBoundaryCached.cert258).seeds.map Prod.fst := by
    rw [census258]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert258) 180 512
    4 AffineBoundaryCached.sheets258 AffineBoundaryCached.shadows258
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt258
    (AffineBoundaryCached.checked258) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census259 : (AffineBoundaryCached.cert259).seeds.map Prod.fst = AffineSearchData.allowed259 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 259 is a boundary. -/
theorem boundary259 : TopFiberBoundary 0x6000000000006500080d8002003003000000003a00 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x6000000000006500080d8002003003000000003a00)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete259 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert259).beta ∈
      (AffineBoundaryCached.cert259).seeds.map Prod.fst := by
    rw [census259]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert259) 180 512
    2 AffineBoundaryCached.sheets259 AffineBoundaryCached.shadows259
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt259
    (AffineBoundaryCached.checked259) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census260 : (AffineBoundaryCached.cert260).seeds.map Prod.fst = AffineSearchData.allowed260 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 260 is a boundary. -/
theorem boundary260 : TopFiberBoundary 0x6000000000006880100d8001003003000000003c00 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x6000000000006880100d8001003003000000003c00)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete260 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert260).beta ∈
      (AffineBoundaryCached.cert260).seeds.map Prod.fst := by
    rw [census260]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert260) 180 512
    2 AffineBoundaryCached.sheets260 AffineBoundaryCached.shadows260
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt260
    (AffineBoundaryCached.checked260) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census261 : (AffineBoundaryCached.cert261).seeds.map Prod.fst = AffineSearchData.allowed261 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 261 is a boundary. -/
theorem boundary261 : TopFiberBoundary 0x6006000000000020802400c008801800300000002d := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x6006000000000020802400c008801800300000002d)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete261 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert261).beta ∈
      (AffineBoundaryCached.cert261).seeds.map Prod.fst := by
    rw [census261]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert261) 180 512
    2 AffineBoundaryCached.sheets261 AffineBoundaryCached.shadows261
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt261
    (AffineBoundaryCached.checked261) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census262 : (AffineBoundaryCached.cert262).seeds.map Prod.fst = AffineSearchData.allowed262 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 262 is a boundary. -/
theorem boundary262 : TopFiberBoundary 0x600600000002400080640040008018003000028005 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x600600000002400080640040008018003000028005)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete262 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert262).beta ∈
      (AffineBoundaryCached.cert262).seeds.map Prod.fst := by
    rw [census262]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert262) 180 512
    2 AffineBoundaryCached.sheets262 AffineBoundaryCached.shadows262
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt262
    (AffineBoundaryCached.checked262) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census263 : (AffineBoundaryCached.cert263).seeds.map Prod.fst = AffineSearchData.allowed263 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 263 is a boundary. -/
theorem boundary263 : TopFiberBoundary 0x6009001000004800580d8008003000000000805000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x6009001000004800580d8008003000000000805000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete263 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert263).beta ∈
      (AffineBoundaryCached.cert263).seeds.map Prod.fst := by
    rw [census263]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert263) 180 512
    4 AffineBoundaryCached.sheets263 AffineBoundaryCached.shadows263
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt263
    (AffineBoundaryCached.checked263) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census264 : (AffineBoundaryCached.cert264).seeds.map Prod.fst = AffineSearchData.allowed264 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 264 is a boundary. -/
theorem boundary264 : TopFiberBoundary 0x6009001000006c00180d8000003000000000803000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x6009001000006c00180d8000003000000000803000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete264 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert264).beta ∈
      (AffineBoundaryCached.cert264).seeds.map Prod.fst := by
    rw [census264]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert264) 180 512
    2 AffineBoundaryCached.sheets264 AffineBoundaryCached.shadows264
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt264
    (AffineBoundaryCached.checked264) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census265 : (AffineBoundaryCached.cert265).seeds.map Prod.fst = AffineSearchData.allowed265 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 265 is a boundary. -/
theorem boundary265 : TopFiberBoundary 0x6014002000000002406800c0010028003001000006 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x6014002000000002406800c0010028003001000006)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete265 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert265).beta ∈
      (AffineBoundaryCached.cert265).seeds.map Prod.fst := by
    rw [census265]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert265) 180 512
    4 AffineBoundaryCached.sheets265 AffineBoundaryCached.shadows265
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt265
    (AffineBoundaryCached.checked265) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census266 : (AffineBoundaryCached.cert266).seeds.map Prod.fst = AffineSearchData.allowed266 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 266 is a boundary. -/
theorem boundary266 : TopFiberBoundary 0x6022004000000004806400c0008030003002000005 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x6022004000000004806400c0008030003002000005)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete266 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert266).beta ∈
      (AffineBoundaryCached.cert266).seeds.map Prod.fst := by
    rw [census266]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert266) 180 512
    4 AffineBoundaryCached.sheets266 AffineBoundaryCached.shadows266
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt266
    (AffineBoundaryCached.checked266) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census267 : (AffineBoundaryCached.cert267).seeds.map Prod.fst = AffineSearchData.allowed267 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 267 is a boundary. -/
theorem boundary267 : TopFiberBoundary 0x6030006000000002406800c0010000003003000006 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x6030006000000002406800c0010000003003000006)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete267 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert267).beta ∈
      (AffineBoundaryCached.cert267).seeds.map Prod.fst := by
    rw [census267]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert267) 180 512
    2 AffineBoundaryCached.sheets267 AffineBoundaryCached.shadows267
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt267
    (AffineBoundaryCached.checked267) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census268 : (AffineBoundaryCached.cert268).seeds.map Prod.fst = AffineSearchData.allowed268 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 268 is a boundary. -/
theorem boundary268 : TopFiberBoundary 0x604e008000000004806400c0008000003004000005 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x604e008000000004806400c0008000003004000005)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete268 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert268).beta ∈
      (AffineBoundaryCached.cert268).seeds.map Prod.fst := by
    rw [census268]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert268) 180 512
    4 AffineBoundaryCached.sheets268 AffineBoundaryCached.shadows268
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt268
    (AffineBoundaryCached.checked268) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census269 : (AffineBoundaryCached.cert269).seeds.map Prod.fst = AffineSearchData.allowed269 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 269 is a boundary. -/
theorem boundary269 : TopFiberBoundary 0x60808000800000008202d005001800800640040000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x60808000800000008202d005001800800640040000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete269 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert269).beta ∈
      (AffineBoundaryCached.cert269).seeds.map Prod.fst := by
    rw [census269]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert269) 180 512
    4 AffineBoundaryCached.sheets269 AffineBoundaryCached.shadows269
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt269
    (AffineBoundaryCached.checked269) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census270 : (AffineBoundaryCached.cert270).seeds.map Prod.fst = AffineSearchData.allowed270 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 270 is a boundary. -/
theorem boundary270 : TopFiberBoundary 0x6181200380000000000000000036000006c01c0000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x6181200380000000000000000036000006c01c0000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete270 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert270).beta ∈
      (AffineBoundaryCached.cert270).seeds.map Prod.fst := by
    rw [census270]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert270) 180 512
    4 AffineBoundaryCached.sheets270 AffineBoundaryCached.shadows270
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt270
    (AffineBoundaryCached.checked270) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census271 : (AffineBoundaryCached.cert271).seeds.map Prod.fst = AffineSearchData.allowed271 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 271 is a boundary. -/
theorem boundary271 : TopFiberBoundary 0x640040000000d801100a8018004002000200006000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x640040000000d801100a8018004002000200006000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete271 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert271).beta ∈
      (AffineBoundaryCached.cert271).seeds.map Prod.fst := by
    rw [census271]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert271) 180 512
    8 AffineBoundaryCached.sheets271 AffineBoundaryCached.shadows271
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt271
    (AffineBoundaryCached.checked271) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census272 : (AffineBoundaryCached.cert272).seeds.map Prod.fst = AffineSearchData.allowed272 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 272 is a boundary. -/
theorem boundary272 : TopFiberBoundary 0x640040000000fc01500a8010004002000200000000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x640040000000fc01500a8010004002000200000000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete272 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert272).beta ∈
      (AffineBoundaryCached.cert272).seeds.map Prod.fst := by
    rw [census272]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert272) 180 512
    2 AffineBoundaryCached.sheets272 AffineBoundaryCached.shadows272
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt272
    (AffineBoundaryCached.checked272) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census273 : (AffineBoundaryCached.cert273).seeds.map Prod.fst = AffineSearchData.allowed273 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 273 is a boundary. -/
theorem boundary273 : TopFiberBoundary 0x64008800800000008202d005001400800600040000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x64008800800000008202d005001400800600040000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete273 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert273).beta ∈
      (AffineBoundaryCached.cert273).seeds.map Prod.fst := by
    rw [census273]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert273) 180 512
    4 AffineBoundaryCached.sheets273 AffineBoundaryCached.shadows273
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt273
    (AffineBoundaryCached.checked273) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census274 : (AffineBoundaryCached.cert274).seeds.map Prod.fst = AffineSearchData.allowed274 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 274 is a boundary. -/
theorem boundary274 : TopFiberBoundary 0x650128038000000000000000003a000006801c0000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x650128038000000000000000003a000006801c0000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete274 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert274).beta ∈
      (AffineBoundaryCached.cert274).seeds.map Prod.fst := by
    rw [census274]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert274) 180 512
    4 AffineBoundaryCached.sheets274 AffineBoundaryCached.shadows274
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt274
    (AffineBoundaryCached.checked274) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census275 : (AffineBoundaryCached.cert275).seeds.map Prod.fst = AffineSearchData.allowed275 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 275 is a boundary. -/
theorem boundary275 : TopFiberBoundary 0x6800800000006c0088070028004001000400003000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x6800800000006c0088070028004001000400003000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete275 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert275).beta ∈
      (AffineBoundaryCached.cert275).seeds.map Prod.fst := by
    rw [census275]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert275) 180 512
    8 AffineBoundaryCached.sheets275 AffineBoundaryCached.shadows275
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt275
    (AffineBoundaryCached.checked275) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census276 : (AffineBoundaryCached.cert276).seeds.map Prod.fst = AffineSearchData.allowed276 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 276 is a boundary. -/
theorem boundary276 : TopFiberBoundary 0x680080000000fc0188070008004001000400000000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x680080000000fc0188070008004001000400000000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete276 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert276).beta ∈
      (AffineBoundaryCached.cert276).seeds.map Prod.fst := by
    rw [census276]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert276) 180 512
    2 AffineBoundaryCached.sheets276 AffineBoundaryCached.shadows276
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt276
    (AffineBoundaryCached.checked276) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census277 : (AffineBoundaryCached.cert277).seeds.map Prod.fst = AffineSearchData.allowed277 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 277 is a boundary. -/
theorem boundary277 : TopFiberBoundary 0x688130038000000000000000003c000006401c0000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x688130038000000000000000003c000006401c0000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete277 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert277).beta ∈
      (AffineBoundaryCached.cert277).seeds.map Prod.fst := by
    rw [census277]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert277) 180 512
    4 AffineBoundaryCached.sheets277 AffineBoundaryCached.shadows277
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt277
    (AffineBoundaryCached.checked277) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census278 : (AffineBoundaryCached.cert278).seeds.map Prod.fst = AffineSearchData.allowed278 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 278 is a boundary. -/
theorem boundary278 : TopFiberBoundary 0x6c01380a8002002000000400003000000c00080080 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x6c01380a8002002000000400003000000c00080080)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete278 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert278).beta ∈
      (AffineBoundaryCached.cert278).seeds.map Prod.fst := by
    rw [census278]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert278) 180 512
    2 AffineBoundaryCached.sheets278 AffineBoundaryCached.shadows278
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt278
    (AffineBoundaryCached.checked278) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census279 : (AffineBoundaryCached.cert279).seeds.map Prod.fst = AffineSearchData.allowed279 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 279 is a boundary. -/
theorem boundary279 : TopFiberBoundary 0x7380200180000000000000000030006007c00c0000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x7380200180000000000000000030006007c00c0000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete279 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert279).beta ∈
      (AffineBoundaryCached.cert279).seeds.map Prod.fst := by
    rw [census279]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert279) 180 512
    4 AffineBoundaryCached.sheets279 AffineBoundaryCached.shadows279
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt279
    (AffineBoundaryCached.checked279) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census280 : (AffineBoundaryCached.cert280).seeds.map Prod.fst = AffineSearchData.allowed280 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 280 is a boundary. -/
theorem boundary280 : TopFiberBoundary 0x738068010000000000000000003000a007c0080000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x738068010000000000000000003000a007c0080000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete280 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert280).beta ∈
      (AffineBoundaryCached.cert280).seeds.map Prod.fst := by
    rw [census280]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert280) 180 512
    4 AffineBoundaryCached.sheets280 AffineBoundaryCached.shadows280
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt280
    (AffineBoundaryCached.checked280) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census281 : (AffineBoundaryCached.cert281).seeds.map Prod.fst = AffineSearchData.allowed281 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 281 is a boundary. -/
theorem boundary281 : TopFiberBoundary 0x7380b0008000000000000000003000c007c0040000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x7380b0008000000000000000003000c007c0040000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete281 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert281).beta ∈
      (AffineBoundaryCached.cert281).seeds.map Prod.fst := by
    rw [census281]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert281) 180 512
    4 AffineBoundaryCached.sheets281 AffineBoundaryCached.shadows281
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt281
    (AffineBoundaryCached.checked281) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census282 : (AffineBoundaryCached.cert282).seeds.map Prod.fst = AffineSearchData.allowed282 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 282 is a boundary. -/
theorem boundary282 : TopFiberBoundary 0x7c09c00000000000009000c0018020004e00000000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x7c09c00000000000009000c0018020004e00000000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete282 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert282).beta ∈
      (AffineBoundaryCached.cert282).seeds.map Prod.fst := by
    rw [census282]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert282) 180 512
    6 AffineBoundaryCached.sheets282 AffineBoundaryCached.shadows282
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt282
    (AffineBoundaryCached.checked282) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census283 : (AffineBoundaryCached.cert283).seeds.map Prod.fst = AffineSearchData.allowed283 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 283 is a boundary. -/
theorem boundary283 : TopFiberBoundary 0x8008000000030c09008c001802002000400001b000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x8008000000030c09008c001802002000400001b000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete283 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert283).beta ∈
      (AffineBoundaryCached.cert283).seeds.map Prod.fst := by
    rw [census283]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert283) 180 512
    2 AffineBoundaryCached.sheets283 AffineBoundaryCached.shadows283
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt283
    (AffineBoundaryCached.checked283) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census284 : (AffineBoundaryCached.cert284).seeds.map Prod.fst = AffineSearchData.allowed284 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 284 is a boundary. -/
theorem boundary284 : TopFiberBoundary 0x8008000000032809408c001002002000400001d000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x8008000000032809408c001002002000400001d000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete284 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert284).beta ∈
      (AffineBoundaryCached.cert284).seeds.map Prod.fst := by
    rw [census284]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert284) 180 512
    2 AffineBoundaryCached.sheets284 AffineBoundaryCached.shadows284
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt284
    (AffineBoundaryCached.checked284) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census285 : (AffineBoundaryCached.cert285).seeds.map Prod.fst = AffineSearchData.allowed285 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 285 is a boundary. -/
theorem boundary285 : TopFiberBoundary 0x800800000003600d40840000030020004000018005 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x800800000003600d40840000030020004000018005)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete285 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert285).beta ∈
      (AffineBoundaryCached.cert285).seeds.map Prod.fst := by
    rw [census285]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert285) 180 512
    4 AffineBoundaryCached.sheets285 AffineBoundaryCached.shadows285
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt285
    (AffineBoundaryCached.checked285) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census286 : (AffineBoundaryCached.cert286).seeds.map Prod.fst = AffineSearchData.allowed286 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 286 is a boundary. -/
theorem boundary286 : TopFiberBoundary 0x86810c020004000000000000003a000c0980020020 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x86810c020004000000000000003a000c0980020020)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete286 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert286).beta ∈
      (AffineBoundaryCached.cert286).seeds.map Prod.fst := by
    rw [census286]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert286) 180 512
    8 AffineBoundaryCached.sheets286 AffineBoundaryCached.shadows286
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt286
    (AffineBoundaryCached.checked286) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census287 : (AffineBoundaryCached.cert287).seeds.map Prod.fst = AffineSearchData.allowed287 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 287 is a boundary. -/
theorem boundary287 : TopFiberBoundary 0x8f811c0200040000000000000030000c0900020020 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x8f811c0200040000000000000030000c0900020020)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete287 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert287).beta ∈
      (AffineBoundaryCached.cert287).seeds.map Prod.fst := by
    rw [census287]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert287) 180 512
    2 AffineBoundaryCached.sheets287 AffineBoundaryCached.shadows287
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt287
    (AffineBoundaryCached.checked287) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census288 : (AffineBoundaryCached.cert288).seeds.map Prod.fst = AffineSearchData.allowed288 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 288 is a boundary. -/
theorem boundary288 : TopFiberBoundary 0xa600980a8002002000000400005600000100080080 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0xa600980a8002002000000400005600000100080080)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete288 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert288).beta ∈
      (AffineBoundaryCached.cert288).seeds.map Prod.fst := by
    rw [census288]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert288) 180 512
    2 AffineBoundaryCached.sheets288 AffineBoundaryCached.shadows288
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt288
    (AffineBoundaryCached.checked288) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census289 : (AffineBoundaryCached.cert289).seeds.map Prod.fst = AffineSearchData.allowed289 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 289 is a boundary. -/
theorem boundary289 : TopFiberBoundary 0xb40028108004004000000800005000a00c00180100 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0xb40028108004004000000800005000a00c00180100)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete289 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert289).beta ∈
      (AffineBoundaryCached.cert289).seeds.map Prod.fst := by
    rw [census289]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert289) 180 512
    2 AffineBoundaryCached.sheets289 AffineBoundaryCached.shadows289
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt289
    (AffineBoundaryCached.checked289) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census290 : (AffineBoundaryCached.cert290).seeds.map Prod.fst = AffineSearchData.allowed290 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 290 is a boundary. -/
theorem boundary290 : TopFiberBoundary 0xe700d0020000000000000000000c00600f80100000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0xe700d0020000000000000000000c00600f80100000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete290 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert290).beta ∈
      (AffineBoundaryCached.cert290).seeds.map Prod.fst := by
    rw [census290]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert290) 180 512
    4 AffineBoundaryCached.sheets290 AffineBoundaryCached.shadows290
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt290
    (AffineBoundaryCached.checked290) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census291 : (AffineBoundaryCached.cert291).seeds.map Prod.fst = AffineSearchData.allowed291 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 291 is a boundary. -/
theorem boundary291 : TopFiberBoundary 0xe70160010000000000000000000c00a00f80080000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0xe70160010000000000000000000c00a00f80080000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete291 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert291).beta ∈
      (AffineBoundaryCached.cert291).seeds.map Prod.fst := by
    rw [census291]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert291) 180 512
    4 AffineBoundaryCached.sheets291 AffineBoundaryCached.shadows291
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt291
    (AffineBoundaryCached.checked291) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census292 : (AffineBoundaryCached.cert292).seeds.map Prod.fst = AffineSearchData.allowed292 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 292 is a boundary. -/
theorem boundary292 : TopFiberBoundary 0xe80080000000240128168020000005000400006000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0xe80080000000240128168020000005000400006000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete292 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert292).beta ∈
      (AffineBoundaryCached.cert292).seeds.map Prod.fst := by
    rw [census292]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert292) 180 512
    4 AffineBoundaryCached.sheets292 AffineBoundaryCached.shadows292
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt292
    (AffineBoundaryCached.checked292) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census293 : (AffineBoundaryCached.cert293).seeds.map Prod.fst = AffineSearchData.allowed293 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 293 is a boundary. -/
theorem boundary293 : TopFiberBoundary 0xe80400080000240128168020000000000400406000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0xe80400080000240128168020000000000400406000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete293 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert293).beta ∈
      (AffineBoundaryCached.cert293).seeds.map Prod.fst := by
    rw [census293]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert293) 180 512
    4 AffineBoundaryCached.sheets293 AffineBoundaryCached.shadows293
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt293
    (AffineBoundaryCached.checked293) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census294 : (AffineBoundaryCached.cert294).seeds.map Prod.fst = AffineSearchData.allowed294 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 294 is a boundary. -/
theorem boundary294 : TopFiberBoundary 0xee0050030000000000000000000600c00f00180000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0xee0050030000000000000000000600c00f00180000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete294 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert294).beta ∈
      (AffineBoundaryCached.cert294).seeds.map Prod.fst := by
    rw [census294]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert294) 180 512
    4 AffineBoundaryCached.sheets294 AffineBoundaryCached.shadows294
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt294
    (AffineBoundaryCached.checked294) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census295 : (AffineBoundaryCached.cert295).seeds.map Prod.fst = AffineSearchData.allowed295 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 295 is a boundary. -/
theorem boundary295 : TopFiberBoundary 0xee0088028000000000000000000600a00f00140000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0xee0088028000000000000000000600a00f00140000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete295 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert295).beta ∈
      (AffineBoundaryCached.cert295).seeds.map Prod.fst := by
    rw [census295]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert295) 180 512
    4 AffineBoundaryCached.sheets295 AffineBoundaryCached.shadows295
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt295
    (AffineBoundaryCached.checked295) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census296 : (AffineBoundaryCached.cert296).seeds.map Prod.fst = AffineSearchData.allowed296 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 296 is a boundary. -/
theorem boundary296 : TopFiberBoundary 0xee0170010000000000000000000600a00f00080000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0xee0170010000000000000000000600a00f00080000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete296 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert296).beta ∈
      (AffineBoundaryCached.cert296).seeds.map Prod.fst := by
    rw [census296]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert296) 180 512
    6 AffineBoundaryCached.sheets296 AffineBoundaryCached.shadows296
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt296
    (AffineBoundaryCached.checked296) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census297 : (AffineBoundaryCached.cert297).seeds.map Prod.fst = AffineSearchData.allowed297 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 297 is a boundary. -/
theorem boundary297 : TopFiberBoundary 0xee01a8008000000000000000000600c00f00040000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0xee01a8008000000000000000000600c00f00040000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete297 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert297).beta ∈
      (AffineBoundaryCached.cert297).seeds.map Prod.fst := by
    rw [census297]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert297) 180 512
    6 AffineBoundaryCached.sheets297 AffineBoundaryCached.shadows297
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt297
    (AffineBoundaryCached.checked297) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census298 : (AffineBoundaryCached.cert298).seeds.map Prod.fst = AffineSearchData.allowed298 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 298 is a boundary. -/
theorem boundary298 : TopFiberBoundary 0xf001000000006c00180d8000000003000800003000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0xf001000000006c00180d8000000003000800003000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete298 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert298).beta ∈
      (AffineBoundaryCached.cert298).seeds.map Prod.fst := by
    rw [census298]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert298) 180 512
    2 AffineBoundaryCached.sheets298 AffineBoundaryCached.shadows298
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt298
    (AffineBoundaryCached.checked298) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census299 : (AffineBoundaryCached.cert299).seeds.map Prod.fst = AffineSearchData.allowed299 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 299 is a boundary. -/
theorem boundary299 : TopFiberBoundary 0xf008001000006c00180d8000000000000800803000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0xf008001000006c00180d8000000000000800803000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete299 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert299).beta ∈
      (AffineBoundaryCached.cert299).seeds.map Prod.fst := by
    rw [census299]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert299) 180 512
    2 AffineBoundaryCached.sheets299 AffineBoundaryCached.shadows299
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt299
    (AffineBoundaryCached.checked299) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census300 : (AffineBoundaryCached.cert300).seeds.map Prod.fst = AffineSearchData.allowed300 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 300 is a boundary. -/
theorem boundary300 : TopFiberBoundary 0xfc0070110004004000000800000000c00800140100 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0xfc0070110004004000000800000000c00800140100)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete300 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert300).beta ∈
      (AffineBoundaryCached.cert300).seeds.map Prod.fst := by
    rw [census300]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert300) 180 512
    2 AffineBoundaryCached.sheets300 AffineBoundaryCached.shadows300
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt300
    (AffineBoundaryCached.checked300) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census301 : (AffineBoundaryCached.cert301).seeds.map Prod.fst = AffineSearchData.allowed301 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 301 is a boundary. -/
theorem boundary301 : TopFiberBoundary 0xfc0118138004004000000800000000600800000100 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0xfc0118138004004000000800000000600800000100)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete301 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert301).beta ∈
      (AffineBoundaryCached.cert301).seeds.map Prod.fst := by
    rw [census301]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert301) 180 512
    4 AffineBoundaryCached.sheets301 AffineBoundaryCached.shadows301
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt301
    (AffineBoundaryCached.checked301) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census302 : (AffineBoundaryCached.cert302).seeds.map Prod.fst = AffineSearchData.allowed302 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 302 is a boundary. -/
theorem boundary302 : TopFiberBoundary 0xfc0150130004004000000800000000a00800040100 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0xfc0150130004004000000800000000a00800040100)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete302 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert302).beta ∈
      (AffineBoundaryCached.cert302).seeds.map Prod.fst := by
    rw [census302]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert302) 180 512
    4 AffineBoundaryCached.sheets302 AffineBoundaryCached.shadows302
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt302
    (AffineBoundaryCached.checked302) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census303 : (AffineBoundaryCached.cert303).seeds.map Prod.fst = AffineSearchData.allowed303 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 303 is a boundary. -/
theorem boundary303 : TopFiberBoundary 0xfc0188128004004000000800000000c00800080100 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0xfc0188128004004000000800000000c00800080100)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete303 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert303).beta ∈
      (AffineBoundaryCached.cert303).seeds.map Prod.fst := by
    rw [census303]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert303) 180 512
    4 AffineBoundaryCached.sheets303 AffineBoundaryCached.shadows303
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt303
    (AffineBoundaryCached.checked303) hw he hseed

end Quantum.Stabilizer.Homological.BB.Bravyi360.TopNonempty
