/-
GENERATED FILE — DO NOT HAND-EDIT
Generator: qec-lab:experiments/bb_lab/scripts/bravyi360_kernel/generate.py
Emitter, relative to generator directory:
  emitters/split_orbit_batch_data.py
Data and SHA-256 hashes: research_manifest.json
Regenerate:
  QECLEAN_ROOT=/path/to/QECLean \
    python3 experiments/bb_lab/scripts/bravyi360_kernel/generate.py --force
-/

import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.OrbitBatchData

noncomputable section
set_option maxRecDepth 400000
namespace OrbitBatchCheck
open OrbitBatchData
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
noncomputable def lo2 : Nat := 530545731122305832099624667
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
noncomputable def hi1 : Nat := 707394308163074442799499556
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
noncomputable def yrot (r v : Nat) : Nat := ((v &&& (r*lo2)) <<< 1) ||| ((v >>> 2) &&& (r*(hi1/4)))
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
noncomputable def xrot (r v x : Nat) : Nat :=
  let s := 3*x
  ((v >>> s) &&& (r*((2^(45-s)-1)*(1+2^45)))) |||
    ((v <<< (45-s)) &&& (r*(((2^s-1) <<< (45-s))*(1+2^45))))
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
noncomputable def tr (r v i : Nat) : Nat :=
  xrot r (if i/15 = 0 then v else if i/15 = 1 then yrot r v else yrot r (yrot r v)) (i%15)
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
noncomputable def pcMask (k : Nat) : Nat :=  if k = 0 then 113427455640312821154458202477256070485 else if k = 1 then 68056473384187692692674921486353642291 else if k = 2 then 20016609818878733144904388672456953615 else if k = 3 then 1324055902416102970674609367438786815 else if k = 4 then 5192217631581220737344928932233215 else if k = 5 then 79228162495817593524129366015 else 18446744073709551615
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
noncomputable def popcount128 (r v : Nat) : Nat := (List.range 7).foldl (fun v k => (v &&& (r*pcMask k)) + ((v >>> (2^k)) &&& (r*pcMask k))) v
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
noncomputable def extraCheck (r v : Nat) : Bool :=
  let mask := r*(2^90-1)
  let weights := popcount128 r v
  let ps := r <<< 7
  let prev := r >>> 128
  let s := prev <<< 90
  ((v &&& mask) == v) && ((((r*22+ps-weights) &&& ps) == ps)) &&
    (((((v >>> 128)+s-(v &&& (prev*(2^90-1)))-prev) &&& s) == s))
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
noncomputable def batchCheck (r v expected : Nat) : Bool :=
  let s := r <<< 90
  let l := r*(2^90-1)
  extraCheck r v && ((List.range 45).all fun i => (((tr r v i+s-v) &&& s) == s)) &&
    (((List.range 45).foldl (fun acc i => acc + ((s ^^^ (((tr r v i ^^^ v)+l) &&& s)) >>> 90)) 0) == expected)
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked0 : batchCheck reps0 words0 expected0 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked1 : batchCheck reps1 words1 expected1 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked2 : batchCheck reps2 words2 expected2 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked3 : batchCheck reps3 words3 expected3 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked4 : batchCheck reps4 words4 expected4 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked5 : batchCheck reps5 words5 expected5 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked6 : batchCheck reps6 words6 expected6 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked7 : batchCheck reps7 words7 expected7 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked8 : batchCheck reps8 words8 expected8 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked9 : batchCheck reps9 words9 expected9 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked10 : batchCheck reps10 words10 expected10 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked11 : batchCheck reps11 words11 expected11 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked12 : batchCheck reps12 words12 expected12 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked13 : batchCheck reps13 words13 expected13 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked14 : batchCheck reps14 words14 expected14 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked15 : batchCheck reps15 words15 expected15 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked16 : batchCheck reps16 words16 expected16 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked17 : batchCheck reps17 words17 expected17 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked18 : batchCheck reps18 words18 expected18 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked19 : batchCheck reps19 words19 expected19 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked20 : batchCheck reps20 words20 expected20 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked21 : batchCheck reps21 words21 expected21 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked22 : batchCheck reps22 words22 expected22 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked23 : batchCheck reps23 words23 expected23 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked24 : batchCheck reps24 words24 expected24 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked25 : batchCheck reps25 words25 expected25 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked26 : batchCheck reps26 words26 expected26 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked27 : batchCheck reps27 words27 expected27 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked28 : batchCheck reps28 words28 expected28 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked29 : batchCheck reps29 words29 expected29 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked30 : batchCheck reps30 words30 expected30 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked31 : batchCheck reps31 words31 expected31 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked32 : batchCheck reps32 words32 expected32 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked33 : batchCheck reps33 words33 expected33 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked34 : batchCheck reps34 words34 expected34 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked35 : batchCheck reps35 words35 expected35 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked36 : batchCheck reps36 words36 expected36 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked37 : batchCheck reps37 words37 expected37 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked38 : batchCheck reps38 words38 expected38 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked39 : batchCheck reps39 words39 expected39 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked40 : batchCheck reps40 words40 expected40 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked41 : batchCheck reps41 words41 expected41 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked42 : batchCheck reps42 words42 expected42 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked43 : batchCheck reps43 words43 expected43 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked44 : batchCheck reps44 words44 expected44 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked45 : batchCheck reps45 words45 expected45 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked46 : batchCheck reps46 words46 expected46 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked47 : batchCheck reps47 words47 expected47 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked48 : batchCheck reps48 words48 expected48 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked49 : batchCheck reps49 words49 expected49 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked50 : batchCheck reps50 words50 expected50 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked51 : batchCheck reps51 words51 expected51 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked52 : batchCheck reps52 words52 expected52 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked53 : batchCheck reps53 words53 expected53 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked54 : batchCheck reps54 words54 expected54 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked55 : batchCheck reps55 words55 expected55 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked56 : batchCheck reps56 words56 expected56 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked57 : batchCheck reps57 words57 expected57 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked58 : batchCheck reps58 words58 expected58 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked59 : batchCheck reps59 words59 expected59 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked60 : batchCheck reps60 words60 expected60 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked61 : batchCheck reps61 words61 expected61 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked62 : batchCheck reps62 words62 expected62 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked63 : batchCheck reps63 words63 expected63 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked64 : batchCheck reps64 words64 expected64 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked65 : batchCheck reps65 words65 expected65 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked66 : batchCheck reps66 words66 expected66 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked67 : batchCheck reps67 words67 expected67 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked68 : batchCheck reps68 words68 expected68 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked69 : batchCheck reps69 words69 expected69 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked70 : batchCheck reps70 words70 expected70 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked71 : batchCheck reps71 words71 expected71 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked72 : batchCheck reps72 words72 expected72 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked73 : batchCheck reps73 words73 expected73 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked74 : batchCheck reps74 words74 expected74 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked75 : batchCheck reps75 words75 expected75 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked76 : batchCheck reps76 words76 expected76 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked77 : batchCheck reps77 words77 expected77 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked78 : batchCheck reps78 words78 expected78 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked79 : batchCheck reps79 words79 expected79 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked80 : batchCheck reps80 words80 expected80 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked81 : batchCheck reps81 words81 expected81 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked82 : batchCheck reps82 words82 expected82 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked83 : batchCheck reps83 words83 expected83 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked84 : batchCheck reps84 words84 expected84 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked85 : batchCheck reps85 words85 expected85 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked86 : batchCheck reps86 words86 expected86 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked87 : batchCheck reps87 words87 expected87 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked88 : batchCheck reps88 words88 expected88 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked89 : batchCheck reps89 words89 expected89 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked90 : batchCheck reps90 words90 expected90 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked91 : batchCheck reps91 words91 expected91 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked92 : batchCheck reps92 words92 expected92 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked93 : batchCheck reps93 words93 expected93 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked94 : batchCheck reps94 words94 expected94 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked95 : batchCheck reps95 words95 expected95 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked96 : batchCheck reps96 words96 expected96 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked97 : batchCheck reps97 words97 expected97 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked98 : batchCheck reps98 words98 expected98 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked99 : batchCheck reps99 words99 expected99 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked100 : batchCheck reps100 words100 expected100 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked101 : batchCheck reps101 words101 expected101 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked102 : batchCheck reps102 words102 expected102 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked103 : batchCheck reps103 words103 expected103 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked104 : batchCheck reps104 words104 expected104 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked105 : batchCheck reps105 words105 expected105 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked106 : batchCheck reps106 words106 expected106 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked107 : batchCheck reps107 words107 expected107 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked108 : batchCheck reps108 words108 expected108 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked109 : batchCheck reps109 words109 expected109 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked110 : batchCheck reps110 words110 expected110 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked111 : batchCheck reps111 words111 expected111 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked112 : batchCheck reps112 words112 expected112 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked113 : batchCheck reps113 words113 expected113 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked114 : batchCheck reps114 words114 expected114 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked115 : batchCheck reps115 words115 expected115 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked116 : batchCheck reps116 words116 expected116 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked117 : batchCheck reps117 words117 expected117 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked118 : batchCheck reps118 words118 expected118 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked119 : batchCheck reps119 words119 expected119 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked120 : batchCheck reps120 words120 expected120 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked121 : batchCheck reps121 words121 expected121 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked122 : batchCheck reps122 words122 expected122 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked123 : batchCheck reps123 words123 expected123 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked124 : batchCheck reps124 words124 expected124 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked125 : batchCheck reps125 words125 expected125 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked126 : batchCheck reps126 words126 expected126 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked127 : batchCheck reps127 words127 expected127 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked128 : batchCheck reps128 words128 expected128 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked129 : batchCheck reps129 words129 expected129 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked130 : batchCheck reps130 words130 expected130 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked131 : batchCheck reps131 words131 expected131 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked132 : batchCheck reps132 words132 expected132 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked133 : batchCheck reps133 words133 expected133 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked134 : batchCheck reps134 words134 expected134 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked135 : batchCheck reps135 words135 expected135 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked136 : batchCheck reps136 words136 expected136 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked137 : batchCheck reps137 words137 expected137 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked138 : batchCheck reps138 words138 expected138 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked139 : batchCheck reps139 words139 expected139 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked140 : batchCheck reps140 words140 expected140 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked141 : batchCheck reps141 words141 expected141 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked142 : batchCheck reps142 words142 expected142 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked143 : batchCheck reps143 words143 expected143 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked144 : batchCheck reps144 words144 expected144 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked145 : batchCheck reps145 words145 expected145 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked146 : batchCheck reps146 words146 expected146 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked147 : batchCheck reps147 words147 expected147 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked148 : batchCheck reps148 words148 expected148 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked149 : batchCheck reps149 words149 expected149 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked150 : batchCheck reps150 words150 expected150 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked151 : batchCheck reps151 words151 expected151 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked152 : batchCheck reps152 words152 expected152 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked153 : batchCheck reps153 words153 expected153 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked154 : batchCheck reps154 words154 expected154 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked155 : batchCheck reps155 words155 expected155 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked156 : batchCheck reps156 words156 expected156 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked157 : batchCheck reps157 words157 expected157 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked158 : batchCheck reps158 words158 expected158 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked159 : batchCheck reps159 words159 expected159 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked160 : batchCheck reps160 words160 expected160 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked161 : batchCheck reps161 words161 expected161 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked162 : batchCheck reps162 words162 expected162 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked163 : batchCheck reps163 words163 expected163 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked164 : batchCheck reps164 words164 expected164 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked165 : batchCheck reps165 words165 expected165 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked166 : batchCheck reps166 words166 expected166 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked167 : batchCheck reps167 words167 expected167 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked168 : batchCheck reps168 words168 expected168 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked169 : batchCheck reps169 words169 expected169 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked170 : batchCheck reps170 words170 expected170 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked171 : batchCheck reps171 words171 expected171 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked172 : batchCheck reps172 words172 expected172 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked173 : batchCheck reps173 words173 expected173 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked174 : batchCheck reps174 words174 expected174 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked175 : batchCheck reps175 words175 expected175 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked176 : batchCheck reps176 words176 expected176 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked177 : batchCheck reps177 words177 expected177 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked178 : batchCheck reps178 words178 expected178 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked179 : batchCheck reps179 words179 expected179 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked180 : batchCheck reps180 words180 expected180 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked181 : batchCheck reps181 words181 expected181 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked182 : batchCheck reps182 words182 expected182 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked183 : batchCheck reps183 words183 expected183 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked184 : batchCheck reps184 words184 expected184 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked185 : batchCheck reps185 words185 expected185 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked186 : batchCheck reps186 words186 expected186 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked187 : batchCheck reps187 words187 expected187 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked188 : batchCheck reps188 words188 expected188 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked189 : batchCheck reps189 words189 expected189 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked190 : batchCheck reps190 words190 expected190 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked191 : batchCheck reps191 words191 expected191 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked192 : batchCheck reps192 words192 expected192 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked193 : batchCheck reps193 words193 expected193 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked194 : batchCheck reps194 words194 expected194 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked195 : batchCheck reps195 words195 expected195 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked196 : batchCheck reps196 words196 expected196 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked197 : batchCheck reps197 words197 expected197 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked198 : batchCheck reps198 words198 expected198 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked199 : batchCheck reps199 words199 expected199 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked200 : batchCheck reps200 words200 expected200 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked201 : batchCheck reps201 words201 expected201 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked202 : batchCheck reps202 words202 expected202 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked203 : batchCheck reps203 words203 expected203 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked204 : batchCheck reps204 words204 expected204 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked205 : batchCheck reps205 words205 expected205 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked206 : batchCheck reps206 words206 expected206 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked207 : batchCheck reps207 words207 expected207 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked208 : batchCheck reps208 words208 expected208 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked209 : batchCheck reps209 words209 expected209 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked210 : batchCheck reps210 words210 expected210 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked211 : batchCheck reps211 words211 expected211 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked212 : batchCheck reps212 words212 expected212 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked213 : batchCheck reps213 words213 expected213 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked214 : batchCheck reps214 words214 expected214 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked215 : batchCheck reps215 words215 expected215 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked216 : batchCheck reps216 words216 expected216 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked217 : batchCheck reps217 words217 expected217 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked218 : batchCheck reps218 words218 expected218 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked219 : batchCheck reps219 words219 expected219 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked220 : batchCheck reps220 words220 expected220 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked221 : batchCheck reps221 words221 expected221 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked222 : batchCheck reps222 words222 expected222 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked223 : batchCheck reps223 words223 expected223 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked224 : batchCheck reps224 words224 expected224 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked225 : batchCheck reps225 words225 expected225 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked226 : batchCheck reps226 words226 expected226 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked227 : batchCheck reps227 words227 expected227 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked228 : batchCheck reps228 words228 expected228 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked229 : batchCheck reps229 words229 expected229 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked230 : batchCheck reps230 words230 expected230 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked231 : batchCheck reps231 words231 expected231 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked232 : batchCheck reps232 words232 expected232 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked233 : batchCheck reps233 words233 expected233 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked234 : batchCheck reps234 words234 expected234 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked235 : batchCheck reps235 words235 expected235 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked236 : batchCheck reps236 words236 expected236 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked237 : batchCheck reps237 words237 expected237 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked238 : batchCheck reps238 words238 expected238 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked239 : batchCheck reps239 words239 expected239 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked240 : batchCheck reps240 words240 expected240 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked241 : batchCheck reps241 words241 expected241 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked242 : batchCheck reps242 words242 expected242 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked243 : batchCheck reps243 words243 expected243 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked244 : batchCheck reps244 words244 expected244 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked245 : batchCheck reps245 words245 expected245 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked246 : batchCheck reps246 words246 expected246 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked247 : batchCheck reps247 words247 expected247 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked248 : batchCheck reps248 words248 expected248 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked249 : batchCheck reps249 words249 expected249 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked250 : batchCheck reps250 words250 expected250 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked251 : batchCheck reps251 words251 expected251 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked252 : batchCheck reps252 words252 expected252 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked253 : batchCheck reps253 words253 expected253 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked254 : batchCheck reps254 words254 expected254 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked255 : batchCheck reps255 words255 expected255 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked256 : batchCheck reps256 words256 expected256 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked257 : batchCheck reps257 words257 expected257 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked258 : batchCheck reps258 words258 expected258 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked259 : batchCheck reps259 words259 expected259 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked260 : batchCheck reps260 words260 expected260 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked261 : batchCheck reps261 words261 expected261 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked262 : batchCheck reps262 words262 expected262 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked263 : batchCheck reps263 words263 expected263 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked264 : batchCheck reps264 words264 expected264 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked265 : batchCheck reps265 words265 expected265 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked266 : batchCheck reps266 words266 expected266 = true := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- This packed batch passes all finite orbit checks through the kernel. -/
theorem checked267 : batchCheck reps267 words267 expected267 = true := by decide +kernel
#print axioms checked267
end OrbitBatchCheck
