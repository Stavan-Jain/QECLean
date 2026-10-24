import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.TopBank
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.Join
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.Adjoints
import QEC.Stabilizer.Framework.Homological.Certificate.MaskPeel
import QEC.Stabilizer.Framework.Homological.Certificate.BatchLinear
import QEC.Stabilizer.Framework.Homological.Certificate.PackedListCertificate

noncomputable section
set_option maxRecDepth 100000

namespace Quantum.Stabilizer.Homological.BB.Bravyi360.BottomForest
open F2Mask FiberData PackedDigits

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- A forest component with its full syndrome and selected peeling rows. -/
structure Component where
  root : Nat
  word : Nat
  image : Nat
  steps : List Nat
  deriving Inhabited

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One affine seed, its outside support, and its canonical deck-orbit targets. -/
structure Seed where
  off : Nat
  word : Nat
  targets : List (Nat × Nat)
  deriving Inhabited

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Complete shallow-fiber certificate data. -/
structure Fiber where
  beta : Nat
  weight : Nat
  rhs : Nat
  components : List Component
  seeds : List Seed
  deriving Inhabited

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Selected parity checks used by one forest certificate. -/
noncomputable def selectedRows (r : Fiber) : Nat :=
  (r.components.flatMap fun c => c.steps).foldr (fun q s => Nat.lor (Nat.shiftLeft 1 q) s) 0

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Forest roots read the free coefficients of every supported homogeneous solution. -/
noncomputable def rootMask (r : Fiber) : Nat := xorList (r.components.map fun c => Nat.shiftLeft 1 c.root)

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exposed peeling data in the generic forest-checker format. -/
noncomputable def forest (r : Fiber) : List (Nat × Nat × List Nat) :=
  r.components.map fun c => (c.root,c.word,c.steps)

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Full-syndrome tags retain exactly the combinations solving the original equations. -/
noncomputable def tags (r : Fiber) : List Nat := r.components.map fun c => Nat.xor c.word (Nat.shiftLeft c.image 90)

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- A free-component combination either violates the full syndrome or
reaches a listed deck orbit. -/
noncomputable def candidateOK (beta seed : Nat) (targets : List (Nat × Nat)) (tagged : Nat) : Bool :=
  if Nat.beq (Nat.shiftRight tagged 90) 0 then
    let word := Nat.xor seed (Nat.land tagged (2^90-1))
    let alternative := Nat.xor word beta
    (targets.map Prod.fst).contains (if Nat.ble word alternative then word else alternative)
  else true

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Direct finite checks of support, roots, peeling and candidate coverage. -/
noncomputable def fiberCheck (r : Fiber) : Bool :=
  Nat.blt r.beta (2^90) && Nat.beq (bitCountFast 12 r.beta) r.weight &&
  Nat.blt r.rhs (2^90) &&
  r.components.all (fun c => Nat.blt c.root 90 && Nat.blt c.image (2^90) &&
    Nat.beq (Nat.land c.word r.beta) c.word &&
    Nat.beq (Nat.land c.word (rootMask r)) (Nat.shiftLeft 1 c.root) &&
    Nat.beq (Nat.land c.image (selectedRows r)) 0 && c.steps.all (fun q => Nat.blt q 90)) &&
  peelForestOK (fun q => Nat.land r.beta (bottomERow q)) r.beta 0 (forest r) &&
  r.seeds.all (fun s => Nat.blt s.word (2^90) &&
    Nat.beq (Nat.xor s.word (Nat.land s.word r.beta)) s.off &&
    s.targets.all (fun t => Nat.blt t.1 (2^90) && Nat.blt t.2 58130) &&
    candidateOK r.beta s.word s.targets 0 &&
    xorWalk (candidateOK r.beta s.word s.targets) (tags r) r.components.length 0)

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- A list of all full-E image certificates in one data chunk. -/
noncomputable def ePairs (rs : List Fiber) : List (Nat × Nat) := rs.flatMap fun r =>
  (r.beta,0) :: (r.components.map fun c => (c.word,c.image)) ++ (r.seeds.map fun s => (s.word,r.rhs))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Full-R images for the shadows in one data chunk. -/
noncomputable def rPairs (rs : List Fiber) : List (Nat × Nat) := rs.map fun r => (r.beta,r.rhs)

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- All target joins in a chunk, paired with their common top-bank positions. -/
noncomputable def joinTriples (rs : List Fiber) : List (Nat × Nat × Nat) := rs.flatMap fun r =>
  r.seeds.flatMap fun s => s.targets.map fun t => (t.1,r.beta,topBankMask t.2)

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Verify a list of matrix images with one parallel reconstruction. -/
noncomputable def mapCheck (rows : List (Nat × Nat)) (ps : List (Nat × Nat)) : Bool :=
  Nat.beq (batchRecon (packList 256 (ps.map fun _ => 1)) (packList 256 (ps.map Prod.fst)) rows)
    (packList 256 (ps.map Prod.snd))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Verify all target joins using the actual two sheet-embedding matrices. -/
noncomputable def joinsCheck (ts : List (Nat × Nat × Nat)) : Bool :=
  let rep := packList 256 (ts.map fun _ => 1)
  Nat.beq (Nat.xor (batchRecon rep (packList 256 (ts.map Prod.fst)) bottomLeft)
    (batchRecon rep (packList 256 (ts.map fun t => Nat.xor t.1 t.2.1)) bottomRight))
    (packList 256 (ts.map fun t => t.2.2))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Check one canonical data chunk including all full-matrix equations and top-bank links. -/
noncomputable def groupCheck (rs : List Fiber) : Bool :=
  rs.all fiberCheck && mapCheck bottomEColumns (ePairs rs) &&
    mapCheck bottomRColumns (rPairs rs) && joinsCheck (joinTriples rs)

end Quantum.Stabilizer.Homological.BB.Bravyi360.BottomForest
