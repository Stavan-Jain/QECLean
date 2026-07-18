/-
# Core A-block classification at the bitmask level (de-risk probe, GREEN ~6s)

`classifyCore` (below) proves, by `native_decide` over the 36⁴ ≈ 1.68M normalized
weight-≤5 scan: every gated (∈ im conv baseA) weight-≤5 origin-containing block is
either a hexagon/D-pair A-block, or has no `|b|≤10` completion (its min B-block
coset weight is too big).  This is the COMBINATORIAL HEART of the light-stabilizer
classification — it removes the last research risk (the leaf is feasible and the
fact holds; cross-checked in Python: 68 gated masks, 36 hexdpair + 32 no-completion,
0 violations).

**Bitmask encoding** (≈40× faster than the function encoding): a weight-≤5 A-block
is a 36-bit XOR mask; the `H_A` parity gate and the B-coset are bit operations.

**Data provenance.** `HA_rows` (left-nullspace of `conv baseA`), `hexA`/`MBAcols`/
`Bbasis`/`gdMaps` are exported from the GF(2) computation in the session log.
`hexA_correct` (below) ANCHORS `hexA` to the actual `conv baseA` (native_decide).

**Soundness bridge still TODO** (mechanical, no research risk): anchor `MBAcols`
(= `conv baseB ∘ R`, R a right-inverse of `conv baseA`) and `Bbasis`
(= `conv baseB(Ann A)`) so the B-coset = the actual completion set; the bitmask ↔
function correspondence + `gateM` linearity (so `gateM(conv baseA z) = true ∀z`);
then the assembly (translate-normalize lighter block, apply this, extract witness,
feed the `LightStab` endgame transfers) + the x↔y swap for the B-light case.
-/
import QEC.Stabilizer.Codes.BivariateBicycle.Gross.Defs

open Quantum.Stabilizer.Homological.BB

namespace ClassifyProbe

def HA_rows : List (List Nat) :=
  [[0,1,4,5,18,20],[0,1,2,5,19,21],[2,3,4,5,18,22],[0,3,4,5,19,23],
   [6,7,10,11,24,26],[6,7,8,11,25,27],[8,9,10,11,24,28],[6,9,10,11,25,29],
   [12,13,16,17,30,32],[12,13,14,17,31,33],[14,15,16,17,30,34],[12,15,16,17,31,35]]
def hexA : Array Nat := #[262150,524300,1048600,2097200,4194337,8388611,16777600,33555200,67110400,134220800,268437568,536871104,1073766400,2147532800,4295065600,8590131200,17180004352,34359750656,1572865,3145730,6291460,12582920,8650768,786464,100663360,201326720,402653440,805306880,553649152,50333696,6442455040,12884910080,25769820160,51539640320,35433545728,3221356544]
def MBAcols : Array Nat := #[2185365508,2185232384,1092741043,2185482023,2185465351,2185432070,2424439042,2415919106,1215950017,2431896002,2430828994,2428699010,17725145218,17179869314,9101324353,18202390658,18134102146,17997783170,3277977595,3277981700,0,0,0,0,3632135875,3632398595,0,0,0,0,26298265795,26315079875,0,0,0,0]
def Bbasis : Array Nat := #[37082952697,18541607420,10909896487,5463205811,769133430,464783085]
def gdMaps : Array (Array Nat) := #[#[1,2,3,4,5,0,7,8,9,10,11,6,13,14,15,16,17,12,19,20,21,22,23,18,25,26,27,28,29,24,31,32,33,34,35,30],#[5,0,1,2,3,4,11,6,7,8,9,10,17,12,13,14,15,16,23,18,19,20,21,22,29,24,25,26,27,28,35,30,31,32,33,34],#[19,20,21,22,23,18,25,26,27,28,29,24,31,32,33,34,35,30,1,2,3,4,5,0,7,8,9,10,11,6,13,14,15,16,17,12],#[20,21,22,23,18,19,26,27,28,29,24,25,32,33,34,35,30,31,2,3,4,5,0,1,8,9,10,11,6,7,14,15,16,17,12,13],#[22,23,18,19,20,21,28,29,24,25,26,27,34,35,30,31,32,33,4,5,0,1,2,3,10,11,6,7,8,9,16,17,12,13,14,15],#[23,18,19,20,21,22,29,24,25,26,27,28,35,30,31,32,33,34,5,0,1,2,3,4,11,6,7,8,9,10,17,12,13,14,15,16],#[6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,0,1,2,3,4,5],#[9,10,11,6,7,8,15,16,17,12,13,14,21,22,23,18,19,20,27,28,29,24,25,26,33,34,35,30,31,32,3,4,5,0,1,2],#[15,16,17,12,13,14,21,22,23,18,19,20,27,28,29,24,25,26,33,34,35,30,31,32,3,4,5,0,1,2,9,10,11,6,7,8],#[27,28,29,24,25,26,33,34,35,30,31,32,3,4,5,0,1,2,9,10,11,6,7,8,15,16,17,12,13,14,21,22,23,18,19,20],#[30,31,32,33,34,35,0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29],#[33,34,35,30,31,32,3,4,5,0,1,2,9,10,11,6,7,8,15,16,17,12,13,14,21,22,23,18,19,20,27,28,29,24,25,26]]

def supMask (sup : List (Fin 36)) : Nat := sup.foldl (fun acc i => acc ^^^ (1 <<< i.val)) 0
def gateM (m : Nat) : Bool :=
  HA_rows.all (fun row => (row.foldl (fun acc i => acc ^^^ ((m >>> i) &&& 1)) 0) == 0)
def wtM (m : Nat) : Nat := (List.range 36).foldl (fun acc i => acc + ((m >>> i) &&& 1)) 0
/-- XOR of `cols[i]` over the set bits `i` of `m`. -/
def applyCols (cols : Array Nat) (m : Nat) : Nat :=
  (List.range 36).foldl (fun acc i => if (m >>> i) &&& 1 == 1 then acc ^^^ cols.getD i 0 else acc) 0
/-- min weight over the 64-element B-coset (base `MBA·m`, offsets `span Bbasis`). -/
def minBcoset (m : Nat) : Nat :=
  let base := applyCols MBAcols m
  (List.range 64).foldl (fun acc c =>
    let off := (List.range 6).foldl (fun a i => if (c >>> i) &&& 1 == 1 then a ^^^ Bbasis.getD i 0 else a) 0
    min acc (wtM (base ^^^ off))) 99
def isHexA (m : Nat) : Bool := (List.range 36).any (fun g => m == hexA.getD g 0)
def isDpairA (m : Nat) : Bool :=
  (List.range 36).any (fun g => gdMaps.any (fun gd => m == (hexA.getD g 0 ^^^ hexA.getD (gd.getD g 0) 0)))
def isHexDpairA (m : Nat) : Bool := isHexA m || isDpairA m

/-! ### Soundness anchor: the exported `hexA` data and the gate match actual `conv baseA`. -/

def cellOf (i : Nat) : BaseGroup := ((i / 6 : ℕ), (i % 6 : ℕ))
def bitmaskOf (b : BaseGroup → ZMod 2) : Nat :=
  (List.range 36).foldl (fun acc i => if b (cellOf i) = 1 then acc ^^^ (1 <<< i) else acc) 0

/-- `hexA[g]` IS the bitmask of the actual hexagon A-block `conv baseA δ_g`. -/
theorem hexA_correct : ∀ g : Fin 36,
    hexA.getD g.val 0 = bitmaskOf (conv baseA (Pi.single (cellOf g.val) 1)) := by native_decide
/-- The gate annihilates every hexagon A-block (easy direction on the `im` generators). -/
theorem gate_hexA : ∀ g : Fin 36, gateM (hexA.getD g.val 0) = true := by native_decide

/-- **Core A-block classification (bitmask level)**: a gated weight-≤5 origin-containing
block is a hexagon/D-pair A-block, or has no `|b|≤10` completion. Scans 36⁴ ≈ 1.68M. -/
theorem classifyCore : ∀ q₁ q₂ q₃ q₄ : Fin 36,
    gateM (supMask [0, q₁, q₂, q₃, q₄]) = true →
    isHexDpairA (supMask [0, q₁, q₂, q₃, q₄]) = true
      ∨ 10 < wtM (supMask [0, q₁, q₂, q₃, q₄]) + minBcoset (supMask [0, q₁, q₂, q₃, q₄]) := by
  native_decide

end ClassifyProbe
