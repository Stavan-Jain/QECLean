import QEC.Stabilizer.Framework.Homological.Certificate.PairPlaneCoverage

namespace Quantum.Stabilizer.Homological.F2Mask
open PackedDigits

/-- Fast lookup implementation of the complete pairwise parity plane. -/
def fastPairPlane (width chunk chunks table rep plane : Nat) : Nat :=
  Nat.xor (Nat.mul (fastDilation width chunk table chunks plane) (2^(chunk*chunks)-1))
    (Nat.mul plane rep)

/-- Fast lookup implementation of the outside-coordinate pair domain. -/
def fastPairDomain (width chunk chunks table rep beta : Nat) : Nat :=
  let off := Nat.xor (2^(chunk*chunks)-1) beta
  Nat.land (Nat.mul (fastDilation width chunk table chunks off) (2^(chunk*chunks)-1))
    (Nat.mul off rep)

/-- A certified lookup table implements every parity pair plane exactly. -/
theorem fastPairPlane_eq (width chunk chunks table rep : Nat) (hw : 0 < width)
    (hlookup : ∀ x : Fin (2^chunk), dilationLookup (width*chunk) table x = dilate width chunk x)
    (hrep : rep = packF width (chunk*chunks) (fun _ => 1)) (plane : Nat) :
    fastPairPlane width chunk chunks table rep plane = pairPlaneGrid width (chunk*chunks) plane := by
  unfold fastPairPlane pairPlaneGrid
  rw [fastDilation_eq width chunk table hw hlookup,hrep]
  rfl

/-- A certified lookup table implements the outside pair domain exactly. -/
theorem fastPairDomain_eq (width chunk chunks table rep : Nat) (hw : 0 < width)
    (hlookup : ∀ x : Fin (2^chunk), dilationLookup (width*chunk) table x = dilate width chunk x)
    (hrep : rep = packF width (chunk*chunks) (fun _ => 1)) (beta : Nat) :
    fastPairDomain width chunk chunks table rep beta = pairDomain width (chunk*chunks) beta := by
  unfold fastPairDomain pairDomain
  dsimp only
  rw [fastDilation_eq width chunk table hw hlookup,hrep]
  rfl

/--
A fast parallel pair census is identical to its semantic bit-plane census.
-/
theorem fastPairFilter_eq (width chunk chunks table rep : Nat) (hw : 0 < width)
    (hlookup : ∀ x : Fin (2^chunk), dilationLookup (width*chunk) table x = dilate width chunk x)
    (hrep : rep = packF width (chunk*chunks) (fun _ => 1))
    (planes : List Nat) (target beta : Nat) :
    filterPlanes (planes.map (fastPairPlane width chunk chunks table rep)) target
      (fastPairDomain width chunk chunks table rep beta) =
      filterPlanes (planes.map (pairPlaneGrid width (chunk*chunks))) target
        (pairDomain width (chunk*chunks) beta) := by
  have hp : fastPairPlane width chunk chunks table rep = pairPlaneGrid width (chunk*chunks) :=
    funext (fastPairPlane_eq width chunk chunks table rep hw hlookup hrep)
  rw [hp,fastPairDomain_eq width chunk chunks table rep hw hlookup hrep]

end Quantum.Stabilizer.Homological.F2Mask
