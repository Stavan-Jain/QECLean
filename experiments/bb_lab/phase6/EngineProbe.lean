/-
# Phase 6 — ADVERSARIAL probe: is the Engine support-shape lemma (L3/M3) a finite
#   `decide`/`native_decide` over the 16-element ring F₄[Z₂²], or does it require
#   genuinely symbolic radical-ideal algebra (the claimed "no native_decide shortcut")?

The risk asserts: "the ≥3-layer argument is symbolic over radical ideals, not a finite
native_decide." This probe tests that claim head-on.

F₄[Z₂²] = (ZMod 2 × ZMod 2 → Fin4), a ring of size 4^4 = 256 elements. The Engine lemma:
  (i)  Ann(D) = (D) = {αD + β·uv : α,β ∈ F₄}  — a 2-dimensional ideal (16 elements)
  (ii) every NONZERO element of (D) has support either FULL (4 layers) or CO-POINT
       (3 layers), hence ≥3 nonzero layers.
Here D ∈ {Â₁,Â₃,Â₄,B̂₂,B̂₃,B̂₄}, all squaring to 0; uv = (1,1,1,1).

If (i) and (ii) are decidable finite checks over the 256-element ring, the "no native_decide
shortcut" claim is FALSE and L3/M3 is a finite leaf, not research-grade symbolic algebra.
-/
import QEC.Stabilizer.Codes.BivariateBicycle.Gross.Defs

open Quantum.Stabilizer.Homological.BB

namespace EngineProbe

/-! ## F₄ tables (same model as FrameProbe). -/
def fadd : Fin 4 → Fin 4 → Fin 4 :=
  fun a b => (![![0, 1, 2, 3], ![1, 0, 3, 2], ![2, 3, 0, 1], ![3, 2, 1, 0]] a) b
def fmul : Fin 4 → Fin 4 → Fin 4 :=
  fun a b => (![![0, 0, 0, 0], ![0, 1, 2, 3], ![0, 2, 3, 1], ![0, 3, 1, 2]] a) b

/-! ## F₄[Z₂²] as `ZMod 2 × ZMod 2 → Fin 4`. Layers indexed by Z₂² in the order
   (0,0),(1,0),(0,1),(1,1) = "1, s_x, s_y, s_xs_y". -/
abbrev Ring := ZMod 2 × ZMod 2 → Fin 4

def allS : List (ZMod 2 × ZMod 2) :=
  [((0:ZMod 2),(0:ZMod 2)), (1,0), (0,1), (1,1)]

/-- Convolution product in F₄[Z₂²]. -/
def rmul (p q : Ring) : Ring :=
  fun s => allS.foldl (fun acc s' => fadd acc (fmul (p s') (q (s - s')))) 0

/-- The all-ones socle element `uv = (1,1,1,1)`. -/
def uv : Ring := fun _ => 1

/-- `Â₁ = u + ωv`, value vector `(3,1,2,0)` over (1, s_x, s_y, s_xs_y). -/
def Ahat1 : Ring := fun s =>
  if s = (0,0) then 3 else if s = (1,0) then 1 else if s = (0,1) then 2 else 0
/-- `Â₃ = u + ωv` (η=ω): per the A4 table same shape as Â₁ (radical). -/
def Ahat3 : Ring := fun s =>
  if s = (0,0) then 3 else if s = (1,0) then 1 else if s = (0,1) then 2 else 0
/-- `Â₄ = u + ω²v`, value vector `(1+ω², 1, ω², 0) = (2,1,3,0)`. -/
def Ahat4 : Ring := fun s =>
  if s = (0,0) then 2 else if s = (1,0) then 1 else if s = (0,1) then 3 else 0

def f4list : List (Fin 4) := [0, 1, 2, 3]

/-- All 256 ring elements as explicit list (4 layers × 4 values each). -/
def allRing : List Ring :=
  f4list.flatMap fun a => f4list.flatMap fun b =>
    f4list.flatMap fun c => f4list.map fun d =>
      (fun s => if s = (0,0) then a else if s = (1,0) then b
                else if s = (0,1) then c else d)

/-- All 16 F₄-pairs (α,β) generating the ideal {αD + β·uv}. -/
def all16 : List (Fin 4 × Fin 4) :=
  f4list.flatMap fun a => f4list.map fun b => (a, b)

/-- Number of nonzero layers of a ring element. -/
def nLayers (p : Ring) : Nat :=
  (allS.filter (fun s => decide (p s ≠ 0))).length

/-- `r` agrees as a function with some `αD + β·uv`. -/
def inIdeal (D : Ring) (r : Ring) : Bool :=
  all16.any fun ab =>
    allS.all fun s => decide (r s = fadd (fmul ab.1 (D s)) (fmul ab.2 (uv s)))

/-- `r` is annihilated by `D`: `r ⋆ D = 0`. -/
def annihilatedBy (D : Ring) (r : Ring) : Bool :=
  allS.all fun s => decide (rmul r D s = 0)

/-! ## PROBE 1 — D² = 0 for the radical multipliers (over the 256-ring product). -/
example : rmul Ahat1 Ahat1 = (fun _ => 0) := by native_decide
example : rmul Ahat4 Ahat4 = (fun _ => 0) := by native_decide

/-! ## PROBE 2 — Ann(D) = (D): the 256-element ann set EQUALS the 16-element ideal.
    This is Engine (i). Tests: for every ring element r, `r ⋆ D = 0 ↔ r ∈ {αD+βuv}`. -/
example : allRing.all (fun r => annihilatedBy Ahat1 r == inIdeal Ahat1 r) = true := by
  native_decide
example : allRing.all (fun r => annihilatedBy Ahat4 r == inIdeal Ahat4 r) = true := by
  native_decide

/-! ## PROBE 3 — Engine (ii): every NONZERO ideal element has ≥3 nonzero layers.
    This is the exact L4b "Floor" input. If this `native_decide`s, the claimed
    "symbolic radical-ideal" argument is in fact a finite kernel check. -/
example : all16.all (fun ab =>
    let r : Ring := fun s => fadd (fmul ab.1 (Ahat1 s)) (fmul ab.2 (uv s))
    decide (r = (fun _ => 0)) || decide (nLayers r ≥ 3)) = true := by native_decide

example : all16.all (fun ab =>
    let r : Ring := fun s => fadd (fmul ab.1 (Ahat4 s)) (fmul ab.2 (uv s))
    decide (r = (fun _ => 0)) || decide (nLayers r ≥ 3)) = true := by native_decide

end EngineProbe
