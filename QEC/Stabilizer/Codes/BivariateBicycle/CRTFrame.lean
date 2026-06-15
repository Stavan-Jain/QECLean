/-
# CRT layer frame for the base bb72 complex (A4 §3) — M1 + M3 foundation

Computable F₄, the group algebra `F₄[Z₂²]`, the CRT layer/torus coordinates on
`Z₆`, the six radical multipliers `Â_j`/`B̂_j`, and the **engine support-shape
lemma** over the 256-element ring.  Everything is built on explicit `Fin 4`
tables and `List.foldl` — NO `GaloisField`/`Finsupp`, which are noncomputable and
would defeat `decide`/`native_decide` (the Phase-5 noncomputable-whnf hazard).

Promoted verbatim from the GREEN phase-6 probes `FrameProbe.lean` /
`EngineProbe.lean`; see those for the de-risking history (EngineProbe refuted the
feared "irreducibly symbolic radical-ideal algebra": the ≥3-layer dichotomy is a
finite kernel check).

**CONVENTIONS (A4 §3).** `ω = 2`, `ω² = 3` in the `Fin 4` model;
`Z₆ = Z₂ × Z₃` via `a ↦ (a mod 2, a mod 3)` (`s_x = x³`, `t_x = x⁴`); layers
indexed by `Z₂²` in the order `(0,0),(1,0),(0,1),(1,1) = 1, s_x, s_y, s_xs_y`.

**NOT YET HERE (M2 milestone):** the component transforms `V_j` and the
multiplicativity identity `V_j(A·z) = Â_j·ẑ_j` (needs the F₂-linearity bridge
lemma and carries the repo-left=lab-right / `ω` vs `ω²` convention risk).  This
file is the M1 (F₄ + ring) + M3 (engine) foundation those build on.
-/
import QEC.Stabilizer.Codes.BivariateBicycle.Defs

namespace Quantum
namespace Stabilizer
namespace Homological
namespace BB
namespace CRTFrame

/-! ## §1 Computable F₄ as `Fin 4`: `(0, 1, ω, ω²) ↦ (0, 1, 2, 3)`.

Characteristic-2 addition table and the F₄ multiplication table. -/

/-- F₄ addition (characteristic 2). -/
def fadd : Fin 4 → Fin 4 → Fin 4 :=
  fun a b => (![![0, 1, 2, 3], ![1, 0, 3, 2], ![2, 3, 0, 1], ![3, 2, 1, 0]] a) b

/-- F₄ multiplication. -/
def fmul : Fin 4 → Fin 4 → Fin 4 :=
  fun a b => (![![0, 0, 0, 0], ![0, 1, 2, 3], ![0, 2, 3, 1], ![0, 3, 1, 2]] a) b

/-- `ω^k` for `k ∈ Z₃`: `1, ω, ω²` ↦ `1, 2, 3`. -/
def omegaPow (k : ZMod 3) : Fin 4 := if k = 0 then 1 else if k = 1 then 2 else 3

/-! ### F₄ field axioms (all closed `∀` statements over the 4-element carrier,
discharged by `decide`). -/

theorem fadd_comm : ∀ a b : Fin 4, fadd a b = fadd b a := by decide
theorem fadd_assoc : ∀ a b c : Fin 4, fadd (fadd a b) c = fadd a (fadd b c) := by decide
theorem fadd_zero : ∀ a : Fin 4, fadd a 0 = a := by decide
theorem fadd_self : ∀ a : Fin 4, fadd a a = 0 := by decide
theorem fmul_comm : ∀ a b : Fin 4, fmul a b = fmul b a := by decide
theorem fmul_assoc : ∀ a b c : Fin 4, fmul (fmul a b) c = fmul a (fmul b c) := by decide
theorem fmul_one : ∀ a : Fin 4, fmul a 1 = a := by decide
theorem fmul_zero : ∀ a : Fin 4, fmul a 0 = 0 := by decide
theorem fmul_fadd : ∀ a b c : Fin 4, fmul a (fadd b c) = fadd (fmul a b) (fmul a c) := by decide
/-- F₄ is a field: every nonzero element has a multiplicative inverse. -/
theorem fmul_inv : ∀ a : Fin 4, a ≠ 0 → ∃ b, fmul a b = 1 := by decide

/-! ## §2 The group algebra `F₄[Z₂²] = (Z₂² → Fin 4)`: 16-element carrier,
256-element ring. -/

/-- Carrier of `F₄[Z₂²]`. -/
abbrev Ring := ZMod 2 × ZMod 2 → Fin 4

/-- The four layers in canonical order `(1, s_x, s_y, s_xs_y)`. -/
def allS : List (ZMod 2 × ZMod 2) := [((0 : ZMod 2), (0 : ZMod 2)), (1, 0), (0, 1), (1, 1)]

/-- Convolution product in `F₄[Z₂²]`. -/
def rmul (p q : Ring) : Ring :=
  fun s => allS.foldl (fun acc s' => fadd acc (fmul (p s') (q (s - s')))) 0

/-- The all-ones socle element `uv = 1 + s_x + s_y + s_xs_y`. -/
def uv : Ring := fun _ => 1

/-! ## §3 CRT coordinates on `Z₆`: layer (mod 2) and torus (mod 3). -/

/-- Layer coordinate of `a ∈ Z₆` (reduce mod 2). -/
def layer1 (a : ZMod 6) : ZMod 2 := (a.val : ZMod 2)

/-- Torus coordinate of `a ∈ Z₆` (reduce mod 3). -/
def torus1 (a : ZMod 6) : ZMod 3 := (a.val : ZMod 3)

/-- Layer `s ∈ Z₂²` of a base cell. -/
def layer (g : BaseGroup) : ZMod 2 × ZMod 2 := (layer1 g.1, layer1 g.2)

/-- Torus `t ∈ Z₃²` of a base cell. -/
def torus (g : BaseGroup) : ZMod 3 × ZMod 3 := (torus1 g.1, torus1 g.2)

/-! ## §4 The radical multipliers (A4 §3 table), as value vectors over the
layers `(0,0),(1,0),(0,1),(1,1) = (1, s_x, s_y, s_xs_y)`.

The six radical multipliers `Â₁, Â₃, Â₄, B̂₂, B̂₃, B̂₄` collapse to three distinct
value vectors, each with exactly one zero layer and three distinct nonzero
values — the input to the engine's ≥3-layer dichotomy. -/

/-- `Â₁ = Â₃ = u + ωv`, value vector `(3, 1, 2, 0)`. -/
def Ahat1 : Ring := fun s =>
  if s = (0, 0) then 3 else if s = (1, 0) then 1 else if s = (0, 1) then 2 else 0

/-- `Â₄ = u + ω²v`, value vector `(2, 1, 3, 0)`. -/
def Ahat4 : Ring := fun s =>
  if s = (0, 0) then 2 else if s = (1, 0) then 1 else if s = (0, 1) then 3 else 0

/-- `B̂₂ = B̂₃ = B̂₄ = ωu + v`, value vector `(3, 2, 1, 0)`. -/
def Bhat2 : Ring := fun s =>
  if s = (0, 0) then 3 else if s = (1, 0) then 2 else if s = (0, 1) then 1 else 0

/-! ## §5 Engine support-shape lemma (A4 §3).

For a radical multiplier `D` (here `Â₁`, `Â₄`, `B̂₂` — the three distinct
vectors): `D² = 0`, `Ann(D) = (D) = {αD + β·uv}` (a 2-dimensional ideal), and
every NONZERO ideal element has `≥ 3` nonzero layers.  All three are finite
checks over the 256-element ring (EngineProbe GREEN). -/

/-- The four F₄ values. -/
def f4list : List (Fin 4) := [0, 1, 2, 3]

/-- All 256 ring elements as an explicit list (4 layers × 4 values). -/
def allRing : List Ring :=
  f4list.flatMap fun a => f4list.flatMap fun b =>
    f4list.flatMap fun c => f4list.map fun d =>
      (fun s => if s = (0, 0) then a else if s = (1, 0) then b
                else if s = (0, 1) then c else d)

/-- All 16 F₄-pairs `(α, β)` generating the ideal `{αD + β·uv}`. -/
def all16 : List (Fin 4 × Fin 4) :=
  f4list.flatMap fun a => f4list.map fun b => (a, b)

/-- Number of nonzero layers of a ring element. -/
def nLayers (p : Ring) : Nat := (allS.filter (fun s => decide (p s ≠ 0))).length

/-- `r` agrees as a function with some `αD + β·uv`. -/
def inIdeal (D : Ring) (r : Ring) : Bool :=
  all16.any fun ab => allS.all fun s => decide (r s = fadd (fmul ab.1 (D s)) (fmul ab.2 (uv s)))

/-- `r` is annihilated by `D`: `r ⋆ D = 0`. -/
def annihilatedBy (D : Ring) (r : Ring) : Bool :=
  allS.all fun s => decide (rmul r D s = 0)

/-! ### Engine (D² = 0) for the three radical multipliers. -/

theorem Ahat1_sq : rmul Ahat1 Ahat1 = (fun _ => 0) := by native_decide
theorem Ahat4_sq : rmul Ahat4 Ahat4 = (fun _ => 0) := by native_decide
theorem Bhat2_sq : rmul Bhat2 Bhat2 = (fun _ => 0) := by native_decide

/-! ### Engine (i): `Ann(D) = (D)`.  The 256-element annihilator set equals the
16-element ideal `{αD + β·uv}`. -/

theorem Ahat1_ann_eq_ideal :
    allRing.all (fun r => annihilatedBy Ahat1 r == inIdeal Ahat1 r) = true := by native_decide
theorem Ahat4_ann_eq_ideal :
    allRing.all (fun r => annihilatedBy Ahat4 r == inIdeal Ahat4 r) = true := by native_decide
theorem Bhat2_ann_eq_ideal :
    allRing.all (fun r => annihilatedBy Bhat2 r == inIdeal Bhat2 r) = true := by native_decide

/-! ### Engine (ii): every NONZERO ideal element has `≥ 3` nonzero layers.
This is the exact L4b "Floor" input. -/

theorem Ahat1_ideal_ge3 : all16.all (fun ab =>
    let r : Ring := fun s => fadd (fmul ab.1 (Ahat1 s)) (fmul ab.2 (uv s))
    decide (r = (fun _ => 0)) || decide (nLayers r ≥ 3)) = true := by native_decide
theorem Ahat4_ideal_ge3 : all16.all (fun ab =>
    let r : Ring := fun s => fadd (fmul ab.1 (Ahat4 s)) (fmul ab.2 (uv s))
    decide (r = (fun _ => 0)) || decide (nLayers r ≥ 3)) = true := by native_decide
theorem Bhat2_ideal_ge3 : all16.all (fun ab =>
    let r : Ring := fun s => fadd (fmul ab.1 (Bhat2 s)) (fmul ab.2 (uv s))
    decide (r = (fun _ => 0)) || decide (nLayers r ≥ 3)) = true := by native_decide

end CRTFrame
end BB
end Homological
end Stabilizer
end Quantum
