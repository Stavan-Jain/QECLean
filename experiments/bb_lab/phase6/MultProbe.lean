/-
# Phase 6 — M2-(A) probe: ALL ~10 CRT-frame multiplicativity instances.

The load-bearing CRT-frame identity (A4 §3) is `V_j(P · z) = P̂_j · ẑ_j` (product
in F₄[Z₂²]).  Since both sides are F₂-linear in `z`, it holds for all `z` iff it
holds on the 36 point-mass basis chains `δ_p`.  `FrameProbe.lean` proved the
`(j=1, P=A)` instance GREEN.  This probe extends that to **all 10 instances**
`j ∈ {0,1,2,3,4} × P ∈ {A, B}` — the risk-register step "certify all instances
native_decide GREEN before building above them", so a convention bug
(repo-left=lab-right, ω vs ω², layer/torus orientation) surfaces as a RED
instance here, cheaply, instead of at final engine assembly.

CONVENTIONS (A4 §3, matching FrameProbe): ω=2, ω²=3; Z₆=Z₂×Z₃ via a↦(a%2, a%3);
characters ψ₀=1, ψ₁=ω^{t_y}, ψ₂=ω^{t_x}, ψ₃=ω^{t_x+t_y}, ψ₄=ω^{t_x+2t_y};
Â/B̂ value vectors over (0,0),(1,0),(0,1),(1,1):
  unit 1+u+v = (1,1,1,0)  [Â₀,Â₂,B̂₀,B̂₁]
  u+ωv       = (3,1,2,0)  [Â₁,Â₃]
  u+ω²v      = (2,1,3,0)  [Â₄]
  ωu+v       = (3,2,1,0)  [B̂₂,B̂₃,B̂₄]
Run: `lake env lean experiments/bb_lab/phase6/MultProbe.lean`.
-/
import QEC.Stabilizer.Codes.BivariateBicycle.Defs

open Quantum.Stabilizer.Homological.BB

namespace MultProbe

/-! ## F₄ tables (same model as FrameProbe/EngineProbe). -/
def add : Fin 4 → Fin 4 → Fin 4 :=
  fun a b => (![![0, 1, 2, 3], ![1, 0, 3, 2], ![2, 3, 0, 1], ![3, 2, 1, 0]] a) b
def mul : Fin 4 → Fin 4 → Fin 4 :=
  fun a b => (![![0, 0, 0, 0], ![0, 1, 2, 3], ![0, 2, 3, 1], ![0, 3, 1, 2]] a) b

/-- `ω^k` for `k ∈ Z₃`: `1, ω, ω²` ↦ `1, 2, 3`. -/
def omegaPow (k : ZMod 3) : Fin 4 := if k = 0 then 1 else if k = 1 then 2 else 3

/-! ## CRT coordinates. -/
def layer1 (a : ZMod 6) : ZMod 2 := (a.val : ZMod 2)
def torus1 (a : ZMod 6) : ZMod 3 := (a.val : ZMod 3)
def layer (g : BaseGroup) : ZMod 2 × ZMod 2 := (layer1 g.1, layer1 g.2)

/-! ## The five component characters (A4 §3). -/
def psi0 : BaseGroup → Fin 4 := fun _ => 1
def psi1 : BaseGroup → Fin 4 := fun g => omegaPow (torus1 g.2)
def psi2 : BaseGroup → Fin 4 := fun g => omegaPow (torus1 g.1)
def psi3 : BaseGroup → Fin 4 := fun g => omegaPow (torus1 g.1 + torus1 g.2)
def psi4 : BaseGroup → Fin 4 := fun g => omegaPow (torus1 g.1 + 2 * torus1 g.2)

/-! ## Enumerations. -/
def allG : List BaseGroup :=
  (List.range 6).flatMap (fun a => (List.range 6).map (fun b => ((a : ZMod 6), (b : ZMod 6))))
def allS : List (ZMod 2 × ZMod 2) :=
  (List.range 2).flatMap (fun a => (List.range 2).map (fun b => ((a : ZMod 2), (b : ZMod 2))))

/-- Component transform `V_psi(f)[s] = Σ_{g in layer s, f g = 1} ψ(g)` (sum in F₄). -/
def Vc (psi : BaseGroup → Fin 4) (f : BaseGroup → ZMod 2) (s : ZMod 2 × ZMod 2) : Fin 4 :=
  allG.foldl (fun acc g => if layer g = s ∧ f g = 1 then add acc (psi g) else acc) 0

/-- Group-algebra product in `F₄[Z₂²]`: convolution over `Z₂²`. -/
def conv2 (p q : ZMod 2 × ZMod 2 → Fin 4) (s : ZMod 2 × ZMod 2) : Fin 4 :=
  allS.foldl (fun acc s' => add acc (mul (p s') (q (s - s')))) 0

/-! ## Â/B̂ value vectors (the four distinct ones). -/
/-- `1 + u + v = (1,1,1,0)` (the unit components Â₀,Â₂,B̂₀,B̂₁). -/
def vUnit : ZMod 2 × ZMod 2 → Fin 4 := fun s => if s = (1, 1) then 0 else 1
/-- `u + ωv = (3,1,2,0)` (Â₁,Â₃). -/
def vUwV : ZMod 2 × ZMod 2 → Fin 4 :=
  fun s => if s = (0, 0) then 3 else if s = (1, 0) then 1 else if s = (0, 1) then 2 else 0
/-- `u + ω²v = (2,1,3,0)` (Â₄). -/
def vUw2V : ZMod 2 × ZMod 2 → Fin 4 :=
  fun s => if s = (0, 0) then 2 else if s = (1, 0) then 1 else if s = (0, 1) then 3 else 0
/-- `ωu + v = (3,2,1,0)` (B̂₂,B̂₃,B̂₄). -/
def vWuV : ZMod 2 × ZMod 2 → Fin 4 :=
  fun s => if s = (0, 0) then 3 else if s = (1, 0) then 2 else if s = (0, 1) then 1 else 0

/-! ## Point mass and polynomial-convolution chains. -/
def delta (p : BaseGroup) : BaseGroup → ZMod 2 := fun g => if g = p then 1 else 0
def Aconv (p : BaseGroup) : BaseGroup → ZMod 2 := fun g => baseA (g - p)
def Bconv (p : BaseGroup) : BaseGroup → ZMod 2 := fun g => baseB (g - p)

/-! ## The 10 multiplicativity instances `V_j(P ⋆ δ_p) = P̂_j ⋆ V_j(δ_p)`,
    each native_decide over `p ∈ Z₆²` × layer `s ∈ Z₂²` (144 cases). -/

-- A-block (Â₀=Â₂=unit, Â₁=Â₃=(3,1,2,0), Â₄=(2,1,3,0))
example : ∀ p : BaseGroup, ∀ s, Vc psi0 (Aconv p) s = conv2 vUnit (Vc psi0 (delta p)) s := by native_decide
example : ∀ p : BaseGroup, ∀ s, Vc psi1 (Aconv p) s = conv2 vUwV  (Vc psi1 (delta p)) s := by native_decide
example : ∀ p : BaseGroup, ∀ s, Vc psi2 (Aconv p) s = conv2 vUnit (Vc psi2 (delta p)) s := by native_decide
example : ∀ p : BaseGroup, ∀ s, Vc psi3 (Aconv p) s = conv2 vUwV  (Vc psi3 (delta p)) s := by native_decide
example : ∀ p : BaseGroup, ∀ s, Vc psi4 (Aconv p) s = conv2 vUw2V (Vc psi4 (delta p)) s := by native_decide

-- B-block (B̂₀=B̂₁=unit, B̂₂=B̂₃=B̂₄=(3,2,1,0))
example : ∀ p : BaseGroup, ∀ s, Vc psi0 (Bconv p) s = conv2 vUnit (Vc psi0 (delta p)) s := by native_decide
example : ∀ p : BaseGroup, ∀ s, Vc psi1 (Bconv p) s = conv2 vUnit (Vc psi1 (delta p)) s := by native_decide
example : ∀ p : BaseGroup, ∀ s, Vc psi2 (Bconv p) s = conv2 vWuV  (Vc psi2 (delta p)) s := by native_decide
example : ∀ p : BaseGroup, ∀ s, Vc psi3 (Bconv p) s = conv2 vWuV  (Vc psi3 (delta p)) s := by native_decide
example : ∀ p : BaseGroup, ∀ s, Vc psi4 (Bconv p) s = conv2 vWuV  (Vc psi4 (delta p)) s := by native_decide

end MultProbe
