/-
# Phase 6 — M2 probe: CRT-frame multiplicativity on the basis (DRAFT)

The single load-bearing CRT-frame identity (A4 §3, lines 141-142) is

    V_j(A · z) = Â_j · ẑ_j          (product in F₄[Z₂²])

today machine-checked only on 200 random `z`. Since both sides are F₂-linear in
`z`, it holds for all `z` iff it holds on the 36 point-mass basis chains `δ_p`
(`p ∈ Z₆²`). This probe checks exactly that for component `j = 1`, by `native_decide`
over `p ∈ Z₆²` and layer `s ∈ Z₂²` (36 × 4 = 144 cases) — converting the identity
from "claimed reducible to a finite check" into "demonstrated".

Everything is built on explicit `List.foldl`s with the F₄ tables (no typeclass
instances), so it is fully computable / `native_decide`-able.

CONVENTIONS (A4 §3): Z₆ = Z₂ × Z₃ via `a ↦ (a mod 2, a mod 3)` (s_x = x³, t_x = x⁴);
`ω = 2`, `ω² = 3` in the `Fin 4` model (matching `phase6/Probe.lean`); `ψ₁ = ω^{t_y}`;
`Â₁ = u + ω v` with `u = 1+s_x`, `v = 1+s_y`, i.e. over `(0,0),(1,0),(0,1),(1,1)`
the F₄ vector `(1+ω, 1, ω, 0) = (3, 1, 2, 0)`. If the probe FAILS, the likely culprits
(in order) are: the repo-left=lab-right block flip (try B̂₁ / swap x↔y), `ω` vs `ω²`
in `ψ`, or the layer/torus orientation — the probe is precisely the tool to pin these.
Run: `lake env lean experiments/bb_lab/phase6/FrameProbe.lean`.
-/

import QEC.Stabilizer.Codes.BivariateBicycle.Defs

open Quantum.Stabilizer.Homological.BB

namespace FrameProbe

/-! ## F₄ as `Fin 4` (0, 1, ω, ω²) ↦ (0, 1, 2, 3), char-2 add + F₄ mult tables. -/
def add : Fin 4 → Fin 4 → Fin 4 :=
  fun a b => (![![0, 1, 2, 3], ![1, 0, 3, 2], ![2, 3, 0, 1], ![3, 2, 1, 0]] a) b
def mul : Fin 4 → Fin 4 → Fin 4 :=
  fun a b => (![![0, 0, 0, 0], ![0, 1, 2, 3], ![0, 2, 3, 1], ![0, 3, 1, 2]] a) b

/-- `ω^k` for `k ∈ Z₃`: `1, ω, ω²` ↦ `1, 2, 3`. -/
def omegaPow (k : ZMod 3) : Fin 4 := if k = 0 then 1 else if k = 1 then 2 else 3

/-! ## CRT coordinates on `Z₆`: layer (mod 2) and torus (mod 3). -/
def layer1 (a : ZMod 6) : ZMod 2 := (a.val : ZMod 2)
def torus1 (a : ZMod 6) : ZMod 3 := (a.val : ZMod 3)

/-- Layer `s ∈ Z₂²` of a base cell. -/
def layer (g : BaseGroup) : ZMod 2 × ZMod 2 := (layer1 g.1, layer1 g.2)

/-- Component-1 character `ψ₁(g) = ω^{t_y}`. -/
def psi1 (g : BaseGroup) : Fin 4 := omegaPow (torus1 g.2)

/-! ## Enumerations (explicit lists ⇒ no `Finset`/instance machinery). -/
def allG : List BaseGroup :=
  (List.range 6).flatMap (fun a => (List.range 6).map (fun b => ((a : ZMod 6), (b : ZMod 6))))
def allS : List (ZMod 2 × ZMod 2) :=
  (List.range 2).flatMap (fun a => (List.range 2).map (fun b => ((a : ZMod 2), (b : ZMod 2))))

/-- Component-1 transform `V₁(f)[s] = Σ_{g in layer s, f g = 1} ψ₁(g)` (sum in F₄). -/
def V1 (f : BaseGroup → ZMod 2) (s : ZMod 2 × ZMod 2) : Fin 4 :=
  allG.foldl (fun acc g => if layer g = s ∧ f g = 1 then add acc (psi1 g) else acc) 0

/-- `Â₁ = u + ω v ∈ F₄[Z₂²]`, as the vector `(3, 1, 2, 0)` over `(0,0),(1,0),(0,1),(1,1)`. -/
def Ahat1 (s : ZMod 2 × ZMod 2) : Fin 4 :=
  if s = (0, 0) then 3 else if s = (1, 0) then 1 else if s = (0, 1) then 2 else 0

/-- Group-algebra product in `F₄[Z₂²]`: convolution over `Z₂²`. -/
def conv2 (p q : ZMod 2 × ZMod 2 → Fin 4) (s : ZMod 2 × ZMod 2) : Fin 4 :=
  allS.foldl (fun acc s' => add acc (mul (p s') (q (s - s')))) 0

/-- Point mass `δ_p`. -/
def delta (p : BaseGroup) : BaseGroup → ZMod 2 := fun g => if g = p then 1 else 0

/-- `(baseA ⋆ δ_p)(g) = baseA (g - p)` (convolution with a point mass = translate). -/
def Aconv (p : BaseGroup) : BaseGroup → ZMod 2 := fun g => baseA (g - p)

/-- **M2 probe**: multiplicativity `V₁(A·δ_p) = Â₁ · V₁(δ_p)` on every basis chain
`δ_p` and every layer `s` (36 × 4 = 144 cases). -/
example : ∀ p : BaseGroup, ∀ s : ZMod 2 × ZMod 2,
    V1 (Aconv p) s = conv2 Ahat1 (V1 (delta p)) s := by native_decide

end FrameProbe
