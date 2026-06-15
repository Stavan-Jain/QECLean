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

/-! ## §6 The component transform `V` and its F₂-linearity (M2 bridge).

`V psi s f = Σ_{h : layer h = s, f h = 1} psi h` (sum in F₄).  The load-bearing
fact for the multiplicativity engine is that `V` is **F₂-linear in the chain**
`f` (`V_add`), proved from a generic char-2 fold-splitting lemma (`foldl_char2`,
whose only arithmetic content is one `decide` over the 256 `Bool²×Fin 4³`
accumulator cases).  This is what lifts the basis-chain multiplicativity
(M2-(A): `V_j(baseP⋆δ_p) = P̂_j·V_j(δ_p)`, native_decide on the 36 `δ_p`, all 10
(j,P) instances GREEN in `phase6/MultProbe.lean`) to all chains `z`.  The five
component characters are the A4 §3 frame characters. -/

/-- Enumeration of the base group (36 cells). -/
def allG : List BaseGroup :=
  (List.range 6).flatMap (fun a => (List.range 6).map (fun b => ((a : ZMod 6), (b : ZMod 6))))

/-- Component characters (A4 §3): ψ₀=1, ψ₁=ω^{t_y}, ψ₂=ω^{t_x},
ψ₃=ω^{t_x+t_y}, ψ₄=ω^{t_x+2t_y}. -/
def psi0 : BaseGroup → Fin 4 := fun _ => 1
def psi1 : BaseGroup → Fin 4 := fun g => omegaPow (torus1 g.2)
def psi2 : BaseGroup → Fin 4 := fun g => omegaPow (torus1 g.1)
def psi3 : BaseGroup → Fin 4 := fun g => omegaPow (torus1 g.1 + torus1 g.2)
def psi4 : BaseGroup → Fin 4 := fun g => omegaPow (torus1 g.1 + 2 * torus1 g.2)

/-- Generic char-2 transform: `fadd`-fold of `b` over the cells where `P` holds. -/
def fsum (b : BaseGroup → Fin 4) (P : BaseGroup → Bool) : Fin 4 :=
  allG.foldl (fun acc h => if P h then fadd acc (b h) else acc) 0

/-- **The char-2 fold splits over an XOR predicate** (generic over any list /
predicates; the Fin-4 accumulator step is one `decide` over all 256
`Bool²×Fin 4³` cases). -/
theorem foldl_char2 (b : BaseGroup → Fin 4) (Pf Pg : BaseGroup → Bool) :
    ∀ (L : List BaseGroup) (aF aG : Fin 4),
      fadd (L.foldl (fun acc h => if Pf h then fadd acc (b h) else acc) aF)
           (L.foldl (fun acc h => if Pg h then fadd acc (b h) else acc) aG)
      = L.foldl (fun acc h => if (Pf h != Pg h) then fadd acc (b h) else acc)
          (fadd aF aG) := by
  have accStep : ∀ (p q : Bool) (x y z : Fin 4),
      fadd (if p then fadd x z else x) (if q then fadd y z else y)
        = if (p != q) then fadd (fadd x y) z else fadd x y := by decide
  intro L
  induction L with
  | nil => intro aF aG; rfl
  | cons h t ih =>
    intro aF aG
    simp only [List.foldl_cons]
    rw [ih, accStep (Pf h) (Pg h) aF aG (b h)]

/-- `fsum` is F₂-additive on predicates: XOR of predicates adds the sums. -/
theorem fsum_xor (b : BaseGroup → Fin 4) (Pf Pg : BaseGroup → Bool) :
    fadd (fsum b Pf) (fsum b Pg) = fsum b (fun h => Pf h != Pg h) := by
  have h := foldl_char2 b Pf Pg allG 0 0
  simpa [fsum] using h

/-- The CRT component transform at layer `s`:
`V psi s f = Σ_{h : layer h = s, f h = 1} psi h` (sum in F₄). -/
def V (psi : BaseGroup → Fin 4) (s : ZMod 2 × ZMod 2) (f : BaseGroup → ZMod 2) : Fin 4 :=
  fsum psi (fun h => decide (layer h = s) && decide (f h = 1))

/-- **The F₂-linearity bridge (M2-(B)): `V` is additive in the chain.**  This is
the load-bearing step that lifts the basis-chain multiplicativity (M2-(A),
native_decide on the 36 `δ_p`) to all chains `z`; it is the piece with no
mathlib analogue (F₄ is `Fin 4`+tables, so there is no `AddCommMonoid` to borrow
`Finset.sum` additivity from — hence the hand-rolled char-2 `foldl_char2`). -/
theorem V_add (psi : BaseGroup → Fin 4) (s : ZMod 2 × ZMod 2)
    (f g : BaseGroup → ZMod 2) :
    V psi s (f + g) = fadd (V psi s f) (V psi s g) := by
  have hz : ∀ a b : ZMod 2, decide (a + b = 1) = (decide (a = 1) != decide (b = 1)) := by decide
  have hb : ∀ L F G : Bool, (L && (F != G)) = ((L && F) != (L && G)) := by decide
  unfold V
  rw [fsum_xor]
  congr 1
  funext h
  rw [Pi.add_apply, hz, hb]

end CRTFrame
end BB
end Homological
end Stabilizer
end Quantum
