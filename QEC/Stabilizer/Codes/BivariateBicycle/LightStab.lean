/-
# Light-stabilizer classification (A4 §6.3) — discharging `LightStabilizerClassification`

This module builds toward
`lightStabilizerClassification_holds : LightStabilizerClassification`
(`DangerousSector.lean:528`), the analytic input that makes the dangerous
sector of the gross `[[144,12,12]]` BB code unconditional.

The proof is the CRT-engine classification of A4 §§6.2–6.3, layered as:

  §1  the layer dictionary `d₃` over the torus `Z₃²` (A4 §3 "Layer dictionary"):
      a nonzero `F₂`-function whose `F₄`-valued torus-Fourier support is confined
      to certain Frobenius orbits has a forced minimum weight — `native_decide`
      over the 512 functions.  Entries used downstream (one-block lemma, A4 §6.3):
      `d₃({1}) = d₃({3}) = 6`, `d₃({1,3}) = 4`.

  §2  the base ↔ torus reindex bridge.  The CRT iso `BaseGroup = Z₆² ≅ Z₂² × Z₃²`
      (`g ↦ (layer g, torus g)`) lets the per-layer torus slice of a base chain be
      analysed by the dictionary.  Two bridges connect the abstract `CRTFrame`
      machinery to `§1`:
        - Fourier: `V ψⱼ s b = fhat3 (slice b s) (charⱼ)` (the component transform
          at layer `s` IS the torus-Fourier coefficient of the slice);
        - weight:  `bwt b = Σ_s weight3 (slice b s)` (a block's weight is the sum of
          its layer slice weights).

Subsequent sections (the sharp one-block `≥16` bound L4c, the Floor lemma L4b, the
six per-shape leaves, and the endgame transfers) are added incrementally; nothing
in a tracked file carries a `sorry`.

**Conventions (A4 §3, shared with `CRTFrame`).** `ω = 2`, `ω² = 3` in `Fin 4`;
`Z₆ = Z₂ × Z₃` via `a ↦ (a mod 2, a mod 3)`; torus characters
`ψ₀ = 1` (char `(0,0)`, the parity component `V₀`), `ψ₁ = ω^{t_y}` (`(0,1)`),
`ψ₂ = ω^{t_x}` (`(1,0)`), `ψ₃ = ω^{t_x+t_y}` (`(1,1)`), `ψ₄ = ω^{t_x+2t_y}`
(`(1,2)`).  Each nontrivial char generates a size-2 Frobenius orbit `{c, 2c}`
(since `f` is `F₂`-valued: `f̂(2c) = f̂(c)²`), so checking one representative per
orbit suffices for support confinement.
-/
import QEC.Stabilizer.Codes.BivariateBicycle.CRTFrame

open Quantum.Stabilizer.Homological.BB.CRTFrame

namespace Quantum
namespace Stabilizer
namespace Homological
namespace BB
namespace LightStab

/-! ## §1 The layer dictionary `d₃` over `Z₃²`

For nonzero `f : Z₃² → F₂` whose `F₄`-valued torus-Fourier support is contained in
an orbit set `W`, the Hamming weight is at least `d₃(W)`.  This is the clean finite
core of the one-block lemma (A4 §6.3): there, every layer of a one-block stabilizer
has Fourier support `⊆ {orbit ψ₁, orbit ψ₃}` (the parity, `ψ₂`, `ψ₄` components are
dead), and the dictionary converts that confinement into a per-layer weight floor.

Support confinement is checked at ONE representative per dead orbit (Frobenius makes
this equivalent to checking the whole orbit, for `F₂`-valued `f`); the representatives
are exactly the `CRTFrame` characters `ψ₀..ψ₄`, so `§2`'s Fourier bridge turns each
check into a condition on `V ψⱼ s b`. -/

/-- The 9 torus cells of `Z₃²`. -/
def cells3 : List (ZMod 3 × ZMod 3) :=
  (List.range 3).flatMap (fun a => (List.range 3).map (fun b => ((a : ZMod 3), (b : ZMod 3))))

/-- The torus character value `ω^{a·t_x + b·t_y}` of direction `c = (a,b)` at cell `t`. -/
def tchar (c t : ZMod 3 × ZMod 3) : Fin 4 := omegaPow (c.1 * t.1 + c.2 * t.2)

/-- The `F₄`-valued torus-Fourier coefficient of `f` at character direction
`c = (a, b)`: `Σ_t f(t) · ω^{a·t_x + b·t_y}` (a char-2 `fadd`-fold over the 9
cells; `ω^k = omegaPow k`). -/
def fhat3 (f : ZMod 3 × ZMod 3 → ZMod 2) (c : ZMod 3 × ZMod 3) : Fin 4 :=
  cells3.foldl (fun acc t => if f t = 1 then fadd acc (tchar c t) else acc) 0

/-- Hamming weight of `f` over the 9 torus cells. -/
def weight3 (f : ZMod 3 × ZMod 3 → ZMod 2) : Nat :=
  (cells3.filter (fun t => decide (f t = 1))).length

/-- "Fourier support `⊆ W`": `f̂` vanishes at every (dead-orbit representative)
character in `dead`. -/
def suppOutsideZero (f : ZMod 3 × ZMod 3 → ZMod 2)
    (dead : List (ZMod 3 × ZMod 3)) : Bool :=
  dead.all (fun c => decide (fhat3 f c = 0))

/-! ### Dead-orbit representatives (one char per orbit excluded from `W`). -/

/-- Dead reps for `W = {ψ₁}`: `ψ₀ (0,0)`, `ψ₂ (1,0)`, `ψ₃ (1,1)`, `ψ₄ (1,2)`. -/
def dead1 : List (ZMod 3 × ZMod 3) := [(0, 0), (1, 0), (1, 1), (1, 2)]
/-- Dead reps for `W = {ψ₃}`: `ψ₀ (0,0)`, `ψ₁ (0,1)`, `ψ₂ (1,0)`, `ψ₄ (1,2)`. -/
def dead3 : List (ZMod 3 × ZMod 3) := [(0, 0), (0, 1), (1, 0), (1, 2)]
/-- Dead reps for `W = {ψ₁,ψ₃}`: `ψ₀ (0,0)`, `ψ₂ (1,0)`, `ψ₄ (1,2)`. -/
def dead13 : List (ZMod 3 × ZMod 3) := [(0, 0), (1, 0), (1, 2)]

/-! ### The three dictionary lower bounds (512-function `native_decide`).
These are the exact `d₃`-costs the one-block lemma (A4 §6.3) consumes. -/

/-- `d₃({1}) = 6`: a nonzero `f` with Fourier support `⊆ orbit(ψ₁)` has weight `≥ 6`. -/
theorem d3_psi1_ge6 : ∀ f : ZMod 3 × ZMod 3 → ZMod 2,
    f ≠ 0 → suppOutsideZero f dead1 = true → 6 ≤ weight3 f := by native_decide

/-- `d₃({3}) = 6`: a nonzero `f` with Fourier support `⊆ orbit(ψ₃)` has weight `≥ 6`. -/
theorem d3_psi3_ge6 : ∀ f : ZMod 3 × ZMod 3 → ZMod 2,
    f ≠ 0 → suppOutsideZero f dead3 = true → 6 ≤ weight3 f := by native_decide

/-- `d₃({1,3}) = 4`: a nonzero `f` with Fourier support `⊆ orbit(ψ₁) ∪ orbit(ψ₃)`
has weight `≥ 4`. -/
theorem d3_psi1or3_ge4 : ∀ f : ZMod 3 × ZMod 3 → ZMod 2,
    f ≠ 0 → suppOutsideZero f dead13 = true → 4 ≤ weight3 f := by native_decide

/-! ### Tightness: each bound is attained (guards against a vacuously-true,
over-constrained support predicate). -/

theorem d3_psi1_tight : ∃ f : ZMod 3 × ZMod 3 → ZMod 2,
    f ≠ 0 ∧ suppOutsideZero f dead1 = true ∧ weight3 f = 6 := by native_decide

theorem d3_psi3_tight : ∃ f : ZMod 3 × ZMod 3 → ZMod 2,
    f ≠ 0 ∧ suppOutsideZero f dead3 = true ∧ weight3 f = 6 := by native_decide

theorem d3_psi1or3_tight : ∃ f : ZMod 3 × ZMod 3 → ZMod 2,
    f ≠ 0 ∧ suppOutsideZero f dead13 = true ∧ weight3 f = 4 := by native_decide

/-! ## §2 The base ↔ torus reindex bridge

`BaseGroup = Z₆² ≅ Z₂² × Z₃²` via `g ↦ (layer g, torus g)`; `combineCell` is the
inverse (CRT: `3·s + 4·t (mod 6)` per coordinate).  The layer-`s` torus slice of a
base chain `b` is `slice b s := fun t => b (combineCell s t)`. -/

/-- CRT inverse on one `Z₆` coordinate: the element `≡ s (mod 2)`, `≡ t (mod 3)`. -/
def combine1 (s : ZMod 2) (t : ZMod 3) : ZMod 6 := ((3 * s.val + 4 * t.val : ℕ) : ZMod 6)

/-- CRT inverse `Z₂² × Z₃² → Z₆² = BaseGroup`. -/
def combineCell (s : ZMod 2 × ZMod 2) (t : ZMod 3 × ZMod 3) : BaseGroup :=
  (combine1 s.1 t.1, combine1 s.2 t.2)

/-- The layer-`s` torus slice of a base chain `b`, as a `Z₃² → F₂` function. -/
def slice (b : BaseGroup → ZMod 2) (s : ZMod 2 × ZMod 2) : ZMod 3 × ZMod 3 → ZMod 2 :=
  fun t => b (combineCell s t)

/-! ### Round-trip facts (finite `decide`). -/

theorem layer_combineCell : ∀ (s : ZMod 2 × ZMod 2) (t : ZMod 3 × ZMod 3),
    layer (combineCell s t) = s := by decide
theorem torus_combineCell : ∀ (s : ZMod 2 × ZMod 2) (t : ZMod 3 × ZMod 3),
    torus (combineCell s t) = t := by decide
theorem combineCell_layer_torus : ∀ g : BaseGroup,
    combineCell (layer g) (torus g) = g := by decide
theorem cells3_complete : ∀ t : ZMod 3 × ZMod 3, t ∈ cells3 := by decide

/-! ### `fhat3` is `F₂`-linear (the bridge needs additivity to lift the basis case). -/

/-- `fhat3` is `F₂`-additive in the chain. -/
theorem fhat3_add (f g : ZMod 3 × ZMod 3 → ZMod 2) (c : ZMod 3 × ZMod 3) :
    fhat3 (f + g) c = fadd (fhat3 f c) (fhat3 g c) := by
  have step : ∀ (a b : ZMod 2) (Y W z : Fin 4),
      (if a + b = 1 then fadd (fadd Y W) z else fadd Y W)
        = fadd (if a = 1 then fadd Y z else Y) (if b = 1 then fadd W z else W) := by decide
  have gen : ∀ (L : List (ZMod 3 × ZMod 3)) (aF aG : Fin 4),
      L.foldl (fun acc t => if (f + g) t = 1 then fadd acc (tchar c t) else acc) (fadd aF aG)
        = fadd (L.foldl (fun acc t => if f t = 1 then fadd acc (tchar c t) else acc) aF)
               (L.foldl (fun acc t => if g t = 1 then fadd acc (tchar c t) else acc) aG) := by
    intro L
    induction L with
    | nil => intro aF aG; rfl
    | cons h t ih =>
      intro aF aG
      rw [List.foldl_cons, List.foldl_cons, List.foldl_cons]
      have hhead : (if (f + g) h = 1 then fadd (fadd aF aG) (tchar c h) else fadd aF aG)
          = fadd (if f h = 1 then fadd aF (tchar c h) else aF)
                 (if g h = 1 then fadd aG (tchar c h) else aG) := by
        rw [Pi.add_apply]; exact step (f h) (g h) aF aG _
      rw [hhead]
      exact ih _ _
  have h00 : fadd (0 : Fin 4) 0 = 0 := by decide
  have := gen cells3 0 0
  rw [h00] at this
  simpa [fhat3] using this

theorem fhat3_zero (c : ZMod 3 × ZMod 3) : fhat3 (0 : ZMod 3 × ZMod 3 → ZMod 2) c = 0 := by
  have h := fhat3_add 0 0 c
  rw [add_zero] at h
  exact (fadd_self (fhat3 0 c) ▸ h)

theorem slice_zero (s : ZMod 2 × ZMod 2) : slice (0 : BaseGroup → ZMod 2) s = 0 := by
  funext t; rfl

theorem slice_add (a b : BaseGroup → ZMod 2) (s : ZMod 2 × ZMod 2) :
    slice (a + b) s = slice a s + slice b s := by
  funext t; rfl

/-! ### The Fourier bridge `V ψⱼ s b = fhat3 (slice b s) (charⱼ)`.
Both sides are `F₂`-additive in `b` and agree on every `δ_g` (native_decide over the
36 `g × 4 s`), hence agree for all `b`. -/

/-- Two `F₂`-additive maps `(BaseGroup → ZMod 2) → Fin 4` that agree on every `δ_g`
agree everywhere. -/
theorem fourier_bridge_gen (M N : (BaseGroup → ZMod 2) → Fin 4)
    (hM0 : M 0 = 0) (hN0 : N 0 = 0)
    (hMadd : ∀ a b, M (a + b) = fadd (M a) (M b))
    (hNadd : ∀ a b, N (a + b) = fadd (N a) (N b))
    (hbasis : ∀ g, M (Pi.single g 1) = N (Pi.single g 1)) (b : BaseGroup → ZMod 2) :
    M b = N b := by
  have key : ∀ S : Finset BaseGroup, M (ind S) = N (ind S) := by
    intro S
    induction S using Finset.induction with
    | empty => rw [ind_empty, hM0, hN0]
    | @insert p S hp ih => rw [ind_insert hp, hMadd, hNadd, hbasis p, ih]
  rw [self_eq_ind_filter b]
  exact key _

theorem Nadd (s : ZMod 2 × ZMod 2) (c : ZMod 3 × ZMod 3) (a b : BaseGroup → ZMod 2) :
    fhat3 (slice (a + b) s) c = fadd (fhat3 (slice a s) c) (fhat3 (slice b s) c) := by
  rw [slice_add]; exact fhat3_add _ _ _

theorem Nzero (s : ZMod 2 × ZMod 2) (c : ZMod 3 × ZMod 3) :
    fhat3 (slice (0 : BaseGroup → ZMod 2) s) c = 0 := by rw [slice_zero, fhat3_zero]

theorem basis_agree0 : ∀ (g : BaseGroup) (s : ZMod 2 × ZMod 2),
    V psi0 s (Pi.single g 1) = fhat3 (slice (Pi.single g 1) s) (0, 0) := by native_decide
theorem basis_agree1 : ∀ (g : BaseGroup) (s : ZMod 2 × ZMod 2),
    V psi1 s (Pi.single g 1) = fhat3 (slice (Pi.single g 1) s) (0, 1) := by native_decide
theorem basis_agree2 : ∀ (g : BaseGroup) (s : ZMod 2 × ZMod 2),
    V psi2 s (Pi.single g 1) = fhat3 (slice (Pi.single g 1) s) (1, 0) := by native_decide
theorem basis_agree3 : ∀ (g : BaseGroup) (s : ZMod 2 × ZMod 2),
    V psi3 s (Pi.single g 1) = fhat3 (slice (Pi.single g 1) s) (1, 1) := by native_decide
theorem basis_agree4 : ∀ (g : BaseGroup) (s : ZMod 2 × ZMod 2),
    V psi4 s (Pi.single g 1) = fhat3 (slice (Pi.single g 1) s) (1, 2) := by native_decide

/-- Fourier bridge, `ψ₀` (parity). -/
theorem fourier_bridge0 (b : BaseGroup → ZMod 2) (s : ZMod 2 × ZMod 2) :
    V psi0 s b = fhat3 (slice b s) (0, 0) :=
  fourier_bridge_gen (V psi0 s) (fun b => fhat3 (slice b s) (0, 0))
    (V_zero psi0 s) (Nzero s (0,0)) (V_add psi0 s) (Nadd s (0,0)) (fun g => basis_agree0 g s) b
/-- Fourier bridge, `ψ₁`. -/
theorem fourier_bridge1 (b : BaseGroup → ZMod 2) (s : ZMod 2 × ZMod 2) :
    V psi1 s b = fhat3 (slice b s) (0, 1) :=
  fourier_bridge_gen (V psi1 s) (fun b => fhat3 (slice b s) (0, 1))
    (V_zero psi1 s) (Nzero s (0,1)) (V_add psi1 s) (Nadd s (0,1)) (fun g => basis_agree1 g s) b
/-- Fourier bridge, `ψ₂`. -/
theorem fourier_bridge2 (b : BaseGroup → ZMod 2) (s : ZMod 2 × ZMod 2) :
    V psi2 s b = fhat3 (slice b s) (1, 0) :=
  fourier_bridge_gen (V psi2 s) (fun b => fhat3 (slice b s) (1, 0))
    (V_zero psi2 s) (Nzero s (1,0)) (V_add psi2 s) (Nadd s (1,0)) (fun g => basis_agree2 g s) b
/-- Fourier bridge, `ψ₃`. -/
theorem fourier_bridge3 (b : BaseGroup → ZMod 2) (s : ZMod 2 × ZMod 2) :
    V psi3 s b = fhat3 (slice b s) (1, 1) :=
  fourier_bridge_gen (V psi3 s) (fun b => fhat3 (slice b s) (1, 1))
    (V_zero psi3 s) (Nzero s (1,1)) (V_add psi3 s) (Nadd s (1,1)) (fun g => basis_agree3 g s) b
/-- Fourier bridge, `ψ₄`. -/
theorem fourier_bridge4 (b : BaseGroup → ZMod 2) (s : ZMod 2 × ZMod 2) :
    V psi4 s b = fhat3 (slice b s) (1, 2) :=
  fourier_bridge_gen (V psi4 s) (fun b => fhat3 (slice b s) (1, 2))
    (V_zero psi4 s) (Nzero s (1,2)) (V_add psi4 s) (Nadd s (1,2)) (fun g => basis_agree4 g s) b

/-! ### The weight bridge `bwt b = Σ_s weight3 (slice b s)`. -/

/-- List weight `weight3` equals the `Finset.card` of the support. -/
theorem weight3_eq_card (f : ZMod 3 × ZMod 3 → ZMod 2) :
    weight3 f = (Finset.univ.filter (fun t => f t = 1)).card := by
  have hnd : cells3.Nodup := by decide
  unfold weight3
  rw [← List.toFinset_card_of_nodup (hnd.filter _)]
  congr 1
  ext t
  simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq, Finset.mem_filter,
    Finset.mem_univ, true_and, and_iff_right_iff_imp]
  intro _; exact cells3_complete t

/-- The CRT equivalence `BaseGroup ≃ Z₂² × Z₃²`, `g ↦ (layer g, torus g)`. -/
def baseEquiv : BaseGroup ≃ (ZMod 2 × ZMod 2) × (ZMod 3 × ZMod 3) where
  toFun g := (layer g, torus g)
  invFun st := combineCell st.1 st.2
  left_inv g := combineCell_layer_torus g
  right_inv st := by
    obtain ⟨s, t⟩ := st
    have h1 := layer_combineCell s t
    have h2 := torus_combineCell s t
    simp only [Prod.mk.injEq]
    exact ⟨h1, h2⟩

/-- The base weight of a block `b`, as a `Finset.card`. -/
def bwt (b : BaseGroup → ZMod 2) : Nat := (Finset.univ.filter (fun h => b h = 1)).card

/-- **The weight bridge**: a block's weight is the sum over layers of its torus slice
weights. -/
theorem weight_bridge (b : BaseGroup → ZMod 2) :
    bwt b = ∑ s : ZMod 2 × ZMod 2, weight3 (slice b s) := by
  unfold bwt
  simp only [weight3_eq_card, Finset.card_filter]
  rw [← Equiv.sum_comp baseEquiv.symm (fun h => if b h = 1 then 1 else 0)]
  rw [Fintype.sum_prod_type]
  rfl

end LightStab
end BB
end Homological
end Stabilizer
end Quantum
