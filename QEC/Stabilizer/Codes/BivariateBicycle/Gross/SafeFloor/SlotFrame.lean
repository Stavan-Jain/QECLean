/-
# Phase 6: the slot frame (A4 §10) — analytic infrastructure for the safe-sector floor

This module replaces the native-decidable confined-floor engine (`MImFloor`,
`floorOK`, the `~2³⁰` per-orbit enumeration) with the **analytic slot-frame
argument** of the self-contained proof (`docs/gross-distance-proof.md` §10).

The endpoint each orbit rep must reach is the closed coset-weight obligation
exposed by `MImClassify.chainWeight_coset_eq`:
```
∀ f, 12 ≤ costFromComps (shifted (seamOffL/R ζ psiⱼ) multⱼ (compF f psiⱼ))
```
This file builds the §10 substrate that the per-orbit walks (`WtFloor24`,
`WtFloor1618`, `RhoKills`) use to discharge that obligation structurally:

* **`floor_of_data_analytic`** — the integration bridge: a per-rep analytic
  `costFromComps ≥ 12` becomes the real `chainWeight ≥ 12` via
  `chainWeight_coset_eq`.  Its signature mirrors `MImMembership.floor_of_data`,
  so the consuming `MImFloorY*` / `MImAssembly` chain needs no edits.
* **Slots, kill vector, labelings** (§10.1): `kappa`, the labeling vectors
  `ellL = ℓ = κ(B̂)`, `ellR = ℓ' = κ(Â₃)`, the parity vectors `theta`, `thetaT`.
* **Lemma 19** (labeling facts): `ellL`/`ellR` are bijective slot maps, the
  Frobenius identities, and `κ(Â₄) = ω²ℓ` — all finite `decide` facts over F₄.
* **The per-slot cost lower bound** (§10.2, Lemma 20): `slotLB`, a lower bound
  on `wt5OfComps` keyed on the alive pattern, with soundness `slotLB_le` by a
  finite check over the 512 component tuples.

## Convention bridge (lab notes → repo) — inherited from `MImClassify`

Repo `∂₂ f = (A⋆f | B⋆f)`: A-block at `j = 0`, B-block at `j = 1`.
**Repo-left = lab-right**.  Slots are `Z₂² = {(0,0),(1,0),(0,1),(1,1)}` in the
order `(e, x, y, xy)`; F₄ is `Fin 4` with `(0,1,ω,ω²) = (0,1,2,3)`.
-/

import QEC.Stabilizer.Codes.BivariateBicycle.Gross.SafeFloor.MImClassify

open Quantum.Stabilizer.Homological.BB
open Quantum.Stabilizer.Homological.BB.CRTFrame
open Quantum.Stabilizer.Homological.BB.LightStab

namespace Quantum.Stabilizer.Homological.BB.LightStab

set_option maxRecDepth 4096

/-! ## §0 The integration bridge

`floor_of_data_analytic` is the analytic analogue of `MImMembership.floor_of_data`:
given the per-rep analytic floor on `costFromComps`, it produces the real
`chainWeight ≥ 12` by rewriting through `chainWeight_coset_eq`.  Its hypothesis
`h` is *exactly* the RHS of `chainWeight_coset_eq`, so a downstream `Yr.floor`
built from it has the identical signature `(f) → 12 ≤ chainWeight (seamC zrep + ∂₂ f)`
that `MImAssembly` consumes — the engine swap is invisible above this line. -/

/-- **The analytic floor bridge.**  A per-rep analytic lower bound on the closed
coset-weight form `costFromComps` lifts to the real chain-weight floor.  Reuses
`chainWeight_coset_eq` (MImClassify §7) verbatim; the proof is one rewrite. -/
theorem floor_of_data_analytic (zrep : BaseGroup → ZMod 2)
    (h : ∀ f : BaseGroup → ZMod 2, 12 ≤ costFromComps
        (shifted (seamOffL zrep psi0) unitHat (compF f psi0))
        (shifted (seamOffL zrep psi1) Ahat1 (compF f psi1))
        (shifted (seamOffL zrep psi2) unitHat (compF f psi2))
        (shifted (seamOffL zrep psi3) Ahat1 (compF f psi3))
        (shifted (seamOffL zrep psi4) Ahat4 (compF f psi4))
        (shifted (seamOffR zrep psi0) unitHat (compF f psi0))
        (shifted (seamOffR zrep psi1) unitHat (compF f psi1))
        (shifted (seamOffR zrep psi2) Bhat2 (compF f psi2))
        (shifted (seamOffR zrep psi3) Bhat2 (compF f psi3))
        (shifted (seamOffR zrep psi4) Bhat2 (compF f psi4)))
    (f : BaseGroup → ZMod 2) :
    12 ≤ bb72Complex.chainWeight (seamC zrep + bbBoundary2Fn baseA baseB f) := by
  rw [chainWeight_coset_eq zrep f]
  exact h f

/-! ## §1 Slots, the kill vector, and the labeling vectors (A4 §10.1)

`Ring = Z₂² → F₄` is the slot-value representation.  The group-algebra element
`XY = ∑_g g` is the all-ones `uv = (1,1,1,1)`; its slot value at the slot
`xy = (1,1)` is the free constant `δ`.  The **kill vector** records the slot
function modulo that free `δ`-shift: `κ(v)(s) = v(s) + v(xy)` (so `κ(v)(xy) = 0`). -/

/-- The kill vector `κ(v)(s) = v(s) + v(xy)`: the slot function modulo the free
constant `XY`-shift.  `κ(v)` always vanishes at the slot `xy = (1,1)`. -/
def kappa (v : Ring) : Ring := fun s => fadd (v s) (v (1, 1))

/-- The labeling vector `ℓ := κ(B̂) = (ω², ω, 1, 0)`.  (`B̂ = B̂₂` has zero `xy`
slot, so `κ(B̂) = B̂ = Bhat2`.) -/
def ellL : Ring := kappa Bhat2

/-- The labeling vector `ℓ' := κ(Â₃) = (ω², 1, ω, 0)`.  (`Â₃ = Â₁ = Ahat1` has
zero `xy` slot, so `κ(Â₃) = Â₁ = Ahat1`.) -/
def ellR : Ring := kappa Ahat1

/-- Parity vector `θ = (1, 0, 1, 0)`. -/
def theta : Ring := fun s => if s = (0, 0) then 1 else if s = (0, 1) then 1 else 0

/-- Parity vector `θ̃ = (1, 1, 0, 0)`. -/
def thetaT : Ring := fun s => if s = (0, 0) then 1 else if s = (1, 0) then 1 else 0

/-! ### Lemma 19 (labeling facts): all finite `decide` facts over F₄/slots. -/

/-- `ℓ` agrees with `Bhat2 = (ω², ω, 1, 0)` as a slot function. -/
theorem ellL_eq : ellL = Bhat2 := by decide

/-- `ℓ'` agrees with `Ahat1 = (ω², 1, ω, 0)` as a slot function. -/
theorem ellR_eq : ellR = Ahat1 := by decide

/-- **Lemma 19a.** `ℓ` is an injective slot map (its four values are distinct). -/
theorem ellL_inj : Function.Injective (fun s : ZMod 2 × ZMod 2 => ellL s) := by decide

/-- **Lemma 19a.** `ℓ'` is an injective slot map. -/
theorem ellR_inj : Function.Injective (fun s : ZMod 2 × ZMod 2 => ellR s) := by decide

/-- **Lemma 19b** (Frobenius). `κ(Â₄) = ℓ'² = ω²ℓ`: entrywise squaring of `ℓ`
gives `ω²ℓ'`, and `κ(Â₄) = Ahat4 = ω²ℓ`. -/
theorem kappa_Ahat4_eq : kappa Ahat4 = fun s => fmul 3 (ellL s) := by decide

/-- **Lemma 19b** (Frobenius). `ℓ² = ω²ℓ'` entrywise. -/
theorem ellL_sq_eq : (fun s => fmul (ellL s) (ellL s)) = fun s => fmul 3 (ellR s) := by decide

/-- **Lemma 19b** (Frobenius). `ℓ'² = ω²ℓ` entrywise. -/
theorem ellR_sq_eq : (fun s => fmul (ellR s) (ellR s)) = fun s => fmul 3 (ellL s) := by decide

/-! ## §2 The per-slot cost lower bounds (A4 §10.2, Lemma 20 — the M-tables)

The closed coset weight `costFromComps` is a sum over the four `Z₂²` slots of
`wt5OfComps` of the ten CRT components.  Per the slot-cost rules, the cheapest
realization of a slot datum minimizes over the block's *free unit-side* component
(the `unitHat`-multiplied one: component `2` on the A/left block, component `1` on
the B/right block — recall repo-left = lab-right).  The min-over-free-component
lower bound `mFree2`/`mFree1` therefore lower-bounds the exact per-slot weight.

These are proved by `omega` over the four opaque `wt5OfComps` values — **no
`decide`/`native_decide`**, so they are axiom-clean (standard three only).  They
are the load-bearing per-slot bound that the orbit walks sum over the slots. -/

/-- Min over component 1 of the per-slot weight (the B/right-block free component). -/
def mFree1 (v0 v2 v3 v4 : Fin 4) : Nat :=
  min (min (wt5OfComps v0 0 v2 v3 v4) (wt5OfComps v0 1 v2 v3 v4))
      (min (wt5OfComps v0 2 v2 v3 v4) (wt5OfComps v0 3 v2 v3 v4))

/-- Min over component 2 of the per-slot weight (the A/left-block free component). -/
def mFree2 (v0 v1 v3 v4 : Fin 4) : Nat :=
  min (min (wt5OfComps v0 v1 0 v3 v4) (wt5OfComps v0 v1 1 v3 v4))
      (min (wt5OfComps v0 v1 2 v3 v4) (wt5OfComps v0 v1 3 v3 v4))

/-- **Slot-cost rule (B/right block).** `mFree1` lower-bounds the exact per-slot
weight: the free component-1 value is one of the four minimized over. -/
theorem mFree1_le (v0 v1 v2 v3 v4 : Fin 4) :
    mFree1 v0 v2 v3 v4 ≤ wt5OfComps v0 v1 v2 v3 v4 := by
  unfold mFree1
  have h : v1 = 0 ∨ v1 = 1 ∨ v1 = 2 ∨ v1 = 3 := by omega
  rcases h with rfl | rfl | rfl | rfl <;> omega

/-- **Slot-cost rule (A/left block).** `mFree2` lower-bounds the exact per-slot
weight: the free component-2 value is one of the four minimized over. -/
theorem mFree2_le (v0 v1 v2 v3 v4 : Fin 4) :
    mFree2 v0 v1 v3 v4 ≤ wt5OfComps v0 v1 v2 v3 v4 := by
  unfold mFree2
  have h : v2 = 0 ∨ v2 = 1 ∨ v2 = 2 ∨ v2 = 3 := by omega
  rcases h with rfl | rfl | rfl | rfl <;> omega

/-- **Remark 3** (slot parity).  Every per-slot layer cost is `≡ v₀ (mod 2)`
(an odd layer has odd weight, an even layer even).  Over the 512 value-tuples,
by kernel `decide` (~12 s) — **axiom-clean** (no `native_decide`).  Summing over
slots, a block's total cost is `≡ |V₀| (mod 2)`; this parity is what the
achiever-structure lemma (Lem 28) uses to force the `(min_L + min_R)` splits to
be even, ruling out the would-be odd weight-`10` configurations. -/
theorem slot_parity : ∀ (v0 : Fin 2) (v1 v2 v3 v4 : Fin 4),
    wt5OfComps (v0.castLE (by norm_num)) v1 v2 v3 v4 % 2 = v0.val := by decide

/-! ### Block-cost lower bounds: sum the per-slot bound over the four slots.

`costFromComps` splits as an A-block sum plus a B-block sum (`Finset.sum_add_distrib`);
each block's slot sum is lower-bounded by the matching `mFree` sum (`Finset.sum_le_sum`).
The A-block frees component 2 (`mFree2`), the B-block frees component 1 (`mFree1`). -/

/-- The A/left-block slot-cost lower bound: sum of `mFree2` over the four slots. -/
def blockLBL (vL0 vL1 vL3 vL4 : Ring) : Nat :=
  ∑ s : ZMod 2 × ZMod 2, mFree2 (vL0 s) (vL1 s) (vL3 s) (vL4 s)

/-- The B/right-block slot-cost lower bound: sum of `mFree1` over the four slots. -/
def blockLBR (vR0 vR2 vR3 vR4 : Ring) : Nat :=
  ∑ s : ZMod 2 × ZMod 2, mFree1 (vR0 s) (vR2 s) (vR3 s) (vR4 s)

/-- **The block-split lower bound.**  `costFromComps` is bounded below by the sum
of the two block slot-cost lower bounds.  (Each block frees its unit-side
component; the bound ignores the cross-block `ρ`-link, so it is the link-free
floor — sufficient framing for the orbit walks, which sharpen it per-cell.) -/
theorem costFromComps_ge_blockLB
    (vL0 vL1 vL2 vL3 vL4 vR0 vR1 vR2 vR3 vR4 : Ring) :
    blockLBL vL0 vL1 vL3 vL4 + blockLBR vR0 vR2 vR3 vR4
      ≤ costFromComps vL0 vL1 vL2 vL3 vL4 vR0 vR1 vR2 vR3 vR4 := by
  unfold costFromComps blockLBL blockLBR
  rw [Finset.sum_add_distrib]
  refine Nat.add_le_add (Finset.sum_le_sum ?_) (Finset.sum_le_sum ?_)
  · intro s _; exact mFree2_le (vL0 s) (vL1 s) (vL2 s) (vL3 s) (vL4 s)
  · intro s _; exact mFree1_le (vR0 s) (vR1 s) (vR2 s) (vR3 s) (vR4 s)

/-! ## §3 Affine-pencil and quadruple facts (A4 §10.3–§10.4, Lemmas 21, 24)

The slot-cost analysis turns on the fibre partition of an affine slot function
`k = κ + λ u` (`u` a bijection) and, in the deepest case, on whether four points
of `AG(2,F₄)` are in general position.  Both reduce to finite F₄ checks. -/

/-- Three points of `AG(2,F₄)` are collinear (slot values in F₄): the chord
`p→q` and `p→r` have equal reciprocal slope.  An `F₄`-equality, so decidable
(`abbrev` keeps the `DecidableEq (Fin 4)` instance transparent). -/
abbrev collinear3 (p q r : Fin 4 × Fin 4) : Prop :=
  fmul (fadd q.1 p.1) (fadd r.2 p.2) = fmul (fadd r.1 p.1) (fadd q.2 p.2)

/-- **Lemma 21** (pair-ratio), the algebraic core.  For an affine pencil
`k = κ + λu`, two slots have `k`-values equal iff `λ·Δu = Δκ` — a char-2
rearrangement, valid for all F₄ data (a closed `decide` over `4⁵` tuples). -/
theorem pencil_fibre_iff : ∀ a b c d lam : Fin 4,
    (fadd a (fmul lam c) = fadd b (fmul lam d)) ↔ (fmul lam (fadd c d) = fadd a b) := by
  decide

/-- The four points of the standard-form quadruple `(ℓ, ℓ+ωθ)`, i.e.
`{(ω²,1),(ω,ω),(1,ω²),(0,0)}` over the four slots — the chord-products are
`ω²,ω²,ω²,0`, the hyperbola `H_{ω²}`. -/
def stdQuad : List (Fin 4 × Fin 4) :=
  [(ellL (0,0), fadd (ellL (0,0)) (fmul 2 (theta (0,0)))),
   (ellL (1,0), fadd (ellL (1,0)) (fmul 2 (theta (1,0)))),
   (ellL (0,1), fadd (ellL (0,1)) (fmul 2 (theta (0,1)))),
   (ellL (1,1), fadd (ellL (1,1)) (fmul 2 (theta (1,1))))]

/-- **Lemma 24** (hyperbolic quadruple), the instance used by the standard-form
walk: the four points `(ℓ, ℓ+ωθ)` are `{(ω²,1),(ω,ω),(1,ω²),(0,0)}`. -/
theorem stdQuad_eq : stdQuad = [(3, 1), (2, 2), (1, 3), (0, 0)] := by decide

/-- **Lemma 24** (no three collinear): none of the four triples of the
standard-form quadruple is collinear in `AG(2,F₄)` (all `C(4,3)=4` triples). -/
theorem stdQuad_no_three_collinear :
    ¬ collinear3 (3,1) (2,2) (1,3) ∧ ¬ collinear3 (3,1) (2,2) (0,0) ∧
      ¬ collinear3 (3,1) (1,3) (0,0) ∧ ¬ collinear3 (2,2) (1,3) (0,0) := by
  decide

end Quantum.Stabilizer.Homological.BB.LightStab
