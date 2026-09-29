/-
# Gross ↔ bb72 cover-transfer maps

Instantiates the generic double-cover machinery (`BBCover.lean`) on the 2:1
cover `coverPi : Z₁₂ × Z₆ →+ Z₆ × Z₆`:

* `coverPush0/1` — pushforward `p` (fiber summation) on 0- and 1-chains
* `coverPull0/1` — pullback `τ = · ∘ π` on 0- and 1-chains
* both are chain maps between `grossComplex` and `bb72Complex`
* `coverPush1 ∘ coverPull1 = 0`, `coverPull1` injective, `coverPush1`
  surjective, `ker coverPush1 = range coverPull1`
* `coverPull1_coverPush1 : τ(p(v)) = v + σv` (how the deck homotopy (R)
  enters the Phase-1 distance assembly)
* the weight identity `chainWeight v = chainWeight (p v) + overlapCount v`
  and cycle-membership transfer in both directions.

## Convention bridge (lab notes → repo)

Repo convention: `∂₂ f = (A⋆f | B⋆f)`, `∂₁ c = B⋆c_L + A⋆c_R`; cycle
condition `B⋆v_L = A⋆v_R`.  **Repo-left = lab-right.**
-/

import QEC.Stabilizer.Codes.BivariateBicycle.Gross.Defs
import QEC.Stabilizer.Framework.Homological.BBCover

namespace Quantum
namespace Stabilizer
namespace Homological
namespace BB

open scoped BigOperators

-- Defeq checks through `fiberSum (Prod.map ⇑coverPi id)` (the `coverPush1`
-- bridges and `change`-steps below) unfold deep `Prod`/`ZMod` instance
-- chains and exceed the default recursion depth of 512.
set_option maxRecDepth 4096

/-! ## The polynomials descend -/

/-- The Gross polynomial A descends to its base polynomial. -/
theorem coverPush_grossA : fiberSumFn ⇑coverPi grossA = baseA := by
  decide +kernel

/-- The Gross polynomial B descends to its base polynomial. -/
theorem coverPush_grossB : fiberSumFn ⇑coverPi grossB = baseB := by
  decide +kernel

/-! ## The canonical double-cover bundle -/

/-- The gross ↔ bb72 cover, supplying the shared cover and doubling machinery.
Only the polynomials and elementary covering certificates are specific to
Gross. -/
def grossCoverData : XDoubleCoverData GrossGroup BaseGroup where
  proj := coverPi
  deckS := deckS
  sec := coverSec
  Ac := grossA
  Bc := grossB
  Ab := baseA
  Bb := baseB
  deckS_ne_zero := deckS_ne_zero
  proj_fiber := coverPi_fiber
  proj_sec := coverPi_coverSec
  push_A := coverPush_grossA
  push_B := coverPush_grossB

/-- The bundle's cover complex is the Gross complex. -/
lemma grossCoverData_coverComplex : grossCoverData.coverComplex = grossComplex := rfl

/-- The bundle's base complex is the bb72 complex. -/
lemma grossCoverData_baseComplex : grossCoverData.baseComplex = bb72Complex := rfl

/-! ## Deck data on qubits (`C1 = GrossGroup × Fin 2`) -/

/-- The deck involution on qubit indices: shift the group coordinate by `deckS`,
keep the block. -/
def deckSigma1 : GrossGroup × Fin 2 → GrossGroup × Fin 2 :=
  grossCoverData.deckSigma1

@[simp] lemma deckSigma1_apply (p : GrossGroup × Fin 2) :
    deckSigma1 p = (p.1 + deckS, p.2) := rfl

lemma deckShift1_eq_comp (v : GrossGroup × Fin 2 → ZMod 2) :
    deckShift1 v = v ∘ deckSigma1 := rfl

/-- The deck involution has no fixed qubit. -/
theorem deckSigma1_ne : ∀ p : GrossGroup × Fin 2, deckSigma1 p ≠ p :=
  grossCoverData.deckSigma1_ne

/-- The fibers of `Prod.map coverPi id` on qubit indices are the
`deckSigma1`-orbits. -/
theorem coverPi_prodMap_fiber :
    ∀ q q' : GrossGroup × Fin 2,
      Prod.map ⇑coverPi id q' = Prod.map ⇑coverPi id q
        ↔ q' = q ∨ q' = deckSigma1 q :=
  grossCoverData.proj_prodMap_fiber

/-- Section of `Prod.map coverPi id` on qubit indices. -/
def coverSec1 : BaseGroup × Fin 2 → GrossGroup × Fin 2 :=
  grossCoverData.sec1

/-- The chosen qubit section is a right inverse of the projection. -/
theorem coverPi_prodMap_coverSec1 :
    ∀ p : BaseGroup × Fin 2, Prod.map ⇑coverPi id (coverSec1 p) = p :=
  grossCoverData.proj_prodMap_sec1

/-! ## The four transfer maps -/

/-- Pushforward on 0- and 2-chains. -/
noncomputable def coverPush0 :
    (GrossGroup → ZMod 2) →ₗ[ZMod 2] (BaseGroup → ZMod 2) :=
  grossCoverData.push0

/-- Pushforward on 1-chains (qubits). -/
noncomputable def coverPush1 :
    (GrossGroup × Fin 2 → ZMod 2) →ₗ[ZMod 2] (BaseGroup × Fin 2 → ZMod 2) :=
  grossCoverData.push1

/-- Pullback on 0- and 2-chains. -/
noncomputable def coverPull0 :
    (BaseGroup → ZMod 2) →ₗ[ZMod 2] (GrossGroup → ZMod 2) :=
  grossCoverData.pull0

/-- Pullback on 1-chains (qubits). -/
noncomputable def coverPull1 :
    (BaseGroup × Fin 2 → ZMod 2) →ₗ[ZMod 2] (GrossGroup × Fin 2 → ZMod 2) :=
  grossCoverData.pull1

@[simp] lemma coverPush0_apply (v : GrossGroup → ZMod 2) :
    coverPush0 v = fiberSumFn ⇑coverPi v := rfl

@[simp] lemma coverPush1_apply (v : GrossGroup × Fin 2 → ZMod 2) :
    coverPush1 v = fiberSumFn (Prod.map ⇑coverPi id) v := rfl

@[simp] lemma coverPull0_apply (u : BaseGroup → ZMod 2) :
    coverPull0 u = u ∘ ⇑coverPi := rfl

@[simp] lemma coverPull1_apply (u : BaseGroup × Fin 2 → ZMod 2) :
    coverPull1 u = u ∘ Prod.map ⇑coverPi id := rfl

/-- The generic pushforward agrees with the Gross compatibility interface. -/
lemma grossCoverData_push1 : grossCoverData.push1 = coverPush1 := rfl

/-- The generic pullback agrees with the Gross compatibility interface. -/
lemma grossCoverData_pull1 : grossCoverData.pull1 = coverPull1 := rfl

/-! ## Chain maps -/

/-- `p` is a chain map at level 1: `p₀ ∘ ∂₁ = ∂₁ ∘ p₁`. -/
theorem coverPush_boundary1_comm (c : GrossGroup × Fin 2 → ZMod 2) :
    coverPush0 (grossComplex.boundary1 c)
      = bb72Complex.boundary1 (coverPush1 c) :=
  grossCoverData.push_boundary1_comm c

/-- `p` is a chain map at level 2: `p₁ ∘ ∂₂ = ∂₂ ∘ p₂`. -/
theorem coverPush_boundary2_comm (f : GrossGroup → ZMod 2) :
    coverPush1 (grossComplex.boundary2 f)
      = bb72Complex.boundary2 (coverPush0 f) :=
  grossCoverData.push_boundary2_comm f

/-- `τ` is a chain map at level 1: `∂₁ ∘ τ₁ = τ₀ ∘ ∂₁`. -/
theorem coverPull_boundary1_comm (u : BaseGroup × Fin 2 → ZMod 2) :
    grossComplex.boundary1 (coverPull1 u)
      = coverPull0 (bb72Complex.boundary1 u) :=
  grossCoverData.pull_boundary1_comm u

/-- `τ` is a chain map at level 2: `∂₂ ∘ τ₂ = τ₁ ∘ ∂₂`. -/
theorem coverPull_boundary2_comm (f : BaseGroup → ZMod 2) :
    grossComplex.boundary2 (coverPull0 f)
      = coverPull1 (bb72Complex.boundary2 f) :=
  grossCoverData.pull_boundary2_comm f

/-! ## Exactness package on 1-chains -/

/-- `p ∘ τ = 0` on 1-chains (each fiber contributes twice in char 2). -/
theorem coverPush1_coverPull1_eq_zero (u : BaseGroup × Fin 2 → ZMod 2) :
    coverPush1 (coverPull1 u) = 0 :=
  grossCoverData.push1_pull1_eq_zero u

/-- The projection is surjective on qubits. -/
theorem coverPi_prodMap_surjective :
    Function.Surjective (Prod.map ⇑coverPi (id : Fin 2 → Fin 2)) :=
  grossCoverData.proj_prodMap_surjective

/-- Pullback is injective on qubit chains. -/
theorem coverPull1_injective : Function.Injective ⇑coverPull1 :=
  grossCoverData.pull1_injective

/-- Pullback is injective on vertex and face chains. -/
theorem coverPull0_injective : Function.Injective ⇑coverPull0 :=
  grossCoverData.pull0_injective

/-- Pushforward is surjective on qubit chains. -/
theorem coverPush1_surjective : Function.Surjective ⇑coverPush1 :=
  grossCoverData.push1_surjective

/-- `ker p = range τ` on 1-chains. -/
theorem coverPush1_eq_zero_iff (v : GrossGroup × Fin 2 → ZMod 2) :
    coverPush1 v = 0 ↔ ∃ u : BaseGroup × Fin 2 → ZMod 2, v = coverPull1 u :=
  grossCoverData.push1_eq_zero_iff v

/-- The chain identity `τ(p(v)) = v + σv` = `(1 + σ)v`. This is how the deck
homotopy (R) enters the Phase-1 distance assembly. -/
theorem coverPull1_coverPush1 (v : GrossGroup × Fin 2 → ZMod 2) :
    coverPull1 (coverPush1 v) = v + deckShift1 v :=
  grossCoverData.pull1_push1 v

/-! ## Weight identity -/

/-- The number of qubits in the support of `v` whose deck partner is also in the
support. Counts each doubly-covered fiber twice (matching the informal
`2 · overlap`). -/
noncomputable def overlapCount (v : GrossGroup × Fin 2 → ZMod 2) : ℕ :=
  grossCoverData.overlapCount v

/-- `chainWeight` of a gross 1-chain in terms of raw `Finset` data. -/
lemma grossComplex_chainWeight_eq (v : GrossGroup × Fin 2 → ZMod 2) :
    grossComplex.chainWeight v
      = (Finset.univ.filter fun p : GrossGroup × Fin 2 => v p ≠ 0).card := rfl

/-- `chainWeight` of a base 1-chain in terms of raw `Finset` data. -/
lemma bb72Complex_chainWeight_eq (u : BaseGroup × Fin 2 → ZMod 2) :
    bb72Complex.chainWeight u
      = (Finset.univ.filter fun p : BaseGroup × Fin 2 => u p ≠ 0).card := rfl

/-- Weight identity for the gross → bb72 pushforward: `|v| = |p(v)| + overlap`.
-/
theorem gross_chainWeight_eq (v : GrossGroup × Fin 2 → ZMod 2) :
    grossComplex.chainWeight v
      = bb72Complex.chainWeight (coverPush1 v) + overlapCount v :=
  grossCoverData.chainWeight_eq_push_add_overlap v

/-- Pushing forward can only shrink chain weight. -/
theorem chainWeight_coverPush_le (v : GrossGroup × Fin 2 → ZMod 2) :
    bb72Complex.chainWeight (coverPush1 v) ≤ grossComplex.chainWeight v :=
  grossCoverData.chainWeight_push_le v

/-- Pulling back exactly doubles chain weight (each base qubit in the support
contributes its full two-point fiber). -/
theorem chainWeight_coverPull1 (u : BaseGroup × Fin 2 → ZMod 2) :
    grossComplex.chainWeight (coverPull1 u) = 2 * bb72Complex.chainWeight u :=
  grossCoverData.chainWeight_pull1 u

/-! ## Cycle-membership transfer -/

/-- Pushforwards of cycles are cycles. -/
theorem coverPush1_mem_cycles {v : GrossGroup × Fin 2 → ZMod 2}
    (hv : v ∈ grossComplex.cycles) :
    coverPush1 v ∈ bb72Complex.cycles :=
  grossCoverData.push1_mem_cycles hv

/-- Pullbacks of cycles are cycles. -/
theorem coverPull1_mem_cycles {u : BaseGroup × Fin 2 → ZMod 2}
    (hu : u ∈ bb72Complex.cycles) :
    coverPull1 u ∈ grossComplex.cycles :=
  grossCoverData.pull1_mem_cycles hu

/-- Pushforwards of boundaries are boundaries. -/
theorem coverPush1_mem_boundaries {v : GrossGroup × Fin 2 → ZMod 2}
    (hv : v ∈ grossComplex.boundaries) :
    coverPush1 v ∈ bb72Complex.boundaries :=
  grossCoverData.push1_mem_boundaries hv

/-- Pullbacks of boundaries are boundaries. -/
theorem coverPull1_mem_boundaries {u : BaseGroup × Fin 2 → ZMod 2}
    (hu : u ∈ bb72Complex.boundaries) :
    coverPull1 u ∈ grossComplex.boundaries :=
  grossCoverData.pull1_mem_boundaries hu

end BB
end Homological
end Stabilizer
end Quantum
