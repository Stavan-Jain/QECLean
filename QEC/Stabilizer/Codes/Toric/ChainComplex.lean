import QEC.Stabilizer.Framework.Homological.Generators
import QEC.Stabilizer.Codes.Toric.Homology
import QEC.Stabilizer.Codes.Toric.OperatorChains

/-!
# The toric chain complex as a `HomologicalCode`

`toricHomologicalCode L` packages the toric boundary maps `∂₂`, `∂₁` and the
edge numbering `toricEdgeEquiv L` as a `HomologicalCode`, so that the general
theory of homological CSS codes applies to the toric code.

The constructions of the general theory specialise to the toric ones:

* by definition: its cycles, boundaries and homology are `Z₁ L`, `B₁ L` and
  `H₁ L`, and its chain operators are `toricXOperatorOfChain L` and
  `toricZOperatorOfChain L`;
* `toricHomologicalCode_cutMap_eq`: its cut map, defined as the transpose of
  `∂₁`, is the vertex cut map `δ⁰`; hence `toricBoundary1_cutMap_transpose`,
  the pairing identity `⟨∂₁ c, s⟩ = ⟨c, δ⁰ s⟩`;
* `toricHomologicalCode_singleVtx_eq`, `toricHomologicalCode_singleFace_eq`:
  its indicator chains are `singleVtx` and `singleFace`.
-/

namespace Quantum
namespace Stabilizer
namespace Lattice

open scoped ToricChain
open Homological

/-- The toric chain complex as a `HomologicalCode`: the 0-, 1- and 2-cells are
the vertices, edges and faces of the `L × L` periodic square lattice, with the
boundary maps `∂₁`, `∂₂` and the qubit numbering `edgeToQubitIdx`. -/
noncomputable def toricHomologicalCode (L : ℕ) [Fact (0 < L)] : HomologicalCode where
  C0 := VtxIdx L
  C1 := EdgeIdx L
  C2 := FaceIdx L
  decEq0 := inferInstance
  decEq1 := inferInstance
  decEq2 := inferInstance
  fin0 := inferInstance
  fin1 := inferInstance
  fin2 := inferInstance
  boundary1 := ∂₁ L
  boundary2 := ∂₂ L
  boundary_comp := toricBoundary_comp_zero L
  numQubits := toricNumQubits L
  numQubits_eq := card_edgeIdx L
  edgeEquiv := toricEdgeEquiv L

variable (L : ℕ) [Fact (0 < L)]

/-! ## Definitional identifications -/

theorem toricHomologicalCode_cycles_eq : (toricHomologicalCode L).cycles = Z₁ L := rfl

theorem toricHomologicalCode_boundaries_eq : (toricHomologicalCode L).boundaries = B₁ L := rfl

theorem toricHomologicalCode_H1_eq : (toricHomologicalCode L).H1 = H₁ L := rfl

theorem toricHomologicalCode_numQubits : (toricHomologicalCode L).numQubits = 2 * L * L := rfl

theorem toricHomologicalCode_chainXOperator_eq (c : C1 L) :
    (toricHomologicalCode L).chainXOperator c = toricXOperatorOfChain L c := rfl

theorem toricHomologicalCode_chainZOperator_eq (c : C1 L) :
    (toricHomologicalCode L).chainZOperator c = toricZOperatorOfChain L c := rfl

/-- The indicator 0-chains of `toricHomologicalCode L` are the `singleVtx v`. -/
theorem toricHomologicalCode_singleVtx_eq (v : VtxIdx L) :
    (toricHomologicalCode L).singleVtx v = Lattice.singleVtx v := by
  change (Pi.single v 1 : VtxIdx L → ZMod 2) = fun u => if u = v then 1 else 0
  exact funext fun u => Pi.single_apply v 1 u

/-- The indicator 2-chains of `toricHomologicalCode L` are the
`singleFace f`. -/
theorem toricHomologicalCode_singleFace_eq (f : FaceIdx L) :
    (toricHomologicalCode L).singleFace f = Lattice.singleFace f := by
  change (Pi.single f 1 : FaceIdx L → ZMod 2) = fun p => if p = f then 1 else 0
  exact funext fun p => Pi.single_apply f 1 p

/-! ## The cut map -/

/-- On indicator chains, `δ⁰` is the transpose of `∂₁`: the boundary of the edge
`e` at the vertex `v` is the cut of `v` at `e`. -/
private lemma toricBoundary1_single_apply (e : EdgeIdx L) (v : VtxIdx L) (a : ZMod 2) :
    a * ∂₁ L (Pi.single e 1) v = δ⁰ L (Pi.single v a) e := by
  cases e with
  | h x y =>
    rw [toricBoundary1_apply, toricVertexCutMap_apply_h, Pi.single_comm v a (x, y),
      Pi.single_comm v a (next L x, y)]
    simp [Pi.single_apply, mul_add, Prod.ext_iff]
  | v x y =>
    rw [toricBoundary1_apply, toricVertexCutMap_apply_v, Pi.single_comm v a (x, y),
      Pi.single_comm v a (x, next L y)]
    simp [Pi.single_apply, mul_add, Prod.ext_iff]

/-- The cut map of `toricHomologicalCode L`, defined as the transpose of `∂₁`,
is the vertex cut map `δ⁰`. -/
theorem toricHomologicalCode_cutMap_eq : (toricHomologicalCode L).cutMap = δ⁰ L := by
  refine LinearMap.pi_ext fun v a => funext fun e => ?_
  refine Eq.trans ?_ (toricBoundary1_single_apply L e v a)
  change ∑ u : VtxIdx L, (Pi.single v a : C0 L) u * ∂₁ L (Pi.single e 1) u = _
  simp [Pi.single_apply]

/-- `δ⁰` is the transpose of `∂₁`: `⟨∂₁ c, s⟩ = ⟨c, δ⁰ s⟩` for the standard
pairing `⟨a, b⟩ = ∑ x, a x * b x`. -/
theorem toricBoundary1_cutMap_transpose (c : C1 L) (s : C0 L) :
    ∑ v : VtxIdx L, ∂₁ L c v * s v = ∑ e : EdgeIdx L, c e * δ⁰ L s e := by
  rw [← toricHomologicalCode_cutMap_eq]
  exact (toricHomologicalCode L).boundary1_cutMap_transpose c s

end Lattice
end Stabilizer
end Quantum
