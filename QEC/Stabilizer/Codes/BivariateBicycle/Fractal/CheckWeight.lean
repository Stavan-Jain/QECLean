import QEC.Stabilizer.Codes.BivariateBicycle.Fractal.Code
import QEC.Stabilizer.Framework.Homological.BBDuality
import QEC.Stabilizer.Framework.Homological.AutoPresentation
import Mathlib.InformationTheory.Hamming

/-!
# Weight-six natural generators of the fractal BB family

Every canonical face and vertex stabilizer has Pauli weight exactly six.
These statements concern the sparse natural generators, independently of the
chosen independent basis used to package the stabilizer code.
-/

namespace Quantum.Stabilizer.Homological.BB.Fractal

open HomologicalCode NQubitPauliGroupElement
open scoped BigOperators

/-- Weight adds across the two disjoint BB blocks. -/
private theorem chainWeight_halves {G : Type} [Fintype G] [AddCommGroup G]
    [DecidableEq G] (A B u v : G → ZMod 2) :
    (bbChainComplex A B).chainWeight
      (fun p => if p.2 = 0 then u p.1 else v p.1) = hammingNorm u + hammingNorm v := by
  classical
  simp only [chainWeight, chainSupport, hammingNorm,
    Finset.card_eq_sum_ones, Finset.sum_filter]
  change (∑ p : G × Fin 2, if (if p.2 = 0 then u p.1 else v p.1) ≠ 0 then 1 else 0) = _
  rw [Fintype.sum_prod_type]
  simp [Fin.sum_univ_two, Finset.sum_add_distrib]

/-- Translating a check by convolution preserves its weight. -/
private theorem hammingNorm_conv_single {G : Type} [Fintype G] [AddCommGroup G]
    [DecidableEq G] (a : G → ZMod 2) (g : G) :
    hammingNorm (conv a (Pi.single g 1)) = hammingNorm a := by
  rw [conv_comm, conv_single_left]
  exact card_filter_comp_equiv (Equiv.subRight g) (fun i => a i ≠ 0)

/-- Reflection of the translation group preserves check weight. -/
private theorem hammingNorm_reflect {G : Type} [Fintype G] [AddCommGroup G]
    (a : G → ZMod 2) : hammingNorm (reflect a) = hammingNorm a := by
  classical
  exact card_filter_comp_equiv (Equiv.neg G) (fun i => a i ≠ 0)

/-- Each horizontal classical check contains exactly three nonzero entries. -/
theorem hammingNorm_checkA (s : ℕ) : hammingNorm (checkA s) = 3 := by
  simpa [hammingNorm, checkA] using aSupport_card s

/-- Each vertical classical check contains exactly three nonzero entries. -/
theorem hammingNorm_checkB (s : ℕ) : hammingNorm (checkB s) = 3 := by
  simpa [hammingNorm, checkB] using bSupport_card s

/-- Every natural face-boundary chain has weight exactly six. -/
theorem chainWeight_faceBoundary (s : ℕ) (g : Grid s) :
    (chainComplex s).chainWeight
      ((chainComplex s).boundary2 ((chainComplex s).singleFace g)) = 6 := by
  change (bbChainComplex (checkA s) (checkB s)).chainWeight
    (fun p => if p.2 = 0 then conv (checkA s) (Pi.single g 1) p.1
      else conv (checkB s) (Pi.single g 1) p.1) = 6
  rw [chainWeight_halves, hammingNorm_conv_single, hammingNorm_conv_single,
    hammingNorm_checkA, hammingNorm_checkB]

/-- Every natural vertex-cut chain has weight exactly six. -/
theorem chainWeight_vertexCut (s : ℕ) (g : Grid s) :
    (chainComplex s).chainWeight
      ((chainComplex s).cutMap ((chainComplex s).singleVtx g)) = 6 := by
  change (bbChainComplex (checkA s) (checkB s)).chainWeight
    ((bbChainComplex (checkA s) (checkB s)).cutMap (Pi.single g 1)) = 6
  rw [bb_cutMap_eq]
  have hh := chainWeight_halves (checkA s) (checkB s)
    (conv (reflect (checkB s)) (Pi.single g 1))
    (conv (reflect (checkA s)) (Pi.single g 1))
  simpa only [hammingNorm_conv_single, hammingNorm_reflect,
    hammingNorm_checkA, hammingNorm_checkB] using hh

/-- Every canonical X-type face stabilizer has Pauli weight exactly six. -/
theorem weight_faceStabOf (s : ℕ) (g : Grid s) :
    weight ((chainComplex s).faceStabOf g) = 6 := by
  rw [faceStabOf, weight_chainXOperator]
  exact chainWeight_faceBoundary s g

/-- Every canonical Z-type vertex stabilizer has Pauli weight exactly six. -/
theorem weight_vertexStabOf (s : ℕ) (g : Grid s) :
    weight ((chainComplex s).vertexStabOf g) = 6 := by
  rw [vertexStabOf, weight_chainZOperator]
  exact chainWeight_vertexCut s g

/-- All members of the canonical sparse generating set have weight six. -/
theorem naturalGenerators_weight (s : ℕ)
    (p : NQubitPauliGroupElement (chainComplex s).numQubits)
    (hp : p ∈ (chainComplex s).ZGenerators ∪ (chainComplex s).XGenerators) :
    weight p = 6 := by
  rcases hp with ⟨g, rfl⟩ | ⟨g, rfl⟩
  · exact weight_vertexStabOf s g
  · exact weight_faceStabOf s g

/-- The packaged stabilizer group admits a generating set of weight-six Paulis. -/
theorem exists_weight_six_generating_set (s : ℕ) :
    ∃ S : Set (NQubitPauliGroupElement (chainComplex s).numQubits),
      Subgroup.closure S = (chainComplex s).toStabilizerCode.toStabilizerGroup.toSubgroup ∧
        ∀ p ∈ S, weight p = 6 := by
  refine ⟨(chainComplex s).ZGenerators ∪ (chainComplex s).XGenerators, ?_,
    naturalGenerators_weight s⟩
  rw [toStabilizerCode_toSubgroup_eq]
  rfl

/-- Replacing equal numerical parameters preserves a sparse generating set. -/
private theorem weight_six_generators_cast {n k d n' k' : ℕ}
    (C : Quantum.StabilizerGroup.StabilizerCodeWithDistance n k d)
    (hn : n = n') (hk : k = k')
    (h : ∃ S : Set (NQubitPauliGroupElement n),
      Subgroup.closure S = C.toStabilizerCode.toStabilizerGroup.toSubgroup ∧
        ∀ p ∈ S, weight p = 6) :
    ∃ S : Set (NQubitPauliGroupElement n'),
      Subgroup.closure S =
        (cast (congrArg₂ (fun a b =>
          Quantum.StabilizerGroup.StabilizerCodeWithDistance a b d) hn hk)
          C).toStabilizerCode.toStabilizerGroup.toSubgroup ∧
          ∀ p ∈ S, weight p = 6 := by
  subst n' k'
  exact h

/-- The exact-distance code with numerical parameters has weight-six generators. -/
theorem stabilizerCodeWithDistance_has_weight_six_generating_set (s : ℕ) :
    ∃ S : Set (NQubitPauliGroupElement (2 * period (s + 1) ^ 2)),
      Subgroup.closure S =
        (stabilizerCodeWithDistance s).toStabilizerCode.toStabilizerGroup.toSubgroup ∧
        ∀ p ∈ S, weight p = 6 := by
  have h := weight_six_generators_cast
    (⟨(chainComplex s).toStabilizerCode, chainComplex_hasCodeDistance s⟩ :
      Quantum.StabilizerGroup.StabilizerCodeWithDistance _ _ (seedDistance s))
    (chainComplex_numQubits s) (chainComplex_finrank_H1 s)
    (exists_weight_six_generating_set s)
  exact h

end Quantum.Stabilizer.Homological.BB.Fractal
