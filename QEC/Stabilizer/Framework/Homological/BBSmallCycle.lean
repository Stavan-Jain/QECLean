import QEC.Stabilizer.Framework.Homological.BBDoubling

/-!
# A weight-6 floor for the cycles of a bivariate bicycle code

`SmallCycleData G` bundles a bivariate bicycle code over a finite abelian group
`G`, with polynomials `A` and `B`, together with four hypotheses from which
every nonzero 1-cycle has weight at least 6:

* `epsA`, `epsB`: `A` and `B` each have an odd number of terms;
* `check_two`, `check_four`: no chain supported on the qubit `(0, b)` and one
  further qubit, respectively three further qubits, is a cycle. Both are finite
  statements about the syndromes `SmallCycle.termAt` of single qubits, which
  `decide` can evaluate.

`SmallCycleData.cycle_weight_ge_6` derives the floor. A nonzero cycle can be
translated so that its support contains a qubit `(0, b)`, because `∂₁` commutes
with translations; its weight is even by `cycle_support_even`; and the weights
2 and 4 are excluded by the two checks.

## Main definitions

* `SmallCycle.termAt`, `SmallCycle.syndAt`: the syndrome `∂₁ δ_q` of a single
  qubit `q`, and the syndrome of the indicator chain of a finite set `S` of
  qubits as a sum of `|S|` terms (`SmallCycle.bbBoundary1Fn_indF2`).
* `SmallCycleData`: the bundle, and `SmallCycleData.complex`: its chain complex.

## Main statements

* `SmallCycleData.cycle_weight_ge_6`: every nonzero 1-cycle has weight at
  least 6. In particular so does every nonzero boundary
  (`SmallCycleData.stab_weight_ge_6`).
* `SmallCycleData.chain_floor`, `SmallCycleData.dual_chain_floor`,
  `SmallCycleData.logical_weight_ge_6`: the cycles that are not boundaries, the
  dual cycles that are not dual boundaries, and the nontrivial logical
  operators of the stabilizer group of the complex have weight at least 6.
* `XDoubleCoverData.strongBaseFloor_of_smallCycle`: the hypothesis
  `StrongBaseFloor 6` of the doubling theorem, for a double cover whose base is
  the code of the bundle.
-/

namespace Quantum
namespace Stabilizer
namespace Homological
namespace BB

open scoped BigOperators

/-! ## Sparse syndromes

For the indicator chain of a finite set `S` of qubits, `(∂₁ χ_S) h` is the sum
`syndAt A B S h` with one term per element of `S`, which is much cheaper to
evaluate than the convolutions defining `∂₁`. -/

namespace SmallCycle

variable {G : Type} [Fintype G] [AddCommGroup G]
variable [DecidableEq G] (A B : G → ZMod 2)

/-- The value at the check `h` of the syndrome `∂₁ δ_q` of the qubit `q`:
`B (h - g)` for `q = (g, 0)` and `A (h - g)` for `q = (g, 1)`. -/
def termAt (q : G × Fin 2) (h : G) : ZMod 2 :=
  if q.2 = 0 then B (h - q.1) else A (h - q.1)

/-- The value at the check `h` of the syndrome of the indicator chain of a
finite set `S` of qubits: the sum of `termAt A B q h` over `q ∈ S`. -/
def syndAt (S : Finset (G × Fin 2)) (h : G) : ZMod 2 :=
  ∑ q ∈ S, termAt A B q h

/-- On the indicator chain of a finite set `S`, the boundary map `∂₁` is
`syndAt A B S`. -/
lemma bbBoundary1Fn_indF2 (S : Finset (G × Fin 2)) (h : G) :
    bbBoundary1Fn A B (indF2 S) h = syndAt A B S h := by
  induction S using Finset.induction with
  | empty =>
    rw [indF2_empty, ← bbBoundary1_apply, map_zero]
    rfl
  | insert a S ha ih =>
    rw [indF2_insert ha, bbBoundary1Fn_add, Pi.add_apply, ih, bbBoundary1Fn_single]
    exact (Finset.sum_insert (f := fun q => termAt A B q h) ha).symm

end SmallCycle

/-! ## The bundle -/

/-- A bivariate bicycle code over `G` whose polynomials `A`, `B` each have an
odd number of terms and admit no cycle of weight 2 or 4 through a qubit
`(0, b)`. The two checks quantify over arbitrary tuples of qubits rather than
over sets, so that `decide` can evaluate them. -/
structure SmallCycleData (G : Type)
    [Fintype G] [AddCommGroup G] [DecidableEq G] where
  /-- The polynomial `A`. -/
  A : G → ZMod 2
  /-- The polynomial `B`. -/
  B : G → ZMod 2
  /-- `A` has an odd number of terms. -/
  epsA : ∑ h : G, A h = 1
  /-- `B` has an odd number of terms. -/
  epsB : ∑ h : G, B h = 1
  /-- No cycle of weight 2 through `(0, b)`: the qubit `(0, b)` and any other
  qubit `q` have different syndromes. -/
  check_two : ∀ b : Fin 2, ∀ q : G × Fin 2, q ≠ ((0 : G), b) →
    ∃ h : G, SmallCycle.termAt A B ((0 : G), b) h
      + SmallCycle.termAt A B q h ≠ 0
  /-- No cycle of weight 4 through `(0, b)`: the syndromes of `(0, b)` and of
  three qubits `q₁`, `q₂`, `q₃` other than `(0, b)` do not add up to zero. The
  three qubits need not be distinct; when two of them coincide their syndromes
  cancel and the statement follows from `check_two`. -/
  check_four : ∀ b : Fin 2, ∀ q₁ q₂ q₃ : G × Fin 2,
    q₁ = ((0 : G), b) ∨ q₂ = ((0 : G), b) ∨ q₃ = ((0 : G), b) ∨
    ∃ h : G, SmallCycle.termAt A B ((0 : G), b) h
      + SmallCycle.termAt A B q₁ h + SmallCycle.termAt A B q₂ h
      + SmallCycle.termAt A B q₃ h ≠ 0

namespace SmallCycleData

variable {G : Type} [Fintype G] [AddCommGroup G] [DecidableEq G]
  (D : SmallCycleData G)

/-! ## The weight-6 floor -/

/-- A 1-cycle whose support contains a qubit `(0, b)` has weight at least 6:
its weight is even, and the other points of a support of size 2 or 4 would
contradict `check_two` or `check_four`. -/
private lemma six_le_card_support_of_origin {u : G × Fin 2 → ZMod 2}
    (hcyc : bbBoundary1Fn D.A D.B u = 0) {b : Fin 2} (hb : u ((0 : G), b) ≠ 0) :
    6 ≤ (Finset.univ.filter fun p => u p ≠ 0).card := by
  by_contra hlt
  have hmem : ((0 : G), b) ∈ Finset.univ.filter fun p => u p ≠ 0 :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb⟩
  obtain ⟨k, hk⟩ := cycle_support_even D.A D.B D.epsA D.epsB hcyc
  have hcard := Finset.card_erase_of_mem hmem
  have hpos := Finset.card_pos.mpr ⟨_, hmem⟩
  have hnot := Finset.notMem_erase ((0 : G), b) (Finset.univ.filter fun p => u p ≠ 0)
  -- the syndrome of the support, split off at `(0, b)`, vanishes
  have hsynd : ∀ h, SmallCycle.termAt D.A D.B ((0 : G), b) h
      + SmallCycle.syndAt D.A D.B
        ((Finset.univ.filter fun p => u p ≠ 0).erase ((0 : G), b)) h = 0 := fun h => by
    have h0 := SmallCycle.bbBoundary1Fn_indF2 D.A D.B (Finset.univ.filter fun p => u p ≠ 0) h
    rw [← self_eq_indF2_filter, hcyc, ← Finset.insert_erase hmem, SmallCycle.syndAt,
      Finset.sum_insert hnot] at h0
    exact h0.symm
  obtain h1 | h3 : ((Finset.univ.filter fun p => u p ≠ 0).erase ((0 : G), b)).card = 1
      ∨ ((Finset.univ.filter fun p => u p ≠ 0).erase ((0 : G), b)).card = 3 := by omega
  · obtain ⟨q, hq⟩ := Finset.card_eq_one.mp h1
    rw [hq] at hsynd hnot
    obtain ⟨h, hh⟩ := D.check_two b q (Ne.symm (Finset.notMem_singleton.mp hnot))
    exact hh (by simpa only [SmallCycle.syndAt, Finset.sum_singleton] using hsynd h)
  · obtain ⟨q₁, q₂, q₃, h12, h13, h23, hq⟩ := Finset.card_eq_three.mp h3
    rw [hq] at hsynd hnot
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hnot
    obtain h | h | h | ⟨h, hh⟩ := D.check_four b q₁ q₂ q₃
    · exact hnot.1 h.symm
    · exact hnot.2.1 h.symm
    · exact hnot.2.2 h.symm
    · refine hh ?_
      have hs := hsynd h
      rwa [SmallCycle.syndAt, Finset.sum_insert (by simp [h12, h13]),
        Finset.sum_insert (by simpa using h23), Finset.sum_singleton, ← add_assoc,
        ← add_assoc] at hs

/-- Every nonzero 1-cycle of the complex, boundary or not, has weight at least
6. -/
theorem cycle_weight_ge_6
    (u : G × Fin 2 → ZMod 2)
    (hcyc : bbBoundary1Fn D.A D.B u = 0) (hne : u ≠ 0) :
    6 ≤ (Finset.univ.filter fun p => u p ≠ 0).card := by
  obtain ⟨p, hp⟩ := Function.ne_iff.mp hne
  rw [← card_support_translate1 p.1 u]
  refine D.six_le_card_support_of_origin (b := p.2) ?_ (by simpa using hp)
  rw [bbBoundary1Fn_translate1, hcyc]
  rfl

/-! ## Consequences -/

/-- The bivariate bicycle chain complex of the bundle. -/
noncomputable def complex : HomologicalCode := bbChainComplex D.A D.B

/-- The weight of a 1-chain of `complex` is the size of its support. -/
lemma complex_chainWeight_eq (u : G × Fin 2 → ZMod 2) :
    D.complex.chainWeight u
      = (Finset.univ.filter fun p : G × Fin 2 => u p ≠ 0).card := rfl

/-- Every cycle that is not a boundary has weight at least 6. -/
theorem chain_floor :
    ∀ u ∈ D.complex.cycles, u ∉ D.complex.boundaries →
      6 ≤ D.complex.chainWeight u := fun u hu hnb =>
  D.cycle_weight_ge_6 u hu fun h => hnb (h ▸ zero_mem _)

/-- Every dual cycle that is not a dual boundary has weight at least 6, by the
duality of bivariate bicycle complexes. -/
theorem dual_chain_floor :
    ∀ c ∈ D.complex.dualCycles, c ∉ D.complex.dualBoundaries →
      6 ≤ D.complex.chainWeight c :=
  (bb_cycle_bound_iff_dual_bound D.A D.B 6).mp D.chain_floor

/-- Every nontrivial logical operator of the stabilizer group of the complex
has weight at least 6. -/
theorem logical_weight_ge_6
    (g : NQubitPauliGroupElement D.complex.numQubits)
    (hg : Quantum.StabilizerGroup.IsNontrivialLogicalOperator g
      D.complex.homologicalStabilizerGroup) :
    6 ≤ NQubitPauliGroupElement.weight g :=
  HomologicalCode.chainWeight_lower_bound_transfers D.complex 6
    D.chain_floor D.dual_chain_floor g hg

/-- Every nonzero boundary `∂₂ f` has weight at least 6. -/
theorem stab_weight_ge_6 (f : G → ZMod 2)
    (hne : bbBoundary2Fn D.A D.B f ≠ 0) :
    6 ≤ (Finset.univ.filter
      fun p => bbBoundary2Fn D.A D.B f p ≠ 0).card :=
  D.cycle_weight_ge_6 _ (bbBoundaryFn_comp D.A D.B f) hne

end SmallCycleData

/-! ## The strong base floor of a double cover -/

/-- If the base code of a free double cover `C` is the code of a bundle
`D : SmallCycleData H`, then `C` satisfies `StrongBaseFloor 6`. -/
theorem XDoubleCoverData.strongBaseFloor_of_smallCycle
    {G H : Type} [Fintype G] [AddCommGroup G] [DecidableEq G]
    [Fintype H] [AddCommGroup H] [DecidableEq H]
    (C : XDoubleCoverData G H) (D : SmallCycleData H)
    (hA : C.Ab = D.A) (hB : C.Bb = D.B) :
    C.StrongBaseFloor 6 := fun u hcyc hne =>
  D.cycle_weight_ge_6 u (hA ▸ hB ▸ hcyc) hne

end BB
end Homological
end Stabilizer
end Quantum
