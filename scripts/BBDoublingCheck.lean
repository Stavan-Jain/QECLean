/-
Regression checks for the generic BB doubling route.

The small cover below has two base qubits and four cover qubits. It supplies
its own certificates and derives distance two through the logical-floor,
Bézout, seam-coset, and assembly theorems of `XDoubleCoverData`, so every
hypothesis of the doubling route is discharged at least once. It is a test
fixture, not a second library definition of the four-qubit stabilizer code.

Run after building QEC: `lake env lean scripts/BBDoublingCheck.lean`.
-/
import QEC.Stabilizer.Framework.FoldDouble.BBCover

open Quantum Quantum.Stabilizer.Homological Quantum.Stabilizer.Homological.BB
open scoped Quantum.Stabilizer.Homological.BB

namespace QEC.DoublingCheck

/-- A free two-sheet cover with identical nonzero cover polynomials. -/
def smallCover : XDoubleCoverData (ZMod 2) (ZMod 1) where
  proj := 0
  deckS := 1
  sec := fun _ => 0
  Ac := fun _ => 1
  Bc := fun _ => 1
  Ab := 0
  Bb := 0
  deckS_ne_zero := by decide
  proj_fiber := by decide
  proj_sec := by decide
  push_A := by decide +kernel
  push_B := by decide +kernel

/-- Nontrivial base chains have weight at least one. -/
lemma small_logical_floor : smallCover.LogicalFloor 1 := by
  have hcheck : ∀ u : ZMod 1 × Fin 2 → ZMod 2, u ≠ 0 →
      1 ≤ (Finset.univ.filter fun j => u j ≠ 0).card := by decide +kernel
  intro u _ hnb
  apply hcheck u
  rintro rfl
  exact hnb (zero_mem _)

/-- The deck homotopy comes from the one-monomial Bézout certificate. -/
lemma small_deck_trivial : smallCover.DeckTrivialOnH1 :=
  smallCover.deckTrivial_of_bezout (Pi.single 0 1) 0 (by decide +kernel)

/-- Every base boundary is zero, so the nonzero dangerous sector is empty. -/
lemma small_dangerous_floor : smallCover.DangerousFloorNZ 2 := by
  have hzero : ∀ f : ZMod 1 → ZMod 2,
      bbBoundary2Fn smallCover.Ab smallCover.Bb f = 0 := by decide +kernel
  intro v _ _ hb hne
  obtain ⟨f, hf⟩ := hb
  exact (hne (hf.symm.trans (hzero f))).elim

/-- Each nonzero seam coset has support on both base qubits. -/
lemma small_seam_floor : smallCover.SeamCosetFloor 2 := by
  have hcheck : ∀ ζ f : ZMod 1 → ZMod 2,
      smallCover.seamC ζ + bbBoundary2Fn smallCover.Ab smallCover.Bb f ≠ 0 →
      2 ≤ (Finset.univ.filter fun j =>
        (smallCover.seamC ζ + bbBoundary2Fn smallCover.Ab smallCover.Bb f) j ≠ 0).card := by
    decide +kernel
  intro ζ _ f hnb
  apply hcheck ζ f
  intro hz
  apply hnb
  rw [hz]
  exact zero_mem _

/-- A single base qubit whose diagonal lift survives in cover homology. -/
def smallWitness : ZMod 1 × Fin 2 → ZMod 2 := fun j => if j.2 = 0 then 1 else 0

/-- The witness is a base cycle. -/
lemma small_witness_cycle : smallWitness ∈ smallCover.baseComplex.cycles := by
  change bbBoundary1Fn smallCover.Ab smallCover.Bb smallWitness = 0
  decide +kernel

/-- The base witness has weight one. -/
lemma small_witness_weight : smallCover.baseComplex.chainWeight smallWitness = 1 := by
  change (Finset.univ.filter fun j => smallWitness j ≠ 0).card = 1
  decide +kernel

/-- No cover boundary equals the lifted witness. -/
lemma small_witness_survives : smallCover.pull1 smallWitness ∉
    smallCover.coverComplex.boundaries := by
  have hcheck : ∀ f : ZMod 2 → ZMod 2,
      bbBoundary2Fn smallCover.Ac smallCover.Bc f ≠ smallCover.pull1 smallWitness := by
    decide +kernel
  rintro ⟨f, hf⟩
  exact hcheck f hf

/-- The generic chain assembly doubles distance from one to two. -/
theorem small_chain_distance :
    IsLeast {w : ℕ | ∃ v : ZMod 2 × Fin 2 → ZMod 2,
      v ∈ smallCover.coverComplex.cycles ∧ v ∉ smallCover.coverComplex.boundaries ∧
      smallCover.coverComplex.chainWeight v = w} 2 :=
  smallCover.chain_distance_eq_double small_logical_floor
    small_dangerous_floor
    (smallCover.safeFloor_of_seamCosetFloor small_deck_trivial small_seam_floor)
    smallWitness small_witness_cycle small_witness_weight small_witness_survives

/-- The same certificates give distance two at the Pauli level. -/
theorem small_pauli_distance :
    IsLeast {w : ℕ | ∃ g : NQubitPauliGroupElement smallCover.coverComplex.numQubits,
      StabilizerGroup.IsNontrivialLogicalOperator g
        smallCover.coverComplex.homologicalStabilizerGroup ∧
      NQubitPauliGroupElement.weight g = w} 2 :=
  smallCover.pauli_distance_eq_double small_logical_floor
    small_dangerous_floor
    (smallCover.safeFloor_of_seamCosetFloor small_deck_trivial small_seam_floor)
    smallWitness small_witness_cycle small_witness_weight small_witness_survives

/-- No base boundary is nonzero, so light-boundary admissibility is vacuous. -/
lemma small_admissible : ∀ b : ZMod 1 × Fin 2 → ZMod 2,
    b ∈ smallCover.baseComplex.boundaries → b ≠ 0 →
    smallCover.baseComplex.chainWeight b < 2 * 1 →
    smallCover.LightBoundaryAdmissible 1 b := by
  have hzero : ∀ f : ZMod 1 → ZMod 2,
      bbBoundary2Fn smallCover.Ab smallCover.Bb f = 0 := by decide +kernel
  rintro b ⟨f, hf⟩ hne _
  exact (hne (hf.symm.trans (hzero f))).elim

/-- The packaged Doubling theorem gives the same distance from (H1)–(H5). -/
theorem small_pauli_distance_of_admissible :
    IsLeast {w : ℕ | ∃ g : NQubitPauliGroupElement smallCover.coverComplex.numQubits,
      StabilizerGroup.IsNontrivialLogicalOperator g
        smallCover.coverComplex.homologicalStabilizerGroup ∧
      NQubitPauliGroupElement.weight g = w} 2 :=
  smallCover.pauli_distance_eq_double_of_admissible small_logical_floor
    smallWitness small_witness_cycle small_witness_weight small_witness_survives
    small_deck_trivial small_seam_floor small_admissible

/-- The fold-and-double theorem gives the same distance from (H1)–(H5): the
small cover's qubits paired by the deck translation, through the code-agnostic
distance theorem. -/
theorem small_pauli_distance_of_foldDouble :
    IsLeast {w : ℕ | ∃ g : NQubitPauliGroupElement smallCover.coverComplex.numQubits,
      StabilizerGroup.IsNontrivialLogicalOperator g
        smallCover.coverComplex.homologicalStabilizerGroup ∧
      NQubitPauliGroupElement.weight g = w} 2 :=
  smallCover.isLeast_logicalWeight_two_mul_of_foldDouble small_logical_floor
    smallWitness small_witness_cycle small_witness_weight small_witness_survives
    small_deck_trivial small_seam_floor small_admissible

open Lean in
run_cmd do
  let allowed : NameSet := .ofList [``propext, ``Classical.choice, ``Quot.sound]
  for root in [``small_chain_distance, ``small_pauli_distance,
      ``small_pauli_distance_of_admissible, ``small_pauli_distance_of_foldDouble] do
    let extra := (← collectAxioms root).filter (fun n => !allowed.contains n)
    unless extra.isEmpty do
      throwError "{root} uses forbidden axioms: {extra}"
  logInfo "doubling checks OK — independent four-qubit cover and standard axioms"

end QEC.DoublingCheck
