import QEC.Stabilizer.Codes.Small.Steane7
import QEC.Stabilizer.Framework.Core.CSS.CSSDistance
import QEC.Stabilizer.Framework.Core.Logical.CodeDistance
import QEC.Stabilizer.Foundations.BinarySymplectic.SymplecticInner

/-!
# Steane `[[7, 1, 3]]`: the distance-3 proof

`HasCodeDistance Steane7.stabilizerCode 3`, via `hasCodeDistance_of`:

* **witness** — `logicalX_w3 = X` on qubits `{3,5,6}` (= `logicalX · X1`), an explicit weight-3
  nontrivial logical;
* **no weight-1 logicals** — every weight-1 Pauli anticommutes with a generator
  (`no_weight_one_mem_centralizer_of_anticommute_witness`);
* **no weight-2 logicals** — every weight-2 Pauli anticommutes with a generator
  (`no_weight_two_mem_centralizer_of_anticommute_witness`).

This is the inner/outer distance input that `concat_hasCodeDistance` (M6) consumes for the
Steane⊗Steane `[[49, 1, 9]]` instance (M7).
-/

namespace Quantum.StabilizerGroup.Steane7

open NQubitPauliGroupElement

/-- `DecidableEq` on `NQubitPauliGroupElement n` via field-wise decision (file-local, to keep
the global `native_decide` synthesis path intact — see `FiveQubit_5_1_3.lean`). -/
local instance instDecidableEqNQubitPauliGroupElement (n : ℕ) :
    DecidableEq (NQubitPauliGroupElement n) := fun p q =>
  decidable_of_iff (p.phasePower = q.phasePower ∧ p.operators = q.operators)
    ⟨fun ⟨h1, h2⟩ => by cases p; cases q; simp_all,
     fun h => by cases h; exact ⟨rfl, rfl⟩⟩

/-- `Decidable (Anticommute p q)` for `by decide` (noncomputable, but the kernel reduces it). -/
noncomputable local instance decidableAnticommute {n : ℕ} (p q : NQubitPauliGroupElement n) :
    Decidable (NQubitPauliGroupElement.Anticommute p q) :=
  show Decidable (p * q = NQubitPauliGroupElement.minusOne n * (q * p)) from inferInstance

/-- Anticommutation depends only on operator parts: equal operator parts anticommute with the
same elements. -/
private lemma anticommute_of_operators_eq {n : ℕ} (p q r : NQubitPauliGroupElement n)
    (h : p.operators = q.operators) (h_ac : NQubitPauliGroupElement.Anticommute p r) :
    NQubitPauliGroupElement.Anticommute q r := by
  rw [anticommutes_iff_odd_anticommutes] at h_ac ⊢
  classical
  have : Finset.univ.filter (NQubitPauliGroupElement.anticommutesAt q.operators r.operators) =
      Finset.univ.filter (NQubitPauliGroupElement.anticommutesAt p.operators r.operators) := by
    ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; rw [h]
  rw [this]; exact h_ac

/-- The Steane stabilizer code's subgroup is the closure of the six generators. -/
lemma stabilizerCode_toSubgroup_eq :
    stabilizerCode.toStabilizerGroup.toSubgroup = Subgroup.closure generators := by
  show Subgroup.closure (NQubitPauliGroupElement.listToSet generatorsList) = _
  rw [listToSet_generatorsList]

/-! ## No weight-1 logicals -/

private lemma weight_one_anticomm_witness :
    ∀ i : Fin 7, ∀ P : PauliOperator, P ≠ PauliOperator.I →
      ∃ g ∈ generators, NQubitPauliGroupElement.Anticommute (weightOneAt i P) g := by
  intro i P hP
  fin_cases i <;>
    (match P, hP with
      | PauliOperator.X, _ => first
        | exact ⟨Z1, by simp [generators, ZGenerators, XGenerators], by decide⟩
        | exact ⟨Z2, by simp [generators, ZGenerators, XGenerators], by decide⟩
        | exact ⟨Z3, by simp [generators, ZGenerators, XGenerators], by decide⟩
      | PauliOperator.Y, _ => first
        | exact ⟨Z1, by simp [generators, ZGenerators, XGenerators], by decide⟩
        | exact ⟨Z2, by simp [generators, ZGenerators, XGenerators], by decide⟩
        | exact ⟨Z3, by simp [generators, ZGenerators, XGenerators], by decide⟩
      | PauliOperator.Z, _ => first
        | exact ⟨X1, by simp [generators, ZGenerators, XGenerators], by decide⟩
        | exact ⟨X2, by simp [generators, ZGenerators, XGenerators], by decide⟩
        | exact ⟨X3, by simp [generators, ZGenerators, XGenerators], by decide⟩
      | PauliOperator.I, hP => exact (hP rfl).elim)

/-! ## No weight-2 logicals -/

private lemma weight_two_anticomm_witness :
    ∀ i j : Fin 7, i ≠ j → ∀ P Q : PauliOperator, P ≠ PauliOperator.I → Q ≠ PauliOperator.I →
      ∃ g ∈ generators, NQubitPauliGroupElement.Anticommute (weightTwoAt i j P Q) g := by
  -- The symplectic-inner version is *computable* (unlike `Anticommute`, which routes through the
  -- noncomputable group `*`), so the 7·7·4·4 case table closes by `native_decide`.
  have key : ∀ i j : Fin 7, i ≠ j → ∀ P Q : PauliOperator,
      P ≠ PauliOperator.I → Q ≠ PauliOperator.I → ∃ g ∈ generatorsList,
        NQubitPauliOperator.symplecticInner (weightTwoAt i j P Q).operators g.operators = 1 := by
    native_decide
  intro i j hij P Q hP hQ
  obtain ⟨g, hg_mem, hg_symp⟩ := key i j hij P Q hP hQ
  exact ⟨g, by rw [← listToSet_generatorsList]; exact hg_mem,
    (NQubitPauliOperator.anticommutes_iff_symplectic_inner_one _ _).mpr hg_symp⟩

/-! ## The weight-3 witness -/

/-- Weight-3 logical `X` on qubits `{3,5,6}` (explicit, so `decide` reduces it); equals
`logicalX · X1`. -/
def logicalX_w3 : NQubitPauliGroupElement 7 :=
  ⟨0, (((NQubitPauliOperator.identity 7).set 3 PauliOperator.X).set 5 PauliOperator.X).set 6
      PauliOperator.X⟩

lemma logicalX_w3_eq_mul : logicalX_w3 = logicalX * X1 := by
  apply NQubitPauliGroupElement.ext
  · decide
  · funext i; fin_cases i <;> decide

@[simp] lemma logicalX_w3_weight : NQubitPauliGroupElement.weight logicalX_w3 = 3 := by decide

private lemma logicalX_w3_anticomm_logicalZ :
    NQubitPauliGroupElement.Anticommute logicalX_w3 logicalZ := by
  change logicalX_w3 * logicalZ = NQubitPauliGroupElement.minusOne 7 * (logicalZ * logicalX_w3)
  apply NQubitPauliGroupElement.ext
  · decide
  · funext i; fin_cases i <;> decide

private lemma logicalX_w3_mem_centralizer :
    logicalX_w3 ∈ centralizer stabilizerCode.toStabilizerGroup := by
  rw [logicalX_w3_eq_mul]
  apply (centralizer stabilizerCode.toStabilizerGroup).mul_mem
  · exact logicalX_mem_centralizer
  · apply stabilizer_le_centralizer
    rw [stabilizerCode_toSubgroup_eq]
    exact Subgroup.subset_closure (by simp [generators, XGenerators])

private lemma logicalX_w3_not_mem_subgroup :
    logicalX_w3 ∉ stabilizerCode.toStabilizerGroup.toSubgroup := by
  apply not_mem_stabilizer_of_anticommutes_centralizer _ logicalX_w3 logicalZ
  · exact logicalZ_mem_centralizer
  · exact logicalX_w3_anticomm_logicalZ

private lemma logicalX_w3_no_stab_same_operators :
    ∀ s ∈ stabilizerCode.toStabilizerGroup.toSubgroup, s.operators ≠ logicalX_w3.operators := by
  intro s hs h_ops
  have hs_anti : NQubitPauliGroupElement.Anticommute s logicalZ :=
    anticommute_of_operators_eq logicalX_w3 s logicalZ h_ops.symm logicalX_w3_anticomm_logicalZ
  exact not_mem_stabilizer_of_anticommutes_centralizer
    stabilizerCode.toStabilizerGroup s logicalZ logicalZ_mem_centralizer hs_anti hs

private lemma logicalX_w3_isNontrivial :
    IsNontrivialLogicalOperator logicalX_w3 stabilizerCode.toStabilizerGroup :=
  ⟨logicalX_w3_mem_centralizer, logicalX_w3_not_mem_subgroup,
   logicalX_w3_no_stab_same_operators⟩

/-! ## Distance 3 -/

/-- **The Steane `[[7, 1, 3]]` code has distance 3.** -/
theorem stabilizerCode_hasCodeDistance_three : HasCodeDistance stabilizerCode 3 := by
  refine hasCodeDistance_of stabilizerCode 3 (by decide)
    ⟨logicalX_w3, logicalX_w3_isNontrivial, by decide⟩ ?_
  intro w hw_pos hw_lt g hg_weight h_nontrivial
  rcases (IsNontrivialLogicalOperator_iff g stabilizerCode.toStabilizerGroup).mp h_nontrivial
    with ⟨h_cent, _, _⟩
  interval_cases w
  · exact no_weight_one_mem_centralizer_of_anticommute_witness
      stabilizerCode.toStabilizerGroup generators stabilizerCode_toSubgroup_eq
      weight_one_anticomm_witness g hg_weight h_cent
  · exact no_weight_two_mem_centralizer_of_anticommute_witness
      stabilizerCode.toStabilizerGroup generators stabilizerCode_toSubgroup_eq
      weight_two_anticomm_witness g hg_weight h_cent

end Quantum.StabilizerGroup.Steane7
