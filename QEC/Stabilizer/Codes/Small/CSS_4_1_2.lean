import Mathlib.Tactic
import QEC.Stabilizer.Framework.Core.Stabilizer.StabilizerGroup
import QEC.Stabilizer.Framework.Core.Stabilizer.SubgroupLemmas
import QEC.Stabilizer.Framework.Core.Stabilizer.Centralizer
import QEC.Stabilizer.Framework.Core.Logical.CodeDistance
import QEC.Stabilizer.Framework.Core.CSS.CSSDistance
import QEC.Stabilizer.Framework.Core.Logical.LogicalOperators
import QEC.Stabilizer.Framework.Core.Stabilizer.StabilizerCode
import QEC.Stabilizer.Framework.Symplectic.SymplecticSpan
import QEC.Stabilizer.Foundations.PauliGroup.Commutation
import QEC.Stabilizer.Foundations.PauliGroup.CommutationTactics
import QEC.Stabilizer.Foundations.PauliGroup.NQubitOperator
import QEC.Stabilizer.Foundations.PauliGroup.NQubitElement
import QEC.Stabilizer.Foundations.BinarySymplectic.Core
import QEC.Stabilizer.Foundations.BinarySymplectic.CheckMatrix
import QEC.Stabilizer.Foundations.BinarySymplectic.CheckMatrixDecidable
import QEC.Stabilizer.Framework.Symplectic.IndependentEquiv

namespace Quantum
open scoped BigOperators
open scoped Pauli

namespace StabilizerGroup
namespace CSS_4_1_2

/-!
# The [[4, 1, 2]] LNCY code

The Leung-Nielsen-Chuang-Yamamoto [[4, 1, 2]] code is a four-qubit CSS
stabilizer code encoding one logical qubit, with code distance 2. It detects
(but does not correct) a single arbitrary Pauli error. Originally introduced in
[Leung-Nielsen-Chuang-Yamamoto 1997, `arxiv:quant-ph/9704002`, §II Eqs. 5–6].

## Codewords (LNCY convention, paper Eqs. 5–6)

```
|0_L⟩ = (|0000⟩ + |1111⟩)/√2
|1_L⟩ = (|0011⟩ + |1100⟩)/√2
```

## Stabilizer (chosen to stabilize the LNCY codewords above)

Three generators, n − k = 3:
- `S_Z1 = Z Z I I` (Z-type)
- `S_Z2 = I I Z Z` (Z-type)
- `S_X1 = X X X X` (X-type)

Note: the EC Zoo entry quotes a *dual* tableau `(XXII, IIXX, ZZZZ)` from the
Qiskit preset; that one stabilizes a different 2-d subspace. We use the LNCY
codeword convention as the ground truth.

## Logical operators

- `X̄ = X X I I` (overlaps `S_Z1` at qubits 0, 1; even ⇒ commutes)
- `Z̄ = Z I Z I` (overlaps `S_X1` at qubits 0, 2; even ⇒ commutes)

The two anticommute at qubit 0 only (X·Z vs no I overlap with I·I).

## Outline (decide route)

- §1 generators, §2 the generator list
- §3 decided hypotheses: pairwise commutation, phase zero, independence
- §4 `−I ∉ closure`, §5 the bundled `StabilizerGroup 4`
- §6–§8 logical operators, their anticommutation, centralizer membership
- §9 `StabilizerCode 4 1` + `StabilizerCodeWithLogicals 4 1`
- §10 distance 2 (weight-1 anti-witness function dispatching on `i ∈ {0, 1}`
  vs `i ∈ {2, 3}` to pick the appropriate Z-generator)
-/

open NQubitPauliGroupElement

/-! ## §1 — Generators -/

/-- First Z-check stabilizer: `Z Z I I` (Z on qubits 0, 1). -/
def S_Z1 : NQubitPauliGroupElement 4 := σ[ZZII]

/-- Second Z-check stabilizer: `I I Z Z` (Z on qubits 2, 3). -/
def S_Z2 : NQubitPauliGroupElement 4 := σ[IIZZ]

/-- The X-check stabilizer: `X X X X` (X on every qubit). -/
def S_X1 : NQubitPauliGroupElement 4 := σ[XXXX]

/-! ## §2 — Generator list -/

/-- The generator list (canonical order: Z-checks first, then X-check). -/
def generatorsList : List (NQubitPauliGroupElement 4) :=
  [S_Z1, S_Z2, S_X1]

/-! ## §3 — Decided hypotheses

`S_Z1 = ZZII` overlaps `S_X1 = XXXX` at qubits 0 and 1 and `S_Z2 = IIZZ` at
qubits 2 and 3 — both even, so all pairs commute; `decide` checks the nine
ordered pairs, the phases, and the check-matrix rank. -/

/-- All generators of the [[4, 1, 2]] code pairwise commute. -/
theorem generators_commute :
    ∀ g ∈ listToSet generatorsList, ∀ h ∈ listToSet generatorsList, g * h = h * g := by
  decide

/-- All three generators have phase 0 (no `i` or `−1` factor). -/
lemma AllPhaseZero_generatorsList : AllPhaseZero generatorsList := by
  decide

/-- The check-matrix rows of the three generators are linearly independent over
GF(2). -/
theorem rowsLinearIndependent_generatorsList :
    rowsLinearIndependent generatorsList := by decide

/-- The generator list is an independent generating set. -/
theorem GeneratorsIndependent_4_generatorsList :
    GeneratorsIndependent 4 generatorsList :=
  GeneratorsIndependent_of_rowsLinearIndependent rowsLinearIndependent_generatorsList

/-! ## §4 — `−I` is not in the stabilizer subgroup -/

/-- The closure of the three generators does not contain `−I`. -/
theorem negIdentity_not_mem :
    negIdentity 4 ∉ Subgroup.closure (listToSet generatorsList) :=
  negIdentity_not_mem_of_indep_phase_zero_commute generatorsList
    AllPhaseZero_generatorsList rowsLinearIndependent_generatorsList generators_commute

/-! ## §5 — Bundled `StabilizerGroup 4` -/

/-- The [[4, 1, 2]] stabilizer group, from the generator list. -/
noncomputable def stabilizerGroup : StabilizerGroup 4 :=
  mkStabilizerFromGenerators 4 generatorsList generators_commute negIdentity_not_mem

/-- The bundled stabilizer group's underlying subgroup is the closure of the
generator list. -/
lemma stabilizerGroup_toSubgroup_eq :
    stabilizerGroup.toSubgroup = Subgroup.closure (listToSet generatorsList) := rfl

/-! ## §6 — Logical operators

Logical `X̄ = X X I I` and logical `Z̄ = Z I Z I`, derived from the LNCY
codewords:

```
|0_L⟩ = (|0000⟩ + |1111⟩)/√2,   |1_L⟩ = (|0011⟩ + |1100⟩)/√2
```

`X̄ = XXII` maps `|0_L⟩ ↔ |1_L⟩`. `Z̄ = ZIZI` has eigenvalue +1 on `|0_L⟩` and
−1 on `|1_L⟩` (the parity `(-1)^(q₀ + q₂)` of the codeword basis kets is
constant on each codeword).
-/

/-- Logical X: `X X I I` (overlaps `S_Z1` at qubits 0, 1; even ⇒ commutes). -/
def logicalX : NQubitPauliGroupElement 4 := σ[XXII]

/-- Logical Z: `Z I Z I` (overlaps `S_X1` at qubits 0, 2; even ⇒ commutes). -/
def logicalZ : NQubitPauliGroupElement 4 := σ[ZIZI]

/-! ### §7 — Logical anticommutation -/

/-- `X̄ = XXII` and `Z̄ = ZIZI` anticommute (overlap at qubit 0 only — odd
parity). -/
theorem logicalX_anticommutes_logicalZ :
    NQubitPauliGroupElement.Anticommute logicalX logicalZ := by
  classical
  pauli_anticomm_odd_anticommutes
  have hfilter :
      (Finset.univ.filter
            (NQubitPauliGroupElement.anticommutesAt (n := 4)
              logicalX.operators logicalZ.operators)) =
        ({0} : Finset (Fin 4)) := by
    ext i; fin_cases i <;>
      simp [Finset.mem_filter, NQubitPauliGroupElement.anticommutesAt, logicalX, logicalZ,
        NQubitPauliOperator.set, NQubitPauliOperator.identity, PauliOperator.mulOp]
  rw [hfilter]; decide

/-! ### §8 — Logicals in centralizer (per-generator commutation lemmas) -/

private lemma logicalX_commutes_S_Z1 : logicalX * S_Z1 = S_Z1 * logicalX := by
  classical
  pauli_comm_even_anticommutes
  have hfilter :
      (Finset.univ.filter
            (NQubitPauliGroupElement.anticommutesAt (n := 4)
              logicalX.operators S_Z1.operators)) =
        ({0, 1} : Finset (Fin 4)) := by
    ext i; fin_cases i <;>
      simp [Finset.mem_filter, NQubitPauliGroupElement.anticommutesAt, logicalX, S_Z1,
        NQubitPauliOperator.set, NQubitPauliOperator.identity, PauliOperator.mulOp]
  rw [hfilter]; decide

private lemma logicalX_commutes_S_Z2 : logicalX * S_Z2 = S_Z2 * logicalX := by
  pauli_comm_componentwise [logicalX, S_Z2]

private lemma logicalX_commutes_S_X1 : logicalX * S_X1 = S_X1 * logicalX := by
  pauli_comm_componentwise [logicalX, S_X1]

private lemma logicalZ_commutes_S_Z1 : logicalZ * S_Z1 = S_Z1 * logicalZ := by
  pauli_comm_componentwise [logicalZ, S_Z1]

private lemma logicalZ_commutes_S_Z2 : logicalZ * S_Z2 = S_Z2 * logicalZ := by
  pauli_comm_componentwise [logicalZ, S_Z2]

private lemma logicalZ_commutes_S_X1 : logicalZ * S_X1 = S_X1 * logicalZ := by
  classical
  pauli_comm_even_anticommutes
  have hfilter :
      (Finset.univ.filter
            (NQubitPauliGroupElement.anticommutesAt (n := 4)
              logicalZ.operators S_X1.operators)) =
        ({0, 2} : Finset (Fin 4)) := by
    ext i; fin_cases i <;>
      simp [Finset.mem_filter, NQubitPauliGroupElement.anticommutesAt, logicalZ, S_X1,
        NQubitPauliOperator.set, NQubitPauliOperator.identity, PauliOperator.mulOp]
  rw [hfilter]; decide

/-- `X̄ = XXII` commutes with every element of the stabilizer. -/
theorem logicalX_mem_centralizer :
    logicalX ∈ centralizer stabilizerGroup := by
  rw [StabilizerGroup.mem_centralizer_iff_closure _ _ _ stabilizerGroup_toSubgroup_eq]
  intro s hs
  simp only [generatorsList, listToSet_cons, listToSet_nil, Set.mem_insert_iff,
    Set.mem_empty_iff_false, or_false] at hs
  rcases hs with rfl | rfl | rfl
  · exact logicalX_commutes_S_Z1.symm
  · exact logicalX_commutes_S_Z2.symm
  · exact logicalX_commutes_S_X1.symm

/-- `Z̄ = ZIZI` commutes with every element of the stabilizer. -/
theorem logicalZ_mem_centralizer :
    logicalZ ∈ centralizer stabilizerGroup := by
  rw [StabilizerGroup.mem_centralizer_iff_closure _ _ _ stabilizerGroup_toSubgroup_eq]
  intro s hs
  simp only [generatorsList, listToSet_cons, listToSet_nil, Set.mem_insert_iff,
    Set.mem_empty_iff_false, or_false] at hs
  rcases hs with rfl | rfl | rfl
  · exact logicalZ_commutes_S_Z1.symm
  · exact logicalZ_commutes_S_Z2.symm
  · exact logicalZ_commutes_S_X1.symm

/-! ## §9 — `StabilizerCode 4 1` packaging -/

/-- The single-logical-qubit `LogicalQubitOps` bundle. -/
private noncomputable def logicalOpsCSS_4_1_2 : Fin 1 → LogicalQubitOps 4 stabilizerGroup :=
  fun _ => ⟨logicalX, logicalZ, logicalX_mem_centralizer, logicalZ_mem_centralizer,
            logicalX_anticommutes_logicalZ⟩

/-- The [[4, 1, 2]] LNCY code as a stabilizer code on 4 physical qubits with 1
logical qubit. -/
noncomputable def stabilizerCode : StabilizerCode 4 1 where
  hk := by decide
  generatorsList := generatorsList
  generators_length := rfl
  generators_phaseZero := AllPhaseZero_generatorsList
  generators_independent := GeneratorsIndependent_4_generatorsList
  generators_commute := generators_commute
  closure_no_neg_identity := negIdentity_not_mem

/-- The [[4, 1, 2]] LNCY code packaged with its logical pair
`(logicalX, logicalZ)`. -/
noncomputable def stabilizerCodeWithLogicals : StabilizerCodeWithLogicals 4 1 where
  toStabilizerCode := stabilizerCode
  logicalOps := logicalOpsCSS_4_1_2
  logical_commute_cross := fun ℓ ℓ' h => (h (Subsingleton.elim ℓ ℓ')).elim

/-! ## §10 — Code distance = 2 -/

/-- The stabilizer-code subgroup equals the closure of the generator list. -/
private lemma stabilizerCode_toSubgroup_eq :
    stabilizerCode.toStabilizerGroup.toSubgroup = Subgroup.closure (listToSet generatorsList) :=
  rfl

/-- Helper: a weight-1 Pauli with local Pauli `P ∈ {X, Y}` at qubit `i ∈ {0, 1}`
anticommutes with `S_Z1 = ZZII`. The proof shape mirrors
`FourQubit_4_2_2.weightOneAt_anticomm_Z1` but with the extra constraint
`i ∈ {0, 1}` (qubit indices where `S_Z1` has a Z), which we case-split on by
`rcases`. -/
private lemma weightOneAt_anticomm_S_Z1 (i : Fin 4) (P : PauliOperator)
    (hi : i = 0 ∨ i = 1)
    (hP : P = PauliOperator.X ∨ P = PauliOperator.Y) :
    NQubitPauliGroupElement.Anticommute (weightOneAt i P) S_Z1 := by
  classical
  pauli_anticomm_odd_anticommutes
  have hfilter :
      (Finset.univ.filter
            (NQubitPauliGroupElement.anticommutesAt (n := 4)
              (weightOneAt i P).operators S_Z1.operators)) =
        ({i} : Finset (Fin 4)) := by
    ext j; rcases hi with rfl | rfl <;> rcases hP with rfl | rfl <;> fin_cases j <;>
      simp [Finset.mem_filter, NQubitPauliGroupElement.anticommutesAt,
        weightOneAt, NQubitPauliGroupElement.ofOperator,
        S_Z1, NQubitPauliOperator.set, NQubitPauliOperator.identity, PauliOperator.mulOp]
  rw [hfilter]; simp +decide

/-- Helper: a weight-1 Pauli with local Pauli `P ∈ {X, Y}` at qubit `i ∈ {2, 3}`
anticommutes with `S_Z2 = IIZZ`. -/
private lemma weightOneAt_anticomm_S_Z2 (i : Fin 4) (P : PauliOperator)
    (hi : i = 2 ∨ i = 3)
    (hP : P = PauliOperator.X ∨ P = PauliOperator.Y) :
    NQubitPauliGroupElement.Anticommute (weightOneAt i P) S_Z2 := by
  classical
  pauli_anticomm_odd_anticommutes
  have hfilter :
      (Finset.univ.filter
            (NQubitPauliGroupElement.anticommutesAt (n := 4)
              (weightOneAt i P).operators S_Z2.operators)) =
        ({i} : Finset (Fin 4)) := by
    ext j; rcases hi with rfl | rfl <;> rcases hP with rfl | rfl <;> fin_cases j <;>
      simp [Finset.mem_filter, NQubitPauliGroupElement.anticommutesAt,
        weightOneAt, NQubitPauliGroupElement.ofOperator,
        S_Z2, NQubitPauliOperator.set, NQubitPauliOperator.identity, PauliOperator.mulOp]
  rw [hfilter]; simp +decide

/-- Helper: a weight-1 Pauli with local Pauli `Z` at any qubit `i` anticommutes
with `S_X1 = XXXX`. -/
private lemma weightOneAt_Z_anticomm_S_X1 (i : Fin 4) :
    NQubitPauliGroupElement.Anticommute (weightOneAt i PauliOperator.Z) S_X1 := by
  classical
  pauli_anticomm_odd_anticommutes
  have hfilter :
      (Finset.univ.filter
            (NQubitPauliGroupElement.anticommutesAt (n := 4)
              (weightOneAt i PauliOperator.Z).operators S_X1.operators)) =
        ({i} : Finset (Fin 4)) := by
    ext j; fin_cases i <;> fin_cases j <;>
      simp [Finset.mem_filter, NQubitPauliGroupElement.anticommutesAt,
        weightOneAt, NQubitPauliGroupElement.ofOperator,
        S_X1, NQubitPauliOperator.set, PauliOperator.mulOp]
  rw [hfilter]; simp +decide

/-- Anticommute witness for the [[4,1,2]] LNCY code: every weight-1 Pauli
anticommutes with one of `S_Z1`, `S_Z2`, or `S_X1`. The Z-side splits on
`i ∈ {0, 1}` (use `S_Z1`) vs. `i ∈ {2, 3}` (use `S_Z2`). -/
private lemma weight_one_anticomm_witness :
    ∀ i : Fin 4, ∀ P : PauliOperator, P ≠ PauliOperator.I →
      ∃ g ∈ listToSet generatorsList, NQubitPauliGroupElement.Anticommute
        (weightOneAt i P) g := by
  intro i P hP
  -- Dispatch the i ∈ {0,1} vs i ∈ {2,3} split once, reusable across P = X, P = Y.
  have hi_dichotomy : (i = 0 ∨ i = 1) ∨ (i = 2 ∨ i = 3) := by
    fin_cases i <;> tauto
  match P, hP with
  | PauliOperator.X, _ =>
    rcases hi_dichotomy with hi | hi
    · exact ⟨S_Z1, by simp [generatorsList],
        weightOneAt_anticomm_S_Z1 i _ hi (Or.inl rfl)⟩
    · exact ⟨S_Z2, by simp [generatorsList],
        weightOneAt_anticomm_S_Z2 i _ hi (Or.inl rfl)⟩
  | PauliOperator.Y, _ =>
    rcases hi_dichotomy with hi | hi
    · exact ⟨S_Z1, by simp [generatorsList],
        weightOneAt_anticomm_S_Z1 i _ hi (Or.inr rfl)⟩
    · exact ⟨S_Z2, by simp [generatorsList],
        weightOneAt_anticomm_S_Z2 i _ hi (Or.inr rfl)⟩
  | PauliOperator.Z, _ =>
    exact ⟨S_X1, by simp [generatorsList], weightOneAt_Z_anticomm_S_X1 i⟩
  | PauliOperator.I, hP => exact (hP rfl).elim

/-- The [[4, 1, 2]] LNCY code has distance 2: every weight-1 single-qubit Pauli
anticommutes with at least one stabilizer generator, and `X̄ = XXII` is a
nontrivial logical operator of weight exactly 2. -/
theorem code_has_distance_two : HasCodeDistance stabilizerCode 2 :=
  hasCodeDistance_two_of_anticommute_witness stabilizerCode (listToSet generatorsList)
    stabilizerCode_toSubgroup_eq weight_one_anticomm_witness
    ⟨logicalX, (logicalOpsCSS_4_1_2 0).xOp_nontrivial, by decide⟩

/-- The [[4, 1, 2]] LNCY code packaged with its distance. -/
noncomputable def stabilizerCodeWithDistance : StabilizerCodeWithDistance 4 1 2 where
  toStabilizerCode := stabilizerCode
  hasDistance      := code_has_distance_two

end CSS_4_1_2
end StabilizerGroup
end Quantum
