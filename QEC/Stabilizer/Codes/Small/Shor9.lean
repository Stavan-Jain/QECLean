import Mathlib.Tactic
import QEC.Stabilizer.Foundations.BinarySymplectic.CheckMatrixDecidable
import QEC.Stabilizer.Foundations.PauliGroup.Commutation
import QEC.Stabilizer.Foundations.PauliGroup.Notation
import QEC.Stabilizer.Framework.Core.CodeNotation
import QEC.Stabilizer.Framework.Core.CSS.CSSDistance
import QEC.Stabilizer.Framework.Core.Logical.CodeDistance
import QEC.Stabilizer.Framework.Core.Logical.LogicalOperators
import QEC.Stabilizer.Framework.Core.Stabilizer.StabilizerCode
import QEC.Stabilizer.Framework.Symplectic.Presentation
import QEC.Stabilizer.Framework.Symplectic.SymplecticSpan

/-!
# Shor's code `[[9, 1, 3]]`

Shor's nine-qubit code: a repetition code of cat states, a CSS stabilizer code
encoding one logical qubit, with code distance 3. The nine qubits form three
blocks `{0,1,2}`, `{3,4,5}`, `{6,7,8}`. Of the eight generators (`n − k = 8`),
six Z-checks `ZZ` on adjacent qubits of a block catch bit flips within the
block, and two X-checks, `X` on the first two blocks and on the last two,
compare the blocks' phases.

The code is packaged by the **decide route**: the eight generators form a
literal list, and pairwise commutation, phase zero and check-matrix
independence are closed statements settled by `decide`; `−I ∉ closure` follows
by `negIdentity_not_mem_of_indep_phase_zero_commute`.

Shor's code is *degenerate*: it has weight-two errors that no check detects,
yet its distance is three. The Z-checks form three length-3 repetition codes,
whose check matrix has nonzero, pairwise distinct columns, so every weight-one
or weight-two error with an `X`-component is caught. The two X-checks do not
separate qubits within a block, so `Z_i Z_j` on two qubits of one block
commutes with every check — but such a `Z_i Z_j` is itself a stabilizer (a `ZZ`
check, or the product of a block's two), so it is not a logical. Distance 3 is
`hasCodeDistance_three_of_columns_degenerate`, which is that argument; `X` on
the first block is a nontrivial logical of weight 3.

The logical basis `X̄ = Z⊗⁹`, `Z̄ = X⊗⁹` is in `Shor9Logicals.lean`.

## Outline

- Generators `Z1`–`Z6`, `X1`, `X2` and the list `generatorsList`
- Decided hypotheses: `generators_commute`, `AllPhaseZero_generatorsList`,
  `rowsLinearIndependent_generatorsList`
- `negIdentity_not_mem`, the bundled `stabilizerGroup`
- `presentation`, `stabilizerCode : Code[[9, 1]]`
- Distance 3 (degenerate column condition on `zRow` and `xRow`, weight-3
  logical): `code_has_distance_three`,
  `stabilizerCodeWithDistance : Code[[9, 1, 3]]`
-/

namespace Quantum
namespace StabilizerGroup
namespace Shor9

open NQubitPauliGroupElement
open scoped Pauli

/-! ## Generators -/

/-- First Z-check stabilizer: `ZZIIIIIII` (Z on qubits 0, 1 of the first
block). -/
def Z1 : NQubitPauliGroupElement 9 := σ[ZZIIIIIII]

/-- Second Z-check stabilizer: `IZZIIIIII` (Z on qubits 1, 2 of the first
block). -/
def Z2 : NQubitPauliGroupElement 9 := σ[IZZIIIIII]

/-- Third Z-check stabilizer: `IIIZZIIII` (Z on qubits 3, 4 of the second
block). -/
def Z3 : NQubitPauliGroupElement 9 := σ[IIIZZIIII]

/-- Fourth Z-check stabilizer: `IIIIZZIII` (Z on qubits 4, 5 of the second
block). -/
def Z4 : NQubitPauliGroupElement 9 := σ[IIIIZZIII]

/-- Fifth Z-check stabilizer: `IIIIIIZZI` (Z on qubits 6, 7 of the third
block). -/
def Z5 : NQubitPauliGroupElement 9 := σ[IIIIIIZZI]

/-- Sixth Z-check stabilizer: `IIIIIIIZZ` (Z on qubits 7, 8 of the third
block). -/
def Z6 : NQubitPauliGroupElement 9 := σ[IIIIIIIZZ]

/-- First X-check stabilizer: `XXXXXXIII` (X on the first two blocks). -/
def X1 : NQubitPauliGroupElement 9 := σ[XXXXXXIII]

/-- Second X-check stabilizer: `IIIXXXXXX` (X on the last two blocks). -/
def X2 : NQubitPauliGroupElement 9 := σ[IIIXXXXXX]

/-- The eight generators as a list (Z-checks first, then X-checks). -/
def generatorsList : List (NQubitPauliGroupElement 9) :=
  [Z1, Z2, Z3, Z4, Z5, Z6, X1, X2]

/-! ## Decided hypotheses

Each Z-check meets each X-check in either zero or two qubits, and same-type
generators commute componentwise. `decide` checks the 64 ordered pairs and the
phases. For the check-matrix rank, eight rows on nine qubits, plain `decide`
runs out of heartbeats, so the check is handed straight to the kernel with
`decide +kernel`. -/

/-- All eight generators pairwise commute. -/
lemma generators_commute :
    ∀ g ∈ listToSet generatorsList, ∀ h ∈ listToSet generatorsList, g * h = h * g := by
  decide

/-- Every generator has phase power 0. -/
lemma AllPhaseZero_generatorsList : AllPhaseZero generatorsList := by
  decide

/-- The check-matrix rows of the eight generators are linearly independent. -/
lemma rowsLinearIndependent_generatorsList : rowsLinearIndependent generatorsList := by
  decide +kernel

/-! ## No `−I` in the stabilizer subgroup -/

/-- The closure of the eight generators does not contain `−I`. -/
lemma negIdentity_not_mem : negIdentity 9 ∉ Subgroup.closure (listToSet generatorsList) :=
  negIdentity_not_mem_of_indep_phase_zero_commute generatorsList
    AllPhaseZero_generatorsList rowsLinearIndependent_generatorsList generators_commute

/-! ## Bundled `StabilizerGroup 9` -/

/-- The stabilizer group of Shor's code, generated by `generatorsList`. -/
noncomputable def stabilizerGroup : StabilizerGroup 9 :=
  mkStabilizerFromGenerators 9 generatorsList generators_commute negIdentity_not_mem

/-- The stabilizer subgroup is the closure of the generator list. -/
lemma stabilizerGroup_toSubgroup_eq :
    stabilizerGroup.toSubgroup = Subgroup.closure (listToSet generatorsList) := rfl

/-! ## The bare code `Code[[9, 1]]`

Eight independent, pairwise commuting generators on nine qubits: one logical
qubit. -/

/-- The generator list as a presentation of a `[[9, 1]]` code: its 8
check-matrix rows are linearly independent. -/
def presentation : StabilizerCode.Presentation 9 1 where
  hk := by decide
  generatorsList := generatorsList
  generators_length := rfl
  generators_phaseZero := AllPhaseZero_generatorsList
  generators_independent := rowsLinearIndependent_generatorsList
  generators_commute := generators_commute
  closure_no_neg_identity := negIdentity_not_mem

/-- Shor's code as a stabilizer code `[[9, 1]]`. -/
noncomputable def stabilizerCode : Code[[9, 1]] := presentation.toCode

/-- The stabilizer code's subgroup is the closure of the generator list. -/
lemma stabilizerCode_toSubgroup_eq :
    stabilizerCode.toStabilizerGroup.toSubgroup = Subgroup.closure (listToSet generatorsList) :=
  rfl

/-! ## Distance 3

### No nontrivial logical of weight 1 or 2

Present each check as the set of qubits it acts on. The Z-check matrix has
nonzero, pairwise distinct columns; the X-check matrix has nonzero columns,
but no X-row separates two qubits of the same block. For those pairs, `Z` on
the pair is a stabilizer. -/

/-- The supports of the six Z-checks: adjacent pairs within each block. -/
def zRow : Fin 6 → Finset (Fin 9) := ![{0, 1}, {1, 2}, {3, 4}, {4, 5}, {6, 7}, {7, 8}]

/-- The supports of the two X-checks: the first two blocks, and the last
two. -/
def xRow : Fin 2 → Finset (Fin 9) := ![{0, 1, 2, 3, 4, 5}, {3, 4, 5, 6, 7, 8}]

/-- `Z` on each Z-row is a generator. -/
lemma zOn_zRow_mem : ∀ r, zOn (zRow r) ∈ generatorsList := by decide

/-- `X` on each X-row is a generator. -/
lemma xOn_xRow_mem : ∀ c, xOn (xRow c) ∈ generatorsList := by decide

/-- Every qubit lies on some Z-row: no column is zero. -/
lemma zRow_cover : ∀ i : Fin 9, ∃ r, i ∈ zRow r := by decide

/-- Every qubit lies on some X-row: no column is zero. -/
lemma xRow_cover : ∀ i : Fin 9, ∃ c, i ∈ xRow c := by decide

/-- Any two distinct qubits are separated by some Z-row: no two columns
coincide. -/
lemma zRow_separate : ∀ i j : Fin 9, i ≠ j → ∃ r, (i ∈ zRow r ↔ j ∉ zRow r) := by decide

/-- Vacuously, `X` on any pair the Z-rows do not separate is a stabilizer:
there is no such pair. -/
lemma xOn_pair_mem (i j : Fin 9) (hij : i ≠ j) (h : ∀ r, i ∈ zRow r ↔ j ∈ zRow r) :
    xOn {i, j} ∈ Subgroup.closure (listToSet generatorsList) :=
  let ⟨r, hr⟩ := zRow_separate i j hij
  (iff_not_self ((h r).symm.trans hr)).elim

/-- `Z` on any pair the X-rows do not separate is a block check: a generator
`ZZ` on adjacent qubits, or the product of a block's two generators, `Z` on its
outer qubits. -/
lemma zOn_pair_mem_blockChecks : ∀ i j : Fin 9, i ≠ j → (∀ c, i ∈ xRow c ↔ j ∈ xRow c) →
    zOn {i, j} ∈ [Z1, Z2, Z1 * Z2, Z3, Z4, Z3 * Z4, Z5, Z6, Z5 * Z6] := by
  decide

/-- Every block check is a stabilizer. -/
lemma blockChecks_mem : ∀ s ∈ [Z1, Z2, Z1 * Z2, Z3, Z4, Z3 * Z4, Z5, Z6, Z5 * Z6],
    s ∈ Subgroup.closure (listToSet generatorsList) := by
  have h : ∀ g ∈ generatorsList, g ∈ Subgroup.closure (listToSet generatorsList) :=
    fun g hg => Subgroup.subset_closure hg
  simp only [generatorsList, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at h ⊢
  obtain ⟨h1, h2, h3, h4, h5, h6, -, -⟩ := h
  exact ⟨h1, h2, Subgroup.mul_mem _ h1 h2, h3, h4, Subgroup.mul_mem _ h3 h4, h5, h6,
    Subgroup.mul_mem _ h5 h6⟩

/-- `Z` on any pair the X-rows do not separate is a stabilizer. -/
lemma zOn_pair_mem (i j : Fin 9) (hij : i ≠ j) (h : ∀ c, i ∈ xRow c ↔ j ∈ xRow c) :
    zOn {i, j} ∈ Subgroup.closure (listToSet generatorsList) :=
  blockChecks_mem _ (zOn_pair_mem_blockChecks i j hij h)

/-! ### A nontrivial logical of weight 3

`X` on the first block `{0, 1, 2}` is `X⊗⁹ · X2`: it commutes with every check,
and it anticommutes with `Z` on one qubit per block, `{0, 3, 6}` (= `Z⊗⁹` times
the checks `Z2`, `Z4`, `Z6`), which also commutes with every check. -/

/-- `XXXIIIIII`: a nontrivial logical of weight 3. -/
def minWeightLogical : NQubitPauliGroupElement 9 := σ[XXXIIIIII]

/-- `ZIIZIIZII`: a centralizer element anticommuting with
`minWeightLogical`. -/
def minWeightPartner : NQubitPauliGroupElement 9 := σ[ZIIZIIZII]

/-- `XXXIIIIII` has weight 3. -/
lemma minWeightLogical_weight : weight minWeightLogical = 3 := by decide

/-- `XXXIIIIII` commutes with every element of the stabilizer. -/
lemma minWeightLogical_mem_centralizer : minWeightLogical ∈ centralizer stabilizerGroup :=
  mem_centralizer_of_commute_list stabilizerGroup_toSubgroup_eq (by decide)

/-- `ZIIZIIZII` commutes with every element of the stabilizer. -/
lemma minWeightPartner_mem_centralizer : minWeightPartner ∈ centralizer stabilizerGroup :=
  mem_centralizer_of_commute_list stabilizerGroup_toSubgroup_eq (by decide)

/-- `XXXIIIIII` and `ZIIZIIZII` meet on qubit 0 only, an odd number. -/
lemma minWeightLogical_anticommutes_minWeightPartner :
    Anticommute minWeightLogical minWeightPartner := by decide

/-- `XXXIIIIII` is a nontrivial logical operator: it lies in the centralizer
and anticommutes with the centralizer element `minWeightPartner`. -/
lemma minWeightLogical_isNontrivial :
    IsNontrivialLogicalOperator minWeightLogical stabilizerCode.toStabilizerGroup :=
  isNontrivialLogicalOperator_of_anticommute_centralizer _ minWeightLogical_mem_centralizer
    minWeightPartner_mem_centralizer minWeightLogical_anticommutes_minWeightPartner

/-! ### The code with its distance `Code[[9, 1, 3]]` -/

/-- **Shor's code has distance 3.** Both check matrices have nonzero columns,
the Z-check columns are pairwise distinct, and `Z` on any pair the X-checks
cannot separate is a stabilizer, so no Pauli of weight 1 or 2 is a nontrivial
logical; `XXXIIIIII` is one of weight 3. -/
theorem code_has_distance_three : HasCodeDistance stabilizerCode 3 :=
  hasCodeDistance_three_of_columns_degenerate zRow xRow (listToSet generatorsList) stabilizerCode
    stabilizerCode_toSubgroup_eq zOn_zRow_mem xOn_xRow_mem zRow_cover xRow_cover xOn_pair_mem
    zOn_pair_mem ⟨minWeightLogical, minWeightLogical_isNontrivial, minWeightLogical_weight⟩

/-- Shor's code packaged with its distance. -/
noncomputable def stabilizerCodeWithDistance : Code[[9, 1, 3]] where
  toStabilizerCode := stabilizerCode
  hasDistance := code_has_distance_three

end Shor9
end StabilizerGroup
end Quantum
