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
namespace SixQubit_6_2_2

/-!
# The [[6, 2, 2]] `C_6` code (Knill 2004)

A six-qubit normal self-dual CSS stabilizer code encoding **two logical qubits**
with code distance 2. Originally introduced in [E. Knill, *Quantum computing
with realistically noisy devices*, Nature 434, 39 (2005);
`arxiv:quant-ph/0410199`], where it serves as the outer code in Knill's C_4/C_6
fault-tolerant architecture (with `[[4,2,2]]` at the inner level).

## Stabilizer tableau (Knill / EC Zoo / Qiskit preset ID 126)

```
S_Z1 = Z Z Z Z I I
S_Z2 = Z Z I I Z Z
S_X1 = X X X X I I
S_X2 = X X I I X X
```

Uniform-weight-4 generators; n − k = 4. Each stabilizer corresponds to a square
face of a triangular-prism ladder (3 rungs, periodic boundary).

## Logical operators (Knill 2004 via EC Zoo)

```
X̄_1 = I I X X I I   (= X_L, weight 2, support {2,3})
Z̄_1 = Z I I Z Z I   (= Z_L, weight 3, support {0,3,4})
X̄_2 = I X I X X I   (= X_S, weight 3, support {1,3,4})
Z̄_2 = I I I I Z Z   (= Z_S, weight 2, support {4,5})
```

Anticommutation table: `X̄_1` anticomm `Z̄_1` (overlap {3}, odd), `X̄_2`
anticomm `Z̄_2` (overlap {4}, odd); all other pairwise logical products commute
(cross-pairs have even overlap, same-X / same-Z trivially).

## Equivalence notes

- The Ganti-Onunkwo-Young (GOY) code at r = 1 is the C_6 code (different
  family-presentation; not formalized here).
- The [[k+4, k, 2]] H code at k = 2 is the C_6 code.
- The Khesin-Lu-Shor code at r = 2, m = 3 is the C_6 code.
- The [[4, 2, 2]] code (`FourQubit_4_2_2.lean`) is C_6's structural sibling in
  Knill's C_4/C_6 concatenation; we copy that file's k = 2 logical packaging
  pattern.

## Outline (decide route)

- §1 generators, §2 the generator list
- §3 decided hypotheses: pairwise commutation, phase zero, independence
- §4 `−I ∉ closure`, §5 the bundled `StabilizerGroup 6`
- §6–§8 logical operators, their (anti)commutation, centralizer membership
- §9 `StabilizerCode 6 2` + `StabilizerCodeWithLogicals 6 2`
- §10 distance 2 (weight-1 anti-witness with a three-way qubit partition)
-/

open NQubitPauliGroupElement

/-! ## §1 — Generators

The four Knill stabilizers of C_6. All have phase 0 and uniform weight 4. Qubit
indexing is 0-based; qubits 0,1 are the "top" pair, 2,3 the "middle" pair, 4,5
the "bottom" pair.
-/

/-- First Z-check stabilizer: `Z Z Z Z I I` (Z on qubits 0,1,2,3). -/
def S_Z1 : NQubitPauliGroupElement 6 := σ[ZZZZII]

/-- Second Z-check stabilizer: `Z Z I I Z Z` (Z on qubits 0,1,4,5). -/
def S_Z2 : NQubitPauliGroupElement 6 := σ[ZZIIZZ]

/-- First X-check stabilizer: `X X X X I I` (X on qubits 0,1,2,3). -/
def S_X1 : NQubitPauliGroupElement 6 := σ[XXXXII]

/-- Second X-check stabilizer: `X X I I X X` (X on qubits 0,1,4,5). -/
def S_X2 : NQubitPauliGroupElement 6 := σ[XXIIXX]

/-! ## §2 — Generator list -/

/-- The generator list (canonical order: Z-checks first, then X-checks). -/
def generatorsList : List (NQubitPauliGroupElement 6) :=
  [S_Z1, S_Z2, S_X1, S_X2]

/-! ## §3 — Decided hypotheses

Pairwise overlap counts (all even ⇒ all commute):
- `S_Z1 = ZZZZ II` vs `S_X1 = XXXX II`: anti at {0,1,2,3}, count 4.
- `S_Z1` vs `S_X2 = XX II XX`: anti at {0,1}, count 2.
- `S_Z2 = ZZ II ZZ` vs `S_X1`: anti at {0,1}, count 2.
- `S_Z2` vs `S_X2`: anti at {0,1,4,5}, count 4.

`decide` checks the sixteen ordered pairs, the phases, and the check-matrix
rank. -/

/-- All generators of the [[6, 2, 2]] code pairwise commute. -/
theorem generators_commute :
    ∀ g ∈ listToSet generatorsList, ∀ h ∈ listToSet generatorsList, g * h = h * g := by
  decide

/-- All four generators have phase 0 (no `i` or `−1` factor). -/
lemma AllPhaseZero_generatorsList : AllPhaseZero generatorsList := by
  decide

/-- The check-matrix rows of the four generators are linearly independent over
GF(2). -/
theorem rowsLinearIndependent_generatorsList :
    rowsLinearIndependent generatorsList := by decide

/-- The generator list is an independent generating set. -/
theorem GeneratorsIndependent_6_generatorsList :
    GeneratorsIndependent 6 generatorsList :=
  GeneratorsIndependent_of_rowsLinearIndependent rowsLinearIndependent_generatorsList

/-! ## §4 — `−I` is not in the stabilizer subgroup -/

/-- The closure of the four Knill generators does not contain `−I`. -/
theorem negIdentity_not_mem :
    negIdentity 6 ∉ Subgroup.closure (listToSet generatorsList) :=
  negIdentity_not_mem_of_indep_phase_zero_commute generatorsList
    AllPhaseZero_generatorsList rowsLinearIndependent_generatorsList generators_commute

/-! ## §5 — Bundled `StabilizerGroup 6` -/

/-- The [[6, 2, 2]] C_6 stabilizer group, from the generator list. -/
noncomputable def stabilizerGroup : StabilizerGroup 6 :=
  mkStabilizerFromGenerators 6 generatorsList generators_commute negIdentity_not_mem

/-- The bundled stabilizer group's underlying subgroup is the closure of the
generator list. -/
lemma stabilizerGroup_toSubgroup_eq :
    stabilizerGroup.toSubgroup = Subgroup.closure (listToSet generatorsList) := rfl

/-! ## §6 — Logical operators

The four logical operators per Knill 2004 (via EC Zoo `stab_6_2_2`):

```
X̄_1 = IIXXII   (= X_L, Knill "L" pair)
Z̄_1 = ZIIZZI   (= Z_L, Knill "L" pair)
X̄_2 = IXIXXI   (= X_S, Knill "S" pair)
Z̄_2 = IIIIZZ   (= Z_S, Knill "S" pair)
```

Indexing: `_1` ≡ Knill's "L" (long support on Z, short on X); `_2` ≡ Knill's "S"
(short support on Z, mid support on X).
-/

/-- Logical X for logical qubit 1: `IIXXII` (X on qubits 2, 3). -/
def logicalX_1 : NQubitPauliGroupElement 6 := σ[IIXXII]

/-- Logical X for logical qubit 2: `IXIXXI` (X on qubits 1, 3, 4). -/
def logicalX_2 : NQubitPauliGroupElement 6 := σ[IXIXXI]

/-- Logical Z for logical qubit 1: `ZIIZZI` (Z on qubits 0, 3, 4). -/
def logicalZ_1 : NQubitPauliGroupElement 6 := σ[ZIIZZI]

/-- Logical Z for logical qubit 2: `IIIIZZ` (Z on qubits 4, 5). -/
def logicalZ_2 : NQubitPauliGroupElement 6 := σ[IIIIZZ]

/-! ### Diagonal anticommutation: X̄_ℓ anticommutes Z̄_ℓ -/

/-- `X̄_1 = IIXXII` and `Z̄_1 = ZIIZZI` anticommute (overlap at qubit 3 only —
odd parity). -/
theorem logicalX_1_anticommutes_logicalZ_1 :
    NQubitPauliGroupElement.Anticommute logicalX_1 logicalZ_1 := by
  classical
  pauli_anticomm_odd_anticommutes
  have hfilter :
      (Finset.univ.filter
            (NQubitPauliGroupElement.anticommutesAt (n := 6)
              logicalX_1.operators logicalZ_1.operators)) =
        ({3} : Finset (Fin 6)) := by
    ext i; fin_cases i <;>
      simp [Finset.mem_filter, NQubitPauliGroupElement.anticommutesAt, logicalX_1, logicalZ_1,
        NQubitPauliOperator.set, NQubitPauliOperator.identity, PauliOperator.mulOp]
  rw [hfilter]; decide

/-- `X̄_2 = IXIXXI` and `Z̄_2 = IIIIZZ` anticommute (overlap at qubit 4 only —
odd parity). -/
theorem logicalX_2_anticommutes_logicalZ_2 :
    NQubitPauliGroupElement.Anticommute logicalX_2 logicalZ_2 := by
  classical
  pauli_anticomm_odd_anticommutes
  have hfilter :
      (Finset.univ.filter
            (NQubitPauliGroupElement.anticommutesAt (n := 6)
              logicalX_2.operators logicalZ_2.operators)) =
        ({4} : Finset (Fin 6)) := by
    ext i; fin_cases i <;>
      simp [Finset.mem_filter, NQubitPauliGroupElement.anticommutesAt, logicalX_2, logicalZ_2,
        NQubitPauliOperator.set, NQubitPauliOperator.identity, PauliOperator.mulOp]
  rw [hfilter]; decide

/-! ### Off-diagonal logical commutation (the k = 2 novelty) -/

/-- `X̄_1 = IIXXII` and `X̄_2 = IXIXXI` commute (both X-type — trivial). -/
theorem logicalX_1_commutes_logicalX_2 :
    logicalX_1 * logicalX_2 = logicalX_2 * logicalX_1 := by
  pauli_comm_componentwise [logicalX_1, logicalX_2]

/-- `X̄_1 = IIXXII` and `Z̄_2 = IIIIZZ` commute (disjoint supports {2,3} vs
{4,5} — empty overlap). -/
theorem logicalX_1_commutes_logicalZ_2 :
    logicalX_1 * logicalZ_2 = logicalZ_2 * logicalX_1 := by
  pauli_comm_componentwise [logicalX_1, logicalZ_2]

/-- `X̄_2 = IXIXXI` and `Z̄_1 = ZIIZZI` commute (anticommute at qubits 3,4;
count 2). -/
theorem logicalX_2_commutes_logicalZ_1 :
    logicalX_2 * logicalZ_1 = logicalZ_1 * logicalX_2 := by
  classical
  pauli_comm_even_anticommutes
  have hfilter :
      (Finset.univ.filter
            (NQubitPauliGroupElement.anticommutesAt (n := 6)
              logicalX_2.operators logicalZ_1.operators)) =
        ({3, 4} : Finset (Fin 6)) := by
    ext i; fin_cases i <;>
      simp [Finset.mem_filter, NQubitPauliGroupElement.anticommutesAt, logicalX_2, logicalZ_1,
        NQubitPauliOperator.set, NQubitPauliOperator.identity, PauliOperator.mulOp]
  rw [hfilter]; decide

/-- `Z̄_1 = ZIIZZI` and `Z̄_2 = IIIIZZ` commute (both Z-type — trivial). -/
theorem logicalZ_1_commutes_logicalZ_2 :
    logicalZ_1 * logicalZ_2 = logicalZ_2 * logicalZ_1 := by
  pauli_comm_componentwise [logicalZ_1, logicalZ_2]

/-! ### Logical operators are in the centralizer

Per-generator commutation lemmas (16 total: 4 logicals × 4 generators). Each is
either `pauli_comm_componentwise` (when both factors are same-type or have
disjoint supports) or `pauli_comm_even_anticommutes` with an explicit filter
Finset. Supports of the filter Finsets:

| Logical \ Gen | `S_Z1` (q0,1,2,3) | `S_Z2` (q0,1,4,5) | `S_X1` (q0,1,2,3) | `S_X2` (q0,1,4,5) |
|---------------|-------------------|-------------------|-------------------|-------------------|
| `X̄_1=IIXXII` (q2,3) | {2,3}, 2 | ∅, 0 | both X | both X |
| `X̄_2=IXIXXI` (q1,3,4) | {1,3}, 2 | {1,4}, 2 | both X | both X |
| `Z̄_1=ZIIZZI` (q0,3,4) | both Z | both Z | {0,3}, 2 | {0,4}, 2 |
| `Z̄_2=IIIIZZ` (q4,5) | both Z | both Z | ∅, 0 | {4,5}, 2 |
-/

private lemma logicalX_1_commutes_S_Z1 : logicalX_1 * S_Z1 = S_Z1 * logicalX_1 := by
  classical
  pauli_comm_even_anticommutes
  have hfilter :
      (Finset.univ.filter
            (NQubitPauliGroupElement.anticommutesAt (n := 6)
              logicalX_1.operators S_Z1.operators)) =
        ({2, 3} : Finset (Fin 6)) := by
    ext i; fin_cases i <;>
      simp [Finset.mem_filter, NQubitPauliGroupElement.anticommutesAt, logicalX_1, S_Z1,
        NQubitPauliOperator.set, NQubitPauliOperator.identity, PauliOperator.mulOp]
  rw [hfilter]; decide

private lemma logicalX_1_commutes_S_Z2 : logicalX_1 * S_Z2 = S_Z2 * logicalX_1 := by
  pauli_comm_componentwise [logicalX_1, S_Z2]

private lemma logicalX_1_commutes_S_X1 : logicalX_1 * S_X1 = S_X1 * logicalX_1 := by
  pauli_comm_componentwise [logicalX_1, S_X1]

private lemma logicalX_1_commutes_S_X2 : logicalX_1 * S_X2 = S_X2 * logicalX_1 := by
  pauli_comm_componentwise [logicalX_1, S_X2]

private lemma logicalX_2_commutes_S_Z1 : logicalX_2 * S_Z1 = S_Z1 * logicalX_2 := by
  classical
  pauli_comm_even_anticommutes
  have hfilter :
      (Finset.univ.filter
            (NQubitPauliGroupElement.anticommutesAt (n := 6)
              logicalX_2.operators S_Z1.operators)) =
        ({1, 3} : Finset (Fin 6)) := by
    ext i; fin_cases i <;>
      simp [Finset.mem_filter, NQubitPauliGroupElement.anticommutesAt, logicalX_2, S_Z1,
        NQubitPauliOperator.set, NQubitPauliOperator.identity, PauliOperator.mulOp]
  rw [hfilter]; decide

private lemma logicalX_2_commutes_S_Z2 : logicalX_2 * S_Z2 = S_Z2 * logicalX_2 := by
  classical
  pauli_comm_even_anticommutes
  have hfilter :
      (Finset.univ.filter
            (NQubitPauliGroupElement.anticommutesAt (n := 6)
              logicalX_2.operators S_Z2.operators)) =
        ({1, 4} : Finset (Fin 6)) := by
    ext i; fin_cases i <;>
      simp [Finset.mem_filter, NQubitPauliGroupElement.anticommutesAt, logicalX_2, S_Z2,
        NQubitPauliOperator.set, NQubitPauliOperator.identity, PauliOperator.mulOp]
  rw [hfilter]; decide

private lemma logicalX_2_commutes_S_X1 : logicalX_2 * S_X1 = S_X1 * logicalX_2 := by
  pauli_comm_componentwise [logicalX_2, S_X1]

private lemma logicalX_2_commutes_S_X2 : logicalX_2 * S_X2 = S_X2 * logicalX_2 := by
  pauli_comm_componentwise [logicalX_2, S_X2]

private lemma logicalZ_1_commutes_S_Z1 : logicalZ_1 * S_Z1 = S_Z1 * logicalZ_1 := by
  pauli_comm_componentwise [logicalZ_1, S_Z1]

private lemma logicalZ_1_commutes_S_Z2 : logicalZ_1 * S_Z2 = S_Z2 * logicalZ_1 := by
  pauli_comm_componentwise [logicalZ_1, S_Z2]

private lemma logicalZ_1_commutes_S_X1 : logicalZ_1 * S_X1 = S_X1 * logicalZ_1 := by
  classical
  pauli_comm_even_anticommutes
  have hfilter :
      (Finset.univ.filter
            (NQubitPauliGroupElement.anticommutesAt (n := 6)
              logicalZ_1.operators S_X1.operators)) =
        ({0, 3} : Finset (Fin 6)) := by
    ext i; fin_cases i <;>
      simp [Finset.mem_filter, NQubitPauliGroupElement.anticommutesAt, logicalZ_1, S_X1,
        NQubitPauliOperator.set, NQubitPauliOperator.identity, PauliOperator.mulOp]
  rw [hfilter]; decide

private lemma logicalZ_1_commutes_S_X2 : logicalZ_1 * S_X2 = S_X2 * logicalZ_1 := by
  classical
  pauli_comm_even_anticommutes
  have hfilter :
      (Finset.univ.filter
            (NQubitPauliGroupElement.anticommutesAt (n := 6)
              logicalZ_1.operators S_X2.operators)) =
        ({0, 4} : Finset (Fin 6)) := by
    ext i; fin_cases i <;>
      simp [Finset.mem_filter, NQubitPauliGroupElement.anticommutesAt, logicalZ_1, S_X2,
        NQubitPauliOperator.set, NQubitPauliOperator.identity, PauliOperator.mulOp]
  rw [hfilter]; decide

private lemma logicalZ_2_commutes_S_Z1 : logicalZ_2 * S_Z1 = S_Z1 * logicalZ_2 := by
  pauli_comm_componentwise [logicalZ_2, S_Z1]

private lemma logicalZ_2_commutes_S_Z2 : logicalZ_2 * S_Z2 = S_Z2 * logicalZ_2 := by
  pauli_comm_componentwise [logicalZ_2, S_Z2]

private lemma logicalZ_2_commutes_S_X1 : logicalZ_2 * S_X1 = S_X1 * logicalZ_2 := by
  pauli_comm_componentwise [logicalZ_2, S_X1]

private lemma logicalZ_2_commutes_S_X2 : logicalZ_2 * S_X2 = S_X2 * logicalZ_2 := by
  classical
  pauli_comm_even_anticommutes
  have hfilter :
      (Finset.univ.filter
            (NQubitPauliGroupElement.anticommutesAt (n := 6)
              logicalZ_2.operators S_X2.operators)) =
        ({4, 5} : Finset (Fin 6)) := by
    ext i; fin_cases i <;>
      simp [Finset.mem_filter, NQubitPauliGroupElement.anticommutesAt, logicalZ_2, S_X2,
        NQubitPauliOperator.set, NQubitPauliOperator.identity, PauliOperator.mulOp]
  rw [hfilter]; decide

/-- `X̄_1 = IIXXII` commutes with every element of the stabilizer. -/
theorem logicalX_1_mem_centralizer :
    logicalX_1 ∈ centralizer stabilizerGroup := by
  rw [StabilizerGroup.mem_centralizer_iff_closure _ _ _ stabilizerGroup_toSubgroup_eq]
  intro s hs
  simp only [generatorsList, listToSet_cons, listToSet_nil, Set.mem_insert_iff,
    Set.mem_empty_iff_false, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl
  · exact logicalX_1_commutes_S_Z1.symm
  · exact logicalX_1_commutes_S_Z2.symm
  · exact logicalX_1_commutes_S_X1.symm
  · exact logicalX_1_commutes_S_X2.symm

/-- `X̄_2 = IXIXXI` commutes with every element of the stabilizer. -/
theorem logicalX_2_mem_centralizer :
    logicalX_2 ∈ centralizer stabilizerGroup := by
  rw [StabilizerGroup.mem_centralizer_iff_closure _ _ _ stabilizerGroup_toSubgroup_eq]
  intro s hs
  simp only [generatorsList, listToSet_cons, listToSet_nil, Set.mem_insert_iff,
    Set.mem_empty_iff_false, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl
  · exact logicalX_2_commutes_S_Z1.symm
  · exact logicalX_2_commutes_S_Z2.symm
  · exact logicalX_2_commutes_S_X1.symm
  · exact logicalX_2_commutes_S_X2.symm

/-- `Z̄_1 = ZIIZZI` commutes with every element of the stabilizer. -/
theorem logicalZ_1_mem_centralizer :
    logicalZ_1 ∈ centralizer stabilizerGroup := by
  rw [StabilizerGroup.mem_centralizer_iff_closure _ _ _ stabilizerGroup_toSubgroup_eq]
  intro s hs
  simp only [generatorsList, listToSet_cons, listToSet_nil, Set.mem_insert_iff,
    Set.mem_empty_iff_false, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl
  · exact logicalZ_1_commutes_S_Z1.symm
  · exact logicalZ_1_commutes_S_Z2.symm
  · exact logicalZ_1_commutes_S_X1.symm
  · exact logicalZ_1_commutes_S_X2.symm

/-- `Z̄_2 = IIIIZZ` commutes with every element of the stabilizer. -/
theorem logicalZ_2_mem_centralizer :
    logicalZ_2 ∈ centralizer stabilizerGroup := by
  rw [StabilizerGroup.mem_centralizer_iff_closure _ _ _ stabilizerGroup_toSubgroup_eq]
  intro s hs
  simp only [generatorsList, listToSet_cons, listToSet_nil, Set.mem_insert_iff,
    Set.mem_empty_iff_false, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl
  · exact logicalZ_2_commutes_S_Z1.symm
  · exact logicalZ_2_commutes_S_Z2.symm
  · exact logicalZ_2_commutes_S_X1.symm
  · exact logicalZ_2_commutes_S_X2.symm

/-! ## §9 — `StabilizerCode 6 2` packaging -/

/-- The two-logical-qubit `LogicalQubitOps` family. -/
private def logicalOps6_2_2 : Fin 2 → LogicalQubitOps 6 stabilizerGroup := fun ℓ =>
  match ℓ with
  | 0 => ⟨logicalX_1, logicalZ_1,
            logicalX_1_mem_centralizer, logicalZ_1_mem_centralizer,
            logicalX_1_anticommutes_logicalZ_1⟩
  | 1 => ⟨logicalX_2, logicalZ_2,
            logicalX_2_mem_centralizer, logicalZ_2_mem_centralizer,
            logicalX_2_anticommutes_logicalZ_2⟩

/-- The [[6, 2, 2]] C_6 code as a stabilizer code on 6 physical qubits with 2
logical qubits. -/
noncomputable def stabilizerCode : StabilizerCode 6 2 where
  hk := by decide
  generatorsList := generatorsList
  generators_length := rfl
  generators_phaseZero := AllPhaseZero_generatorsList
  generators_independent := GeneratorsIndependent_6_generatorsList
  generators_commute := generators_commute
  closure_no_neg_identity := negIdentity_not_mem

/-- The C_6 [[6, 2, 2]] code packaged with its logical basis `(X̄₁, Z̄₁)`,
`(X̄₂, Z̄₂)` (`logicalX_1`/`logicalZ_1`, `logicalX_2`/`logicalZ_2`). -/
noncomputable def stabilizerCodeWithLogicals : StabilizerCodeWithLogicals 6 2 where
  toStabilizerCode := stabilizerCode
  logicalOps := logicalOps6_2_2
  logical_commute_cross := by
    intro ℓ ℓ' hne
    fin_cases ℓ <;> fin_cases ℓ'
    · exact (hne rfl).elim
    · refine ⟨logicalX_1_commutes_logicalX_2, logicalX_1_commutes_logicalZ_2, ?_, ?_⟩
      · exact logicalX_2_commutes_logicalZ_1.symm
      · exact logicalZ_1_commutes_logicalZ_2
    · refine ⟨logicalX_1_commutes_logicalX_2.symm, logicalX_2_commutes_logicalZ_1, ?_, ?_⟩
      · exact logicalX_1_commutes_logicalZ_2.symm
      · exact logicalZ_1_commutes_logicalZ_2.symm
    · exact (hne rfl).elim

/-! ## §10 — Code distance = 2 -/

/-- The stabilizer-code subgroup equals the closure of the generator list. -/
private lemma stabilizerCode_toSubgroup_eq :
    stabilizerCode.toStabilizerGroup.toSubgroup = Subgroup.closure (listToSet generatorsList) :=
  rfl

/-- Helper: a weight-1 Pauli with local Pauli `P ∈ {X, Y}` at qubit
`i ∈ {0,1,2,3}` (the support of `S_Z1`) anticommutes with `S_Z1 = ZZZZ II`. -/
private lemma weightOneAt_anticomm_S_Z1 (i : Fin 6) (P : PauliOperator)
    (hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3)
    (hP : P = PauliOperator.X ∨ P = PauliOperator.Y) :
    NQubitPauliGroupElement.Anticommute (weightOneAt i P) S_Z1 := by
  classical
  pauli_anticomm_odd_anticommutes
  have hfilter :
      (Finset.univ.filter
            (NQubitPauliGroupElement.anticommutesAt (n := 6)
              (weightOneAt i P).operators S_Z1.operators)) =
        ({i} : Finset (Fin 6)) := by
    ext j
    rcases hi with rfl | rfl | rfl | rfl <;> rcases hP with rfl | rfl <;> fin_cases j <;>
      simp [Finset.mem_filter, NQubitPauliGroupElement.anticommutesAt,
        weightOneAt, NQubitPauliGroupElement.ofOperator,
        S_Z1, NQubitPauliOperator.set, NQubitPauliOperator.identity, PauliOperator.mulOp]
  rw [hfilter]; simp +decide

/-- Helper: a weight-1 Pauli with local Pauli `P ∈ {X, Y}` at qubit
`i ∈ {0,1,4,5}` (the support of `S_Z2`) anticommutes with `S_Z2 = ZZ II ZZ`. -/
private lemma weightOneAt_anticomm_S_Z2 (i : Fin 6) (P : PauliOperator)
    (hi : i = 0 ∨ i = 1 ∨ i = 4 ∨ i = 5)
    (hP : P = PauliOperator.X ∨ P = PauliOperator.Y) :
    NQubitPauliGroupElement.Anticommute (weightOneAt i P) S_Z2 := by
  classical
  pauli_anticomm_odd_anticommutes
  have hfilter :
      (Finset.univ.filter
            (NQubitPauliGroupElement.anticommutesAt (n := 6)
              (weightOneAt i P).operators S_Z2.operators)) =
        ({i} : Finset (Fin 6)) := by
    ext j
    rcases hi with rfl | rfl | rfl | rfl <;> rcases hP with rfl | rfl <;> fin_cases j <;>
      simp [Finset.mem_filter, NQubitPauliGroupElement.anticommutesAt,
        weightOneAt, NQubitPauliGroupElement.ofOperator,
        S_Z2, NQubitPauliOperator.set, NQubitPauliOperator.identity, PauliOperator.mulOp]
  rw [hfilter]; simp +decide

/-- Helper: a weight-1 Pauli with local Pauli `Z` at qubit `i ∈ {0,1,2,3}` (the
support of `S_X1`) anticommutes with `S_X1 = XXXX II`. -/
private lemma weightOneAt_Z_anticomm_S_X1 (i : Fin 6)
    (hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) :
    NQubitPauliGroupElement.Anticommute (weightOneAt i PauliOperator.Z) S_X1 := by
  classical
  pauli_anticomm_odd_anticommutes
  have hfilter :
      (Finset.univ.filter
            (NQubitPauliGroupElement.anticommutesAt (n := 6)
              (weightOneAt i PauliOperator.Z).operators S_X1.operators)) =
        ({i} : Finset (Fin 6)) := by
    ext j
    rcases hi with rfl | rfl | rfl | rfl <;> fin_cases j <;>
      simp [Finset.mem_filter, NQubitPauliGroupElement.anticommutesAt,
        weightOneAt, NQubitPauliGroupElement.ofOperator,
        S_X1, NQubitPauliOperator.set, NQubitPauliOperator.identity, PauliOperator.mulOp]
  rw [hfilter]; simp +decide

/-- Helper: a weight-1 Pauli with local Pauli `Z` at qubit `i ∈ {0,1,4,5}` (the
support of `S_X2`) anticommutes with `S_X2 = XX II XX`. -/
private lemma weightOneAt_Z_anticomm_S_X2 (i : Fin 6)
    (hi : i = 0 ∨ i = 1 ∨ i = 4 ∨ i = 5) :
    NQubitPauliGroupElement.Anticommute (weightOneAt i PauliOperator.Z) S_X2 := by
  classical
  pauli_anticomm_odd_anticommutes
  have hfilter :
      (Finset.univ.filter
            (NQubitPauliGroupElement.anticommutesAt (n := 6)
              (weightOneAt i PauliOperator.Z).operators S_X2.operators)) =
        ({i} : Finset (Fin 6)) := by
    ext j
    rcases hi with rfl | rfl | rfl | rfl <;> fin_cases j <;>
      simp [Finset.mem_filter, NQubitPauliGroupElement.anticommutesAt,
        weightOneAt, NQubitPauliGroupElement.ofOperator,
        S_X2, NQubitPauliOperator.set, NQubitPauliOperator.identity, PauliOperator.mulOp]
  rw [hfilter]; simp +decide

/-- Anticommute witness for the C_6 code: every weight-1 Pauli anticommutes with
at least one stabilizer generator.

Strategy: 3-way `hi_trichotomy` partition of qubits ({0,1} | {2,3} | {4,5}),
dispatched on the local Pauli `P`:
- `P = X` or `P = Y`: pick a Z-stab.
  - `i ∈ {0,1}`: both `S_Z1` and `S_Z2` work; pick `S_Z1` canonically.
  - `i ∈ {2,3}`: only `S_Z1` covers; use it.
  - `i ∈ {4,5}`: only `S_Z2` covers; use it.
- `P = Z`: pick an X-stab — same partition.
  - `i ∈ {0,1}`: pick `S_X1` canonically.
  - `i ∈ {2,3}`: only `S_X1` covers.
  - `i ∈ {4,5}`: only `S_X2` covers.
-/
private lemma weight_one_anticomm_witness :
    ∀ i : Fin 6, ∀ P : PauliOperator, P ≠ PauliOperator.I →
      ∃ g ∈ listToSet generatorsList, NQubitPauliGroupElement.Anticommute
        (weightOneAt i P) g := by
  intro i P hP
  -- 3-way trichotomy: i ∈ {0,1} (both Z-stabs cover; pick S_Z1) |
  --                   i ∈ {2,3} (only S_Z1) | i ∈ {4,5} (only S_Z2).
  -- Dual partition holds for the X-stabs.
  have hi_trichotomy : (i = 0 ∨ i = 1) ∨ (i = 2 ∨ i = 3) ∨ (i = 4 ∨ i = 5) := by
    fin_cases i <;> tauto
  match P, hP with
  | PauliOperator.X, _ =>
    rcases hi_trichotomy with hi | hi | hi
    · -- i ∈ {0,1}: pick S_Z1 (also covers).
      refine ⟨S_Z1, by simp [generatorsList], ?_⟩
      exact weightOneAt_anticomm_S_Z1 i _
        (by rcases hi with rfl | rfl <;> tauto) (Or.inl rfl)
    · -- i ∈ {2,3}: pick S_Z1 (only one that covers).
      refine ⟨S_Z1, by simp [generatorsList], ?_⟩
      exact weightOneAt_anticomm_S_Z1 i _
        (by rcases hi with rfl | rfl <;> tauto) (Or.inl rfl)
    · -- i ∈ {4,5}: pick S_Z2 (only one that covers).
      refine ⟨S_Z2, by simp [generatorsList], ?_⟩
      exact weightOneAt_anticomm_S_Z2 i _
        (by rcases hi with rfl | rfl <;> tauto) (Or.inl rfl)
  | PauliOperator.Y, _ =>
    rcases hi_trichotomy with hi | hi | hi
    · refine ⟨S_Z1, by simp [generatorsList], ?_⟩
      exact weightOneAt_anticomm_S_Z1 i _
        (by rcases hi with rfl | rfl <;> tauto) (Or.inr rfl)
    · refine ⟨S_Z1, by simp [generatorsList], ?_⟩
      exact weightOneAt_anticomm_S_Z1 i _
        (by rcases hi with rfl | rfl <;> tauto) (Or.inr rfl)
    · refine ⟨S_Z2, by simp [generatorsList], ?_⟩
      exact weightOneAt_anticomm_S_Z2 i _
        (by rcases hi with rfl | rfl <;> tauto) (Or.inr rfl)
  | PauliOperator.Z, _ =>
    rcases hi_trichotomy with hi | hi | hi
    · -- i ∈ {0,1}: pick S_X1.
      refine ⟨S_X1, by simp [generatorsList], ?_⟩
      exact weightOneAt_Z_anticomm_S_X1 i (by rcases hi with rfl | rfl <;> tauto)
    · -- i ∈ {2,3}: pick S_X1 (only one that covers).
      refine ⟨S_X1, by simp [generatorsList], ?_⟩
      exact weightOneAt_Z_anticomm_S_X1 i (by rcases hi with rfl | rfl <;> tauto)
    · -- i ∈ {4,5}: pick S_X2 (only one that covers).
      refine ⟨S_X2, by simp [generatorsList], ?_⟩
      exact weightOneAt_Z_anticomm_S_X2 i (by rcases hi with rfl | rfl <;> tauto)
  | PauliOperator.I, hP => exact (hP rfl).elim

/-- The C_6 [[6, 2, 2]] code has distance 2: every weight-1 single-qubit Pauli
anticommutes with at least one stabilizer generator (T31), and `X̄_1 = IIXXII`
is a nontrivial logical operator of weight exactly 2. -/
theorem code_has_distance_two : HasCodeDistance stabilizerCode 2 :=
  hasCodeDistance_two_of_anticommute_witness stabilizerCode (listToSet generatorsList)
    stabilizerCode_toSubgroup_eq weight_one_anticomm_witness
    ⟨logicalX_1, (logicalOps6_2_2 0).xOp_nontrivial, by decide⟩

/-- The C_6 [[6, 2, 2]] code packaged with its distance. -/
noncomputable def stabilizerCodeWithDistance : StabilizerCodeWithDistance 6 2 2 where
  toStabilizerCode := stabilizerCode
  hasDistance      := code_has_distance_two

end SixQubit_6_2_2
end StabilizerGroup
end Quantum
