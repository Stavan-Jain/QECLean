import Mathlib.Tactic
import QEC.Stabilizer.Core.StabilizerGroup
import QEC.Stabilizer.Core.SubgroupLemmas
import QEC.Stabilizer.Core.Centralizer
import QEC.Stabilizer.Core.CodeDistance
import QEC.Stabilizer.Core.CSSDistance
import QEC.Stabilizer.Core.LogicalOperators
import QEC.Stabilizer.Core.StabilizerCode
import QEC.Stabilizer.PauliGroup.Commutation
import QEC.Stabilizer.PauliGroup.CommutationTactics
import QEC.Stabilizer.PauliGroup.NQubitOperator
import QEC.Stabilizer.PauliGroup.NQubitElement
import QEC.Stabilizer.BinarySymplectic.Core
import QEC.Stabilizer.BinarySymplectic.CheckMatrix
import QEC.Stabilizer.BinarySymplectic.CheckMatrixDecidable
import QEC.Stabilizer.BinarySymplectic.IndependentEquiv
import QEC.Stabilizer.BinarySymplectic.SymplecticInner
import QEC.Stabilizer.BinarySymplectic.SymplecticSpan

namespace Quantum
open scoped BigOperators

namespace StabilizerGroup
namespace FiveQubit_5_1_3

/-!
# The five-qubit perfect code [[5, 1, 3]] (Laflamme et al. 1996)

The smallest stabilizer code that corrects an arbitrary single-qubit error.
It encodes `k = 1` logical qubit in `n = 5` physical qubits with distance
`d = 3`, saturating the quantum Hamming bound.

## Stabilizer generators (cyclic shifts of XZZXI)

| Name | Pauli string |
|------|--------------|
| g₁   | `X Z Z X I`  |
| g₂   | `I X Z Z X`  |
| g₃   | `X I X Z Z`  |
| g₄   | `Z X I X Z`  |

## Logical operators

`X̄ = X X X X X`, `Z̄ = Z Z Z Z Z` (full-support, same as Steane7 / Shor9).

## Non-CSS divergence

This is the **first non-CSS code** in the repository. Each generator
contains both `X` and `Z` factors on different qubits, so it satisfies
neither `IsZTypeElement` nor `IsXTypeElement`. Consequently:

* §3 (typing predicates) — SKIPPED.
* §4–§5 (cross-commutation + all-pair commutation) — done as 6 explicit
  pairwise commutations, then bundled via `rcases` on the 4-element
  generator set. No CSS shortcut.
* §6 (`−I ∉ closure`) — uses `negIdentity_not_mem_of_independent_phase_zero`
  (a general-form helper introduced for this code; see `gap_audit.md`),
  *not* `CSS.negIdentity_not_mem_closure_union`.
* §14 (distance proof) — preferentially `native_decide` on full
  `HasCodeDistance`; if that fails, manual enumeration of weight-1
  (via existing helper) and weight-2 (via a new helper —
  `no_weight_two_mem_centralizer_of_anticommute_witness`).

## References

* Laflamme, Miquel, Paz, Zurek, `arxiv:quant-ph/9602019`
* Bennett, DiVincenzo, Smolin, Wootters, `arxiv:quant-ph/9604024`
* EC Zoo `stab_5_1_3`, cross-referenced with Qiskit `preset:qiskit ID 21`

This file is a **Stage-2 skeleton**: every theorem ends in a `sorry`
tagged `TODO(stab_5_1_3-T<n>): …`. Stage 4 closes them per the plan in
`pipeline/attempts/stab_5_1_3/plan.md`.
-/

open NQubitPauliGroupElement

/-! ## §1 — Generators (cyclic shifts of `XZZXI`) -/

/-- First generator: `X Z Z X I` (positions 0..4). -/
def g1 : NQubitPauliGroupElement 5 :=
  ⟨0,
    ((((NQubitPauliOperator.identity 5).set 0 PauliOperator.X).set 1 PauliOperator.Z).set 2
      PauliOperator.Z).set 3 PauliOperator.X⟩

/-- Second generator: `I X Z Z X` (cyclic shift of `g1` by 1). -/
def g2 : NQubitPauliGroupElement 5 :=
  ⟨0,
    ((((NQubitPauliOperator.identity 5).set 1 PauliOperator.X).set 2 PauliOperator.Z).set 3
      PauliOperator.Z).set 4 PauliOperator.X⟩

/-- Third generator: `X I X Z Z` (cyclic shift of `g1` by 2). -/
def g3 : NQubitPauliGroupElement 5 :=
  ⟨0,
    ((((NQubitPauliOperator.identity 5).set 0 PauliOperator.X).set 2 PauliOperator.X).set 3
      PauliOperator.Z).set 4 PauliOperator.Z⟩

/-- Fourth generator: `Z X I X Z` (cyclic shift of `g1` by 3). -/
def g4 : NQubitPauliGroupElement 5 :=
  ⟨0,
    ((((NQubitPauliOperator.identity 5).set 0 PauliOperator.Z).set 1 PauliOperator.X).set 3
      PauliOperator.X).set 4 PauliOperator.Z⟩

/-! ## §2 — Generator set and subgroup

Non-CSS: a single flat generator set, no `ZGenerators`/`XGenerators`
partition. -/

/-- The four stabilizer generators of the [[5, 1, 3]] code. -/
def generators : Set (NQubitPauliGroupElement 5) :=
  {g1, g2, g3, g4}

/-- The [[5, 1, 3]] stabilizer subgroup: closure of `{g1, g2, g3, g4}`. -/
noncomputable def subgroup : Subgroup (NQubitPauliGroupElement 5) :=
  Subgroup.closure generators

/-! ## §3 — Z/X-type predicates

SKIPPED: this is a non-CSS code. Each `gᵢ` carries both `X` and `Z`
factors on different qubits, so `IsZTypeElement` and `IsXTypeElement`
both fail.
-/

/-! ## §4 — Pairwise commutation of generators (6 unordered pairs)

Each pair has an even number of anticommuting qubit positions (count = 2
in every case — see `informal_spec.md` for the explicit Finsets).
Closed by `pauli_comm_even_anticommutes` + explicit Finset computation,
mirroring `Steane7.lean`'s `Zᵢ_comm_Xⱼ` pattern.
-/

private lemma g1_comm_g2 : g1 * g2 = g2 * g1 := by
  classical
  pauli_comm_even_anticommutes
  have hfilter :
      (Finset.univ.filter
            (NQubitPauliGroupElement.anticommutesAt (n := 5) g1.operators g2.operators)) =
        ({1, 3} : Finset (Fin 5)) := by
    ext i; fin_cases i <;>
      simp [Finset.mem_filter, NQubitPauliGroupElement.anticommutesAt, g1, g2,
        NQubitPauliOperator.set, NQubitPauliOperator.identity, PauliOperator.mulOp]
  rw [hfilter]; decide

private lemma g1_comm_g3 : g1 * g3 = g3 * g1 := by
  classical
  pauli_comm_even_anticommutes
  have hfilter :
      (Finset.univ.filter
            (NQubitPauliGroupElement.anticommutesAt (n := 5) g1.operators g3.operators)) =
        ({2, 3} : Finset (Fin 5)) := by
    ext i; fin_cases i <;>
      simp [Finset.mem_filter, NQubitPauliGroupElement.anticommutesAt, g1, g3,
        NQubitPauliOperator.set, NQubitPauliOperator.identity, PauliOperator.mulOp]
  rw [hfilter]; decide

private lemma g1_comm_g4 : g1 * g4 = g4 * g1 := by
  classical
  pauli_comm_even_anticommutes
  have hfilter :
      (Finset.univ.filter
            (NQubitPauliGroupElement.anticommutesAt (n := 5) g1.operators g4.operators)) =
        ({0, 1} : Finset (Fin 5)) := by
    ext i; fin_cases i <;>
      simp [Finset.mem_filter, NQubitPauliGroupElement.anticommutesAt, g1, g4,
        NQubitPauliOperator.set, NQubitPauliOperator.identity, PauliOperator.mulOp]
  rw [hfilter]; decide

private lemma g2_comm_g3 : g2 * g3 = g3 * g2 := by
  classical
  pauli_comm_even_anticommutes
  have hfilter :
      (Finset.univ.filter
            (NQubitPauliGroupElement.anticommutesAt (n := 5) g2.operators g3.operators)) =
        ({2, 4} : Finset (Fin 5)) := by
    ext i; fin_cases i <;>
      simp [Finset.mem_filter, NQubitPauliGroupElement.anticommutesAt, g2, g3,
        NQubitPauliOperator.set, NQubitPauliOperator.identity, PauliOperator.mulOp]
  rw [hfilter]; decide

private lemma g2_comm_g4 : g2 * g4 = g4 * g2 := by
  classical
  pauli_comm_even_anticommutes
  have hfilter :
      (Finset.univ.filter
            (NQubitPauliGroupElement.anticommutesAt (n := 5) g2.operators g4.operators)) =
        ({3, 4} : Finset (Fin 5)) := by
    ext i; fin_cases i <;>
      simp [Finset.mem_filter, NQubitPauliGroupElement.anticommutesAt, g2, g4,
        NQubitPauliOperator.set, NQubitPauliOperator.identity, PauliOperator.mulOp]
  rw [hfilter]; decide

private lemma g3_comm_g4 : g3 * g4 = g4 * g3 := by
  classical
  pauli_comm_even_anticommutes
  have hfilter :
      (Finset.univ.filter
            (NQubitPauliGroupElement.anticommutesAt (n := 5) g3.operators g4.operators)) =
        ({0, 3} : Finset (Fin 5)) := by
    ext i; fin_cases i <;>
      simp [Finset.mem_filter, NQubitPauliGroupElement.anticommutesAt, g3, g4,
        NQubitPauliOperator.set, NQubitPauliOperator.identity, PauliOperator.mulOp]
  rw [hfilter]; decide

/-! ## §5 — All-pair commutation (full stabilizer abelianness) -/

/-- All four generators pairwise commute. -/
theorem generators_commute :
    ∀ g ∈ generators, ∀ h ∈ generators, g * h = h * g := by
  classical
  intro g hg h hh
  simp only [generators, Set.mem_insert_iff, Set.mem_singleton_iff] at hg hh
  rcases hg with rfl | rfl | rfl | rfl <;>
    rcases hh with rfl | rfl | rfl | rfl <;>
    first
      | rfl
      | exact g1_comm_g2 | exact g1_comm_g2.symm
      | exact g1_comm_g3 | exact g1_comm_g3.symm
      | exact g1_comm_g4 | exact g1_comm_g4.symm
      | exact g2_comm_g3 | exact g2_comm_g3.symm
      | exact g2_comm_g4 | exact g2_comm_g4.symm
      | exact g3_comm_g4 | exact g3_comm_g4.symm

/-! ## §7 — Generator list and `listToSet` equality

(Section §7 of `_TEMPLATE.lean`; moved here before §6 because the
`negIdentity_not_mem` proof refers to the list-form independence.)
-/

/-- Generators as a list (for symplectic-span / independence arguments). -/
def generatorsList : List (NQubitPauliGroupElement 5) :=
  [g1, g2, g3, g4]

/-- The list-form generators have the same elements as the set-form `generators`. -/
lemma listToSet_generatorsList :
    NQubitPauliGroupElement.listToSet generatorsList = generators := by
  simp only [generatorsList, generators,
    NQubitPauliGroupElement.listToSet_cons, NQubitPauliGroupElement.listToSet_nil]
  ext g
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_empty_iff_false,
    or_false]

/-! ## §9 — Phase-zero and generator independence -/

/-- Every element of the generators list has phase power 0. -/
lemma AllPhaseZero_generatorsList :
    NQubitPauliGroupElement.AllPhaseZero generatorsList := by
  rw [generatorsList, NQubitPauliGroupElement.AllPhaseZero_cons]
  exact ⟨rfl, (NQubitPauliGroupElement.AllPhaseZero_cons _ _).mpr
    ⟨rfl, (NQubitPauliGroupElement.AllPhaseZero_cons _ _).mpr
      ⟨rfl, (NQubitPauliGroupElement.AllPhaseZero_cons _ _).mpr
        ⟨rfl, NQubitPauliGroupElement.AllPhaseZero_nil⟩⟩⟩⟩

/-- The check-matrix rows of the four generators are linearly independent. -/
theorem rowsLinearIndependent_generatorsList :
    NQubitPauliGroupElement.rowsLinearIndependent generatorsList := by decide

/-- The generator list is an independent generating set. -/
theorem GeneratorsIndependent_5_generatorsList :
    GeneratorsIndependent 5 generatorsList :=
  GeneratorsIndependent_of_rowsLinearIndependent 5 generatorsList
    rowsLinearIndependent_generatorsList

/-! ## §6 — `−I` is not in the stabilizer subgroup

**Non-CSS divergence**: cannot use
`CSS.negIdentity_not_mem_closure_union`. We rely on a general-form
helper `negIdentity_not_mem_of_independent_phase_zero` (to be added in
`Core/SubgroupLemmas.lean` — see `gap_audit.md` Gap 1). Until that
helper lands, this proof is `sorry`.
-/

/-- `−I` is not in the [[5, 1, 3]] stabilizer subgroup. -/
theorem negIdentity_not_mem :
    negIdentity 5 ∉ subgroup := by
  sorry -- TODO(stab_5_1_3-T2): WIP — see Core helper plan below.

/-! ## §8 — Bundled `StabilizerGroup 5` -/

/-- The [[5, 1, 3]] stabilizer group as a `StabilizerGroup 5`. -/
noncomputable def stabilizerGroup : StabilizerGroup 5 :=
  mkStabilizerFromGenerators 5 generatorsList
    (by rw [listToSet_generatorsList]; exact generators_commute)
    (by rw [listToSet_generatorsList]; exact negIdentity_not_mem)

/-- The bundled stabilizer subgroup agrees with the set-form `subgroup`. -/
lemma stabilizerGroup_toSubgroup_eq :
    stabilizerGroup.toSubgroup = subgroup := by
  simp only [stabilizerGroup, mkStabilizerFromGenerators, subgroup]
  rw [listToSet_generatorsList]

/-! ## §10 — Logical operators

Standard Gottesman / EC Zoo convention: full-support all-X and all-Z.
-/

/-- Logical `X̄`: `X` on all five qubits. -/
def logicalX : NQubitPauliGroupElement 5 :=
  ⟨0, NQubitPauliOperator.X 5⟩

/-- Logical `Z̄`: `Z` on all five qubits. -/
def logicalZ : NQubitPauliGroupElement 5 :=
  ⟨0, NQubitPauliOperator.Z 5⟩

/-- Optional logical `Ȳ` with the convention `Ȳ = i X̄ Z̄`. -/
noncomputable def logicalY : NQubitPauliGroupElement 5 :=
  NQubitPauliGroupElement.phaseI 5 * (logicalX * logicalZ)

/-! ## §11 — Logical anticommutation (`X̄` and `Z̄`)

For all-X / all-Z logicals, the dedicated lemma
`NQubitPauliOperator.allX_allZ_anticommute` closes this in one line
(since `n = 5` is odd).
-/

/-- `X̄` and `Z̄` anticommute (since `n = 5` is odd). -/
theorem logicalX_anticommutes_logicalZ :
    NQubitPauliGroupElement.Anticommute logicalX logicalZ :=
  NQubitPauliOperator.allX_allZ_anticommute 5 (by decide)

/-! ## §12 — Logicals in centralizer

Eight per-generator commutation lemmas (4 for `logicalX`, 4 for
`logicalZ`), each closed by `pauli_comm_even_anticommutes` + explicit
Finset. Then bundled via `Subgroup.forall_comm_closure_iff`.
-/

private lemma logicalX_commutes_g1 : logicalX * g1 = g1 * logicalX := by
  classical
  pauli_comm_even_anticommutes
  have hfilter :
      (Finset.univ.filter
            (NQubitPauliGroupElement.anticommutesAt (n := 5) logicalX.operators g1.operators)) =
        ({1, 2} : Finset (Fin 5)) := by
    ext i; fin_cases i <;>
      simp [Finset.mem_filter, NQubitPauliGroupElement.anticommutesAt, logicalX, g1,
        NQubitPauliOperator.X, NQubitPauliOperator.set, NQubitPauliOperator.identity,
        PauliOperator.mulOp]
  rw [hfilter]; decide

private lemma logicalX_commutes_g2 : logicalX * g2 = g2 * logicalX := by
  classical
  pauli_comm_even_anticommutes
  have hfilter :
      (Finset.univ.filter
            (NQubitPauliGroupElement.anticommutesAt (n := 5) logicalX.operators g2.operators)) =
        ({2, 3} : Finset (Fin 5)) := by
    ext i; fin_cases i <;>
      simp [Finset.mem_filter, NQubitPauliGroupElement.anticommutesAt, logicalX, g2,
        NQubitPauliOperator.X, NQubitPauliOperator.set, NQubitPauliOperator.identity,
        PauliOperator.mulOp]
  rw [hfilter]; decide

private lemma logicalX_commutes_g3 : logicalX * g3 = g3 * logicalX := by
  classical
  pauli_comm_even_anticommutes
  have hfilter :
      (Finset.univ.filter
            (NQubitPauliGroupElement.anticommutesAt (n := 5) logicalX.operators g3.operators)) =
        ({3, 4} : Finset (Fin 5)) := by
    ext i; fin_cases i <;>
      simp [Finset.mem_filter, NQubitPauliGroupElement.anticommutesAt, logicalX, g3,
        NQubitPauliOperator.X, NQubitPauliOperator.set, NQubitPauliOperator.identity,
        PauliOperator.mulOp]
  rw [hfilter]; decide

private lemma logicalX_commutes_g4 : logicalX * g4 = g4 * logicalX := by
  classical
  pauli_comm_even_anticommutes
  have hfilter :
      (Finset.univ.filter
            (NQubitPauliGroupElement.anticommutesAt (n := 5) logicalX.operators g4.operators)) =
        ({0, 4} : Finset (Fin 5)) := by
    ext i; fin_cases i <;>
      simp [Finset.mem_filter, NQubitPauliGroupElement.anticommutesAt, logicalX, g4,
        NQubitPauliOperator.X, NQubitPauliOperator.set, NQubitPauliOperator.identity,
        PauliOperator.mulOp]
  rw [hfilter]; decide

private lemma logicalZ_commutes_g1 : logicalZ * g1 = g1 * logicalZ := by
  classical
  pauli_comm_even_anticommutes
  have hfilter :
      (Finset.univ.filter
            (NQubitPauliGroupElement.anticommutesAt (n := 5) logicalZ.operators g1.operators)) =
        ({0, 3} : Finset (Fin 5)) := by
    ext i; fin_cases i <;>
      simp [Finset.mem_filter, NQubitPauliGroupElement.anticommutesAt, logicalZ, g1,
        NQubitPauliOperator.Z, NQubitPauliOperator.set, NQubitPauliOperator.identity,
        PauliOperator.mulOp]
  rw [hfilter]; decide

private lemma logicalZ_commutes_g2 : logicalZ * g2 = g2 * logicalZ := by
  classical
  pauli_comm_even_anticommutes
  have hfilter :
      (Finset.univ.filter
            (NQubitPauliGroupElement.anticommutesAt (n := 5) logicalZ.operators g2.operators)) =
        ({1, 4} : Finset (Fin 5)) := by
    ext i; fin_cases i <;>
      simp [Finset.mem_filter, NQubitPauliGroupElement.anticommutesAt, logicalZ, g2,
        NQubitPauliOperator.Z, NQubitPauliOperator.set, NQubitPauliOperator.identity,
        PauliOperator.mulOp]
  rw [hfilter]; decide

private lemma logicalZ_commutes_g3 : logicalZ * g3 = g3 * logicalZ := by
  classical
  pauli_comm_even_anticommutes
  have hfilter :
      (Finset.univ.filter
            (NQubitPauliGroupElement.anticommutesAt (n := 5) logicalZ.operators g3.operators)) =
        ({0, 2} : Finset (Fin 5)) := by
    ext i; fin_cases i <;>
      simp [Finset.mem_filter, NQubitPauliGroupElement.anticommutesAt, logicalZ, g3,
        NQubitPauliOperator.Z, NQubitPauliOperator.set, NQubitPauliOperator.identity,
        PauliOperator.mulOp]
  rw [hfilter]; decide

private lemma logicalZ_commutes_g4 : logicalZ * g4 = g4 * logicalZ := by
  classical
  pauli_comm_even_anticommutes
  have hfilter :
      (Finset.univ.filter
            (NQubitPauliGroupElement.anticommutesAt (n := 5) logicalZ.operators g4.operators)) =
        ({1, 3} : Finset (Fin 5)) := by
    ext i; fin_cases i <;>
      simp [Finset.mem_filter, NQubitPauliGroupElement.anticommutesAt, logicalZ, g4,
        NQubitPauliOperator.Z, NQubitPauliOperator.set, NQubitPauliOperator.identity,
        PauliOperator.mulOp]
  rw [hfilter]; decide

/-- `X̄` commutes with every element of the stabilizer. -/
theorem logicalX_mem_centralizer :
    logicalX ∈ centralizer stabilizerGroup := by
  rw [StabilizerGroup.mem_centralizer_iff, stabilizerGroup_toSubgroup_eq, subgroup]
  rw [Subgroup.forall_comm_closure_iff]
  intro s hs
  simp only [generators, Set.mem_insert_iff, Set.mem_singleton_iff] at hs
  rcases hs with rfl | rfl | rfl | rfl
  · exact logicalX_commutes_g1.symm
  · exact logicalX_commutes_g2.symm
  · exact logicalX_commutes_g3.symm
  · exact logicalX_commutes_g4.symm

/-- `Z̄` commutes with every element of the stabilizer. -/
theorem logicalZ_mem_centralizer :
    logicalZ ∈ centralizer stabilizerGroup := by
  rw [StabilizerGroup.mem_centralizer_iff, stabilizerGroup_toSubgroup_eq, subgroup]
  rw [Subgroup.forall_comm_closure_iff]
  intro s hs
  simp only [generators, Set.mem_insert_iff, Set.mem_singleton_iff] at hs
  rcases hs with rfl | rfl | rfl | rfl
  · exact logicalZ_commutes_g1.symm
  · exact logicalZ_commutes_g2.symm
  · exact logicalZ_commutes_g3.symm
  · exact logicalZ_commutes_g4.symm

/-! ## §13 — `StabilizerCode 5 1` packaging -/

/-- The single logical-qubit data (`k = 1`). -/
private def logicalOps5_1_3 : Fin 1 → LogicalQubitOps 5 stabilizerGroup :=
  fun _ => ⟨logicalX, logicalZ,
            logicalX_mem_centralizer, logicalZ_mem_centralizer,
            logicalX_anticommutes_logicalZ⟩

/-- The [[5, 1, 3]] five-qubit perfect code as a `StabilizerCode 5 1`. -/
noncomputable def stabilizerCode : StabilizerCode 5 1 where
  hk := by decide
  generatorsList := generatorsList
  generators_length := rfl
  generators_phaseZero := AllPhaseZero_generatorsList
  generators_independent := GeneratorsIndependent_5_generatorsList
  generators_commute := by rw [listToSet_generatorsList]; exact generators_commute
  closure_no_neg_identity := by rw [listToSet_generatorsList]; exact negIdentity_not_mem
  logicalOps := logicalOps5_1_3
  logical_commute_cross := fun ℓ ℓ' h => (h (Subsingleton.elim ℓ ℓ')).elim

/-- Bridge: the stabilizer-code's underlying subgroup is the closure of `generators`.
Used to translate distance proofs against `stabilizerGroup` into proofs against
`stabilizerCode.toStabilizerGroup`. -/
private lemma stabilizerCode_toSubgroup_eq :
    stabilizerCode.toStabilizerGroup.toSubgroup = Subgroup.closure generators := by
  change (Subgroup.closure (NQubitPauliGroupElement.listToSet generatorsList) : _) =
    Subgroup.closure generators
  rw [listToSet_generatorsList]

/-! ## §14 — Code distance = 3

Strategy (preferred, in order of decreasing optimism):

1. **Optimistic**: `native_decide` on the full `HasCodeDistance` predicate.
   For `n = 5`, the universe is `4 × 4^5 = 4096` group elements; with
   the 16-element stabilizer subgroup and 4 generators, total work is
   ~262k operations. Likely closes in seconds.

2. **Manual enumeration**: via `hasCodeDistance_of`, splitting into
   - `d ≥ 1` (decide),
   - weight-3 witness (`logicalX_weight3 := logicalX * g1`,
     non-trivial by a "mul-by-stab preserves non-triviality" lemma —
     see `gap_audit.md` Gap 3),
   - lower bound: no weight-1 or weight-2 Pauli is in the centralizer.
     Weight-1 via the existing helper
     `no_weight_one_mem_centralizer_of_anticommute_witness`; weight-2
     via a new helper `no_weight_two_mem_centralizer_of_anticommute_witness`
     (`gap_audit.md` Gap 2).

The skeleton below shows the manual-enumeration shape with explicit
sorries, so Stage 4 can swap in `native_decide` at the top if that
works.
-/

/-- The [[5, 1, 3]] five-qubit perfect code has distance 3. -/
theorem code_has_distance_three : HasCodeDistance stabilizerCode 3 := by
  sorry -- TODO(stab_5_1_3-T9): WIP — distance proof; try native_decide first.

end FiveQubit_5_1_3
end StabilizerGroup
end Quantum
