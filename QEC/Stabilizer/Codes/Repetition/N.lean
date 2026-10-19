import Mathlib.Tactic
import Mathlib.Data.List.OfFn
import QEC.Stabilizer.Framework.Core.Stabilizer.StabilizerGroup
import QEC.Stabilizer.Framework.Core.Stabilizer.StabilizerCode
import QEC.Stabilizer.Framework.Core.Stabilizer.SubgroupLemmas
import QEC.Stabilizer.Framework.Core.CSS.CSSNoNegI
import QEC.Stabilizer.Framework.Core.CSS.CSSDistance
import QEC.Stabilizer.Framework.Core.CodeNotation
import QEC.Stabilizer.Framework.Core.Logical.LogicalOperators
import QEC.Stabilizer.Framework.Core.Stabilizer.Centralizer
import QEC.Stabilizer.Foundations.PauliGroup.Commutation
import QEC.Stabilizer.Foundations.PauliGroup.CommutationTactics
import QEC.Stabilizer.Foundations.BinarySymplectic.SymplecticInner
import QEC.Stabilizer.Foundations.BinarySymplectic.CheckMatrix
import QEC.Stabilizer.Foundations.BinarySymplectic.CheckMatrixDecidable
import QEC.Stabilizer.Foundations.BinarySymplectic.Core
import QEC.Stabilizer.Framework.Symplectic.IndependentEquiv
import QEC.Stabilizer.Framework.Symplectic.Presentation
import QEC.Stabilizer.Foundations.PauliGroup.NQubitOperator
import QEC.Stabilizer.Foundations.PauliGroupSingle.Operator

namespace Quantum
open scoped BigOperators

namespace StabilizerGroup
namespace RepetitionCodeN

/-!
# The repetition code on `n + 2` qubits `[[n+2, 1, 1]]`

The parametric version of `RepetitionCode3`, defined on **`n + 2` qubits** to
make the adjacent-pair indexing clean. The generators are the `Z`-checks
`Z_i Z_{i+1}` for `i : Fin (n+1)`, acting on qubits `i` and `i+1`; there are no
`X`-checks.

Being parametric, the family takes the **CSS route** rather than the decide
route: the generator list is a `List.ofFn` that `decide` cannot evaluate, so
the generators commute because they are all Z-type, `−I ∉ closure` comes from
`CSS.negIdentity_not_mem_closure_union` with no `X`-generators, and
independence from a column-by-column induction on the check matrix.

As a *quantum* code it has distance 1 for every `n`: `Z` on qubit `0` commutes
with every check but anticommutes with `X⊗ⁿ⁺²`, which also commutes with every
check, so it is a weight-one nontrivial logical.

The logical basis `X̄ = X⊗ⁿ⁺²`, `Z̄ = Z⊗ⁿ⁺²` (for odd `n + 2`) is in
`NLogicals.lean`.

## Outline

- Generators `ZPair` and the list `generatorsList`; check-matrix independence
  `rowsLinearIndependent_generatorsList`
- Z-typing and `generators_commute`
- `negIdentity_not_mem`, the bundled `stabilizerGroup`
- `stabilizerCode : Code[[n+2, 1]]`
- Distance 1 (weight-1 witness): `code_has_distance_one`,
  `stabilizerCodeWithDistance : Code[[n+2, 1, 1]]`
-/

open NQubitPauliGroupElement
open scoped Pauli

/-!
## Generators
-/

/-- The adjacent Z-check `Z_i Z_{i+1}` on `n+2` qubits, indexed by
`i : Fin (n+1)`. -/
def ZPair (n : ℕ) (i : Fin (n + 1)) : NQubitPauliGroupElement (n + 2) :=
  σ[n + 2 | Fin.castSucc i ↦ Z, Fin.succ i ↦ Z]

def ZGenerators (n : ℕ) : Set (NQubitPauliGroupElement (n + 2)) :=
  Set.range (ZPair n)

def XGenerators (n : ℕ) : Set (NQubitPauliGroupElement (n + 2)) :=
  (∅ : Set (NQubitPauliGroupElement (n + 2)))

def generators (n : ℕ) : Set (NQubitPauliGroupElement (n + 2)) :=
  ZGenerators n ∪ XGenerators n

/-- Generators as a list (for check-matrix and independence arguments). -/
def generatorsList (n : ℕ) : List (NQubitPauliGroupElement (n + 2)) :=
  List.ofFn (ZPair n)

lemma generatorsList_length (n : ℕ) : (generatorsList n).length = n + 1 := by
  simp only [generatorsList, List.length_ofFn]

lemma generatorsList_get (n : ℕ) (i : Fin (generatorsList n).length) :
    (generatorsList n).get i = ZPair n (Fin.cast (generatorsList_length n) i) := by
  simp only [generatorsList, List.get_ofFn]

/-- The list of generators has the same elements as `ZGenerators n`. -/
lemma listToSet_generatorsList (n : ℕ) :
    listToSet (generatorsList n) = ZGenerators n := by
  rw [generatorsList, ZGenerators, NQubitPauliGroupElement.listToSet_ofFn]

/-- Every element of the generators list has phase power 0. -/
lemma AllPhaseZero_generatorsList (n : ℕ) :
    NQubitPauliGroupElement.AllPhaseZero (generatorsList n) := by
  rw [generatorsList]
  exact NQubitPauliGroupElement.AllPhaseZero_ofFn (ZPair n) (fun _ => rfl)

noncomputable def subgroup (n : ℕ) : Subgroup (NQubitPauliGroupElement (n + 2)) :=
  Subgroup.closure (generators n)

/-- `ZPair n i` has Z at qubits `castSucc i` and `succ i`, and I elsewhere. -/
lemma ZPair_operators_at (n : ℕ) (i : Fin (n + 1)) (k : Fin (n + 2)) :
    (ZPair n i).operators k =
      if k = Fin.castSucc i ∨ k = Fin.succ i then PauliOperator.Z else PauliOperator.I := by
  simp only [ZPair, NQubitPauliOperator.set, NQubitPauliOperator.identity]
  by_cases hk1 : k = Fin.succ i <;> by_cases hk2 : k = Fin.castSucc i <;> simp [hk1, hk2]

/-- Z-column of the check matrix: row `i` has 1 at Z-qubit `k` iff `k` is one of
the two qubits. -/
lemma checkMatrix_ZColumn (n : ℕ) (i : Fin (generatorsList n).length) (k : Fin (n + 2)) :
    checkMatrix (generatorsList n) i (Fin.natAdd (n + 2) k) =
      if k = Fin.castSucc (Fin.cast (generatorsList_length n) i)
          ∨ k = Fin.succ (Fin.cast (generatorsList_length n) i)
      then (1 : ZMod 2) else 0 := by
  simp only [checkMatrix, generatorsList_get, NQubitPauliOperator.toSymplectic_Z_part,
    ZPair_operators_at]
  split_ifs <;> simp only [PauliOperator.toSymplecticSingle_Z, PauliOperator.toSymplecticSingle_I]

/-- Row index for generator `j`:
`(generatorsList n).get (rowIdx n j) = ZPair n j`. -/
def rowIdx (n : ℕ) (j : Fin (n + 1)) : Fin (generatorsList n).length :=
  Fin.cast (generatorsList_length n).symm j

lemma rowIdx_cast (n : ℕ) (j : Fin (n + 1)) :
    Fin.cast (generatorsList_length n) (rowIdx n j) = j :=
  (Fin.rightInverse_cast (generatorsList_length n)) j

lemma rowIdx_injective (n : ℕ) (j j' : Fin (n + 1)) (h : rowIdx n j = rowIdx n j') : j = j' := by
  rw [← rowIdx_cast n j, ← rowIdx_cast n j', h]

/-- At Z-column for qubit `0`, only row `rowIdx n 0` contributes. -/
lemma sum_ZColumn_zero (n : ℕ) (f : Fin (generatorsList n).length → ZMod 2) :
    (∑ i : Fin (generatorsList n).length,
        f i * checkMatrix (generatorsList n) i (Fin.natAdd (n + 2) ⟨0, Nat.zero_lt_succ (n + 1)⟩)) =
      f (rowIdx n ⟨0, Nat.zero_lt_succ n⟩) := by
  set a := rowIdx n ⟨0, Nat.zero_lt_succ n⟩
  set col0 := Fin.natAdd (n + 2) ⟨0, Nat.zero_lt_succ (n + 1)⟩
  have key (i : Fin (generatorsList n).length) :
      checkMatrix (generatorsList n) i col0 = if i = a then (1 : ZMod 2) else 0 := by
    rw [checkMatrix_ZColumn]
    congr 1
    apply propext
    constructor
    · intro h
      rcases h with h0 | h1
      · have hval : (Fin.cast (generatorsList_length n) i).val = 0 := by
          have h0val := congr_arg Fin.val h0
          have hzero : (⟨0, Nat.zero_lt_succ (n + 1)⟩ : Fin (n + 2)).val = 0 := rfl
          rw [hzero] at h0val
          have castSucc_val : (Fin.castSucc (Fin.cast (generatorsList_length n) i)).val =
              (Fin.cast (generatorsList_length n) i).val % (n + 2) := by
            simp only [← Fin.coe_eq_castSucc, Fin.val_natCast]
          rw [castSucc_val] at h0val
          have hlt := Nat.lt_succ_of_lt (Fin.cast (generatorsList_length n) i).2
          rw [Nat.mod_eq_of_lt hlt] at h0val
          exact h0val.symm
        have hcast : Fin.cast (generatorsList_length n) i = ⟨0, Nat.zero_lt_succ n⟩ := Fin.ext hval
        rw [← (Fin.leftInverse_cast (generatorsList_length n)) i, hcast]
        rfl
      · exfalso
        exact Fin.succ_ne_zero (Fin.cast (generatorsList_length n) i) h1.symm
    · intro heq
      left
      rw [heq, rowIdx_cast]
      exact Fin.castSucc_zero.symm
  rw [Finset.sum_congr rfl (fun i _ => by rw [key i])]
  simp only [mul_ite, mul_zero]
  have sum_eq : (∑ x, if x = a then f x * 1 else 0) = (∑ x, if x = a then f x else 0) :=
    Finset.sum_congr rfl (fun x _ => by split_ifs <;> simp [*])
  rw [sum_eq, Finset.sum_ite_eq' Finset.univ a f, if_pos (Finset.mem_univ a)]

/-- At Z-column for qubit `n+1`, only row `rowIdx n ⟨n, _⟩` contributes. -/
lemma sum_ZColumn_last (n : ℕ) (f : Fin (generatorsList n).length → ZMod 2) :
    (∑ i : Fin (generatorsList n).length,
        f i * checkMatrix (generatorsList n) i
          (Fin.natAdd (n + 2) ⟨n + 1, Nat.lt_succ_self (n + 1)⟩)) =
      f (rowIdx n ⟨n, Nat.lt_succ_self n⟩) := by
  set a := rowIdx n ⟨n, Nat.lt_succ_self n⟩
  set colLast := Fin.natAdd (n + 2) ⟨n + 1, Nat.lt_succ_self (n + 1)⟩
  have key (i : Fin (generatorsList n).length) :
      checkMatrix (generatorsList n) i colLast = if i = a then (1 : ZMod 2) else 0 := by
    rw [checkMatrix_ZColumn]
    congr 1
    apply propext
    constructor
    · intro h
      rcases h with h0 | h1
      · exfalso
        have h0val := congr_arg Fin.val h0
        have castSucc_eq : (Fin.castSucc (Fin.cast (generatorsList_length n) i)).val =
            (Fin.cast (generatorsList_length n) i).val := by
          simp only [← Fin.coe_eq_castSucc, Fin.val_natCast,
            Nat.mod_eq_of_lt (Nat.lt_succ_of_lt (Fin.cast (generatorsList_length n) i).2)]
        rw [castSucc_eq] at h0val
        have hlt : (Fin.cast (generatorsList_length n) i).val < n + 1 := (Fin.cast _ i).2
        rw [← h0val] at hlt
        exact Nat.lt_irrefl (n + 1) hlt
      · have hval : (Fin.cast (generatorsList_length n) i).val = n := by
          have h1val := congr_arg Fin.val h1
          simp only [Fin.val_succ] at h1val
          omega
        have hcast : Fin.cast (generatorsList_length n) i = ⟨n, Nat.lt_succ_self n⟩ := Fin.ext hval
        rw [← (Fin.leftInverse_cast (generatorsList_length n)) i, hcast]
        rfl
    · intro heq
      right
      rw [heq, rowIdx_cast]
      exact Fin.ext rfl
  rw [Finset.sum_congr rfl (fun i _ => by rw [key i])]
  simp only [mul_ite, mul_zero]
  have sum_eq : (∑ x, if x = a then f x * 1 else 0) = (∑ x, if x = a then f x else 0) :=
    Finset.sum_congr rfl (fun x _ => by split_ifs <;> simp [*])
  rw [sum_eq, Finset.sum_ite_eq' Finset.univ a f, if_pos (Finset.mem_univ a)]

/-- At Z-column for qubit `j` with `1 ≤ j ≤ n`, rows `rowIdx n (j-1)` and
`rowIdx n j` contribute. -/
lemma sum_ZColumn_mid (n : ℕ) (f : Fin (generatorsList n).length → ZMod 2) (j : ℕ)
    (hj : j < n + 2) (hj1 : 1 ≤ j) (hjn : j ≤ n) :
    (∑ i : Fin (generatorsList n).length,
        f i * checkMatrix (generatorsList n) i (Fin.natAdd (n + 2) ⟨j, hj⟩)) =
      f (rowIdx n ⟨j - 1, by omega⟩) + f (rowIdx n ⟨j, by omega⟩) := by
  have h_rows : ∀ i : Fin (generatorsList n).length,
      checkMatrix (generatorsList n) i (Fin.natAdd (n + 2) ⟨j, hj⟩) =
      if i = rowIdx n ⟨j - 1, by omega⟩ ∨ i = rowIdx n ⟨j, by grind⟩ then 1 else 0 := by
    intros i
    rw [checkMatrix_ZColumn];
    simp +decide [ Fin.ext_iff, rowIdx ];
    grind +ring
  generalize_proofs at *;
  simp_all +decide [ Finset.sum_ite ];
  rw [Finset.sum_eq_add (rowIdx n ⟨j - 1, by assumption⟩) (rowIdx n ⟨j, by assumption⟩)] <;>
    norm_num [Fin.ext_iff]
  · simp +decide [ Quantum.StabilizerGroup.RepetitionCodeN.rowIdx ];
    omega;
  · tauto

/-- The check-matrix rows of the parametric repetition-code generators are
linearly independent. -/
theorem rowsLinearIndependent_generatorsList (n : ℕ) :
    NQubitPauliGroupElement.rowsLinearIndependent (generatorsList n) := by
  unfold Quantum.NQubitPauliGroupElement.rowsLinearIndependent;
  have h_check_matrix_rows_lin_indep :
      ∀ (f : Fin (generatorsList n).length → ZMod 2),
      (∀ i, ∑ j, f j * checkMatrix (generatorsList n) j i = 0) → f = 0 := by
    intro f hf
    have h_zero : ∀ j : Fin (n + 1), f (rowIdx n j) = 0 := by
      intro j
      induction j using Fin.induction with
      | zero =>
        specialize hf (Fin.natAdd (n + 2) ⟨0, Nat.zero_lt_succ (n + 1)⟩)
        rw [sum_ZColumn_zero] at hf; aesop
      | succ j ih =>
        have := hf (Fin.natAdd (n + 2) (Fin.castSucc j.succ))
        rw [sum_ZColumn_mid] at this <;> norm_num at *
        refine (eq_zero_iff_eq_zero_of_add_eq_zero this).mp ih
    ext i; specialize h_zero ( Fin.cast ( generatorsList_length n ) i ) ; aesop;
  rw [ Fintype.linearIndependent_iff ];
  intro g hg i
  specialize h_check_matrix_rows_lin_indep g
  simp_all +decide [funext_iff, Finset.sum_apply]

/-- The parametric repetition-code generator list is an independent generating
set. -/
theorem GeneratorsIndependent_generatorsList (n : ℕ) :
    GeneratorsIndependent (n + 2) (generatorsList n) :=
  GeneratorsIndependent_of_rowsLinearIndependent (rowsLinearIndependent_generatorsList n)

/-!
## Typing: Z-type generators
-/

lemma ZGenerators_are_ZType (n : ℕ) :
    ∀ g, g ∈ ZGenerators n → NQubitPauliGroupElement.IsZTypeElement g := by
  classical
  intro g hg
  rcases hg with ⟨i, rfl⟩
  refine ⟨rfl, ?_⟩
  intro j
  by_cases h1 : j = Fin.succ i
  · subst h1
    exact Or.inr (by simp [ZPair, NQubitPauliOperator.set])
  · by_cases h2 : j = Fin.castSucc i
    · subst h2
      exact Or.inr (by simp [ZPair, NQubitPauliOperator.set, h1])
    · simp [ZPair, NQubitPauliOperator.set, NQubitPauliOperator.identity, h1, h2,
        PauliOperator.IsZType]

/-!
## Abelian: commutation of the generated subgroup
-/

private lemma ZType_commutes {m : ℕ} {g h : NQubitPauliGroupElement m}
    (hg : NQubitPauliGroupElement.IsZTypeElement g)
    (hh : NQubitPauliGroupElement.IsZTypeElement h) :
    g * h = h * g := by
  classical
  apply NQubitPauliGroupElement.commutes_of_componentwise_commutes
  intro k
  have hg' := hg.2 k
  have hh' := hh.2 k
  rcases hg' with hgI | hgZ <;> rcases hh' with hhI | hhZ
  · simp [PauliOperator.mulOp, hgI, hhI]
  · simp [PauliOperator.mulOp, hgI, hhZ]
  · simp [PauliOperator.mulOp, hgZ, hhI]
  · simp [PauliOperator.mulOp, hgZ, hhZ]

theorem generators_commute (n : ℕ) :
    ∀ g ∈ generators n, ∀ h ∈ generators n, g * h = h * g := by
  classical
  intro g hg h hh
  simp only [generators, XGenerators, Set.union_empty] at hg hh
  exact ZType_commutes (ZGenerators_are_ZType n g hg) (ZGenerators_are_ZType n h hh)

/-!
## No `−I` in the stabilizer subgroup

`CSS.negIdentity_not_mem_closure_union` with an empty set of X-generators.
-/

theorem negIdentity_not_mem (n : ℕ) :
    negIdentity (n + 2) ∉ subgroup n := by
  have hX :
      ∀ x, x ∈ XGenerators n → NQubitPauliGroupElement.IsXTypeElement x := by
    intro x hx
    simp [XGenerators] at hx
  have hZX :
      ∀ z ∈ ZGenerators n, ∀ x ∈ XGenerators n, z * x = x * z := by
    intro z hz x hx
    simp [XGenerators] at hx
  simpa [subgroup, generators] using
    (CSS.negIdentity_not_mem_closure_union (ZGenerators n) (XGenerators n)
      (ZGenerators_are_ZType n) hX hZX)

lemma listToSet_generators_eq (n : ℕ) :
    listToSet (generatorsList n) = generators n := by
  rw [listToSet_generatorsList, generators, XGenerators, Set.union_empty]

/-!
## Bundled `StabilizerGroup (n+2)`
-/

/-- The repetition code as a stabilizer group (canonical: from generator list).
-/
noncomputable def stabilizerGroup (n : ℕ) : StabilizerGroup (n + 2) :=
  mkStabilizerFromGenerators (n + 2) (generatorsList n)
    (by rw [listToSet_generators_eq]; exact generators_commute n)
    (by rw [listToSet_generators_eq]; exact negIdentity_not_mem n)

/-- The stabilizer subgroup is the closure of the generator set. -/
lemma stabilizerGroup_toSubgroup_eq (n : ℕ) : (stabilizerGroup n).toSubgroup = subgroup n := by
  simp only [stabilizerGroup, mkStabilizerFromGenerators, subgroup]
  rw [listToSet_generators_eq]

/-!
## The bare code `Code[[n+2, 1]]`

The `n + 1` nearest-neighbour `ZZ` generators are independent and commute, on
`n + 2` qubits: one logical qubit, for every `n`.
-/

/-- The `n + 1` nearest-neighbour `ZZ` checks as a presentation of an
`[[n+2, 1]]` code. -/
def presentation (n : ℕ) : StabilizerCode.Presentation (n + 2) 1 where
  hk := Nat.succ_le_succ (Nat.zero_le (n + 1))
  generatorsList := generatorsList n
  generators_length := by rw [generatorsList_length]; omega
  generators_phaseZero := AllPhaseZero_generatorsList n
  generators_independent := rowsLinearIndependent_generatorsList n
  generators_commute := by
    have h := generators_commute n
    rw [← listToSet_generators_eq] at h
    exact h
  closure_no_neg_identity := by rw [listToSet_generators_eq]; exact negIdentity_not_mem n

/-- The repetition code on `n + 2` qubits as a stabilizer code `[[n+2, 1]]`. -/
noncomputable def stabilizerCode (n : ℕ) : Code[[n + 2, 1]] := (presentation n).toCode

/-- The stabilizer code's subgroup is the closure of the generator set. -/
lemma stabilizerCode_toSubgroup_eq (n : ℕ) :
    (stabilizerCode n).toStabilizerGroup.toSubgroup = subgroup n :=
  stabilizerGroup_toSubgroup_eq n

/-!
## Distance 1

Every nontrivial logical of positive weight trivially has weight at least 1,
so there is no lower bound to prove: only a weight-1 witness.

### A nontrivial logical of weight 1

The repetition code protects against bit flips only: a single phase flip `Z` on
qubit `0` commutes with every `ZZ` check, yet it is not a stabilizer, since it
anticommutes with `X⊗ⁿ⁺²`, which meets each check on two qubits and so also
commutes with every check. Unlike the logical basis, this needs no parity
assumption on `n`.
-/

/-- `Z` on qubit `0`: a nontrivial logical of weight 1 (for odd `n + 2`, it is
`Z̄ = Z⊗ⁿ⁺²` times a stabilizer). -/
def minWeightLogical (n : ℕ) : NQubitPauliGroupElement (n + 2) :=
  weightOneAt 0 PauliOperator.Z

/-- `X` on all `n + 2` qubits: a centralizer element anticommuting with
`minWeightLogical`. -/
def minWeightPartner (n : ℕ) : NQubitPauliGroupElement (n + 2) :=
  ⟨0, NQubitPauliOperator.X (n + 2)⟩

lemma minWeightLogical_weight (n : ℕ) : weight (minWeightLogical n) = 1 := by
  rw [weight, NQubitPauliOperator.weight, Finset.card_eq_one]
  refine ⟨0, Finset.ext fun k => ?_⟩
  by_cases hk : k = 0 <;>
    simp [minWeightLogical, weightOneAt, NQubitPauliOperator.mem_support, hk]

/-- `Z` on qubit `0` is Z-type, so it commutes with every (Z-type) check. -/
lemma minWeightLogical_mem_centralizer (n : ℕ) :
    minWeightLogical n ∈ centralizer (stabilizerGroup n) := by
  rw [StabilizerGroup.mem_centralizer_iff_closure _ _ (generators n)
    (stabilizerGroup_toSubgroup_eq n)]
  intro s hs
  simp only [generators, XGenerators, Set.union_empty] at hs
  refine ZType_commutes (ZGenerators_are_ZType n s hs) ⟨rfl, fun k => ?_⟩
  by_cases hk : k = 0 <;> simp [minWeightLogical, weightOneAt, hk, PauliOperator.IsZType]

/-- `X⊗ⁿ⁺²` meets each check `Z_i Z_{i+1}` on exactly two qubits. -/
private lemma minWeightPartner_commutes_ZPair (n : ℕ) (i : Fin (n + 1)) :
    minWeightPartner n * ZPair n i = ZPair n i * minWeightPartner n := by
  classical
  pauli_comm_even_anticommutes
  have hfilter :
      (Finset.univ.filter
            (anticommutesAt (minWeightPartner n).operators (ZPair n i).operators)) =
        ({Fin.castSucc i, Fin.succ i} : Finset (Fin (n + 2))) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton, Finset.mem_univ,
      true_and, minWeightPartner, ZPair, NQubitPauliOperator.X, NQubitPauliOperator.set,
      NQubitPauliOperator.identity, NQubitPauliGroupElement.anticommutesAt]
    by_cases hj1 : j = Fin.castSucc i <;> by_cases hj2 : j = Fin.succ i
    · subst hj1
      simp only [↓reduceIte, ite_self, PauliOperator.mulOp_X_Z, Fin.isValue,
        PauliOperator.mulOp_Z_X, Fin.reduceAdd, true_or]
    · subst hj1
      simp only [↓reduceIte, ite_self, PauliOperator.mulOp_X_Z, Fin.isValue,
        PauliOperator.mulOp_Z_X, Fin.reduceAdd, true_or]
    · subst hj2
      simp only [↓reduceIte, PauliOperator.mulOp_X_Z, Fin.isValue, PauliOperator.mulOp_Z_X,
        Fin.reduceAdd, or_true]
    · simp only [if_neg hj1, if_neg hj2, PauliOperator.mulOp_X_I, PauliOperator.mulOp_I_X]
      omega
  rw [hfilter]
  have hne : Fin.castSucc i ∉ {Fin.succ i} :=
    fun h => Fin.castSucc_lt_succ.ne (Finset.mem_singleton.mp h)
  rw [Finset.card_insert_of_notMem hne, Finset.card_singleton]
  exact even_two

/-- `X⊗ⁿ⁺²` commutes with every element of the stabilizer. -/
lemma minWeightPartner_mem_centralizer (n : ℕ) :
    minWeightPartner n ∈ centralizer (stabilizerGroup n) := by
  rw [StabilizerGroup.mem_centralizer_iff_closure _ _ (generators n)
    (stabilizerGroup_toSubgroup_eq n)]
  intro s hs
  simp only [generators, XGenerators, Set.mem_union, Set.mem_empty_iff_false] at hs
  rcases hs with ⟨i, rfl⟩ | hEmp
  · exact (minWeightPartner_commutes_ZPair n i).symm
  · exact False.elim hEmp

/-- `Z` on qubit `0` meets `X⊗ⁿ⁺²` on a single qubit, so they anticommute. -/
lemma minWeightLogical_anticommutes_minWeightPartner (n : ℕ) :
    Anticommute (minWeightLogical n) (minWeightPartner n) := by
  rw [minWeightLogical, anticommute_weightOneAt_iff]
  simp [minWeightPartner, NQubitPauliOperator.X]

/-- `Z` on qubit `0` is a nontrivial logical operator: it lies in the
centralizer and anticommutes with the centralizer element `minWeightPartner`. -/
lemma minWeightLogical_isNontrivial (n : ℕ) :
    IsNontrivialLogicalOperator (minWeightLogical n) (stabilizerCode n).toStabilizerGroup :=
  isNontrivialLogicalOperator_of_anticommute_centralizer _ (minWeightLogical_mem_centralizer n)
    (minWeightPartner_mem_centralizer n) (minWeightLogical_anticommutes_minWeightPartner n)

/-! ### The code with its distance `Code[[n+2, 1, 1]]` -/

/-- **The repetition code has distance 1.** Every nontrivial logical of
positive weight has weight at least 1, and `Z` on qubit `0` attains it. -/
theorem code_has_distance_one (n : ℕ) : HasCodeDistance (stabilizerCode n) 1 :=
  ⟨le_rfl, fun _ _ hw => hw, minWeightLogical n, minWeightLogical_isNontrivial n,
    minWeightLogical_weight n⟩

/-- The repetition code on `n + 2` qubits packaged with its distance. -/
noncomputable def stabilizerCodeWithDistance (n : ℕ) : Code[[n + 2, 1, 1]] where
  toStabilizerCode := stabilizerCode n
  hasDistance := code_has_distance_one n

end RepetitionCodeN
end StabilizerGroup

end Quantum
