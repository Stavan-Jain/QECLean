import Mathlib.Tactic
import QEC.Stabilizer.Foundations.PauliGroup.NQubitOperator
import QEC.Stabilizer.Framework.Core.CSS.CSSPredicates
import QEC.Stabilizer.Foundations.PauliGroup.Commutation

/-!
# Support lemmas for `set` and for typed operators

Lemmas about `NQubitPauliOperator.set`, the operation that builds an n-qubit
Pauli operator one qubit at a time, and about the supports of Z-type and X-type
operators:

- `set_apply_eq`, `set_apply_ne`: the components of `set op i p`;
- `mem_support_set_same_iff`, `mem_support_set_ne_iff`,
  `support_set_subset_insert`: its support;
- `IsZType_set_of_IsZType`, `IsXType_set_of_IsXType`: `set` preserves the Z-type
  and X-type predicates;
- `NQubitPauliGroupElement.anticommutesAt_iff_mem_support_both_of_ZXType` and
  `anticommutesAt_iff_mem_support_both_of_XZType`: a Z-type and an X-type
  operator anticommute at qubit `i` iff `i` lies in both supports.
-/

namespace Quantum
namespace NQubitPauliOperator

variable {n : ℕ}

/-- `set` writes the requested Pauli at the target index. -/
@[simp] lemma set_apply_eq (op : NQubitPauliOperator n) (i : Fin n) (p : PauliOperator) :
    set op i p i = p := by
  simp [set]

/-- `set` leaves all other indices unchanged. -/
@[simp] lemma set_apply_ne (op : NQubitPauliOperator n) (i j : Fin n) (p : PauliOperator)
    (h : j ≠ i) :
    set op i p j = op j := by
  simp [set, h]

/-- The edited index is in the support of `set op i p` iff `p ≠ I`. -/
@[simp] lemma mem_support_set_same_iff
    (op : NQubitPauliOperator n) (i : Fin n) (p : PauliOperator) :
    i ∈ support (set op i p) ↔ p ≠ PauliOperator.I := by
  simp [support, set]

/-- Any other index is in the support of `set op i p` iff it is in the support
of `op`. -/
@[simp] lemma mem_support_set_ne_iff
    (op : NQubitPauliOperator n) (i j : Fin n) (p : PauliOperator) (h : j ≠ i) :
    j ∈ support (set op i p) ↔ j ∈ support op := by
  simp [support, set, h]

/-- The support of `set op i p` is contained in `insert i (support op)`. -/
lemma support_set_subset_insert (op : NQubitPauliOperator n) (i : Fin n) (p : PauliOperator) :
    support (set op i p) ⊆ insert i (support op) := by
  intro j hj
  rcases eq_or_ne j i with rfl | hji
  · exact Finset.mem_insert_self _ _
  · exact Finset.mem_insert_of_mem ((mem_support_set_ne_iff op i j p hji).1 hj)

/-- Setting a Z-type single-qubit operator preserves n-qubit Z-type. -/
lemma IsZType_set_of_IsZType (op : NQubitPauliOperator n) (i : Fin n) (p : PauliOperator)
    (hop : IsZType op) (hp : PauliOperator.IsZType p) :
    IsZType (set op i p) := by
  intro j
  change PauliOperator.IsZType (if j = i then p else op j)
  split_ifs
  exacts [hp, hop j]

/-- Setting an X-type single-qubit operator preserves n-qubit X-type. -/
lemma IsXType_set_of_IsXType (op : NQubitPauliOperator n) (i : Fin n) (p : PauliOperator)
    (hop : IsXType op) (hp : PauliOperator.IsXType p) :
    IsXType (set op i p) := by
  intro j
  change PauliOperator.IsXType (if j = i then p else op j)
  split_ifs
  exacts [hp, hop j]

/-- Setting a `Z` preserves n-qubit Z-type. -/
lemma IsZType_set_Z_of_IsZType (op : NQubitPauliOperator n) (i : Fin n) (hop : IsZType op) :
    IsZType (set op i PauliOperator.Z) :=
  IsZType_set_of_IsZType op i PauliOperator.Z hop PauliOperator.IsZType_Z

/-- Setting an `X` preserves n-qubit X-type. -/
lemma IsXType_set_X_of_IsXType (op : NQubitPauliOperator n) (i : Fin n) (hop : IsXType op) :
    IsXType (set op i PauliOperator.X) :=
  IsXType_set_of_IsXType op i PauliOperator.X hop PauliOperator.IsXType_X

end NQubitPauliOperator

namespace NQubitPauliGroupElement

variable {n : ℕ}

/-- A Z-type operator `p` and an X-type operator `q` anticommute at qubit `i`
iff `i` is in the support of both. -/
lemma anticommutesAt_iff_mem_support_both_of_ZXType
    {p q : NQubitPauliOperator n}
    (hp : NQubitPauliOperator.IsZType p)
    (hq : NQubitPauliOperator.IsXType q)
    (i : Fin n) :
    anticommutesAt p q i ↔ i ∈ p.support ∧ i ∈ q.support := by
  rcases hp i with h | h <;> rcases hq i with h' | h' <;>
    simp [anticommutesAt, NQubitPauliOperator.support, h, h']

/-- An X-type operator `p` and a Z-type operator `q` anticommute at qubit `i`
iff `i` is in the support of both. -/
lemma anticommutesAt_iff_mem_support_both_of_XZType
    {p q : NQubitPauliOperator n}
    (hp : NQubitPauliOperator.IsXType p)
    (hq : NQubitPauliOperator.IsZType q)
    (i : Fin n) :
    anticommutesAt p q i ↔ i ∈ p.support ∧ i ∈ q.support := by
  rcases hp i with h | h <;> rcases hq i with h' | h' <;>
    simp [anticommutesAt, NQubitPauliOperator.support, h, h']

end NQubitPauliGroupElement
end Quantum
