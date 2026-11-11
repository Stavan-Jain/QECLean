import Mathlib.Data.Finset.Card
import QEC.Stabilizer.Framework.Symplectic.SymplecticSpan
import QEC.Stabilizer.Foundations.BinarySymplectic.SymplecticInner
import QEC.Stabilizer.Foundations.PauliGroup.NQubitOperator
import QEC.Stabilizer.Foundations.PauliGroup.NQubitElement

/-!
# Weight-two operators in the symplectic span

To show that a code has no nontrivial logical operator of weight `2`, one shows
that every weight-`2` operator commuting with all generators in `L` has its
symplectic vector in `sympSpan L`. This file reduces that statement to a finite
check:

- `weight_two_in_span_of_per_pair`: it suffices to treat, for each pair of
  distinct qubits `i ≠ j`, the operators with support exactly `{i, j}`;
- `weight_2_pair_by_enum`: for a fixed pair, it suffices to treat the `9`
  operators that carry non-identity Paulis `pi`, `pj` at `i`, `j`;
- `weight_2_in_span_by_enum`: the combination of the two, whose hypothesis
  quantifies only over `Fin n`, `Fin n` and two single-qubit Paulis and is
  therefore decidable by enumeration.
-/

namespace Quantum

variable {n : ℕ}

namespace NQubitPauliGroupElement

open NQubitPauliOperator Submodule

/-- If, for every pair of distinct qubits `i ≠ j`, every operator with support
`{i, j}` that commutes with all elements of `L` has its symplectic vector in
`sympSpan L`, then so does every weight-`2` operator that commutes with all
elements of `L`. -/
theorem weight_two_in_span_of_per_pair (L : List (NQubitPauliGroupElement n))
    (h_per_pair : ∀ i j : Fin n, i ≠ j →
      ∀ op : NQubitPauliOperator n,
        NQubitPauliOperator.support op = {i, j} →
          (∀ g ∈ L, NQubitPauliOperator.symplecticInner op g.operators = 0) →
            NQubitPauliOperator.toSymplectic op ∈ sympSpan L)
    (op : NQubitPauliOperator n) (h_weight : NQubitPauliOperator.weight op = 2)
    (h_comm : ∀ g ∈ L, NQubitPauliOperator.symplecticInner op g.operators = 0) :
    NQubitPauliOperator.toSymplectic op ∈ sympSpan L := by
  obtain ⟨i, j, hij, h_supp⟩ := Finset.card_eq_two.mp h_weight
  exact h_per_pair i j hij op h_supp h_comm

/-- An operator with support `{i, j}` is determined by its non-identity Paulis
at `i` and `j`. So a statement about all such operators that commute with `L`
follows from the same statement for the `9` operators
`fun k => if k = i then pi else if k = j then pj else I` with `pi, pj ≠ I`. -/
theorem weight_2_pair_by_enum (L : List (NQubitPauliGroupElement n)) (i j : Fin n)
    (h : ∀ (pi pj : PauliOperator), pi ≠ .I → pj ≠ .I →
      let op : NQubitPauliOperator n := fun k => if k = i then pi else if k = j then pj else .I
      (∀ g ∈ L, NQubitPauliOperator.symplecticInner op g.operators = 0) →
      NQubitPauliOperator.toSymplectic op ∈ sympSpan L)
    (op : NQubitPauliOperator n) (h_supp : NQubitPauliOperator.support op = {i, j})
    (h_comm : ∀ g ∈ L, NQubitPauliOperator.symplecticInner op g.operators = 0) :
    NQubitPauliOperator.toSymplectic op ∈ sympSpan L := by
  have h_mem : ∀ k, op k ≠ .I ↔ k = i ∨ k = j := fun k => by
    rw [← NQubitPauliOperator.mem_support, h_supp, Finset.mem_insert, Finset.mem_singleton]
  have hop : op = fun k => if k = i then op i else if k = j then op j else .I := by
    funext k
    split_ifs with hki hkj
    · rw [hki]
    · rw [hkj]
    · exact not_not.mp fun hk => ((h_mem k).mp hk).elim hki hkj
  rw [hop]
  exact h (op i) (op j) ((h_mem i).mpr (.inl rfl)) ((h_mem j).mpr (.inr rfl)) (by rwa [← hop])

/-- Every weight-`2` operator commuting with all elements of `L` has its
symplectic vector in `sympSpan L`, provided this holds for the operators
`fun k => if k = i then pi else if k = j then pj else I` with `i ≠ j` and
`pi, pj ≠ I`. The hypothesis `h` ranges over `Fin n × Fin n` and pairs of
single-qubit Paulis rather than over all `4 ^ n` operators, so that `decide`
can check it for a concrete code. -/
theorem weight_2_in_span_by_enum (L : List (NQubitPauliGroupElement n))
    (h : ∀ (i j : Fin n), i ≠ j → ∀ (pi pj : PauliOperator), pi ≠ .I → pj ≠ .I →
      let op : NQubitPauliOperator n := fun k => if k = i then pi else if k = j then pj else .I
      (∀ g ∈ L, NQubitPauliOperator.symplecticInner op g.operators = 0) →
      NQubitPauliOperator.toSymplectic op ∈ sympSpan L)
    (op : NQubitPauliOperator n) (h_weight : NQubitPauliOperator.weight op = 2)
    (h_comm : ∀ g ∈ L, NQubitPauliOperator.symplecticInner op g.operators = 0) :
    NQubitPauliOperator.toSymplectic op ∈ sympSpan L :=
  weight_two_in_span_of_per_pair L (fun i j hij => weight_2_pair_by_enum L i j (h i j hij))
    op h_weight h_comm

end NQubitPauliGroupElement

end Quantum
