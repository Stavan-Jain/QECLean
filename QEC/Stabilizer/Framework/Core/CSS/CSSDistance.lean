import QEC.Stabilizer.Framework.Core.Stabilizer.StabilizerGroup
import QEC.Stabilizer.Framework.Core.Stabilizer.Centralizer
import QEC.Stabilizer.Framework.Core.CSS.CSSPredicates
import QEC.Stabilizer.Framework.Core.Logical.CodeDistance
import QEC.Stabilizer.Foundations.PauliGroup.Notation
import QEC.Stabilizer.Foundations.PauliGroup.NQubitOperator
import QEC.Stabilizer.Foundations.PauliGroup.NQubitElement
import QEC.Stabilizer.Foundations.PauliGroup.Commutation
import QEC.Stabilizer.Foundations.PauliGroupSingle
import QEC.Stabilizer.Foundations.BinarySymplectic.SymplecticInner

/-!
# Distance closers for low-weight Paulis

Criteria that establish `HasCodeDistance C 2` and `HasCodeDistance C 3` from
checks that run over generators, qubits and single-qubit Paulis rather than
over all low-weight group elements.

A Pauli of weight one or two has the operator part of `weightOneAt i P` or of
`weightTwoAt i j P Q`. If some generator anticommutes with that element, the
Pauli is not in the centralizer, hence not a logical operator:

- `no_weight_one_mem_centralizer_of_anticommute_witness` and
  `no_weight_two_mem_centralizer_of_anticommute_witness`: no Pauli of weight one
  (two) is in the centralizer when every weight-one (weight-two) pattern
  anticommutes with a generator;
- `no_weight_two_logical_of_anticommute_or_stabilizer`: the variant for
  degenerate codes, where a weight-two pattern may instead be a stabilizer up to
  phase;
- `hasCodeDistance_two_of_anticommute_witness`: distance `2` from the weight-one
  criterion and a nontrivial logical operator of weight `2`;
- `hasCodeDistance_three_of_anticommute_witness`: distance `3` from the
  weight-one and weight-two criteria and a nontrivial logical operator of
  weight `3`;
- `anticommute_weightOneAt_iff`, `anticommute_weightTwoAt_iff`: anticommutation
  with a weight-one or weight-two element, read off one or two qubits.

A CSS check is named by its support: `zOn S` and `xOn S` are `Z` and `X` on the
qubits of `S`. Their type (`IsZTypeElement_zOn`, `IsXTypeElement_xOn`), weight
(`weight_zOn`, `weight_xOn`), check-matrix rows and commutation
(`commutes_xOn_zOn_iff`, `anticommute_xOn_zOn_iff`: `xOn S` and `zOn T` commute
iff `S ∩ T` has even cardinality) are read off the supports.

For a CSS code whose generators are `zOn S` and `xOn S` for the rows `S` of two
classical check matrices, the criteria become conditions on the columns of
those matrices:

- `hasCodeDistance_three_of_columns`: distance `3` when every column is nonzero
  and any two columns differ, on both sides;
- `hasCodeDistance_three_of_columns_degenerate`: the same for degenerate codes,
  where two columns may agree provided the corresponding weight-two operator is
  a stabilizer.
-/

namespace Quantum
namespace StabilizerGroup

variable {n : ℕ}

open NQubitPauliGroupElement
open PauliOperator

/-!
## Weight-one and weight-two elements
-/

/-- The weight-1 group element at qubit `i` with single-qubit Pauli `P` (phase
0). -/
def weightOneAt (i : Fin n) (P : PauliOperator) : NQubitPauliGroupElement n :=
  ofOperator (fun k => if k = i then P else .I)

/-- The weight-2 group element at qubits `i ≠ j` with single-qubit Paulis `P` at
qubit `i` and `Q` at qubit `j` (phase 0). -/
def weightTwoAt (i j : Fin n) (P Q : PauliOperator) : NQubitPauliGroupElement n :=
  ofOperator (fun k => if k = i then P else if k = j then Q else .I)

/-- A weight-one Pauli has the operator part of `weightOneAt i P`, where `i` is
its support qubit and `P` its (non-identity) Pauli there. -/
lemma exists_operators_eq_weightOneAt (g : NQubitPauliGroupElement n) (hg : weight g = 1) :
    ∃ i, g.operators i ≠ .I ∧ g.operators = (weightOneAt i (g.operators i)).operators := by
  obtain ⟨i, hsupp⟩ := (Finset.card_eq_one (s := support g)).mp hg
  have hmem : ∀ k, g.operators k ≠ .I ↔ k = i := fun k => by
    rw [← mem_support, hsupp, Finset.mem_singleton]
  refine ⟨i, (hmem i).2 rfl, funext fun k => ?_⟩
  change g.operators k = if k = i then g.operators i else .I
  split_ifs with hki
  · rw [hki]
  · exact not_not.mp (mt (hmem k).1 hki)

/-- A weight-two Pauli has the operator part of `weightTwoAt i j P Q`, where
`i ≠ j` are its two support qubits and `P`, `Q` its (non-identity) Paulis
there. -/
lemma exists_operators_eq_weightTwoAt (g : NQubitPauliGroupElement n) (hg : weight g = 2) :
    ∃ i j, i ≠ j ∧ g.operators i ≠ .I ∧ g.operators j ≠ .I ∧
      g.operators = (weightTwoAt i j (g.operators i) (g.operators j)).operators := by
  obtain ⟨i, j, hij, hsupp⟩ := (Finset.card_eq_two (s := support g)).mp hg
  have hmem : ∀ k, g.operators k ≠ .I ↔ k = i ∨ k = j := fun k => by
    rw [← mem_support, hsupp, Finset.mem_insert, Finset.mem_singleton]
  refine ⟨i, j, hij, (hmem i).2 (.inl rfl), (hmem j).2 (.inr rfl), funext fun k => ?_⟩
  change g.operators k = if k = i then g.operators i else if k = j then g.operators j else .I
  split_ifs with hki hkj
  · rw [hki]
  · rw [hkj]
  · exact not_not.mp (mt (hmem k).1 (not_or.mpr ⟨hki, hkj⟩))

/-!
## Anticommute witnesses

A generator that anticommutes with a weight-one or weight-two element excludes
every Pauli with the same operator part from the centralizer, since
anticommutation only depends on operator parts.
-/

/-- If `g` has the operator part of an element `w` that anticommutes with some
generator of `S`, then `g` is not in the centralizer of `S`. -/
lemma not_mem_centralizer_of_anticommute_generator (S : StabilizerGroup n)
    (genSet : Set (NQubitPauliGroupElement n))
    (h_closure : S.toSubgroup = Subgroup.closure genSet)
    {g w s : NQubitPauliGroupElement n} (hop : g.operators = w.operators) (hs : s ∈ genSet)
    (h_anti : Anticommute w s) : g ∉ centralizer S := fun h_cent =>
  ((anticommute_congr_left hop).mpr h_anti).not_commute
    ((mem_centralizer_iff_closure g S genSet h_closure).mp h_cent s hs).symm

/-- If for every qubit `i` and every single-qubit Pauli `P ≠ I` there exists a
generator in `genSet` that anticommutes with the weight-1 element at `i` with
Pauli `P`, then no weight-1 Pauli is in the centralizer of the stabilizer group
generated by `genSet`. -/
theorem no_weight_one_mem_centralizer_of_anticommute_witness (S : StabilizerGroup n)
    (genSet : Set (NQubitPauliGroupElement n))
    (h_closure : S.toSubgroup = Subgroup.closure genSet)
    (h_anticomm : ∀ i : Fin n, ∀ P : PauliOperator, P ≠ .I →
      ∃ g ∈ genSet, Anticommute (weightOneAt i P) g)
    (g : NQubitPauliGroupElement n) (hg : weight g = 1)
    (h_cent : g ∈ centralizer S) : False := by
  obtain ⟨i, hi, hop⟩ := exists_operators_eq_weightOneAt g hg
  obtain ⟨s, hs, h_anti⟩ := h_anticomm i _ hi
  exact not_mem_centralizer_of_anticommute_generator S genSet h_closure hop hs h_anti h_cent

/-- If for every pair of distinct qubits `i ≠ j` and every pair of non-identity
single-qubit Paulis `P, Q` there exists a generator in `genSet` that
anticommutes with the corresponding weight-2 element, then no weight-2 Pauli is
in the centralizer of the stabilizer group generated by `genSet`. -/
theorem no_weight_two_mem_centralizer_of_anticommute_witness (S : StabilizerGroup n)
    (genSet : Set (NQubitPauliGroupElement n))
    (h_closure : S.toSubgroup = Subgroup.closure genSet)
    (h_anticomm : ∀ i j : Fin n, i ≠ j → ∀ P Q : PauliOperator, P ≠ .I → Q ≠ .I →
      ∃ g ∈ genSet, Anticommute (weightTwoAt i j P Q) g)
    (g : NQubitPauliGroupElement n) (hg : weight g = 2)
    (h_cent : g ∈ centralizer S) : False := by
  obtain ⟨i, j, hij, hi, hj, hop⟩ := exists_operators_eq_weightTwoAt g hg
  obtain ⟨s, hs, h_anti⟩ := h_anticomm i j hij _ _ hi hj
  exact not_mem_centralizer_of_anticommute_generator S genSet h_closure hop hs h_anti h_cent

/-- The degenerate counterpart of
`no_weight_two_mem_centralizer_of_anticommute_witness`. A weight-two pattern no
generator detects does lie in the centralizer, but it is harmless if it is a
stabilizer up to phase. So it suffices that every pattern is detected *or* has
the operator part of a stabilizer element: then no weight-two Pauli is a
nontrivial logical. -/
theorem no_weight_two_logical_of_anticommute_or_stabilizer (S : StabilizerGroup n)
    (genSet : Set (NQubitPauliGroupElement n))
    (h_closure : S.toSubgroup = Subgroup.closure genSet)
    (h_cases : ∀ i j : Fin n, i ≠ j → ∀ P Q : PauliOperator, P ≠ .I → Q ≠ .I →
      (∃ g ∈ genSet, Anticommute (weightTwoAt i j P Q) g) ∨
        ∃ s ∈ S.toSubgroup, s.operators = (weightTwoAt i j P Q).operators)
    (g : NQubitPauliGroupElement n) (hg : weight g = 2) :
    ¬IsNontrivialLogicalOperator g S := by
  rintro ⟨h_cent, h_ne⟩
  obtain ⟨i, j, hij, hi, hj, hop⟩ := exists_operators_eq_weightTwoAt g hg
  rcases h_cases i j hij _ _ hi hj with ⟨s, hs, h_anti⟩ | ⟨s, hs, hs_op⟩
  · exact not_mem_centralizer_of_anticommute_generator S genSet h_closure hop hs h_anti h_cent
  · exact h_ne s hs (hs_op.trans hop.symm)

/-!
## Distance 2 and 3

The only positive weight below `2` is `1`, so the weight-one anticommute
witness together with one nontrivial logical operator of weight `2` gives
distance `2`. Adding the weight-two anticommute witness and a nontrivial
logical operator of weight `3` gives distance `3`.
-/

/-- **Distance 2 from an anticommute witness.** If the stabilizer group of `C`
is generated by `genSet`, every weight-1 element `weightOneAt i P` anticommutes
with some generator, and some nontrivial logical operator has weight `2`, then
`C` has distance `2`. -/
theorem hasCodeDistance_two_of_anticommute_witness {k : ℕ} (C : StabilizerCode n k)
    (genSet : Set (NQubitPauliGroupElement n))
    (h_closure : C.toStabilizerGroup.toSubgroup = Subgroup.closure genSet)
    (h_anticomm : ∀ i : Fin n, ∀ P : PauliOperator, P ≠ .I →
      ∃ g ∈ genSet, Anticommute (weightOneAt i P) g)
    (h_witness : ∃ g, IsNontrivialLogicalOperator g C.toStabilizerGroup ∧ weight g = 2) :
    HasCodeDistance C 2 := by
  refine hasCodeDistance_of C 2 (by decide) h_witness ?_
  intro w hw_pos hw_lt g hg_weight h_nontrivial
  interval_cases w
  exact no_weight_one_mem_centralizer_of_anticommute_witness C.toStabilizerGroup
    genSet h_closure h_anticomm g hg_weight h_nontrivial.1

/-- **Distance 3 from anticommute witnesses.** If the stabilizer group of `C` is
generated by `genSet`, every weight-1 element `weightOneAt i P` and every
weight-2 element `weightTwoAt i j P Q` anticommutes with some generator, and
some nontrivial logical operator has weight `3`, then `C` has distance `3`. -/
theorem hasCodeDistance_three_of_anticommute_witness {k : ℕ} (C : StabilizerCode n k)
    (genSet : Set (NQubitPauliGroupElement n))
    (h_closure : C.toStabilizerGroup.toSubgroup = Subgroup.closure genSet)
    (h_one : ∀ i : Fin n, ∀ P : PauliOperator, P ≠ .I →
      ∃ g ∈ genSet, Anticommute (weightOneAt i P) g)
    (h_two : ∀ i j : Fin n, i ≠ j → ∀ P Q : PauliOperator, P ≠ .I → Q ≠ .I →
      ∃ g ∈ genSet, Anticommute (weightTwoAt i j P Q) g)
    (h_witness : ∃ g, IsNontrivialLogicalOperator g C.toStabilizerGroup ∧ weight g = 3) :
    HasCodeDistance C 3 := by
  refine hasCodeDistance_of C 3 (by decide) h_witness ?_
  intro w hw_pos hw_lt g hg_weight h_nontrivial
  interval_cases w
  · exact no_weight_one_mem_centralizer_of_anticommute_witness C.toStabilizerGroup genSet
      h_closure h_one g hg_weight h_nontrivial.1
  · exact no_weight_two_mem_centralizer_of_anticommute_witness C.toStabilizerGroup genSet
      h_closure h_two g hg_weight h_nontrivial.1

/-!
## Anticommutation of weight-1 and weight-2 elements, qubit by qubit

`weightOneAt i P` and `weightTwoAt i j P Q` are the identity away from the named
qubits, so the symplectic inner product with any `g` — which decides
anticommutation, by `anticommutes_iff_symplectic_inner_one` — collapses to one
or two single-qubit terms.
-/

/-- A weight-one Pauli anticommutes with `g` iff its single qubit does. -/
theorem anticommute_weightOneAt_iff (i : Fin n) (P : PauliOperator)
    (g : NQubitPauliGroupElement n) :
    Anticommute (weightOneAt i P) g ↔ symplecticProductSingle P (g.operators i) = 1 := by
  rw [NQubitPauliOperator.anticommutes_iff_symplectic_inner_one,
    NQubitPauliOperator.symplecticInner,
    Finset.sum_eq_single i (fun k _ hk => by simp [weightOneAt, hk]) (by simp)]
  simp [weightOneAt]

/-- A weight-two Pauli anticommutes with `g` iff exactly one of its two qubits
does. -/
theorem anticommute_weightTwoAt_iff {i j : Fin n} (hij : i ≠ j) (P Q : PauliOperator)
    (g : NQubitPauliGroupElement n) :
    Anticommute (weightTwoAt i j P Q) g ↔
      symplecticProductSingle P (g.operators i) +
        symplecticProductSingle Q (g.operators j) = 1 := by
  rw [NQubitPauliOperator.anticommutes_iff_symplectic_inner_one,
    NQubitPauliOperator.symplecticInner,
    Finset.sum_eq_add i j hij (fun k _ hk => by simp [weightTwoAt, hk.1, hk.2]) (by simp) (by simp)]
  simp [weightTwoAt, hij.symm]

/-!
## CSS checks as supports

A CSS generator is `Z` (or `X`) along a row of the classical parity-check matrix
and the identity elsewhere. `zOn S` / `xOn S` name that element by its support
`S`, so that a CSS code's generators can be handed to the distance closers below
as a family of `Finset`s.
-/

/-- The phase-0 element acting as `Z` on every qubit of `S` and trivially
elsewhere. -/
def zOn (S : Finset (Fin n)) : NQubitPauliGroupElement n :=
  ofOperator fun k => if k ∈ S then .Z else .I

/-- The phase-0 element acting as `X` on every qubit of `S` and trivially
elsewhere. -/
def xOn (S : Finset (Fin n)) : NQubitPauliGroupElement n :=
  ofOperator fun k => if k ∈ S then .X else .I

@[simp] lemma zOn_operators (S : Finset (Fin n)) (k : Fin n) :
    (zOn S).operators k = if k ∈ S then .Z else .I := rfl

@[simp] lemma xOn_operators (S : Finset (Fin n)) (k : Fin n) :
    (xOn S).operators k = if k ∈ S then .X else .I := rfl

/-- `Z` on a support is Z-type. -/
lemma IsZTypeElement_zOn (S : Finset (Fin n)) : IsZTypeElement (zOn S) :=
  ⟨rfl, fun k => by by_cases hk : k ∈ S <;> simp [hk, PauliOperator.IsZType]⟩

/-- `X` on a support is X-type. -/
lemma IsXTypeElement_xOn (S : Finset (Fin n)) : IsXTypeElement (xOn S) :=
  ⟨rfl, fun k => by by_cases hk : k ∈ S <;> simp [hk, PauliOperator.IsXType]⟩

/-- `Z` on `S` has weight `|S|`. -/
lemma weight_zOn (S : Finset (Fin n)) : weight (zOn S) = S.card := by
  simp [zOn, NQubitPauliOperator.weight, NQubitPauliOperator.support]

/-- `X` on `S` has weight `|S|`. -/
lemma weight_xOn (S : Finset (Fin n)) : weight (xOn S) = S.card := by
  simp [xOn, NQubitPauliOperator.weight, NQubitPauliOperator.support]

/-- `Z` on every qubit. -/
lemma zOn_univ : zOn (Finset.univ : Finset (Fin n)) = ⟨0, NQubitPauliOperator.Z n⟩ :=
  congrArg (NQubitPauliGroupElement.mk 0) (funext fun k => if_pos (Finset.mem_univ k))

/-- `X` on every qubit. -/
lemma xOn_univ : xOn (Finset.univ : Finset (Fin n)) = ⟨0, NQubitPauliOperator.X n⟩ :=
  congrArg (NQubitPauliGroupElement.mk 0) (funext fun k => if_pos (Finset.mem_univ k))

open scoped Pauli in
/-- `Z` on a single qubit. -/
lemma zOn_singleton (i : Fin n) : zOn {i} = σ[n | i ↦ Z] :=
  congrArg (NQubitPauliGroupElement.mk 0) <| funext fun k => by
    by_cases hi : k = i <;> simp [NQubitPauliOperator.set, NQubitPauliOperator.identity, hi]

open scoped Pauli in
/-- `X` on a single qubit. -/
lemma xOn_singleton (i : Fin n) : xOn {i} = σ[n | i ↦ X] :=
  congrArg (NQubitPauliGroupElement.mk 0) <| funext fun k => by
    by_cases hi : k = i <;> simp [NQubitPauliOperator.set, NQubitPauliOperator.identity, hi]

open scoped Pauli in
/-- `Z` on a pair of qubits. -/
lemma zOn_pair (i j : Fin n) : zOn {i, j} = σ[n | i ↦ Z, j ↦ Z] :=
  congrArg (NQubitPauliGroupElement.mk 0) <| funext fun k => by
    by_cases hi : k = i <;> by_cases hj : k = j <;>
      simp [NQubitPauliOperator.set, NQubitPauliOperator.identity, hi, hj]

open scoped Pauli in
/-- `X` on a pair of qubits. -/
lemma xOn_pair (i j : Fin n) : xOn {i, j} = σ[n | i ↦ X, j ↦ X] :=
  congrArg (NQubitPauliGroupElement.mk 0) <| funext fun k => by
    by_cases hi : k = i <;> by_cases hj : k = j <;>
      simp [NQubitPauliOperator.set, NQubitPauliOperator.identity, hi, hj]

/-- The `Z`-half of the check-matrix row of `zOn S` is the indicator of `S`. -/
@[simp] lemma toSymplectic_zOn_natAdd (S : Finset (Fin n)) (k : Fin n) :
    NQubitPauliOperator.toSymplectic (zOn S).operators (Fin.natAdd n k) =
      if k ∈ S then 1 else 0 := by
  rw [NQubitPauliOperator.toSymplectic_Z_part]
  by_cases hk : k ∈ S <;> simp [hk]

/-- The `X`-half of the check-matrix row of `zOn S` vanishes. -/
@[simp] lemma toSymplectic_zOn_castAdd (S : Finset (Fin n)) (k : Fin n) :
    NQubitPauliOperator.toSymplectic (zOn S).operators (Fin.castAdd n k) = 0 := by
  rw [NQubitPauliOperator.toSymplectic_X_part]
  by_cases hk : k ∈ S <;> simp [hk]

/-- The `X`-half of the check-matrix row of `xOn S` is the indicator of `S`. -/
@[simp] lemma toSymplectic_xOn_castAdd (S : Finset (Fin n)) (k : Fin n) :
    NQubitPauliOperator.toSymplectic (xOn S).operators (Fin.castAdd n k) =
      if k ∈ S then 1 else 0 := by
  rw [NQubitPauliOperator.toSymplectic_X_part]
  by_cases hk : k ∈ S <;> simp [hk]

/-- The `Z`-half of the check-matrix row of `xOn S` vanishes. -/
@[simp] lemma toSymplectic_xOn_natAdd (S : Finset (Fin n)) (k : Fin n) :
    NQubitPauliOperator.toSymplectic (xOn S).operators (Fin.natAdd n k) = 0 := by
  rw [NQubitPauliOperator.toSymplectic_Z_part]
  by_cases hk : k ∈ S <;> simp [hk]

/-- `X` on `S` and `Z` on `T` anticommute at the qubits of `S ∩ T`, so their
symplectic inner product is `|S ∩ T|` modulo `2`. -/
lemma symplecticInner_xOn_zOn (S T : Finset (Fin n)) :
    ⟪xOn S, zOn T⟫ₛ = ((S ∩ T).card : ZMod 2) := by
  have h : ∀ k, symplecticProductSingle ((xOn S).operators k) ((zOn T).operators k) =
      if k ∈ S ∩ T then 1 else 0 := fun k => by
    by_cases hS : k ∈ S <;> by_cases hT : k ∈ T <;> simp [hS, hT]
  rw [NQubitPauliOperator.symplecticInner, Finset.sum_congr rfl fun k _ => h k,
    Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.univ_inter]

/-- `X` on `S` commutes with `Z` on `T` iff the supports meet in an even number
of qubits. -/
lemma commutes_xOn_zOn_iff (S T : Finset (Fin n)) :
    xOn S * zOn T = zOn T * xOn S ↔ Even (S ∩ T).card := by
  rw [NQubitPauliOperator.commutes_iff_symplectic_inner_zero, symplecticInner_xOn_zOn,
    ZMod.natCast_eq_zero_iff_even]

/-- `X` on `S` anticommutes with `Z` on `T` iff the supports meet in an odd
number of qubits. -/
lemma anticommute_xOn_zOn_iff (S T : Finset (Fin n)) :
    Anticommute (xOn S) (zOn T) ↔ Odd (S ∩ T).card := by
  rw [NQubitPauliOperator.anticommutes_iff_symplectic_inner_one, symplecticInner_xOn_zOn,
    ZMod.natCast_eq_one_iff_odd]

/-- A `Z`-check on `S` detects the weight-one Pauli `P` at `i` iff `i ∈ S` and
`P` has an `X`-component (`P = X` or `P = Y`, i.e. `X`-bit `1`). -/
lemma anticommute_weightOneAt_zOn_iff (i : Fin n) (P : PauliOperator) (S : Finset (Fin n)) :
    Anticommute (weightOneAt i P) (zOn S) ↔ i ∈ S ∧ P.toSymplecticSingle.1 = 1 := by
  rw [anticommute_weightOneAt_iff]
  by_cases hi : i ∈ S <;> simp [hi]

/-- An `X`-check on `S` detects the weight-one Pauli `P` at `i` iff `i ∈ S` and
`P` has a `Z`-component (`P = Z` or `P = Y`, i.e. `Z`-bit `1`). -/
lemma anticommute_weightOneAt_xOn_iff (i : Fin n) (P : PauliOperator) (S : Finset (Fin n)) :
    Anticommute (weightOneAt i P) (xOn S) ↔ i ∈ S ∧ P.toSymplecticSingle.2 = 1 := by
  rw [anticommute_weightOneAt_iff]
  by_cases hi : i ∈ S <;> simp [hi]

/-- A `Z`-check on `S` detects a weight-two Pauli iff the `X`-bits it sees (at
`i` if `i ∈ S`, at `j` if `j ∈ S`) sum to `1`. -/
lemma anticommute_weightTwoAt_zOn_iff {i j : Fin n} (hij : i ≠ j) (P Q : PauliOperator)
    (S : Finset (Fin n)) :
    Anticommute (weightTwoAt i j P Q) (zOn S) ↔
      (if i ∈ S then P.toSymplecticSingle.1 else 0) +
        (if j ∈ S then Q.toSymplecticSingle.1 else 0) = 1 := by
  rw [anticommute_weightTwoAt_iff hij]
  by_cases hi : i ∈ S <;> by_cases hj : j ∈ S <;> simp [hi, hj]

/-- An `X`-check on `S` detects a weight-two Pauli iff the `Z`-bits it sees sum
to `1`. -/
lemma anticommute_weightTwoAt_xOn_iff {i j : Fin n} (hij : i ≠ j) (P Q : PauliOperator)
    (S : Finset (Fin n)) :
    Anticommute (weightTwoAt i j P Q) (xOn S) ↔
      (if i ∈ S then P.toSymplecticSingle.2 else 0) +
        (if j ∈ S then Q.toSymplecticSingle.2 else 0) = 1 := by
  rw [anticommute_weightTwoAt_iff hij]
  by_cases hi : i ∈ S <;> by_cases hj : j ∈ S <;> simp [hi, hj]

/-- `X` on a pair is `weightTwoAt` with `X` at both qubits. -/
lemma xOn_pair_operators (i j : Fin n) :
    (xOn {i, j}).operators = (weightTwoAt i j .X .X).operators := by
  funext k
  by_cases hki : k = i <;> by_cases hkj : k = j <;> simp [weightTwoAt, hki, hkj]

/-- `Z` on a pair is `weightTwoAt` with `Z` at both qubits. -/
lemma zOn_pair_operators (i j : Fin n) :
    (zOn {i, j}).operators = (weightTwoAt i j .Z .Z).operators := by
  funext k
  by_cases hki : k = i <;> by_cases hkj : k = j <;> simp [weightTwoAt, hki, hkj]

/-- `X` times `Z` on a pair is `Y` on the pair, up to phase. -/
lemma xOn_mul_zOn_pair_operators (i j : Fin n) :
    (xOn {i, j} * zOn {i, j}).operators = (weightTwoAt i j .Y .Y).operators := by
  funext k
  change (((xOn {i, j}).operators k).mulOp ((zOn {i, j}).operators k)).operator = _
  by_cases hki : k = i <;> by_cases hkj : k = j <;> simp [weightTwoAt, hki, hkj]

/-!
## Distance 3 for CSS codes: the column condition

Write a Pauli `E` as an `X`-support `A` (the qubits carrying `X` or `Y`) and a
`Z`-support `B` (those carrying `Z` or `Y`). `E` commutes with the `Z`-check on
row `S` iff `|A ∩ S|` is even, and with the `X`-check on `S` iff `|B ∩ S|` is
even. So `E` goes undetected iff `A` is a codeword of the classical code with
check rows `zRow` and `B` one of the code with check rows `xRow`. If both
classical codes have distance `≥ 3` — every column of the check matrix is
nonzero (`_cover`: each qubit lies on some row) and any two columns are distinct
(`_sep`: any two qubits are separated by some row) — then a codeword of weight
`≤ 2` is zero, so `|A|, |B| ≤ 2` forces `A = B = ∅`: no Pauli of weight `1` or
`2` is undetected.

`weight_one_anticomm_witness_of_columns` and
`weight_two_anticomm_witness_of_columns` are that argument at weights one and
two, phrased as the anticommute witnesses consumed by
`no_weight_one_mem_centralizer_of_anticommute_witness` and
`no_weight_two_mem_centralizer_of_anticommute_witness`;
`hasCodeDistance_three_of_columns` combines them with a nontrivial logical
operator of weight `3`. The model case is the Steane `[[7,1,3]]` code, whose
Hamming check matrix has exactly the seven nonzero columns of length three.
-/

section Columns

variable {ι κ : Type*} (zRow : ι → Finset (Fin n)) (xRow : κ → Finset (Fin n))
  (genSet : Set (NQubitPauliGroupElement n))

/-- No weight-one Pauli goes undetected when every qubit lies on a `Z`-row and
on an `X`-row. -/
theorem weight_one_anticomm_witness_of_columns
    (hz : ∀ r, zOn (zRow r) ∈ genSet) (hx : ∀ c, xOn (xRow c) ∈ genSet)
    (hz_cover : ∀ i, ∃ r, i ∈ zRow r) (hx_cover : ∀ i, ∃ c, i ∈ xRow c) :
    ∀ i : Fin n, ∀ P : PauliOperator, P ≠ .I →
      ∃ g ∈ genSet, Anticommute (weightOneAt i P) g := by
  intro i P hP
  rcases toSymplecticSingle_fst_eq_zero_or_one P with hPx | hPx
  · -- `P = Z`: any `X`-row through `i` detects it.
    obtain ⟨c, hc⟩ := hx_cover i
    exact ⟨xOn (xRow c), hx c, (anticommute_weightOneAt_xOn_iff i P _).mpr
      ⟨hc, toSymplecticSingle_snd_eq_one_of_fst_eq_zero hP hPx⟩⟩
  · -- `P ∈ {X, Y}`: any `Z`-row through `i` detects it.
    obtain ⟨r, hr⟩ := hz_cover i
    exact ⟨zOn (zRow r), hz r, (anticommute_weightOneAt_zOn_iff i P _).mpr ⟨hr, hPx⟩⟩

/-- No weight-two Pauli goes undetected when, in addition, any two qubits are
separated by a `Z`-row and by an `X`-row. -/
theorem weight_two_anticomm_witness_of_columns
    (hz : ∀ r, zOn (zRow r) ∈ genSet) (hx : ∀ c, xOn (xRow c) ∈ genSet)
    (hz_cover : ∀ i, ∃ r, i ∈ zRow r)
    (hz_sep : ∀ i j, i ≠ j → ∃ r, (i ∈ zRow r ↔ j ∉ zRow r))
    (hx_sep : ∀ i j, i ≠ j → ∃ c, (i ∈ xRow c ↔ j ∉ xRow c)) :
    ∀ i j : Fin n, i ≠ j → ∀ P Q : PauliOperator, P ≠ .I → Q ≠ .I →
      ∃ g ∈ genSet, Anticommute (weightTwoAt i j P Q) g := by
  intro i j hij P Q hP hQ
  rcases toSymplecticSingle_fst_eq_zero_or_one P with hPx | hPx <;>
    rcases toSymplecticSingle_fst_eq_zero_or_one Q with hQx | hQx
  · -- `P = Q = Z`: an `X`-row separating `i` from `j` sees exactly one of them.
    obtain ⟨c, hc⟩ := hx_sep i j hij
    refine ⟨xOn (xRow c), hx c, (anticommute_weightTwoAt_xOn_iff hij P Q _).mpr ?_⟩
    rw [toSymplecticSingle_snd_eq_one_of_fst_eq_zero hP hPx,
      toSymplecticSingle_snd_eq_one_of_fst_eq_zero hQ hQx]
    by_cases hi : i ∈ xRow c <;> simp_all
  · -- Only `Q` has an `X`-component: a `Z`-row through `j` sees it alone.
    obtain ⟨r, hr⟩ := hz_cover j
    refine ⟨zOn (zRow r), hz r, (anticommute_weightTwoAt_zOn_iff hij P Q _).mpr ?_⟩
    simp [hr, hPx, hQx]
  · -- Only `P` has an `X`-component: a `Z`-row through `i` sees it alone.
    obtain ⟨r, hr⟩ := hz_cover i
    refine ⟨zOn (zRow r), hz r, (anticommute_weightTwoAt_zOn_iff hij P Q _).mpr ?_⟩
    simp [hr, hPx, hQx]
  · -- Both have an `X`-component: a `Z`-row separating `i` from `j` sees exactly one.
    obtain ⟨r, hr⟩ := hz_sep i j hij
    refine ⟨zOn (zRow r), hz r, (anticommute_weightTwoAt_zOn_iff hij P Q _).mpr ?_⟩
    rw [hPx, hQx]
    by_cases hi : i ∈ zRow r <;> simp_all

/-- **Distance 3 from the column condition.** A CSS stabilizer code `C`,
generated by `genSet`, whose `Z`-checks `zOn (zRow r)` and `X`-checks
`xOn (xRow c)` lie in `genSet`, has distance exactly `3` as soon as both check
matrices have nonzero, pairwise distinct columns (classical distance `≥ 3` on
each side) and some nontrivial logical of weight `3` is exhibited. -/
theorem hasCodeDistance_three_of_columns {k : ℕ} (C : StabilizerCode n k)
    (h_closure : C.toStabilizerGroup.toSubgroup = Subgroup.closure genSet)
    (hz : ∀ r, zOn (zRow r) ∈ genSet) (hx : ∀ c, xOn (xRow c) ∈ genSet)
    (hz_cover : ∀ i, ∃ r, i ∈ zRow r) (hx_cover : ∀ i, ∃ c, i ∈ xRow c)
    (hz_sep : ∀ i j, i ≠ j → ∃ r, (i ∈ zRow r ↔ j ∉ zRow r))
    (hx_sep : ∀ i j, i ≠ j → ∃ c, (i ∈ xRow c ↔ j ∉ xRow c))
    (h_witness : ∃ g, IsNontrivialLogicalOperator g C.toStabilizerGroup ∧ weight g = 3) :
    HasCodeDistance C 3 :=
  hasCodeDistance_three_of_anticommute_witness C genSet h_closure
    (weight_one_anticomm_witness_of_columns zRow xRow genSet hz hx hz_cover hx_cover)
    (weight_two_anticomm_witness_of_columns zRow xRow genSet hz hx hz_cover hz_sep hx_sep)
    h_witness

/-!
### Degenerate codes: pairs the checks cannot separate

`hasCodeDistance_three_of_columns` needs both check matrices to have pairwise
distinct columns. A degenerate code can fail that and still have distance `3`.
In Shor's `[[9,1,3]]` code the two `X`-checks see the three qubits of a block
identically, so `Z₀Z₁` commutes with every check — but `Z₀Z₁` is itself a
stabilizer, not a logical.

The variant below trades each separation hypothesis for exactly that escape.
When the `Z`-rows do not separate `i` from `j`, `X` on `{i, j}` must be a
stabilizer (`hz_pair`); when the `X`-rows do not, `Z` on `{i, j}` must be
(`hx_pair`). An undetected weight-two Pauli is then `X X`, `Z Z` or `Y Y` on
such a pair, with the operator part of `xOn {i, j}`, `zOn {i, j}` or their
product. For a non-degenerate code the premises of `hz_pair` and `hx_pair`
never hold, so this generalizes `hasCodeDistance_three_of_columns`.
-/

/-- With nonzero columns, a weight-two Pauli on `{i, j}` is either detected by
some check, or `X X`, `Z Z` or `Y Y` on a pair the corresponding rows do not
separate — and then, by `hz_pair` / `hx_pair`, it has the operator part of a
stabilizer element. -/
theorem weight_two_anticomm_or_stabilizer_of_columns
    (hz : ∀ r, zOn (zRow r) ∈ genSet) (hx : ∀ c, xOn (xRow c) ∈ genSet)
    (hz_cover : ∀ i, ∃ r, i ∈ zRow r) (hx_cover : ∀ i, ∃ c, i ∈ xRow c)
    (hz_pair : ∀ i j, i ≠ j → (∀ r, i ∈ zRow r ↔ j ∈ zRow r) →
      xOn {i, j} ∈ Subgroup.closure genSet)
    (hx_pair : ∀ i j, i ≠ j → (∀ c, i ∈ xRow c ↔ j ∈ xRow c) →
      zOn {i, j} ∈ Subgroup.closure genSet) :
    ∀ i j : Fin n, i ≠ j → ∀ P Q : PauliOperator, P ≠ .I → Q ≠ .I →
      (∃ g ∈ genSet, Anticommute (weightTwoAt i j P Q) g) ∨
        ∃ s ∈ Subgroup.closure genSet, s.operators = (weightTwoAt i j P Q).operators := by
  intro i j hij P Q hP hQ
  -- A `Z`-row detects the pair iff it sees an odd number of `X`-components, an
  -- `X`-row iff it sees an odd number of `Z`-components.
  have zDet : ∀ r, (if i ∈ zRow r then P.toSymplecticSingle.1 else 0) +
      (if j ∈ zRow r then Q.toSymplecticSingle.1 else 0) = 1 →
      ∃ g ∈ genSet, Anticommute (weightTwoAt i j P Q) g :=
    fun r h => ⟨_, hz r, (anticommute_weightTwoAt_zOn_iff hij P Q _).mpr h⟩
  have xDet : ∀ c, (if i ∈ xRow c then P.toSymplecticSingle.2 else 0) +
      (if j ∈ xRow c then Q.toSymplecticSingle.2 else 0) = 1 →
      ∃ g ∈ genSet, Anticommute (weightTwoAt i j P Q) g :=
    fun c h => ⟨_, hx c, (anticommute_weightTwoAt_xOn_iff hij P Q _).mpr h⟩
  have hP' : P = .X ∨ P = .Y ∨ P = .Z := by cases P <;> first | exact absurd rfl hP | simp
  have hQ' : Q = .X ∨ Q = .Y ∨ Q = .Z := by cases Q <;> first | exact absurd rfl hQ | simp
  rcases hP' with rfl | rfl | rfl <;> rcases hQ' with rfl | rfl | rfl
  · -- `X X`: detected by a `Z`-row separating `i` from `j`, else `X` on the pair.
    by_cases h : ∀ r, i ∈ zRow r ↔ j ∈ zRow r
    · exact .inr ⟨_, hz_pair i j hij h, xOn_pair_operators i j⟩
    · obtain ⟨r, hr⟩ := not_forall.mp h
      exact .inl (zDet r (by
        by_cases hi : i ∈ zRow r <;> by_cases hj : j ∈ zRow r <;> simp [hi, hj] at hr ⊢))
  · -- `X Y`: only `j` has a `Z`-component; an `X`-row through `j` sees it.
    obtain ⟨c, hc⟩ := hx_cover j
    exact .inl (xDet c (by simp [hc]))
  · -- `X Z`: only `i` has an `X`-component; a `Z`-row through `i` sees it.
    obtain ⟨r, hr⟩ := hz_cover i
    exact .inl (zDet r (by simp [hr]))
  · -- `Y X`: only `i` has a `Z`-component.
    obtain ⟨c, hc⟩ := hx_cover i
    exact .inl (xDet c (by simp [hc]))
  · -- `Y Y`: detected unless neither row family separates the pair, and then it
    -- is `X` times `Z` on the pair.
    by_cases hzs : ∀ r, i ∈ zRow r ↔ j ∈ zRow r
    · by_cases hxs : ∀ c, i ∈ xRow c ↔ j ∈ xRow c
      · exact .inr ⟨_, Subgroup.mul_mem _ (hz_pair i j hij hzs) (hx_pair i j hij hxs),
          xOn_mul_zOn_pair_operators i j⟩
      · obtain ⟨c, hc⟩ := not_forall.mp hxs
        exact .inl (xDet c (by
          by_cases hi : i ∈ xRow c <;> by_cases hj : j ∈ xRow c <;> simp [hi, hj] at hc ⊢))
    · obtain ⟨r, hr⟩ := not_forall.mp hzs
      exact .inl (zDet r (by
        by_cases hi : i ∈ zRow r <;> by_cases hj : j ∈ zRow r <;> simp [hi, hj] at hr ⊢))
  · -- `Y Z`: only `i` has an `X`-component.
    obtain ⟨r, hr⟩ := hz_cover i
    exact .inl (zDet r (by simp [hr]))
  · -- `Z X`: only `j` has an `X`-component.
    obtain ⟨r, hr⟩ := hz_cover j
    exact .inl (zDet r (by simp [hr]))
  · -- `Z Y`: only `j` has an `X`-component.
    obtain ⟨r, hr⟩ := hz_cover j
    exact .inl (zDet r (by simp [hr]))
  · -- `Z Z`: detected by an `X`-row separating `i` from `j`, else `Z` on the pair.
    by_cases h : ∀ c, i ∈ xRow c ↔ j ∈ xRow c
    · exact .inr ⟨_, hx_pair i j hij h, zOn_pair_operators i j⟩
    · obtain ⟨c, hc⟩ := not_forall.mp h
      exact .inl (xDet c (by
        by_cases hi : i ∈ xRow c <;> by_cases hj : j ∈ xRow c <;> simp [hi, hj] at hc ⊢))

/-- **Distance 3 from the column condition, degenerate version.** As
`hasCodeDistance_three_of_columns`, but a pair of qubits need not be separated
by the checks: if no `Z`-row separates `i` from `j` it suffices that `X` on
`{i, j}` is a stabilizer, and if no `X`-row does, that `Z` on `{i, j}` is. -/
theorem hasCodeDistance_three_of_columns_degenerate {k : ℕ} (C : StabilizerCode n k)
    (h_closure : C.toStabilizerGroup.toSubgroup = Subgroup.closure genSet)
    (hz : ∀ r, zOn (zRow r) ∈ genSet) (hx : ∀ c, xOn (xRow c) ∈ genSet)
    (hz_cover : ∀ i, ∃ r, i ∈ zRow r) (hx_cover : ∀ i, ∃ c, i ∈ xRow c)
    (hz_pair : ∀ i j, i ≠ j → (∀ r, i ∈ zRow r ↔ j ∈ zRow r) →
      xOn {i, j} ∈ Subgroup.closure genSet)
    (hx_pair : ∀ i j, i ≠ j → (∀ c, i ∈ xRow c ↔ j ∈ xRow c) →
      zOn {i, j} ∈ Subgroup.closure genSet)
    (h_witness : ∃ g, IsNontrivialLogicalOperator g C.toStabilizerGroup ∧ weight g = 3) :
    HasCodeDistance C 3 := by
  refine hasCodeDistance_of C 3 (by decide) h_witness ?_
  intro w hw_pos hw_lt g hg_weight h_nontrivial
  interval_cases w
  · exact no_weight_one_mem_centralizer_of_anticommute_witness C.toStabilizerGroup genSet
      h_closure (weight_one_anticomm_witness_of_columns zRow xRow genSet hz hx hz_cover hx_cover)
      g hg_weight h_nontrivial.1
  · exact no_weight_two_logical_of_anticommute_or_stabilizer C.toStabilizerGroup genSet h_closure
      (h_closure ▸ weight_two_anticomm_or_stabilizer_of_columns zRow xRow genSet hz hx hz_cover
        hx_cover hz_pair hx_pair) g hg_weight h_nontrivial

end Columns

end StabilizerGroup
end Quantum
