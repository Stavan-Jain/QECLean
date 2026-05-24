import Mathlib.Tactic
import QEC.Stabilizer.Framework.Core.Stabilizer.StabilizerGroup
import QEC.Stabilizer.Framework.Core.Stabilizer.StabilizerCode
import QEC.Stabilizer.Framework.Core.Stabilizer.SubgroupLemmas
import QEC.Stabilizer.Framework.Core.CSS.CSSPredicates
import QEC.Stabilizer.Framework.Core.CSS.CSSNoNegI
import QEC.Stabilizer.Framework.Core.CSS.CSSCommutationLemmas
import QEC.Stabilizer.Framework.Core.CSS.CSSDistance
import QEC.Stabilizer.Framework.Core.Stabilizer.Centralizer
import QEC.Stabilizer.Framework.Core.Logical.CodeDistance
import QEC.Stabilizer.Framework.Core.Logical.LogicalOperators
import QEC.Stabilizer.Foundations.PauliGroup.Commutation
import QEC.Stabilizer.Foundations.PauliGroup.CommutationTactics
import QEC.Stabilizer.Foundations.PauliGroup.NQubitOperator
import QEC.Stabilizer.Foundations.PauliGroup.NQubitElement
import QEC.Stabilizer.Foundations.BinarySymplectic.Core
import QEC.Stabilizer.Foundations.BinarySymplectic.CheckMatrix
import QEC.Stabilizer.Foundations.BinarySymplectic.CheckMatrixDecidable
import QEC.Stabilizer.Foundations.BinarySymplectic.SymplecticInner
import QEC.Stabilizer.Framework.Symplectic.IndependentEquiv

namespace Quantum
open scoped BigOperators

namespace StabilizerGroup
namespace GOY

/-!
# The Ganti-Onunkwo-Young `[[6r, 2r, 2]]` code family

A parametric CSS quantum error-detecting code on `n = 6r` physical qubits
with `k = 2r` logical qubits and distance `d = 2`. Introduced in
[Ganti–Onunkwo–Young 2013, `arxiv:1309.1674`] to support practical scalable
adiabatic quantum computation. See EC Zoo: `https://errorcorrectionzoo.org/c/goy`.

## Parameters

- Physical qubits: `n = 6r`
- Logical qubits: `k = 2r`
- Distance: `d = 2`
- Family: CSS, **variable-weight stabilizers** (2 and 4r weights)
- Parameter constraint: `[Fact (1 ≤ r)]` (`r = 0` gives a trivial empty code)

## Qubit indexing (0-based, row-major)

For `i : Fin (2r)`, the three physical qubits of "logical row i" are:

```
qubit_x i := 3 * i.val      ∈ Fin (6r)    -- paper (i+1, x)
qubit_0 i := 3 * i.val + 1  ∈ Fin (6r)    -- paper (i+1, 0)
qubit_z i := 3 * i.val + 2  ∈ Fin (6r)    -- paper (i+1, z)
```

## Stabilizer generators (from [GOY Eq. (3), §III, p.3])

4r generators total: `2r − 1` weight-2 X-links + 1 weight-4r XBig +
`2r − 1` weight-2 Z-links + 1 weight-4r ZBig.

```
XLink i := X X on qubits {qubit_x i, qubit_x (i+1)}     for i ∈ Fin (2r-1)
XBig    := X on every (i,0) and (i,z) qubit             (weight 4r)
ZLink i := Z Z on qubits {qubit_z i, qubit_z (i+1)}     for i ∈ Fin (2r-1)
ZBig    := Z on every (i,x) and (i,0) qubit             (weight 4r)
```

## Logical operators (from [GOY Eq. (4), §III, p.3])

For each `i : Fin (2r)`:

```
logicalX i := X on qubits {qubit_x i, qubit_0 i}    (weight 2)
logicalZ i := Z on qubits {qubit_0 i, qubit_z i}    (weight 2)
```

Diagonal anticommutation: at qubit `(i, 0) = qubit_0 i`, logicalX has X and
logicalZ has Z; these anticommute. At qubit `(i, x)` only logicalX is
non-identity; at qubit `(i, z)` only logicalZ. Anticomm cardinality 1, odd.
Off-diagonal pairs `(logicalX i, logicalZ j)` for `i ≠ j` have disjoint
row-supports; anticomm cardinality 0, even.

## Relation to `Codes/Small/SixQubit_6_2_2.lean` (the C_6 case)

At `r = 1`, this is the [[6, 2, 2]] C_6 code per the EC Zoo. Our
formalization uses GOY's natural presentation (2 weight-2 + 2 weight-4
generators), while `SixQubit_6_2_2.lean` uses Knill's presentation (4
weight-4 generators). Both describe the **same code subspace**, but the
two stabilizer groups are not generator-equal; we do NOT prove the
subgroup equality here (mirroring `Iceberg/N.lean` ↔ `FourQubit_4_2_2.lean`).

## File status

**Stage-2 skeleton.** Every theorem ends in a `sorry` tagged
`TODO(goy-T<n>): <one-line hint>`. Stage 4 closes them. The proof
strategies are documented in `pipeline/attempts/goy/plan.md`.
-/

open NQubitPauliGroupElement

/-! ## Local convenience: physical-qubit accessors

For each logical-row index `i : Fin (2r)`, the three physical qubits of
that row are at indices `3 * i.val + {0, 1, 2}` in `Fin (6r)`.
-/

/-- x-qubit of logical row `i`: physical-qubit index `3 * i.val`. -/
@[inline] private def qubit_x {r : ℕ} [Fact (1 ≤ r)] (i : Fin (2 * r)) :
    Fin (6 * r) :=
  ⟨3 * i.val, by
    have h : 1 ≤ r := Fact.out
    have hi : i.val < 2 * r := i.isLt
    omega⟩

/-- 0-qubit of logical row `i`: physical-qubit index `3 * i.val + 1`. -/
@[inline] private def qubit_0 {r : ℕ} [Fact (1 ≤ r)] (i : Fin (2 * r)) :
    Fin (6 * r) :=
  ⟨3 * i.val + 1, by
    have h : 1 ≤ r := Fact.out
    have hi : i.val < 2 * r := i.isLt
    omega⟩

/-- z-qubit of logical row `i`: physical-qubit index `3 * i.val + 2`. -/
@[inline] private def qubit_z {r : ℕ} [Fact (1 ≤ r)] (i : Fin (2 * r)) :
    Fin (6 * r) :=
  ⟨3 * i.val + 2, by
    have h : 1 ≤ r := Fact.out
    have hi : i.val < 2 * r := i.isLt
    omega⟩

/-- Embed a link-index `i : Fin (2r-1)` as the "left endpoint" row-index in
`Fin (2r)` (= `i.val`). -/
@[inline] private def linkIdx {r : ℕ} [Fact (1 ≤ r)] (i : Fin (2 * r - 1)) :
    Fin (2 * r) :=
  ⟨i.val, by
    have h : 1 ≤ r := Fact.out
    have hi : i.val < 2 * r - 1 := i.isLt
    omega⟩

/-- Embed a link-index `i : Fin (2r-1)` as the "right endpoint" row-index in
`Fin (2r)` (= `i.val + 1`). -/
@[inline] private def linkIdxSucc {r : ℕ} [Fact (1 ≤ r)] (i : Fin (2 * r - 1)) :
    Fin (2 * r) :=
  ⟨i.val + 1, by
    have h : 1 ≤ r := Fact.out
    have hi : i.val < 2 * r - 1 := i.isLt
    omega⟩

/-! ### Distinctness lemmas (used in filter equalities throughout) -/

private lemma qubit_x_ne_qubit_0 {r : ℕ} [Fact (1 ≤ r)] (i j : Fin (2 * r)) :
    qubit_x i ≠ qubit_0 j := by
  intro heq
  have := congrArg Fin.val heq
  simp only [qubit_x, qubit_0] at this
  omega

private lemma qubit_x_ne_qubit_z {r : ℕ} [Fact (1 ≤ r)] (i j : Fin (2 * r)) :
    qubit_x i ≠ qubit_z j := by
  intro heq
  have := congrArg Fin.val heq
  simp only [qubit_x, qubit_z] at this
  omega

private lemma qubit_0_ne_qubit_z {r : ℕ} [Fact (1 ≤ r)] (i j : Fin (2 * r)) :
    qubit_0 i ≠ qubit_z j := by
  intro heq
  have := congrArg Fin.val heq
  simp only [qubit_0, qubit_z] at this
  omega

private lemma qubit_x_inj {r : ℕ} [Fact (1 ≤ r)] {i j : Fin (2 * r)}
    (h : qubit_x i = qubit_x j) : i = j := by
  have := congrArg Fin.val h
  simp only [qubit_x] at this
  apply Fin.ext
  omega

private lemma qubit_0_inj {r : ℕ} [Fact (1 ≤ r)] {i j : Fin (2 * r)}
    (h : qubit_0 i = qubit_0 j) : i = j := by
  have := congrArg Fin.val h
  simp only [qubit_0] at this
  apply Fin.ext
  omega

private lemma qubit_z_inj {r : ℕ} [Fact (1 ≤ r)] {i j : Fin (2 * r)}
    (h : qubit_z i = qubit_z j) : i = j := by
  have := congrArg Fin.val h
  simp only [qubit_z] at this
  apply Fin.ext
  omega

private lemma linkIdx_ne_linkIdxSucc {r : ℕ} [Fact (1 ≤ r)]
    (i : Fin (2 * r - 1)) : linkIdx i ≠ linkIdxSucc i := by
  intro heq
  have := congrArg Fin.val heq
  simp only [linkIdx, linkIdxSucc] at this
  omega

/-! ## §1 — Generators

GOY has 4 generator types, listed below in the order the paper presents
them (Eq. (3)):

1. `XLink i` for `i : Fin (2r-1)`: weight-2 X stabilizer on adjacent x-qubits.
2. `XBig`: weight-4r all-X stabilizer on all 0- and z-qubits.
3. `ZLink i` for `i : Fin (2r-1)`: weight-2 Z stabilizer on adjacent z-qubits.
4. `ZBig`: weight-4r all-Z stabilizer on all x- and 0-qubits.
-/

/-- X-link generator `i ∈ Fin (2r-1)`: X on qubits `{qubit_x (linkIdx i),
qubit_x (linkIdxSucc i)}`. Weight 2. -/
def XLink (r : ℕ) [Fact (1 ≤ r)] (i : Fin (2 * r - 1)) :
    NQubitPauliGroupElement (6 * r) :=
  ⟨0,
    ((NQubitPauliOperator.identity (6 * r)).set (qubit_x (linkIdx i)) PauliOperator.X).set
      (qubit_x (linkIdxSucc i)) PauliOperator.X⟩

/-- Z-link generator `i ∈ Fin (2r-1)`: Z on qubits `{qubit_z (linkIdx i),
qubit_z (linkIdxSucc i)}`. Weight 2. -/
def ZLink (r : ℕ) [Fact (1 ≤ r)] (i : Fin (2 * r - 1)) :
    NQubitPauliGroupElement (6 * r) :=
  ⟨0,
    ((NQubitPauliOperator.identity (6 * r)).set (qubit_z (linkIdx i)) PauliOperator.Z).set
      (qubit_z (linkIdxSucc i)) PauliOperator.Z⟩

/-- The all-X "big" generator: X at every 0-qubit and every z-qubit (the
qubits with `i.val % 3 ∈ {1, 2}`). Weight `4r`. -/
def XBig (r : ℕ) [Fact (1 ≤ r)] : NQubitPauliGroupElement (6 * r) :=
  ⟨0, fun k => if k.val % 3 = 0 then PauliOperator.I else PauliOperator.X⟩

/-- The all-Z "big" generator: Z at every x-qubit and every 0-qubit (the
qubits with `i.val % 3 ∈ {0, 1}`). Weight `4r`. -/
def ZBig (r : ℕ) [Fact (1 ≤ r)] : NQubitPauliGroupElement (6 * r) :=
  ⟨0, fun k => if k.val % 3 = 2 then PauliOperator.I else PauliOperator.Z⟩

/-! ## §2 — Generator sets and subgroup

The Z-generators set is the union of all `ZLink i` and `{ZBig}`; symmetric
for X.
-/

/-- The set of Z-generators: `{ZLink i : i ∈ Fin (2r-1)} ∪ {ZBig}`. -/
def ZGenerators (r : ℕ) [Fact (1 ≤ r)] : Set (NQubitPauliGroupElement (6 * r)) :=
  (Set.range (ZLink r)) ∪ {ZBig r}

/-- The set of X-generators: `{XLink i : i ∈ Fin (2r-1)} ∪ {XBig}`. -/
def XGenerators (r : ℕ) [Fact (1 ≤ r)] : Set (NQubitPauliGroupElement (6 * r)) :=
  (Set.range (XLink r)) ∪ {XBig r}

/-- Full generator set: Z-side ∪ X-side. -/
def generators (r : ℕ) [Fact (1 ≤ r)] : Set (NQubitPauliGroupElement (6 * r)) :=
  ZGenerators r ∪ XGenerators r

/-- The GOY stabilizer subgroup: closure of all `4r` generators. -/
noncomputable def subgroup (r : ℕ) [Fact (1 ≤ r)] :
    Subgroup (NQubitPauliGroupElement (6 * r)) :=
  Subgroup.closure (generators r)

/-! ## §3 — Z-type / X-type predicates

Each generator (link or big) is uniformly Z-type or X-type by construction.
-/

/-- T1: every `ZLink i` is Z-type (Z on two specific qubits, I elsewhere). -/
lemma ZLink_isZType (r : ℕ) [Fact (1 ≤ r)] (i : Fin (2 * r - 1)) :
    NQubitPauliGroupElement.IsZTypeElement (ZLink r i) := by
  sorry  -- TODO(goy-T1): split_ifs on qubit position; IsZType for Z and I

/-- T2: `ZBig r` is Z-type (Z or I at every qubit, depending on `i.val % 3`). -/
lemma ZBig_isZType (r : ℕ) [Fact (1 ≤ r)] :
    NQubitPauliGroupElement.IsZTypeElement (ZBig r) := by
  sorry  -- TODO(goy-T2): mod-3 case analysis on qubit role

/-- T3: every `XLink i` is X-type. Mirror of T1. -/
lemma XLink_isXType (r : ℕ) [Fact (1 ≤ r)] (i : Fin (2 * r - 1)) :
    NQubitPauliGroupElement.IsXTypeElement (XLink r i) := by
  sorry  -- TODO(goy-T3): mirror of T1 with Z↔X

/-- T4: `XBig r` is X-type. Mirror of T2. -/
lemma XBig_isXType (r : ℕ) [Fact (1 ≤ r)] :
    NQubitPauliGroupElement.IsXTypeElement (XBig r) := by
  sorry  -- TODO(goy-T4): mirror of T2 with Z↔X

/-- T5: every element of `ZGenerators r` is Z-type. -/
lemma ZGenerators_are_ZType (r : ℕ) [Fact (1 ≤ r)] :
    ∀ g, g ∈ ZGenerators r → NQubitPauliGroupElement.IsZTypeElement g := by
  sorry  -- TODO(goy-T5): rcases hg into Set.range case (T1) or singleton case (T2)

/-- T6: every element of `XGenerators r` is X-type. -/
lemma XGenerators_are_XType (r : ℕ) [Fact (1 ≤ r)] :
    ∀ g, g ∈ XGenerators r → NQubitPauliGroupElement.IsXTypeElement g := by
  sorry  -- TODO(goy-T6): mirror of T5

/-! ## §4 — Cross-commutation (Z-generators commute with X-generators)

Four cases (T7a-d):
- ZLink · XLink: disjoint qubit roles (z vs x, mod-3 distinct). Commute via
  componentwise.
- ZLink · XBig: overlap at the two z-qubits of the link, count 2 (even).
- ZBig · XLink: overlap at the two x-qubits of the link, count 2 (even).
- ZBig · XBig: overlap at all 0-qubits, count `2r` (even).
-/

private lemma ZLink_comm_XLink (r : ℕ) [Fact (1 ≤ r)]
    (i j : Fin (2 * r - 1)) :
    ZLink r i * XLink r j = XLink r j * ZLink r i := by
  sorry  -- TODO(goy-T7a): pauli_comm_componentwise (disjoint x- vs z-qubit roles)

private lemma ZLink_comm_XBig (r : ℕ) [Fact (1 ≤ r)] (i : Fin (2 * r - 1)) :
    ZLink r i * XBig r = XBig r * ZLink r i := by
  -- TODO(goy-T7b): pauli_comm_even_anticommutes; filter equals the two
  -- z-qubits of the link, cardinality 2.
  sorry

private lemma ZBig_comm_XLink (r : ℕ) [Fact (1 ≤ r)] (i : Fin (2 * r - 1)) :
    ZBig r * XLink r i = XLink r i * ZBig r := by
  -- TODO(goy-T7c): pauli_comm_even_anticommutes; filter equals the two
  -- x-qubits of the link, cardinality 2.
  sorry

private lemma ZBig_comm_XBig (r : ℕ) [Fact (1 ≤ r)] :
    ZBig r * XBig r = XBig r * ZBig r := by
  -- TODO(goy-T7d): pauli_comm_even_anticommutes; filter is the image of
  -- `qubit_0` (all 0-qubits), cardinality `2 * r`, even.
  sorry

/-- T7: every Z-generator commutes with every X-generator. -/
lemma ZGenerators_commute_XGenerators (r : ℕ) [Fact (1 ≤ r)] :
    ∀ z ∈ ZGenerators r, ∀ x ∈ XGenerators r, z * x = x * z := by
  -- TODO(goy-T7): 4-way rcases over ZGenerators / XGenerators set
  -- membership; dispatch to T7a-d.
  sorry

/-! ## §5 — All-pair commutation -/

private lemma ZType_commutes {r : ℕ} [Fact (1 ≤ r)] {g h : NQubitPauliGroupElement (6 * r)}
    (hg : NQubitPauliGroupElement.IsZTypeElement g)
    (hh : NQubitPauliGroupElement.IsZTypeElement h) :
    g * h = h * g :=
  CSSCommutationLemmas.ZType_commutes hg hh

private lemma XType_commutes {r : ℕ} [Fact (1 ≤ r)] {g h : NQubitPauliGroupElement (6 * r)}
    (hg : NQubitPauliGroupElement.IsXTypeElement g)
    (hh : NQubitPauliGroupElement.IsXTypeElement h) :
    g * h = h * g :=
  CSSCommutationLemmas.XType_commutes hg hh

/-- T8: all generators pairwise commute. -/
theorem generators_commute (r : ℕ) [Fact (1 ≤ r)] :
    ∀ g ∈ generators r, ∀ h ∈ generators r, g * h = h * g := by
  sorry  -- TODO(goy-T8): CSS structural argument via T5, T6, T7

/-! ## §6 — `−I` is not in the stabilizer subgroup -/

/-- T9: `−I` is not in the GOY stabilizer subgroup (CSS argument). -/
theorem negIdentity_not_mem (r : ℕ) [Fact (1 ≤ r)] :
    negIdentity (6 * r) ∉ subgroup r := by
  sorry  -- TODO(goy-T9): CSS.negIdentity_not_mem_closure_union consuming T5, T6, T7

/-! ## §7 — Generator list and `listToSet` equality

The list form is: ZLinks (in `Fin (2r-1)` order) ++ [ZBig] ++ XLinks ++ [XBig].
Length = (2r-1) + 1 + (2r-1) + 1 = 4r = n - k.
-/

/-- The generator list, canonical order: Z-links, then ZBig, then X-links,
then XBig. Length `4r`. -/
def generatorsList (r : ℕ) [Fact (1 ≤ r)] :
    List (NQubitPauliGroupElement (6 * r)) :=
  ((List.finRange (2 * r - 1)).map (ZLink r) ++ [ZBig r]) ++
  ((List.finRange (2 * r - 1)).map (XLink r) ++ [XBig r])

/-- T10: the generator list and the generator set agree. -/
lemma listToSet_generatorsList (r : ℕ) [Fact (1 ≤ r)] :
    NQubitPauliGroupElement.listToSet (generatorsList r) = generators r := by
  sorry  -- TODO(goy-T10): unfold; map listToSet over Set.range + singleton; ext g; mem dispatch

/-- T11: all generators have phase 0. -/
lemma AllPhaseZero_generatorsList (r : ℕ) [Fact (1 ≤ r)] :
    NQubitPauliGroupElement.AllPhaseZero (generatorsList r) := by
  sorry  -- TODO(goy-T11): AllPhaseZero closed under append + map; each constructor has phase 0

/-- T12 (the hardest theorem): the check-matrix rows of `generatorsList r` are
linearly independent over `ZMod 2`. The matrix has block-diagonal X-side /
Z-side structure; within each block, the 2r-1 link rows form a path-graph
incidence pattern over the (x or z)-qubit columns, and the "big" row lives
in the complementary 0-qubit-and-other columns. Cascading column
specializations peel off the link coefficients in order. -/
theorem rowsLinearIndependent_generatorsList (r : ℕ) [Fact (1 ≤ r)] :
    NQubitPauliGroupElement.rowsLinearIndependent (generatorsList r) := by
  sorry  -- TODO(goy-T12): chain-independence cascade — see plan.md § T12

theorem GeneratorsIndependent_generatorsList (r : ℕ) [Fact (1 ≤ r)] :
    GeneratorsIndependent (6 * r) (generatorsList r) :=
  GeneratorsIndependent_of_rowsLinearIndependent (6 * r) (generatorsList r)
    (rowsLinearIndependent_generatorsList r)

/-! ## §8 — Bundled `StabilizerGroup (6 * r)` -/

/-- T13: the GOY stabilizer group from the generator list. -/
noncomputable def stabilizerGroup (r : ℕ) [Fact (1 ≤ r)] :
    StabilizerGroup (6 * r) :=
  mkStabilizerFromGenerators (6 * r) (generatorsList r)
    (by rw [listToSet_generatorsList]; exact generators_commute r)
    (by rw [listToSet_generatorsList]; exact negIdentity_not_mem r)

/-- T14: the bundled stabilizer group's underlying subgroup equals the set-form
closure. -/
lemma stabilizerGroup_toSubgroup_eq (r : ℕ) [Fact (1 ≤ r)] :
    (stabilizerGroup r).toSubgroup = subgroup r := by
  sorry  -- TODO(goy-T14): unfold; rw [listToSet_generatorsList]

/-! ## §10 — Logical operators

For each `i : Fin (2r)`:
- `logicalX r i`: X at qubits `{qubit_x i, qubit_0 i}` (weight 2)
- `logicalZ r i`: Z at qubits `{qubit_0 i, qubit_z i}` (weight 2)
-/

/-- Logical X for logical-qubit `i`: X on qubits `qubit_x i` and `qubit_0 i`. -/
def logicalX (r : ℕ) [Fact (1 ≤ r)] (i : Fin (2 * r)) :
    NQubitPauliGroupElement (6 * r) :=
  ⟨0,
    ((NQubitPauliOperator.identity (6 * r)).set (qubit_x i) PauliOperator.X).set
      (qubit_0 i) PauliOperator.X⟩

/-- Logical Z for logical-qubit `i`: Z on qubits `qubit_0 i` and `qubit_z i`. -/
def logicalZ (r : ℕ) [Fact (1 ≤ r)] (i : Fin (2 * r)) :
    NQubitPauliGroupElement (6 * r) :=
  ⟨0,
    ((NQubitPauliOperator.identity (6 * r)).set (qubit_0 i) PauliOperator.Z).set
      (qubit_z i) PauliOperator.Z⟩

/-! ## §11 — Logical (anti)commutation -/

/-- T15: diagonal anticommutation `X̄_i ⊥ Z̄_i`. Anticomm support is exactly
`{qubit_0 i}` (cardinality 1, odd). -/
theorem logicalX_anticommutes_logicalZ_diag (r : ℕ) [Fact (1 ≤ r)]
    (i : Fin (2 * r)) :
    NQubitPauliGroupElement.Anticommute (logicalX r i) (logicalZ r i) := by
  sorry
  -- TODO(goy-T15): pauli_anticomm_odd_anticommutes; filter = {qubit_0 i}, card 1, odd

/-- T16a: `X̄_i * X̄_j = X̄_j * X̄_i` (always — both X-type). -/
theorem logicalX_commutes_logicalX (r : ℕ) [Fact (1 ≤ r)]
    (i j : Fin (2 * r)) :
    logicalX r i * logicalX r j = logicalX r j * logicalX r i := by
  sorry
  -- TODO(goy-T16a): commutes_of_componentwise_commutes; per-qubit split_ifs; X·X = X·X

/-- T16b: `Z̄_i * Z̄_j = Z̄_j * Z̄_i` (always — both Z-type). -/
theorem logicalZ_commutes_logicalZ (r : ℕ) [Fact (1 ≤ r)]
    (i j : Fin (2 * r)) :
    logicalZ r i * logicalZ r j = logicalZ r j * logicalZ r i := by
  sorry
  -- TODO(goy-T16b): commutes_of_componentwise_commutes; per-qubit Z·Z = Z·Z

/-- T16c: `X̄_i * Z̄_j = Z̄_j * X̄_i` when `i ≠ j` (disjoint row-supports). -/
theorem logicalX_commutes_logicalZ_offdiag (r : ℕ) [Fact (1 ≤ r)]
    {i j : Fin (2 * r)} (hij : i ≠ j) :
    logicalX r i * logicalZ r j = logicalZ r j * logicalX r i := by
  -- TODO(goy-T16c): commutes_of_componentwise_commutes; row-disjoint
  -- supports — `qubit_x i, qubit_0 i ∉ {qubit_0 j, qubit_z j}` when i ≠ j
  -- (via omega on 3i, 3i+1, 3j+1, 3j+2).
  sorry

/-! ## §12 — Logicals in the centralizer

Per-generator commutation lemmas (each logical × each generator type):

- `logicalX_commutes_XLink j`, `logicalX_commutes_XBig`: same-type (X). Trivial.
- `logicalX_commutes_ZLink j`: disjoint roles (x- vs z-qubits). Componentwise.
- `logicalX_commutes_ZBig`: overlap = {qubit_x i, qubit_0 i}, count 2, even.

Symmetric for `logicalZ`.
-/

private lemma logicalX_commutes_XLink (r : ℕ) [Fact (1 ≤ r)]
    (i : Fin (2 * r)) (j : Fin (2 * r - 1)) :
    logicalX r i * XLink r j = XLink r j * logicalX r i := by
  sorry
  -- TODO(goy-logX-XLink): both X-type, commutes_of_componentwise_commutes

private lemma logicalX_commutes_XBig (r : ℕ) [Fact (1 ≤ r)]
    (i : Fin (2 * r)) :
    logicalX r i * XBig r = XBig r * logicalX r i := by
  sorry
  -- TODO(goy-logX-XBig): both X-type, commutes_of_componentwise_commutes

private lemma logicalX_commutes_ZLink (r : ℕ) [Fact (1 ≤ r)]
    (i : Fin (2 * r)) (j : Fin (2 * r - 1)) :
    logicalX r i * ZLink r j = ZLink r j * logicalX r i := by
  -- TODO(goy-logX-ZLink): disjoint roles (logicalX at x- and 0-qubits;
  -- ZLink at z-qubits). commutes_of_componentwise_commutes.
  sorry

private lemma logicalX_commutes_ZBig (r : ℕ) [Fact (1 ≤ r)]
    (i : Fin (2 * r)) :
    logicalX r i * ZBig r = ZBig r * logicalX r i := by
  -- TODO(goy-logX-ZBig): pauli_comm_even_anticommutes;
  -- filter = {qubit_x i, qubit_0 i}, cardinality 2.
  sorry

private lemma logicalZ_commutes_XLink (r : ℕ) [Fact (1 ≤ r)]
    (i : Fin (2 * r)) (j : Fin (2 * r - 1)) :
    logicalZ r i * XLink r j = XLink r j * logicalZ r i := by
  -- TODO(goy-logZ-XLink): disjoint roles (logicalZ at 0- and z-qubits;
  -- XLink at x-qubits). commutes_of_componentwise_commutes.
  sorry

private lemma logicalZ_commutes_XBig (r : ℕ) [Fact (1 ≤ r)]
    (i : Fin (2 * r)) :
    logicalZ r i * XBig r = XBig r * logicalZ r i := by
  -- TODO(goy-logZ-XBig): pauli_comm_even_anticommutes;
  -- filter = {qubit_0 i, qubit_z i}, cardinality 2.
  sorry

private lemma logicalZ_commutes_ZLink (r : ℕ) [Fact (1 ≤ r)]
    (i : Fin (2 * r)) (j : Fin (2 * r - 1)) :
    logicalZ r i * ZLink r j = ZLink r j * logicalZ r i := by
  sorry
  -- TODO(goy-logZ-ZLink): both Z-type, commutes_of_componentwise_commutes

private lemma logicalZ_commutes_ZBig (r : ℕ) [Fact (1 ≤ r)]
    (i : Fin (2 * r)) :
    logicalZ r i * ZBig r = ZBig r * logicalZ r i := by
  sorry
  -- TODO(goy-logZ-ZBig): both Z-type, commutes_of_componentwise_commutes

/-- T17: every `logicalX r i` is in the centralizer of the stabilizer. -/
theorem logicalX_mem_centralizer (r : ℕ) [Fact (1 ≤ r)]
    (i : Fin (2 * r)) :
    logicalX r i ∈ centralizer (stabilizerGroup r) := by
  sorry
  -- TODO(goy-T17): mem_centralizer_iff_closure + forall_comm_closure_iff
  -- + 4-way dispatch over ZLink / ZBig / XLink / XBig (T7 helpers above)

/-- T18: every `logicalZ r i` is in the centralizer of the stabilizer. -/
theorem logicalZ_mem_centralizer (r : ℕ) [Fact (1 ≤ r)]
    (i : Fin (2 * r)) :
    logicalZ r i ∈ centralizer (stabilizerGroup r) := by
  sorry
  -- TODO(goy-T18): mirror of T17 for logicalZ

/-! ## §13 — `StabilizerCode (6 * r) (2 * r)` packaging -/

/-- The `2r`-many-logical-qubit data for the GOY code. -/
private def logicalOpsGOY (r : ℕ) [Fact (1 ≤ r)] :
    Fin (2 * r) → LogicalQubitOps (6 * r) (stabilizerGroup r) :=
  fun i => ⟨logicalX r i, logicalZ r i,
    logicalX_mem_centralizer r i, logicalZ_mem_centralizer r i,
    logicalX_anticommutes_logicalZ_diag r i⟩

/-- T19: the GOY code as a stabilizer code `[[6r, 2r]]`. -/
noncomputable def stabilizerCode (r : ℕ) [Fact (1 ≤ r)] :
    StabilizerCode (6 * r) (2 * r) where
  hk := by
    have h : 1 ≤ r := Fact.out
    omega
  generatorsList := generatorsList r
  generators_length := by
    -- |ZLinks ++ [ZBig] ++ XLinks ++ [XBig]| = (2r-1) + 1 + (2r-1) + 1 = 4r = 6r - 2r
    sorry  -- TODO(goy-T19-length): simp [generatorsList, List.length_*]; omega
  generators_phaseZero := AllPhaseZero_generatorsList r
  generators_independent := GeneratorsIndependent_generatorsList r
  generators_commute := by
    rw [listToSet_generatorsList]; exact generators_commute r
  closure_no_neg_identity := by
    rw [listToSet_generatorsList]; exact negIdentity_not_mem r
  logicalOps := logicalOpsGOY r
  logical_commute_cross := by
    -- TODO(goy-T19-cross): structural-refine pattern from Iceberg/N.lean
    -- — uses T16a (logicalX·logicalX), T16b (logicalZ·logicalZ),
    -- T16c (logicalX·logicalZ off-diagonal).
    sorry

/-! ## §14 — Code distance = 2 -/

/-- T20: bridge between `stabilizerCode`'s subgroup and the set-form closure
of the generators. -/
private lemma stabilizerCode_toSubgroup_eq (r : ℕ) [Fact (1 ≤ r)] :
    (stabilizerCode r).toStabilizerGroup.toSubgroup =
      Subgroup.closure (generators r) := by
  -- TODO(goy-T20): change to closure-of-listToSet form, then
  -- `rw [listToSet_generatorsList]`.
  sorry

/-- Helper for T21: `coveringXLink j` returns an `XLink` index whose support
includes `qubit_x j`. -/
private def coveringXLink (r : ℕ) [Fact (1 ≤ r)] (j : Fin (2 * r)) :
    Fin (2 * r - 1) :=
  if h : j.val < 2 * r - 1 then
    ⟨j.val, h⟩
  else
    ⟨2 * r - 2, by have := Fact.out (p := (1 ≤ r)); omega⟩

/-- Helper for T21: `coveringZLink j` returns a `ZLink` index whose support
includes `qubit_z j`. -/
private def coveringZLink (r : ℕ) [Fact (1 ≤ r)] (j : Fin (2 * r)) :
    Fin (2 * r - 1) :=
  if h : j.val < 2 * r - 1 then
    ⟨j.val, h⟩
  else
    ⟨2 * r - 2, by have := Fact.out (p := (1 ≤ r)); omega⟩

/-- Weight-1 X-anchored Pauli at an x-qubit anticommutes with the
`coveringXLink` choice. -/
private lemma weightOneAt_X_anticomm_coveringXLink (r : ℕ) [Fact (1 ≤ r)]
    (j : Fin (2 * r)) :
    NQubitPauliGroupElement.Anticommute (weightOneAt (qubit_x j) PauliOperator.Z)
      (XLink r (coveringXLink r j)) := by
  sorry
  -- TODO(goy-T21h1): coveringXLink choice gives anticomm filter exactly {qubit_x j}, card 1

/-- Weight-1 Pauli (X or Y) at a z-qubit anticommutes with the
`coveringZLink` choice. -/
private lemma weightOneAt_XorY_anticomm_coveringZLink (r : ℕ) [Fact (1 ≤ r)]
    (j : Fin (2 * r)) (P : PauliOperator)
    (hP : P = PauliOperator.X ∨ P = PauliOperator.Y) :
    NQubitPauliGroupElement.Anticommute (weightOneAt (qubit_z j) P)
      (ZLink r (coveringZLink r j)) := by
  -- TODO(goy-T21h2): coveringZLink choice gives anticomm filter exactly
  -- {qubit_z j}, cardinality 1.
  sorry

/-- Weight-1 Pauli (X or Y) at a 0-qubit anticommutes with `ZBig`. -/
private lemma weightOneAt_XorY_at_qubit_0_anticomm_ZBig (r : ℕ) [Fact (1 ≤ r)]
    (j : Fin (2 * r)) (P : PauliOperator)
    (hP : P = PauliOperator.X ∨ P = PauliOperator.Y) :
    NQubitPauliGroupElement.Anticommute (weightOneAt (qubit_0 j) P) (ZBig r) := by
  sorry
  -- TODO(goy-T21h3): ZBig has Z at qubit_0 j; anticomm filter = {qubit_0 j}, card 1

/-- Weight-1 Pauli (X or Y) at an x-qubit anticommutes with `ZBig`. -/
private lemma weightOneAt_XorY_at_qubit_x_anticomm_ZBig (r : ℕ) [Fact (1 ≤ r)]
    (j : Fin (2 * r)) (P : PauliOperator)
    (hP : P = PauliOperator.X ∨ P = PauliOperator.Y) :
    NQubitPauliGroupElement.Anticommute (weightOneAt (qubit_x j) P) (ZBig r) := by
  sorry
  -- TODO(goy-T21h4): ZBig has Z at qubit_x j; anticomm filter = {qubit_x j}, card 1

/-- Weight-1 Z at a 0-qubit anticommutes with `XBig`. -/
private lemma weightOneAt_Z_at_qubit_0_anticomm_XBig (r : ℕ) [Fact (1 ≤ r)]
    (j : Fin (2 * r)) :
    NQubitPauliGroupElement.Anticommute (weightOneAt (qubit_0 j) PauliOperator.Z)
      (XBig r) := by
  sorry
  -- TODO(goy-T21h5): XBig has X at qubit_0 j; anticomm filter = {qubit_0 j}, card 1

/-- Weight-1 Z at a z-qubit anticommutes with `XBig`. -/
private lemma weightOneAt_Z_at_qubit_z_anticomm_XBig (r : ℕ) [Fact (1 ≤ r)]
    (j : Fin (2 * r)) :
    NQubitPauliGroupElement.Anticommute (weightOneAt (qubit_z j) PauliOperator.Z)
      (XBig r) := by
  sorry
  -- TODO(goy-T21h6): XBig has X at qubit_z j; anticomm filter = {qubit_z j}, card 1

/-- T21: every weight-1 Pauli anticommutes with some stabilizer generator.

Trichotomy on `i.val % 3` (qubit role), then dispatch on `P ∈ {X, Y, Z}`:

- role 0 (x-qubit) × P ∈ {X, Y}: witness `ZBig`.
- role 0 (x-qubit) × P = Z: witness `XLink (coveringXLink j)`.
- role 1 (0-qubit) × P ∈ {X, Y}: witness `ZBig`.
- role 1 (0-qubit) × P = Z: witness `XBig`.
- role 2 (z-qubit) × P ∈ {X, Y}: witness `ZLink (coveringZLink j)`.
- role 2 (z-qubit) × P = Z: witness `XBig`.
-/
private lemma weight_one_anticomm_witness (r : ℕ) [Fact (1 ≤ r)] :
    ∀ i : Fin (6 * r), ∀ P : PauliOperator, P ≠ PauliOperator.I →
      ∃ g ∈ generators r, NQubitPauliGroupElement.Anticommute
        (weightOneAt i P) g := by
  sorry
  -- TODO(goy-T21): mod-3 trichotomy on i.val + 3-way match on P, dispatch to helpers T21h1-h6

/-- Helper for T22: `weight (logicalX r ⟨0, h0lt⟩) = 2` (parametric weight
computation; the support is `{qubit_x 0, qubit_0 0} = {0, 1}`). -/
private lemma weight_logicalX (r : ℕ) [Fact (1 ≤ r)] (i : Fin (2 * r)) :
    NQubitPauliGroupElement.weight (logicalX r i) = 2 := by
  -- TODO(goy-weight-logicalX): support = {qubit_x i, qubit_0 i};
  -- cardinality 2 via card_insert_of_notMem + card_singleton.
  sorry

/-- T22: the GOY `[[6r, 2r, 2]]` code has distance exactly 2. -/
theorem code_has_distance_two (r : ℕ) [Fact (1 ≤ r)] :
    HasCodeDistance (stabilizerCode r) 2 := by
  have h1 : 1 ≤ r := Fact.out
  have h0lt : 0 < 2 * r := by omega
  refine hasCodeDistance_two_of_anticommute_witness (stabilizerCode r) (generators r)
    (stabilizerCode_toSubgroup_eq r) (weight_one_anticomm_witness r) ?_
  refine ⟨logicalX r ⟨0, h0lt⟩, ?_, ?_⟩
  · exact (logicalOpsGOY r ⟨0, h0lt⟩).xOp_nontrivial
  · exact weight_logicalX r ⟨0, h0lt⟩

/-- T23: the GOY code packaged with its distance. -/
noncomputable def stabilizerCodeWithDistance (r : ℕ) [Fact (1 ≤ r)] :
    StabilizerCodeWithDistance (6 * r) (2 * r) 2 where
  toStabilizerCode := stabilizerCode r
  hasDistance      := code_has_distance_two r

end GOY
end StabilizerGroup
end Quantum
