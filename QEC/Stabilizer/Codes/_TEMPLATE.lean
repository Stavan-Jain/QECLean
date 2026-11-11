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
# Template for a stabilizer-code formalization

This file documents the structure shared by the concrete codes under
`Codes/Small/` and `Codes/Repetition/`. It contains no declarations: the
content is the prose and the code samples below, which are taken from the
Steane code (`Small/Steane7.lean`, `Small/Steane7Logicals.lean`). To formalize
a new code, follow the sections in order, keeping the section titles, the
declaration names and the docstring wording, and changing only the parameters
and the Pauli strings.

## Two files per code

Each code is split across two modules, both in the namespace
`Quantum.StabilizerGroup.<Code>`:

- `<Code>.lean` — the code and its distance, in this order: generators, decided
  hypotheses, `−I`, the bundled stabilizer group, the bare code, the distance.
  It ends in `stabilizerCodeWithDistance` and never mentions a logical basis:
  the distance witness carries its own nontriviality proof.
- `<Code>Logicals.lean` — imports `<Code>.lean` and adds the chosen logical
  basis: logical operators, anticommutation, centralizer membership. It ends
  in `stabilizerCodeWithLogicals`.

Anything that needs the logical basis (transversal gates, logical Clifford
actions) goes in a further file importing the logicals file, as in
`Small/Steane7TransversalGates.lean`. Both modules must be imported by the
umbrella file of their family (`Codes/Small.lean`, …); a module that no
umbrella imports is never compiled.

## Two routes

- The **decide route** is the default for every literal code, CSS or not: the
  generators form a literal `List`, and each hypothesis about them is a closed
  decidable statement that `decide` settles.
- The **CSS route** is for parametric families, whose generator lists range
  over a symbolic number of qubits, which `decide` cannot evaluate. It replaces
  the *Decided hypotheses* and *No `−I`* sections by proofs from the Z/X typing
  of the generators; see the last section.

## File header

A code file opens with the import list of this file, then the module
docstring, then

```lean
namespace Quantum
namespace StabilizerGroup
namespace Steane7

open NQubitPauliGroupElement
open scoped Pauli
```

The module docstring states, in this order: the name and parameters of the
code and its generators (with the codewords, when a convention has to be
fixed); the paragraph on the decide route; the paragraph naming the distance
closer and the weight-`d` logical; a pointer to the logicals file with the
logical basis; and an `## Outline` listing the declarations section by section.
The logicals file opens with `import QEC.Stabilizer.Codes.<Family>.<Code>`, a
module docstring stating the logical basis and why it is one (the action on the
codewords, the overlaps with the checks), an `## Outline`, and the same
`namespace` / `open` lines.
-/

/-!
## Generators

An `[[n, k]]` code has `n − k` generators, each an `NQubitPauliGroupElement n`
with phase power `0`, written with the scoped notation `σ[…]` (`open scoped
Pauli`). A CSS code names its Z-checks `Z1, Z2, …` and its X-checks
`X1, X2, …`; a non-CSS code names its generators `g1, g2, …`.

```lean
/-- First Z-check stabilizer: `ZZZIZII` (Z on row `r₁ = {0,1,2,4}`). -/
def Z1 : NQubitPauliGroupElement 7 := σ[ZZZIZII]
```

`σ[ZZZIZII]` elaborates to exactly the literal
`⟨0, (NQubitPauliOperator.identity 7).set 0 .Z |>.set 1 .Z |>.set 2 .Z |>.set 4 .Z⟩`
(`.set` at the non-identity positions, in increasing order), and goals display
such literals back as `σ[…]`. Qubits are indexed from 0: the `k`-th letter is
the operator on qubit `k`. The phase-less Pauli string, an
`NQubitPauliOperator n`, is `P[…]`, and `iσ[…]`, `-σ[…]`, `-iσ[…]` are the
elements with phase `i`, `−1`, `−i`.

The generators are then collected in a literal list, Z-checks first:

```lean
/-- The six generators as a list (Z-checks first, then X-checks). -/
def generatorsList : List (NQubitPauliGroupElement 7) :=
  [Z1, Z2, Z3, X1, X2, X3]
```

Everything below is built from this list. Its length must be `n − k`, which
`StabilizerCode.Presentation.generators_length` checks by `rfl`.

**Parametric variant.** When the number of qubits and the positions are terms
rather than numerals, use the symbolic form of the notation,
`σ[n | i ↦ Z, j ↦ Z]`, which elaborates to exactly
`⟨0, ((NQubitPauliOperator.identity n).set i .Z).set j .Z⟩` (the `.set`s in the
written order; letters `X`, `Y`, `Z` only), and write the list as `List.ofFn`
or as a `List.map` over the list of indices:

```lean
/-- The adjacent Z-check `Z_i Z_{i+1}` on `n + 2` qubits. -/
def ZPair (n : ℕ) (i : Fin (n + 1)) : NQubitPauliGroupElement (n + 2) :=
  σ[n + 2 | Fin.castSucc i ↦ Z, Fin.succ i ↦ Z]
```

`Repetition/N.lean`, `Iceberg/N.lean` and `Toric/CodeN.lean` do this. A family
whose natural generator list is redundant (the toric code lists all `2L²`
vertex and face stabilizers, two more than `n − k`) needs a separate trimmed
list of length exactly `n − k` with the same closure; see
`Toric/StabilizerCode.lean`.
-/

/-!
## Decided hypotheses

Three closed statements about the generator list, each settled by `decide`.
The paragraph under the section title says why the generators commute (the
overlap of each Z-check with each X-check is even) and how many ordered pairs
`decide` checks.

```lean
/-- All six generators pairwise commute. -/
lemma generators_commute :
    ∀ g ∈ listToSet generatorsList, ∀ h ∈ listToSet generatorsList, g * h = h * g := by
  decide

/-- Every generator has phase power 0. -/
lemma AllPhaseZero_generatorsList : AllPhaseZero generatorsList := by
  decide

/-- The check-matrix rows of the six generators are linearly independent. -/
lemma rowsLinearIndependent_generatorsList : rowsLinearIndependent generatorsList := by
  decide
```

`generators_commute` is stated over `listToSet generatorsList`, the form taken
by `mkStabilizerFromGenerators` and by the `−I` lemma. Membership in
`listToSet L` is by definition membership in `L`, so the same lemma also fills
the field `StabilizerCode.Presentation.generators_commute`, which quantifies
over the list. More generally, a statement about `g ∈ generatorsList` is
accepted wherever one about `g ∈ listToSet generatorsList` is expected.

The quantifiers over the list are decided by instances pinned to
`List.decidableBAll` (`instDecidablePairwiseCommuteListToSet`,
`instDecidableCommuteList`, `instDecidableAllPhaseZero`); the kernel then
checks one closed identity between literals per pair. Without a pinned
instance, `decide` on a statement `∀ g ∈ generatorsList, …` of another shape
falls back on enumerating all `4 · 4ⁿ` group elements and fails. For a
hypothesis `hg : g ∈ generatorsList`, split into the generators with
`fin_cases hg` instead.

`decide` checks row independence by enumerating the `2 ^ (n − k)` coefficient
vectors. Use `decide +kernel` when plain `decide` runs out of heartbeats, as
for the eight rows of `Small/Shor9.lean`. Beyond roughly twenty generators use
a rank certificate: `scripts/RankCertificateGen.lean` prints one, and
`rowsLinearIndependent_of_rankCertCheck _ rankCert (by decide +kernel)` checks
it in polynomial time, as `Toric/RankCertificate.lean` does.

Row independence is the hypothesis that ties the number of generators to `k`.
It is stronger than independence of the generators as a set, which does not
see a repeated generator.
-/

/-!
## No `−I` in the stabilizer subgroup

Phase-0, pairwise commuting generators with linearly independent check-matrix
rows never generate `−I`, so this section is one application of
`negIdentity_not_mem_of_indep_phase_zero_commute` to the three decided
hypotheses.

```lean
/-- The closure of the six generators does not contain `−I`. -/
lemma negIdentity_not_mem : negIdentity 7 ∉ Subgroup.closure (listToSet generatorsList) :=
  negIdentity_not_mem_of_indep_phase_zero_commute generatorsList
    AllPhaseZero_generatorsList rowsLinearIndependent_generatorsList generators_commute
```
-/

/-!
## Bundled `StabilizerGroup n`

The stabilizer group is built from the list by `mkStabilizerFromGenerators`,
and its subgroup is the closure of the list by definition.

```lean
/-- The stabilizer group of the Steane code, generated by `generatorsList`. -/
noncomputable def stabilizerGroup : StabilizerGroup 7 :=
  mkStabilizerFromGenerators 7 generatorsList generators_commute negIdentity_not_mem

/-- The stabilizer subgroup is the closure of the generator list. -/
lemma stabilizerGroup_toSubgroup_eq :
    stabilizerGroup.toSubgroup = Subgroup.closure (listToSet generatorsList) := rfl
```

`stabilizerGroup_toSubgroup_eq` is how every later argument gets from the
bundled group to its generators: centralizer membership through
`mem_centralizer_of_commute_list`, logical gates through
`isLogicalGate_of_generator_set_conjugation`.
-/

/-!
## The bare code `Code[[n, k]]`

`StabilizerCode n k` (notation `Code[[n, k]]`) is a stabilizer group with
`2 ^ (n − k)` elements; it mentions no generators. A concrete code is written
down as a `StabilizerCode.Presentation n k`, whose fields are the generator
list and the facts proved above, and `Presentation.toCode` derives the
cardinality from row independence. The paragraph under the section title
counts the generators and the logical qubits.

```lean
/-- The generator list as a presentation of a `[[7, 1]]` code: its 6
check-matrix rows are linearly independent. -/
def presentation : StabilizerCode.Presentation 7 1 where
  hk := by decide
  generatorsList := generatorsList
  generators_length := rfl
  generators_phaseZero := AllPhaseZero_generatorsList
  generators_independent := rowsLinearIndependent_generatorsList
  generators_commute := generators_commute
  closure_no_neg_identity := negIdentity_not_mem

/-- The Steane code as a stabilizer code `[[7, 1]]`. -/
noncomputable def stabilizerCode : Code[[7, 1]] := presentation.toCode

/-- The stabilizer code's subgroup is the closure of the generator list. -/
lemma stabilizerCode_toSubgroup_eq :
    stabilizerCode.toStabilizerGroup.toSubgroup = Subgroup.closure (listToSet generatorsList) :=
  rfl
```

`stabilizerCode.toStabilizerGroup` and `stabilizerGroup` are definitionally
equal, so facts about the centralizer of `stabilizerGroup` apply to the code.
A presentation whose generator list is `noncomputable` is marked
`noncomputable` too.
-/

/-!
## Distance `d`

The section has three subsections: no nontrivial logical of weight below `d`,
a nontrivial logical of weight `d`, and the code with its distance. All of it
is stated on the bare `stabilizerCode`, since `HasCodeDistance` depends only on
the stabilizer group.

### No nontrivial logical of weight `1`, …, `d − 1`

What goes here depends on the closer used in the last subsection.

**Anticommute witnesses** (`hasCodeDistance_two_of_anticommute_witness`,
`hasCodeDistance_three_of_anticommute_witness`). Every Pauli of weight 1 (and
of weight 2, for distance 3) anticommutes with some generator. The statements
are closed, and `decide` checks every case. This works for any code, CSS or
not; `Small/CSS_4_1_2.lean`, `Small/FourQubit_4_2_2.lean`,
`Small/SixQubit_6_2_2.lean` and `Small/FiveQubit_5_1_3.lean` use it.

```lean
/-- Every weight-1 Pauli anticommutes with some generator. -/
private lemma weight_one_anticomm_witness :
    ∀ i : Fin 5, ∀ P : PauliOperator, P ≠ .I →
      ∃ g ∈ generatorsList, Anticommute (weightOneAt i P) g := by
  decide

/-- Every weight-2 Pauli anticommutes with some generator. -/
private lemma weight_two_anticomm_witness :
    ∀ i j : Fin 5, i ≠ j → ∀ P Q : PauliOperator, P ≠ .I → Q ≠ .I →
      ∃ g ∈ generatorsList, Anticommute (weightTwoAt i j P Q) g := by
  decide
```

**Column condition** (`hasCodeDistance_three_of_columns`, for CSS codes).
Present each check as the `Finset` of qubits it acts on; `zOn S` and `xOn S`
are `Z` and `X` on `S`. The closer needs only the classical conditions on the
two check matrices: no column is zero and no two columns coincide.

```lean
/-- The Hamming parity-check rows `r₁ = {0,1,2,4}`, `r₂ = {0,1,3,5}`,
`r₃ = {0,2,3,6}`. -/
def row : Fin 3 → Finset (Fin 7) := ![{0, 1, 2, 4}, {0, 1, 3, 5}, {0, 2, 3, 6}]

/-- `Z` on each Hamming row is a generator. -/
lemma zOn_row_mem : ∀ r, zOn (row r) ∈ generatorsList := by decide

/-- `X` on each Hamming row is a generator. -/
lemma xOn_row_mem : ∀ r, xOn (row r) ∈ generatorsList := by decide

/-- Every qubit lies on some Hamming row: no column is zero. -/
lemma row_cover : ∀ i : Fin 7, ∃ r, i ∈ row r := by decide

/-- Any two distinct qubits are separated by some Hamming row: no two columns
coincide. -/
lemma row_separate : ∀ i j : Fin 7, i ≠ j → ∃ r, (i ∈ row r ↔ j ∉ row r) := by decide
```

A code whose Z-checks and X-checks have different supports defines `zRow` and
`xRow` and proves `zOn_zRow_mem`, `xOn_xRow_mem`, `zRow_cover`, `xRow_cover`,
`zRow_separate`, `xRow_separate`. For a *degenerate* code, whose checks leave
some pairs of qubits unseparated, `hasCodeDistance_three_of_columns_degenerate`
replaces each `_separate` hypothesis by a pair condition: `X` (respectively
`Z`) on every pair the Z-rows (respectively X-rows) do not separate is a
stabilizer. `Small/Shor9.lean` is the example. In a parametric family the
column conditions are proved from the shape of the columns, as
`Small/QuantumHamming.lean` does.

**Anything else.** `hasCodeDistance_of` takes `1 ≤ d`, the weight-`d` logical,
and a proof that no element of weight `1 ≤ w < d` is a nontrivial logical.
`interval_cases w` splits the latter into one goal per weight.

### A nontrivial logical of weight `d`

The witness is a centralizer element together with a *partner*: a second
centralizer element it anticommutes with, which makes it nontrivial by
`isNontrivialLogicalOperator_of_anticommute_centralizer`. It is usually a
stabilizer multiple of a logical operator, and the partner the corresponding
multiple of the conjugate logical operator. The paragraph under the subsection
title explains the choice.

```lean
/-- `IIIXIXX`: a nontrivial logical of weight 3. -/
def minWeightLogical : NQubitPauliGroupElement 7 := σ[IIIXIXX]

/-- `IIIZIZZ`: a centralizer element anticommuting with `minWeightLogical`. -/
def minWeightPartner : NQubitPauliGroupElement 7 := σ[IIIZIZZ]

/-- `IIIXIXX` has weight 3. -/
lemma minWeightLogical_weight : weight minWeightLogical = 3 := by decide

/-- `IIIXIXX` commutes with every element of the stabilizer. -/
lemma minWeightLogical_mem_centralizer : minWeightLogical ∈ centralizer stabilizerGroup :=
  mem_centralizer_of_commute_list stabilizerGroup_toSubgroup_eq (by decide)

/-- `IIIZIZZ` commutes with every element of the stabilizer. -/
lemma minWeightPartner_mem_centralizer : minWeightPartner ∈ centralizer stabilizerGroup :=
  mem_centralizer_of_commute_list stabilizerGroup_toSubgroup_eq (by decide)

/-- `IIIXIXX` and `IIIZIZZ` meet on qubits 3, 5 and 6, an odd number. -/
lemma minWeightLogical_anticommutes_minWeightPartner :
    Anticommute minWeightLogical minWeightPartner := by decide

/-- `IIIXIXX` is a nontrivial logical operator: it lies in the centralizer and
anticommutes with the centralizer element `minWeightPartner`. -/
lemma minWeightLogical_isNontrivial :
    IsNontrivialLogicalOperator minWeightLogical stabilizerCode.toStabilizerGroup :=
  isNontrivialLogicalOperator_of_anticommute_centralizer _ minWeightLogical_mem_centralizer
    minWeightPartner_mem_centralizer minWeightLogical_anticommutes_minWeightPartner
```

`mem_centralizer_of_commute_list` reduces membership in the centralizer to
commuting with each element of `generatorsList`, which `decide` checks.

### The code with its distance `Code[[n, k, d]]`

The distance theorem is the only `theorem` of the file. It applies the closer
to the closure equation, the lemmas of the first subsection and the witness.
Its docstring states the argument in one sentence.

```lean
/-- **The Steane code has distance 3.** Both check matrices are the Hamming
matrix, whose columns are nonzero and pairwise distinct, so no Pauli of weight
1 or 2 is a nontrivial logical; `IIIXIXX` is one of weight 3. -/
theorem code_has_distance_three : HasCodeDistance stabilizerCode 3 :=
  hasCodeDistance_three_of_columns row row (listToSet generatorsList) stabilizerCode
    stabilizerCode_toSubgroup_eq zOn_row_mem xOn_row_mem row_cover row_cover row_separate
    row_separate ⟨minWeightLogical, minWeightLogical_isNontrivial, minWeightLogical_weight⟩

/-- The Steane code packaged with its distance. -/
noncomputable def stabilizerCodeWithDistance : Code[[7, 1, 3]] where
  toStabilizerCode := stabilizerCode
  hasDistance := code_has_distance_three
```

With the anticommute witnesses the theorem reads

```lean
theorem code_has_distance_three : HasCodeDistance stabilizerCode 3 :=
  hasCodeDistance_three_of_anticommute_witness stabilizerCode (listToSet generatorsList)
    stabilizerCode_toSubgroup_eq weight_one_anticomm_witness weight_two_anticomm_witness
    ⟨minWeightLogical, minWeightLogical_isNontrivial, minWeightLogical_weight⟩
```

and for distance 2 it is `code_has_distance_two`, by
`hasCodeDistance_two_of_anticommute_witness` with the weight-1 witness alone.
-/

/-!
## Logicals file: logical operators

For `k = 1` the logical operators are `logicalX` and `logicalZ`; for `k ≥ 2`
they are `logicalX_1`, `logicalZ_1`, `logicalX_2`, `logicalZ_2`, …. Write them
with `σ[…]`, or as `⟨0, NQubitPauliOperator.X n⟩` and
`⟨0, NQubitPauliOperator.Z n⟩` when they are `X` or `Z` on every qubit.

```lean
/-- Logical X: X on all seven qubits. -/
def logicalX : NQubitPauliGroupElement 7 :=
  ⟨0, NQubitPauliOperator.X 7⟩

/-- Logical Z: Z on all seven qubits. -/
def logicalZ : NQubitPauliGroupElement 7 :=
  ⟨0, NQubitPauliOperator.Z 7⟩
```

## Logicals file: anticommutation

Each `X̄ℓ` anticommutes with its own `Z̄ℓ`, a closed statement; the docstring
says on which qubits they meet.

```lean
/-- `X̄ = X⊗⁷` and `Z̄ = Z⊗⁷` anticommute: they meet on all seven qubits, an odd
number. -/
lemma logicalX_anticommutes_logicalZ : Anticommute logicalX logicalZ := by
  decide
```

In a parametric family with `X̄ = X⊗ⁿ` and `Z̄ = Z⊗ⁿ` this is
`NQubitPauliOperator.allX_allZ_anticommute`, which needs `n` odd.

## Logicals file: centralizer membership

One lemma per logical operator, each by `mem_centralizer_of_commute_list`.

```lean
/-- `X̄ = X⊗⁷` commutes with every element of the stabilizer. -/
lemma logicalX_mem_centralizer : logicalX ∈ centralizer stabilizerGroup :=
  mem_centralizer_of_commute_list stabilizerGroup_toSubgroup_eq (by decide)

/-- `Z̄ = Z⊗⁷` commutes with every element of the stabilizer. -/
lemma logicalZ_mem_centralizer : logicalZ ∈ centralizer stabilizerGroup :=
  mem_centralizer_of_commute_list stabilizerGroup_toSubgroup_eq (by decide)
```

## Logicals file: the code with its logical basis `Code[[n, k]]ₗ`

`StabilizerCodeWithLogicals n k` (notation `Code[[n, k]]ₗ`) extends the bare
code with a `LogicalQubitOps` pair for each logical qubit and the fact that the
operators of distinct logical qubits commute. For `k = 1` that last field is
vacuous:

```lean
/-- The Steane code with its logical basis `X̄ = X⊗⁷`, `Z̄ = Z⊗⁷`. -/
noncomputable def stabilizerCodeWithLogicals : Code[[7, 1]]ₗ where
  toStabilizerCode := stabilizerCode
  logicalOps _ := ⟨logicalX, logicalZ, logicalX_mem_centralizer, logicalZ_mem_centralizer,
    logicalX_anticommutes_logicalZ⟩
  logical_commute_cross ℓ ℓ' h := (h (Subsingleton.elim ℓ ℓ')).elim
```

For `k ≥ 2` the pairs are listed by cases and the cross-commutation is a closed
statement; the docstring says why the operators of distinct logical qubits
commute (`Small/FourQubit_4_2_2Logicals.lean`,
`Small/SixQubit_6_2_2Logicals.lean`):

```lean
noncomputable def stabilizerCodeWithLogicals : Code[[4, 2]]ₗ where
  toStabilizerCode := stabilizerCode
  logicalOps
    | 0 => ⟨logicalX_1, logicalZ_1, logicalX_1_mem_centralizer, logicalZ_1_mem_centralizer,
        logicalX_1_anticommutes_logicalZ_1⟩
    | 1 => ⟨logicalX_2, logicalZ_2, logicalX_2_mem_centralizer, logicalZ_2_mem_centralizer,
        logicalX_2_anticommutes_logicalZ_2⟩
  logical_commute_cross := by decide
```
-/

/-!
## The CSS route for parametric families

When the generator list is not a literal, because the number of qubits is
symbolic, `decide` has nothing to evaluate, and three sections change. The file
keeps the same order and the same declaration names; `Repetition/N.lean`,
`Iceberg/N.lean`, `Small/QuantumHamming.lean` and `Toric/CodeN.lean` follow
this route.

**Generators.** Besides the list, define the generators as sets, and the
subgroup they generate. The proof of `listToSet_generatorsList` depends on how
the family indexes its generators:

```lean
def ZGenerators : Set (NQubitPauliGroupElement n) := Set.range ZStab
def XGenerators : Set (NQubitPauliGroupElement n) := Set.range XStab
def generators : Set (NQubitPauliGroupElement n) := ZGenerators ∪ XGenerators

noncomputable def subgroup : Subgroup (NQubitPauliGroupElement n) :=
  Subgroup.closure generators

lemma listToSet_generatorsList : listToSet generatorsList = generators := by
  simp only [generatorsList, generators, ZGenerators, XGenerators, listToSet_ofFn]
```

**Commutation and `−I`.** Prove that the Z-generators are Z-type
(`IsZTypeElement`: phase power 0 and each factor `I` or `Z`), that the
X-generators are X-type, and that each Z-generator commutes with each
X-generator. The last is a parity count: the tactic
`pauli_comm_even_anticommutes` reduces it to the statement that the two
generators differ non-trivially on an even number of qubits. Two elements of
the same type commute (`IsZTypeElement.commute`, `IsXTypeElement.commute`),
which gives `generators_commute` over `generators`, and
`CSS.negIdentity_not_mem_closure_union` gives `negIdentity_not_mem` from the
same three facts:

```lean
lemma ZGenerators_isZType : ∀ g ∈ ZGenerators, IsZTypeElement g
lemma XGenerators_isXType : ∀ g ∈ XGenerators, IsXTypeElement g
lemma ZGenerators_commute_XGenerators : ∀ z ∈ ZGenerators, ∀ x ∈ XGenerators, z * x = x * z

lemma generators_commute : ∀ g ∈ generators, ∀ h ∈ generators, g * h = h * g := by
  rintro g (hgZ | hgX) h (hhZ | hhX)
  · exact (ZGenerators_isZType g hgZ).commute (ZGenerators_isZType h hhZ)
  · exact ZGenerators_commute_XGenerators g hgZ h hhX
  · exact (ZGenerators_commute_XGenerators h hhZ g hgX).symm
  · exact (XGenerators_isXType g hgX).commute (XGenerators_isXType h hhX)

lemma negIdentity_not_mem : negIdentity n ∉ subgroup :=
  CSS.negIdentity_not_mem_closure_union ZGenerators XGenerators
    ZGenerators_isZType XGenerators_isXType ZGenerators_commute_XGenerators
```

`AllPhaseZero_generatorsList` follows from `AllPhaseZero_ofFn`, and
`rowsLinearIndependent_generatorsList` needs a proof from the shape of the
check matrix.

**Stabilizer group and code.** `mkStabilizerFromGenerators` and the
presentation take statements over `listToSet generatorsList`, so rewrite with
`listToSet_generatorsList`; `stabilizerGroup_toSubgroup_eq` is stated against
`subgroup`, and `stabilizerCode_toSubgroup_eq` is the same equation for the
code.

```lean
noncomputable def stabilizerGroup : StabilizerGroup n :=
  mkStabilizerFromGenerators n generatorsList
    (by rw [listToSet_generatorsList]; exact generators_commute)
    (by rw [listToSet_generatorsList]; exact negIdentity_not_mem)

lemma stabilizerGroup_toSubgroup_eq : stabilizerGroup.toSubgroup = subgroup :=
  congrArg Subgroup.closure listToSet_generatorsList
```

The presentation field `generators_commute` quantifies over the list, so there
the rewrite goes the other way, into the hypothesis:

```lean
  generators_commute := by
    have h := generators_commute
    rw [← listToSet_generatorsList] at h
    exact h
  closure_no_neg_identity := by rw [listToSet_generatorsList]; exact negIdentity_not_mem
```

**Centralizer membership.** `mem_centralizer_iff_closure` with
`stabilizerGroup_toSubgroup_eq` reduces membership in the centralizer to
commuting with each element of `generators`, and
`rintro s (⟨i, rfl⟩ | ⟨i, rfl⟩)` splits that into the Z-generators and the
X-generators.

**Distance.** The same closers apply, with `generators` as the generating set
and the side conditions proved rather than decided. Families whose distance
grows with the parameter prove it in separate files through the homological
framework of `Framework/Homological/Distance.lean`; see `Toric/Distance.lean`
and `RotatedSurface/Distance.lean`.
-/
