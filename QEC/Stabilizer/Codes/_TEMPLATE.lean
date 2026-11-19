module

public import Mathlib.Tactic
public import QEC.Stabilizer.Foundations.BinarySymplectic.CheckMatrixDecidable
public import QEC.Stabilizer.Foundations.PauliGroup.Commutation
public import QEC.Stabilizer.Foundations.PauliGroup.Notation
public import QEC.Stabilizer.Framework.Core.CodeNotation
public import QEC.Stabilizer.Framework.Core.CSS.CSSDistance
public import QEC.Stabilizer.Framework.Core.Logical.CodeDistance
public import QEC.Stabilizer.Framework.Core.Logical.LogicalOperators
public import QEC.Stabilizer.Framework.Core.Stabilizer.StabilizerCode
public import QEC.Stabilizer.Framework.Symplectic.DistanceDecide
public import QEC.Stabilizer.Framework.Symplectic.Presentation
public import QEC.Stabilizer.Framework.Symplectic.SymplecticSpan

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
  hypotheses, the bare code, the distance.
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

Every file uses Lean's module system, with the header of this file: `module`,
then `public import` lines, the module docstring, and `@[expose] public section`
before the first declaration (the `@[expose]` keeps definitions unfoldable for
the `decide` proofs downstream). The umbrella entry is a `public import` too.

## Two routes

- The **decide route** is the default for every literal code, CSS or not: the
  generators form a literal `List`, and each hypothesis about them is a closed
  decidable statement that `decide` settles.
- The **CSS route** is for parametric families, whose generator lists range
  over a symbolic number of qubits, which `decide` cannot evaluate. It replaces
  the *Decided hypotheses* section by proofs from the Z/X typing of the
  generators; see the last section.

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

@[expose] public section

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
    ∀ g ∈ generatorsList, ∀ h ∈ generatorsList, g * h = h * g := by
  decide

/-- Every generator has phase power 0. -/
lemma AllPhaseZero_generatorsList : AllPhaseZero generatorsList := by
  decide

/-- The check-matrix rows of the six generators are linearly independent. -/
lemma rowsLinearIndependent_generatorsList : rowsLinearIndependent generatorsList := by
  decide
```

`generators_commute` quantifies over the list, the form taken by
`StabilizerCode.Presentation` and `mkStabilizerFromGenerators`. The set
`listToSet generatorsList` appears only inside `Subgroup.closure`; membership
in it is by definition membership in the list, so a statement about
`g ∈ generatorsList` is accepted wherever one about
`g ∈ listToSet generatorsList` is expected.

The quantifiers over the list are decided by instances pinned to
`List.decidableBAll` (`instDecidablePairwiseCommute`,
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

/-- The Steane code as a stabilizer code `[[7, 1]]`. -/
noncomputable def stabilizerCode : Code[[7, 1]] := presentation.toCode
```

The field `closure_no_neg_identity` (`−I` is not generated) is left out: its
default derives it from the phase, independence and commutation fields, by
`negIdentity_not_mem_of_indep_phase_zero_commute`. A presentation whose
generator list is `noncomputable` is marked `noncomputable` too.

The code's group `stabilizerCode.toStabilizerGroup` is the stabilizer group
of the file: no separate `StabilizerGroup n` is built.
Centralizer membership goes through the presentation:
`presentation.mem_centralizer_iff` says an element is in the centralizer iff it
commutes with every generator. `presentation.toCode_toSubgroup` (`rfl`) is how
the other arguments get from the group to its generators: the column-condition
closers, and logical gates through
`isLogicalGate_of_generator_set_conjugation`.
-/

/-!
## Distance `d`

**The decide closer** (`presentation.hasCodeDistance_of_decide`,
`Framework/Symplectic/DistanceDecide.lean`) is the default for every literal
code, CSS or not, degenerate or not. It takes a weight-`d` logical and two
`decide +kernel` proofs:

- `IsLogicalWitness`: the witness has weight `d`, commutes with every
  generator, and is not a product of generators up to phase. No anticommuting
  partner is needed.
- `NoLogicalBelow`: every Pauli of weight `1, …, d − 1` anticommutes with some
  generator or is a stabilizer up to phase. The second case absorbs
  degeneracy: Shor's `Z_i Z_j` within a block passes it as a stabilizer.

Use `decide +kernel`, not `decide`: the elaborator runs out of recursion depth
on the span checks. The cost is `∑_{w < d} C(n, w) · 3 ^ w` patterns, a few
seconds for `[[9, 1, 3]]`.

The witness is usually a stabilizer multiple of a logical operator. The
paragraph under the section title says which, and why it commutes with every
generator. The sample is from the five-qubit code
(`Small/FiveQubit_5_1_3.lean`).

```lean
/-- `IYYIX`: a nontrivial logical of weight 3. -/
def minWeightLogical : NQubitPauliGroupElement 5 := σ[IYYIX]

/-- **The five-qubit code has distance 3.** `IYYIX` is a nontrivial logical of
weight 3, and every Pauli of weight 1 or 2 anticommutes with some generator. -/
theorem code_has_distance_three : HasCodeDistance stabilizerCode 3 :=
  presentation.hasCodeDistance_of_decide minWeightLogical (by decide +kernel) (by decide +kernel)

/-- The five-qubit code packaged with its distance. -/
noncomputable def stabilizerCodeWithDistance : Code[[5, 1, 3]] where
  toStabilizerCode := stabilizerCode
  hasDistance := code_has_distance_three
```

For distance 2 the theorem is `code_has_distance_two`. `Small/FiveQubit_5_1_3`,
`Small/Shor9`, `Small/FourQubit_4_2_2`, `Small/SixQubit_6_2_2` and
`Small/CSS_4_1_2` use the decide closer; `Small/Steane7` keeps the column
condition below, as its worked example.

**The column condition** (`hasCodeDistance_three_of_columns`, for CSS codes)
puts the argument on the page instead of in a decided table, and is the route
for parametric families, which `decide` cannot evaluate. Present each check as
the `Finset` of qubits it acts on (`zOn S`, `xOn S`); the closer needs only
that no column of either check matrix is zero and no two coincide.
`Small/Steane7.lean` is the worked example and `Small/QuantumHamming.lean` its
parametric version. For a degenerate code,
`hasCodeDistance_three_of_columns_degenerate` replaces each separation
hypothesis by a pair condition. This route needs its own nontriviality proof
for the witness, by `isNontrivialLogicalOperator_of_anticommute_centralizer`
with an anticommuting partner, as in `Small/Steane7.lean`.

**Anything else.** `hasCodeDistance_of` takes `1 ≤ d`, the weight-`d` logical,
and a proof that no element of weight `1 ≤ w < d` is a nontrivial logical.
`interval_cases w` splits the latter into one goal per weight.
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

One lemma per logical operator, each by `presentation.mem_centralizer_iff`.

```lean
/-- `X̄ = X⊗⁷` commutes with every element of the stabilizer. -/
lemma logicalX_mem_centralizer : logicalX ∈ centralizer stabilizerCode.toStabilizerGroup :=
  presentation.mem_centralizer_iff.2 (by decide)

/-- `Z̄ = Z⊗⁷` commutes with every element of the stabilizer. -/
lemma logicalZ_mem_centralizer : logicalZ ∈ centralizer stabilizerCode.toStabilizerGroup :=
  presentation.mem_centralizer_iff.2 (by decide)
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
`Iceberg/N.lean`, `Small/QuantumHamming.lean` and
`Toric/CodeN.lean` follow this route.

**Generators.** Name the checks `ZStab` and `XStab`, and state each as `Z` or
`X` on its support (`zOn S`, `xOn S`), by definition or by a lemma
`ZStab_eq_zOn` / `XStab_eq_xOn`: the type, the check-matrix row and the
commutation of `zOn S` and `xOn S` are then read off the supports. Besides the
list, define the generators as sets, and the subgroup they generate.
`listToSet_generatorsList` follows from `listToSet_append` and
`listToSet_ofFn`:

```lean
/-- The Z-check stabilizer of row `a`: `Z` on the qubits of the row. -/
def ZStab (a : Fin r) : NQubitPauliGroupElement n := zOn (row a)

/-- The X-check stabilizer of row `a`: `X` on the qubits of the row. -/
def XStab (a : Fin r) : NQubitPauliGroupElement n := xOn (row a)

def generatorsList : List (NQubitPauliGroupElement n) :=
  List.ofFn ZStab ++ List.ofFn XStab

def ZGenerators : Set (NQubitPauliGroupElement n) := Set.range ZStab
def XGenerators : Set (NQubitPauliGroupElement n) := Set.range XStab
def generators : Set (NQubitPauliGroupElement n) := ZGenerators ∪ XGenerators

noncomputable def subgroup : Subgroup (NQubitPauliGroupElement n) :=
  Subgroup.closure generators

/-- The generator list has the elements of the generator set. -/
lemma listToSet_generatorsList : listToSet generatorsList = generators := by
  rw [generatorsList, listToSet_append, listToSet_ofFn, listToSet_ofFn]
  rfl
```

**Hypotheses on the generators.** This section replaces *Decided hypotheses*,
under the title `## Hypotheses on the generators`; its paragraph says why the
checks commute and names the pivot column of each row. The Z-generators are
Z-type (`IsZTypeElement_zOn`), the X-generators are X-type
(`IsXTypeElement_xOn`), and a Z-generator commutes with an X-generator because
their supports meet in an even number of qubits (`commutes_xOn_zOn_iff`). Two
elements of the same type commute (`IsZTypeElement.commute`,
`IsXTypeElement.commute`), which gives `generators_commute` over `generators`:

```lean
lemma ZGenerators_isZType : ∀ g ∈ ZGenerators, IsZTypeElement g := by
  rintro _ ⟨a, rfl⟩
  exact IsZTypeElement_zOn _

lemma XGenerators_isXType : ∀ g ∈ XGenerators, IsXTypeElement g := by
  rintro _ ⟨a, rfl⟩
  exact IsXTypeElement_xOn _

lemma ZGenerators_commute_XGenerators :
    ∀ z ∈ ZGenerators, ∀ x ∈ XGenerators, z * x = x * z := by
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
  exact ((commutes_xOn_zOn_iff _ _).mpr (even_card_row_inter_row b a)).symm

lemma generators_commute : ∀ g ∈ generators, ∀ h ∈ generators, g * h = h * g := by
  rintro g (hgZ | hgX) h (hhZ | hhX)
  · exact (ZGenerators_isZType g hgZ).commute (ZGenerators_isZType h hhZ)
  · exact ZGenerators_commute_XGenerators g hgZ h hhX
  · exact (ZGenerators_commute_XGenerators h hhZ g hgX).symm
  · exact (XGenerators_isXType g hgX).commute (XGenerators_isXType h hhX)
```

`AllPhaseZero_generatorsList` follows from `AllPhaseZero_ofFn`. Independence is
`rowsLinearIndependent_ofFn_of_pivots`: name, for each row of the check matrix,
a pivot column where that row is `1` and every later row is `0`. For a Z-check
the pivot is the `Z`-column `Fin.natAdd n q` of a qubit `q` of its support that
no later Z-check contains, and for an X-check the `X`-column `Fin.castAdd n q`;
the entries are computed by `toSymplectic_zOn_natAdd`,
`toSymplectic_zOn_castAdd`, `toSymplectic_xOn_castAdd` and
`toSymplectic_xOn_natAdd`. A list `List.ofFn ZStab ++ List.ofFn XStab` is first
rewritten as one `List.ofFn` with `List.ofFn_fin_append`, and the rows are then
split with `Fin.addCases`:

```lean
/-- The check-matrix rows of the generators are linearly independent. -/
lemma rowsLinearIndependent_generatorsList : rowsLinearIndependent generatorsList := by
  rw [generatorsList, ← List.ofFn_fin_append]
  refine rowsLinearIndependent_ofFn_of_pivots _
    (Fin.append (fun a => Fin.natAdd _ (pivot a)) fun a => Fin.castAdd _ (pivot a))
    (fun i => ?_) (fun i j hij => ?_)
  -- one case per block of rows, by `induction i using Fin.addCases`
```

**The bare code.** The presentation field `generators_commute` quantifies over
the list, and `commute_list_of_listToSet_eq` transfers the set statement to it
along `listToSet_generatorsList`; `closure_no_neg_identity` is again left to
its default. `stabilizerCode_toSubgroup_eq` is stated against `subgroup`:

```lean
  generators_commute :=
    commute_list_of_listToSet_eq listToSet_generatorsList generators_commute

lemma stabilizerCode_toSubgroup_eq : stabilizerCode.toStabilizerGroup.toSubgroup = subgroup :=
  congrArg Subgroup.closure listToSet_generatorsList
```

**Centralizer membership.** `mem_centralizer_iff_closure` with
`stabilizerCode_toSubgroup_eq` reduces membership in the centralizer to
commuting with each element of `generators`, and
`rintro _ (⟨a, rfl⟩ | ⟨a, rfl⟩)` splits that into the Z-generators and the
X-generators. The families state it once for supports, as
`xOn_mem_centralizer` and `zOn_mem_centralizer` under the title
`## Centralizer criteria`: `X` on `S` commutes with the stabilizer when `S`
meets the support of every Z-check in an even number of qubits.

**Distance.** The same closers apply, with `generators` as the generating set
and the side conditions proved rather than decided. Families whose distance
grows with the parameter prove it in separate files through the homological
framework of `Framework/Homological/Distance.lean`; see `Toric/Distance.lean`
and `RotatedSurface/Distance.lean`.
-/
