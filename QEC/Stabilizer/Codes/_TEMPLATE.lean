import Mathlib.Tactic
import QEC.Stabilizer.Framework.Core.Stabilizer.StabilizerGroup
import QEC.Stabilizer.Framework.Core.Stabilizer.StabilizerCode
import QEC.Stabilizer.Framework.Core.Stabilizer.SubgroupLemmas
import QEC.Stabilizer.Framework.Core.CSS.CSSPredicates
import QEC.Stabilizer.Framework.Core.CSS.CSSNoNegI
import QEC.Stabilizer.Framework.Core.CSS.CSSCommutationLemmas
import QEC.Stabilizer.Framework.Core.Stabilizer.Centralizer
import QEC.Stabilizer.Framework.Core.Logical.CodeDistance
import QEC.Stabilizer.Framework.Core.Logical.LogicalOperators
import QEC.Stabilizer.Foundations.PauliGroup.Commutation
import QEC.Stabilizer.Foundations.PauliGroup.CommutationTactics
import QEC.Stabilizer.Foundations.PauliGroup.NQubitOperator
import QEC.Stabilizer.Foundations.PauliGroup.NQubitElement
import QEC.Stabilizer.Foundations.PauliGroup.Notation
import QEC.Stabilizer.Foundations.BinarySymplectic.Core
import QEC.Stabilizer.Foundations.BinarySymplectic.CheckMatrix
import QEC.Stabilizer.Foundations.BinarySymplectic.CheckMatrixDecidable
import QEC.Stabilizer.Framework.Symplectic.IndependentEquiv

/-!
# Template — standard stabilizer-code formalization (decide route)

This file documents **the canonical structure** for formalizing a CSS stabilizer
code in this repo. It is *not* a working code — the actual content is in the
embedded code samples below. Copy this file, rename it to `<CodeName>.lean`,
fill in the parameters / Pauli strings, and adapt section by section.

The pattern was first established in `Steane7.lean`; this file is the explicit,
copy-paste-ready version. The skeleton-drafter agent
(`.claude/agents/qec-skeleton-drafter.md`) uses this file as its primary
structural reference.

## When to use this template

Use as-is for **CSS codes with `k = 1` logical qubit** (the most common case):
Steane7, Shor9, RepetitionCode3, RepetitionCodeN. The structure scales
straightforwardly to:

- **`k ≥ 2`** — see variant notes under §13 (packaging) and §10–§11 (logical
  operators). The only field that genuinely changes is `logical_commute_cross`
  of the `StabilizerCodeWithLogicals` bundle — for `k = 1` the
  `Subsingleton.elim` shortcut suffices; for `k ≥ 2` you need explicit
  case-splits on `Fin k × Fin k`. The bare `StabilizerCode` is the same shape
  for every `k`.
- **Parametric families** (toric, rotated surface, …) — generators are defined
  as functions of `L` (the toric, repetition and iceberg families write theirs
  with the symbolic `σ[n | i ↦ Z, …]` form, see §1; the rotated surface code
  builds them through the homological-code layer instead), the subgroup is
  parametric, and the `StabilizerCode` packaging often requires a *trimmed*
  generator list (see `ToricCodeNStabilizerCode.lean` for the pattern). The
  distance proof typically lives in a *separate file* (`<Code>Distance.lean`).
- **Non-CSS codes** (Pauli-mixed generators) — nothing changes in §2–§6: the
  decide route never looks at the Z/X split. Only the distance argument (§14)
  is different, since the CSS closers no longer apply. `FiveQubit_5_1_3.lean`
  is the reference.

## Section overview

The **decide route** (§2–§6) is the default for every literal code: the
generators form a literal `List`, and each hypothesis of `StabilizerCode`
is a closed decidable statement. The **CSS route** (§7–§9) is kept for
parametric families, whose generator lists are `List.ofFn` terms that
`decide` cannot evaluate.

- §1 — Generator definitions (`Z1`, `Z2`, …, `X1`, `X2`, …). Always.
- §2 — Generator list `generatorsList`. Always.
- §3 — Pairwise commutation `generators_commute`, by `decide`. Literal codes.
- §4 — Phase-zero + check-matrix independence, by `decide`. Always.
- §5 — `negIdentity ∉ closure`, from §3–§4. Literal codes.
- §6 — Bundled `StabilizerGroup n` and its `toSubgroup` equation. Always.
- §7 — CSS route: generator sets and the Z/X typing lemmas. Parametric only.
- §8 — CSS route: cross-commutation and `generators_commute`. Parametric only.
- §9 — CSS route: `negIdentity ∉ closure` and the `listToSet` bridge.
  Parametric only.
- §10 — Logical operators (`logicalX`, `logicalZ`, optional `logicalY`).
  When `k ≥ 1`.
- §11 — Logical anticommutation. When `k ≥ 1`.
- §12 — Logicals in centralizer. When `k ≥ 1`.
- §13 — `StabilizerCode n k` (bare) + `StabilizerCodeWithLogicals n k`
  packaging. Always.
- §14 — `HasCodeDistance`. Optional (often in a sibling file for parametric
  codes).

## File header pattern

Open with a doc-section citing the original paper and stating the generators /
logical operators / distance claim explicitly. The informal_spec.md produced by
the skeleton drafter should populate this verbatim.
-/

namespace Quantum
namespace StabilizerGroup
namespace _Template

open NQubitPauliGroupElement
open scoped Pauli

/-!
## §1 — Generators

For an `[[n, k, d]]` CSS code, you need `m_Z` Z-type generators and `m_X` X-type
generators, with `m_Z + m_X = n - k`. Each is an `NQubitPauliGroupElement n`
with `phasePower = 0`, written with the scoped `σ[…]` construction notation
(`open scoped Pauli`, provided by
`QEC.Stabilizer.Foundations.PauliGroup.Notation` — see this file's header).

Pattern (Steane code, [[7, 1, 3]], `m_Z = m_X = 3`):

```lean
/-- Z-check on row r₁ = {0,1,2,4}: Z on qubits 0,1,2,4 and I elsewhere. -/
def Z1 : NQubitPauliGroupElement 7 := σ[ZZZIZII]
```

`σ[ZZZIZII]` elaborates to **exactly** the literal normal form

```lean
⟨0,
  (((NQubitPauliOperator.identity 7).set 0 PauliOperator.Z).set 1 PauliOperator.Z).set 2
    PauliOperator.Z |>.set 4 PauliOperator.Z⟩
```

(`.set` applied at the non-identity positions in increasing index order), so
`rfl`/`decide`/`simp` behavior is identical to writing the chain by hand, and
goals display such literals back as `σ[…]`.

Conventions:

- `phasePower = 0` always for stabilizer generators — the plain `σ[…]` form.
  (Phase-prefix variants exist for other elements: `iσ[…]` = phase `i`,
  `-σ[…]` = phase `-1`, `-iσ[…]` = phase `-i`.)
- 0-based qubit indexing: the k-th letter is the operator on qubit k.
- One `def` per generator. Name them `Z1, Z2, …, X1, X2, …`.
- The bare Pauli string with no phase (an `NQubitPauliOperator n`) is `P[…]`:
  `σ[ZZZIZII].operators = P[ZZZIZII]` by `rfl`, and `P[…]` elaborates to exactly
  the bare `.set` chain. Reach for it in `operators`-level statements (support,
  check-matrix rows) rather than spelling the chain out.

**Non-CSS variant.** Mixed-Pauli generators use the same notation (e.g., the
5-qubit perfect code's `σ[XZZXI]`); there is no Z/X partition.

**Parametric variant.** When the qubit count and the positions are terms
rather than numerals, use the symbolic form with the same leading tokens:

```lean
/-- The adjacent Z-check `Z_i Z_{i+1}` on `n + 2` qubits. -/
def ZPair (n : ℕ) (i : Fin (n + 1)) : NQubitPauliGroupElement (n + 2) :=
  σ[n + 2 | Fin.castSucc i ↦ Z, Fin.succ i ↦ Z]
```

`σ[n | i ↦ Z, j ↦ Z]` elaborates to exactly
`⟨0, ((NQubitPauliOperator.identity n).set i PauliOperator.Z).set j PauliOperator.Z⟩`,
the `.set`s in the written order, so the usual
`simp [NQubitPauliOperator.set, NQubitPauliOperator.identity]` unfolding is
unchanged; `P[n | …]` is the phase-less string, and the phase prefixes work the
same way. Letters are `X`, `Y`, `Z` only — leave identity qubits out. See
`Repetition/N.lean`, `Iceberg/N.lean`, and `Toric/CodeN.lean` (`vertexStab`,
`faceStab`) for uses.
-/

/-!
## §2 — Generator list

Put the generators in a literal `List`, Z-checks first, then X-checks. The
list is the **single source of truth**: the bundled `StabilizerGroup` (§6)
and the `StabilizerCode` (§13) are both built from it, and every downstream
membership argument is a case split on its elements.

```lean
/-- The six generators as a list (Z-checks first, then X-checks). -/
def generatorsList : List (NQubitPauliGroupElement 7) :=
  [Z1, Z2, Z3, X1, X2, X3]
```

Length must equal `n - k`; this is enforced by
`StabilizerCode.generators_length` (§13), where it is `rfl`.

**Parametric variant.** Write the list as `List.ofFn f` and take the CSS
route (§7–§9). For toric / rotated-surface codes with parametric `L`, the
natural full generator list (all `2L²` vertex + face stabilizers of the toric
code) is *redundant* — its length exceeds `n - k` — so define a separate
*trimmed* list `generatorsListPackaged` of length exactly `n - k` and prove
the closures equal. See `Toric/StabilizerCode.lean` for the pattern.
-/

/-!
## §3 — Pairwise commutation, by `decide`

`StabilizerCode.generators_commute` quantifies over
`NQubitPauliGroupElement.listToSet generatorsList`. For a literal list that is
a finite conjunction of closed identities between `σ[…]` literals, and the
kernel settles each one through the global
`DecidableEq (NQubitPauliGroupElement n)` instance (the bounded quantifier is
pinned to `List.decidableBAll` by `instDecidablePairwiseCommuteListToSet` in
`Core/Stabilizer/StabilizerCode.lean`, so instance search does not wander off
into `Fintype.decidableForallFintype`):

```lean
/-- All six generators pairwise commute. -/
theorem generators_commute :
    ∀ g ∈ listToSet generatorsList, ∀ h ∈ listToSet generatorsList, g * h = h * g := by
  decide
```

This one `decide` replaces the typing lemmas, the per-pair
`pauli_comm_even_anticommutes` proofs and the four-way `rcases` of the CSS
route. It closes in well under a second for every literal code on `main`
(`n ≤ 9`, up to eight generators). Record the overlap counts in the
doc-comment anyway — the reader still wants to know *why* the pairs commute.

**Non-CSS variant.** Identical: `decide` does not care whether the
generators are Z/X-pure.
-/

/-!
## §4 — Phase-zero + check-matrix independence

These two facts feed `StabilizerCode.generators_phaseZero` and
`StabilizerCode.generators_independent` (§13), and together with §3 they are
the inputs to the `−I` lemma of §5.

```lean
/-- Every generator has phase power 0. -/
lemma AllPhaseZero_generatorsList : AllPhaseZero generatorsList := by
  decide

/-- The check-matrix rows of the generators are linearly independent. -/
theorem rowsLinearIndependent_generatorsList :
    rowsLinearIndependent generatorsList := by decide

/-- The generator list is an independent generating set. -/
theorem GeneratorsIndependent_n_generatorsList : GeneratorsIndependent n generatorsList :=
  GeneratorsIndependent_of_rowsLinearIndependent rowsLinearIndependent_generatorsList
```

`decide` closes both for every small code on `main`; the one exception is
`rowsLinearIndependent` for Shor's code (eight rows on nine qubits), where
plain `decide` runs out of heartbeats and `decide +kernel` is used instead.
Reach for `decide +kernel` before anything heavier, never `native_decide`
(banned, see CLAUDE.md § "Axiom policy"). For parametric codes with `L ≥ 2`,
replace `decide` with a parametric independence proof — see
`rowsLinearIndependent_generatorsListPackaged` in `Toric/StabilizerCode.lean`.
-/

/-!
## §5 — `−I` is not in the stabilizer subgroup

Phase-0, pairwise-commuting generators with linearly independent symplectic
rows never generate `−I`: that is
`negIdentity_not_mem_of_indep_phase_zero_commute` in
`Framework/Symplectic/SymplecticSpan.lean`, and §3–§4 are exactly its
hypotheses.

```lean
/-- The closure of the generators does not contain −I. -/
theorem negIdentity_not_mem : negIdentity n ∉ Subgroup.closure (listToSet generatorsList) :=
  negIdentity_not_mem_of_indep_phase_zero_commute generatorsList
    AllPhaseZero_generatorsList rowsLinearIndependent_generatorsList generators_commute
```

Note the statement is against `Subgroup.closure (listToSet generatorsList)`
— the same subgroup `mkStabilizerFromGenerators` builds — so §6 and §13 can
use it directly, with no `listToSet` rewrite.
-/

/-!
## §6 — Bundled `StabilizerGroup n`

Define the canonical `StabilizerGroup n` from `generatorsList` using the smart
constructor `mkStabilizerFromGenerators` (in `Core/Stabilizer/StabilizerCode.lean`).
Its `toSubgroup` is `Subgroup.closure (listToSet generatorsList)` by
definition, so the equation lemma is `rfl`:

```lean
noncomputable def stabilizerGroup : StabilizerGroup n :=
  mkStabilizerFromGenerators n generatorsList generators_commute negIdentity_not_mem

lemma stabilizerGroup_toSubgroup_eq :
    stabilizerGroup.toSubgroup = Subgroup.closure (listToSet generatorsList) := rfl
```

Keep the lemma even though it is `rfl`: `rw [stabilizerGroup_toSubgroup_eq]`
and `mem_centralizer_iff_closure _ _ _ stabilizerGroup_toSubgroup_eq` are how
the centralizer proofs (§12), the distance closers (§14) and downstream files
(`Steane7Distance.lean`, `Steane7TransversalGates.lean`) get from the bundled
group to an explicit generating set. Membership in `listToSet generatorsList`
is then a case split:

```lean
  intro s hs
  simp only [generatorsList, listToSet_cons, listToSet_nil, Set.mem_insert_iff,
    Set.mem_empty_iff_false, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl
```

and `g ∈ listToSet generatorsList` for a named generator `g` is
`by simp [generatorsList]`.

**Parametric variant (CSS route).** When `generatorsList` is `List.ofFn f`
(or the qubit count is symbolic), `decide` has nothing to evaluate. Keep the
`Set`-valued generator sets and the Z/X typing lemmas of §7, prove
`generators_commute` from the CSS commutation shortcuts (§8), and get `−I`
from `CSS.negIdentity_not_mem_closure_union` (§9). `Repetition/N.lean`,
`Iceberg/N.lean`, `Toric/CodeN.lean`, `RotatedSurface/CodeN.lean` and
`Small/QuantumHamming.lean` are the codes on this route; every literal code
under `Codes/Small/` and `Repetition/Three.lean` is on the decide route.
-/

/-!
## §7 — CSS route: generator sets and Z/X typing (parametric families)

Bundle the generators into `Set`s plus their union. The subgroup must be
`noncomputable` because mathlib's `Group` instance on
`NQubitPauliGroupElement` is noncomputable as of v4.30 (see CLAUDE.md).

```lean
def ZGenerators : Set (NQubitPauliGroupElement n) := Set.range ZStab
def XGenerators : Set (NQubitPauliGroupElement n) := Set.range XStab
def generators : Set (NQubitPauliGroupElement n) := ZGenerators ∪ XGenerators

noncomputable def subgroup : Subgroup (NQubitPauliGroupElement n) :=
  Subgroup.closure generators
```

Then prove that every Z-generator is Z-type (operator is `I` or `Z` on every
qubit) and similarly for X. These predicates feed the CSS shortcuts of §8–§9.

```lean
lemma ZGenerators_are_ZType :
    ∀ g, g ∈ ZGenerators → NQubitPauliGroupElement.IsZTypeElement g := by
  rintro g ⟨i, rfl⟩
  constructor
  · rfl  -- phase = 0
  · intro j; simp [ZStab, NQubitPauliOperator.set, NQubitPauliOperator.identity,
      PauliOperator.IsZType]; split_ifs <;> simp
```

Helpful imports: `Core/CSS/CSSPredicates.lean` defines `IsZTypeElement`,
`IsXTypeElement`, plus the per-qubit `PauliOperator.IsZType` /
`PauliOperator.IsXType`.
-/

/-!
## §8 — CSS route: cross-commutation and `generators_commute`

For each `(z, x) ∈ ZGenerators × XGenerators`, prove `z * x = x * z` with the
parity characterization: `pauli_comm_even_anticommutes`
(`PauliGroup/CommutationTactics.lean`) turns the commutation goal into
"the set of anticommuting qubits has even cardinality", which is closed by
identifying that `Finset` explicitly.

```lean
lemma ZGenerators_commute_XGenerators :
    ∀ z ∈ ZGenerators, ∀ x ∈ XGenerators, z * x = x * z := by
  rintro z ⟨i, rfl⟩ x ⟨j, rfl⟩
  pauli_comm_even_anticommutes
  -- residual goal: even number of anticommuting qubits between ZStab i and XStab j
  …
```

Combine with the typing lemmas via `Core/CSS/CSSCommutationLemmas.lean`: two
Z-type elements always commute, and so do two X-type elements.

```lean
theorem generators_commute :
    ∀ g ∈ generators, ∀ h ∈ generators, g * h = h * g := by
  rintro g (hgZ | hgX) h (hhZ | hhX)
  · exact CSSCommutationLemmas.ZType_commutes (ZGenerators_are_ZType g hgZ)
      (ZGenerators_are_ZType h hhZ)
  · exact ZGenerators_commute_XGenerators g hgZ h hhX
  · exact (ZGenerators_commute_XGenerators h hhZ g hgX).symm
  · exact CSSCommutationLemmas.XType_commutes (XGenerators_are_XType g hgX)
      (XGenerators_are_XType h hhX)
```
-/

/-!
## §9 — CSS route: `−I ∉ subgroup` and the `listToSet` bridge

`CSS.negIdentity_not_mem_closure_union` in `Core/CSS/CSSNoNegI.lean` needs
only the Z/X partition, the typing lemmas and their cross-commutation:

```lean
theorem negIdentity_not_mem : negIdentity n ∉ subgroup :=
  CSS.negIdentity_not_mem_closure_union ZGenerators XGenerators
    ZGenerators_are_ZType XGenerators_are_XType ZGenerators_commute_XGenerators
```

The `StabilizerCode` fields (§13) are stated over `listToSet generatorsList`,
so bridge the two forms once and rewrite with it:

```lean
lemma listToSet_generatorsList : listToSet generatorsList = generators := by
  simp only [generatorsList, generators, ZGenerators, XGenerators, listToSet_ofFn,
    List.map_ofFn]  -- shape depends on how the family indexes its stabilizers

noncomputable def stabilizerGroup : StabilizerGroup n :=
  mkStabilizerFromGenerators n generatorsList
    (by rw [listToSet_generatorsList]; exact generators_commute)
    (by rw [listToSet_generatorsList]; exact negIdentity_not_mem)

lemma stabilizerGroup_toSubgroup_eq : stabilizerGroup.toSubgroup = subgroup :=
  congrArg Subgroup.closure listToSet_generatorsList
```

`listToSet_ofFn` and `AllPhaseZero_ofFn` (`Framework/Symplectic/IndependentEquiv.lean`)
are the `List.ofFn` counterparts of the literal-list lemmas.
-/

/-!
## §10 — Logical operators

For an `[[n, k, d]]` code, define `k` `logicalX_i` and `k` `logicalZ_i`. For
`k = 1`, names are simply `logicalX` / `logicalZ`. For `k ≥ 2`, index them
explicitly (`logicalX_1`, `logicalX_2`, …, `logicalZ_1`, `logicalZ_2`, …).

```lean
/-- Logical X: X on all qubits (Steane, Shor; for surface codes the support
is a non-contractible loop instead). -/
def logicalX : NQubitPauliGroupElement n :=
  ⟨0, NQubitPauliOperator.X n⟩

def logicalZ : NQubitPauliGroupElement n :=
  ⟨0, NQubitPauliOperator.Z n⟩
```

`NQubitPauliOperator.X n` and `.Z n` are the "all-X" / "all-Z" operators —
convenient when the logical operator has the full-support form. For other
support patterns, use the `.set` chain pattern from §1.

**Logical Y.** Optional, with the canonical phase convention `Ȳ = i X̄ Z̄`:

```lean
noncomputable def logicalY : NQubitPauliGroupElement n :=
  NQubitPauliGroupElement.phaseI n * (logicalX * logicalZ)

lemma logicalY_eq_phase2_allY :
    logicalY = ({ phasePower := (2 : Fin 4), operators := NQubitPauliOperator.Y n } :
      NQubitPauliGroupElement n) := by
  ext
  · decide
  · simp [logicalY, logicalX, logicalZ, NQubitPauliGroupElement.mul,
          NQubitPauliGroupElement.mulOp, NQubitPauliOperator.X, NQubitPauliOperator.Z,
          NQubitPauliOperator.Y, NQubitPauliOperator.identity, PauliOperator.mulOp]
```

**`k ≥ 2` variant.** Define `logicalX_i`, `logicalZ_i` per logical-qubit
index. The (anti)commutation pattern in §11 expands to *pairwise* relations
(see §11 variant note).
-/

/-!
## §11 — Logical anticommutation

For `k = 1`, prove that `logicalX` anticommutes with `logicalZ`. When both are
all-X / all-Z, the dedicated lemma `NQubitPauliOperator.allX_allZ_anticommute`
closes this in one line:

```lean
theorem logicalX_anticommutes_logicalZ :
    NQubitPauliGroupElement.Anticommute logicalX logicalZ :=
  NQubitPauliOperator.allX_allZ_anticommute n (by decide)
```

The `(by decide)` discharges `Odd n` (anticommutation requires odd `n` for the
all-X/all-Z pair to anticommute — true for Steane7 (n=7), false for [[4,2,2]]
(n=4)).

**Non-all-X variant.** For partial-support logicals, use
`pauli_comm_even_anticommutes` like in §4 and compute the anticommute filter
explicitly.

**`k ≥ 2` variant.** You need *four* relations per logical qubit *pair*:

```lean
-- For each (i, j) ∈ Fin k × Fin k:
theorem logicalX_anticommutes_logicalZ_diag (i : Fin k) :
    NQubitPauliGroupElement.Anticommute (logicalX i) (logicalZ i)

theorem logicalX_commutes_logicalZ_offdiag (i j : Fin k) (h : i ≠ j) :
    (logicalX i) * (logicalZ j) = (logicalZ j) * (logicalX i)

theorem logicalX_commutes_logicalX (i j : Fin k) :
    (logicalX i) * (logicalX j) = (logicalX j) * (logicalX i)

theorem logicalZ_commutes_logicalZ (i j : Fin k) :
    (logicalZ i) * (logicalZ j) = (logicalZ j) * (logicalZ i)
```

These feed `StabilizerCode.logical_commute_cross` (see §13).
-/

/-!
## §12 — Logicals in centralizer

Show that each `logicalX_i` and `logicalZ_i` commutes with every
stabilizer-group element. `mem_centralizer_iff_closure` (`Core/Stabilizer/Centralizer.lean`)
reduces this to the generators, given the §6 equation; then case-split on the
list and close each generator by `decide` (the identity is closed) or by a
prepared per-generator lemma:

```lean
theorem logicalX_mem_centralizer : logicalX ∈ centralizer stabilizerGroup := by
  rw [StabilizerGroup.mem_centralizer_iff_closure _ _ _ stabilizerGroup_toSubgroup_eq]
  intro s hs
  simp only [generatorsList, listToSet_cons, listToSet_nil, Set.mem_insert_iff,
    Set.mem_empty_iff_false, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
```

Do **not** try to `decide` the whole `∀ s ∈ listToSet generatorsList, …`
goal in one go: instance search picks `Fintype.decidableForallFintype` for
that shape and the kernel enumerates all `4 · 4ⁿ` group elements
("maximum recursion depth has been reached"). The `rcases` first is what
keeps each `decide` a closed identity.

When a per-generator identity is worth a name (it is reused, or the parity
argument is the point), state it as a `private lemma` with
`pauli_comm_even_anticommutes` + an explicit anticommutation `Finset`, and
`exact logicalX_commutes_Z1.symm` in the corresponding case — see
`CSS_4_1_2.lean`, `FourQubit_4_2_2.lean`, `SixQubit_6_2_2.lean`.

**Parametric variant.** The generating set is `generators` (§7) and the
equation is `stabilizerGroup_toSubgroup_eq : … = subgroup` (§9); after
`rw [subgroup]` the membership hypothesis destructures as
`rintro s (⟨i, rfl⟩ | ⟨i, rfl⟩)`. If you fall back to `Subgroup.closure_induction`
instead (cases `| mem | one | mul | inv`, v4.30 naming), three things
recurrently go wrong (per CLAUDE.md): the `one` case needs a `change` before
`rw [one_mul]` to beta-reduce `(fun y _ => …) 1`; `mul_assoc` / `one_mul` /
`mul_one` must be qualified `_root_.…` while `open NQubitPauliGroupElement`
is in scope; and the per-generator commutation lemmas must be separate
`private lemma`s stated before the theorem.
-/

/-!
## §13 — `StabilizerCode n k` packaging, and the logical basis on top

Two bundled structures. The **bare code** combines §2–§5 only: a stabilizer
code *is* its stabilizer group, presented by `n − k` independent generators.
The **logical basis** (§10–§12) is derived data and lives in a separate
`StabilizerCodeWithLogicals n k`, which `extends` the bare code:

```lean
/-- The bare `[[n, k]]` code. No logical operators are bundled here. -/
noncomputable def stabilizerCode : StabilizerCode n k where
  hk := by decide                          -- 0 < k ≤ n; trivial for fixed values
  generatorsList := generatorsList
  generators_length := rfl                 -- length = n - k by construction
  generators_phaseZero := AllPhaseZero_generatorsList
  generators_independent := GeneratorsIndependent_n_generatorsList
  generators_commute := generators_commute          -- §3 (CSS route: rw the bridge first)
  closure_no_neg_identity := negIdentity_not_mem     -- §5

private def logicalOps_<CodeName> : Fin k → LogicalQubitOps n stabilizerGroup :=
  fun _ => ⟨logicalX, logicalZ, logicalX_mem_centralizer, logicalZ_mem_centralizer,
            logicalX_anticommutes_logicalZ⟩

/-- The code with its chosen logical basis. -/
noncomputable def stabilizerCodeWithLogicals : StabilizerCodeWithLogicals n k where
  toStabilizerCode := stabilizerCode
  logicalOps := logicalOps_<CodeName>
  logical_commute_cross := fun ℓ ℓ' h => (h (Subsingleton.elim ℓ ℓ')).elim
```

With `import QEC.Stabilizer.Framework.Core.CodeNotation` and
`open scoped Quantum.StabilizerGroup`, the two types can be written
`Code[[n, k]]` and `Code[[n, k]]ₗ`. Keep the distance section (§14) on the bare
`stabilizerCode`: `HasCodeDistance` only depends on the stabilizer group, so a
code whose logical basis is not (yet) chosen still carries its distance proof,
and `stabilizerCodeWithDistance : Code[[n, k, d]]` extends the bare code, not
the one with logicals.

The `logical_commute_cross` shortcut `(h (Subsingleton.elim ℓ ℓ')).elim`
discharges the field vacuously when `k = 1` (only one possible index, so the
hypothesis `ℓ ≠ ℓ'` is automatically false).

**`k ≥ 2` variant.** The `Subsingleton.elim` trick **does not apply**. Spell out
the cross-commutation by case-split on `Fin k × Fin k` (the bare
`stabilizerCode` is unchanged):

```lean
private def logicalOps_<CodeName> : Fin k → LogicalQubitOps n stabilizerGroup
  | 0 => ⟨logicalX_1, logicalZ_1, logicalX_1_mem_centralizer,
           logicalZ_1_mem_centralizer, logicalX_1_anticommutes_logicalZ_1⟩
  | 1 => ⟨logicalX_2, logicalZ_2, logicalX_2_mem_centralizer,
           logicalZ_2_mem_centralizer, logicalX_2_anticommutes_logicalZ_2⟩
  -- ... one per logical qubit

noncomputable def stabilizerCodeWithLogicals : StabilizerCodeWithLogicals n k where
  toStabilizerCode := stabilizerCode
  logicalOps := logicalOps_<CodeName>
  logical_commute_cross := fun ℓ ℓ' h => by
    fin_cases ℓ <;> fin_cases ℓ' <;> first
      | exact absurd rfl h
      | exact ⟨logicalX_commutes_logicalX_offdiag _ _,
                logicalX_commutes_logicalZ_offdiag _ _,
                logicalZ_commutes_logicalX_offdiag _ _,
                logicalZ_commutes_logicalZ_offdiag _ _⟩
```

The bundled `∧` of four equalities is the off-diagonal commutation requirement.
See `gap_audit.md` template in `.claude/agents/qec-skeleton-drafter.md` for a
discussion of why a smart constructor `LogicalQubitOps.cross_commute_pair` could
clean this up.
-/

/-!
## §14 — `HasCodeDistance` (optional)

Every distance proof on `main` is kernel-only. `native_decide` is banned
repo-wide (CLAUDE.md § "Axiom policy"), so there is no "decide the whole
`HasCodeDistance` predicate" shortcut, and no `sorry` placeholder either: pick
the closer that matches the code's shape. All of them are stated on the bare
`stabilizerCode` of §13 — `HasCodeDistance` depends only on the stabilizer
group, and only the witness's nontriviality proof touches the logical basis.
The two CSS closers live in `Framework/Core/CSS/CSSDistance.lean`, the general
one in `Framework/Core/Logical/CodeDistance.lean`. All three consume the same
two ingredients — the §13 closure equation

```lean
lemma stabilizerCode_toSubgroup_eq :
    stabilizerCode.toStabilizerGroup.toSubgroup = Subgroup.closure (listToSet generatorsList) :=
  rfl  -- §6; on the CSS route, `stabilizerGroup_toSubgroup_eq` against `generators`
```

and an explicit witness `⟨g, h_nontrivial, by decide⟩`, a nontrivial logical of
weight exactly `d` — and every finite side condition closes with `decide`
(`Decidable (Anticommute p q)` is a global instance, see
`PauliGroup/Commutation.lean`).

**Distance 2, CSS** — `hasCodeDistance_two_of_anticommute_witness`. Supply a
witness function: for every qubit `i` and non-identity Pauli `P`, a generator
anticommuting with `weightOneAt i P`. `fin_cases` on `i`, `match` on `P`, and
let `first` backtrack over the generators of the right type (`Z`-generators
detect `X`/`Y`, `X`-generators detect `Z`). See `Codes/Small/CSS_4_1_2.lean`
and `FourQubit_4_2_2.lean`.

```lean
private lemma weight_one_anticomm_witness :
    ∀ i : Fin n, ∀ P : PauliOperator, P ≠ PauliOperator.I →
      ∃ g ∈ listToSet generatorsList, NQubitPauliGroupElement.Anticommute
        (weightOneAt i P) g := by
  intro i P hP
  fin_cases i <;>
    (match P, hP with
    | PauliOperator.X, _ => first
      | exact ⟨Z1, by simp [generatorsList], by decide⟩
      | exact ⟨Z2, by simp [generatorsList], by decide⟩
    | PauliOperator.Y, _ => first
      | exact ⟨Z1, by simp [generatorsList], by decide⟩
      | exact ⟨Z2, by simp [generatorsList], by decide⟩
    | PauliOperator.Z, _ => first
      | exact ⟨X1, by simp [generatorsList], by decide⟩
      | exact ⟨X2, by simp [generatorsList], by decide⟩
    | PauliOperator.I, hP => exact (hP rfl).elim)

theorem code_has_distance_two : HasCodeDistance stabilizerCode 2 :=
  hasCodeDistance_two_of_anticommute_witness stabilizerCode (listToSet generatorsList)
    stabilizerCode_toSubgroup_eq weight_one_anticomm_witness
    ⟨logicalX, (logicalOps_<CodeName> 0).xOp_nontrivial, by decide⟩
```

**Distance 3, CSS** — `hasCodeDistance_three_of_columns`. Present each check
as the `Finset` of qubits it acts on (`zOn S` / `xOn S` are `Z` / `X` on `S`);
the closer then needs only the classical column conditions on both check
matrices — no column is zero, no two columns coincide — each a closed
statement over `Fin n` that `decide` settles. See
`Codes/Small/Steane7Distance.lean` (self-dual, so one `row` serves both sides).

```lean
def zRow : Fin 3 → Finset (Fin 7) := ![{0, 1, 2, 4}, {0, 1, 3, 5}, {0, 2, 3, 6}]

lemma Z1_eq_zOn : Z1 = zOn {0, 1, 2, 4} :=
  NQubitPauliGroupElement.ext _ _ rfl (funext fun i => by fin_cases i <;> rfl)

lemma zOn_row_mem (r : Fin 3) : zOn (zRow r) ∈ listToSet generatorsList := by
  fin_cases r <;> simp [zRow, generatorsList, Z1_eq_zOn, Z2_eq_zOn, Z3_eq_zOn]

lemma zRow_cover : ∀ i : Fin 7, ∃ r, i ∈ zRow r := by decide

lemma zRow_separate : ∀ i j : Fin 7, i ≠ j → ∃ r, (i ∈ zRow r ↔ j ∉ zRow r) := by
  decide
-- … and the same for `xRow` / `xOn_row_mem` / `xRow_cover` / `xRow_separate`.

theorem code_has_distance_three : HasCodeDistance stabilizerCode 3 :=
  hasCodeDistance_three_of_columns zRow xRow (listToSet generatorsList) stabilizerCode
    stabilizerCode_toSubgroup_eq zOn_row_mem xOn_row_mem zRow_cover xRow_cover
    zRow_separate xRow_separate ⟨logicalXw3, logicalXw3_isNontrivial, logicalXw3_weight⟩
```

The weight-3 witness is usually a stabilizer multiple of `logicalX` (`X̄ · X₁`
for Steane); its weight is `by decide`, and its nontriviality comes from
`isNontrivialLogicalOperator_of_anticommute_centralizer`
(`Core/Logical/LogicalOperators.lean`): it lies in the centralizer and
anticommutes with the centralizer element `Z̄`.

**General case** (non-CSS, or no closer fits) — `hasCodeDistance_of`. It asks
for `d ≥ 1`, the weight-`d` witness, and, for every `1 ≤ w < d`, that no
weight-`w` element is a nontrivial logical. `interval_cases w` splits the last
goal, and each weight is ruled out with an *anti-witness table* fed to
`no_weight_one_mem_centralizer_of_anticommute_witness` /
`no_weight_two_mem_centralizer_of_anticommute_witness` (they live in
`CSSDistance.lean` but assume nothing CSS — any generating set works, which is
how the non-CSS `[[5,1,3]]` uses them). The weight-2 table is the weight-1 one
nested: `match` on `(P, Q)`, then `fin_cases i <;> fin_cases j`, with `first`
backtracking over `exact absurd rfl hij` (the diagonal) and the generators. See
`Codes/Small/FiveQubit_5_1_3.lean` and qec-lab's `docs/lean-patterns.md`
§ non-CSS distance.

```lean
theorem code_has_distance_three : HasCodeDistance stabilizerCode 3 := by
  refine hasCodeDistance_of stabilizerCode 3 (by decide)
    ⟨logicalX_w3, logicalX_w3_isNontrivial, by decide⟩ ?_
  intro w hw_pos hw_lt g hg_weight h_nontrivial
  rcases (IsNontrivialLogicalOperator_iff g stabilizerCode.toStabilizerGroup).mp h_nontrivial
    with ⟨h_cent, _⟩
  interval_cases w
  · exact no_weight_one_mem_centralizer_of_anticommute_witness
      stabilizerCode.toStabilizerGroup (listToSet generatorsList) stabilizerCode_toSubgroup_eq
      weight_one_anticomm_witness g hg_weight h_cent
  · exact no_weight_two_mem_centralizer_of_anticommute_witness
      stabilizerCode.toStabilizerGroup (listToSet generatorsList) stabilizerCode_toSubgroup_eq
      weight_two_anticomm_witness g hg_weight h_cent
```

Whichever route, finish by bundling the code with its distance
(`Code[[n, k, d]]` is the scoped notation for `StabilizerCodeWithDistance n k d`
from `Framework/Core/CodeNotation.lean`):

```lean
noncomputable def stabilizerCodeWithDistance : Code[[n, k, d]] where
  toStabilizerCode := stabilizerCode
  hasDistance := code_has_distance_three
```

For **parametric families**, the distance proof typically lives in a *separate
file* (`<Code>Distance.lean`, `<Code>DistanceX.lean`, `<Code>DistanceZ.lean`).
Patterns:

- The X-side and Z-side bounds are proved separately (CSS structure).
- For surface-style codes, the homological framework in
  `Framework/Homological/Distance.lean` provides the abstract bridge — see
  `RotatedSurface/Distance.lean` and `Toric/Distance.lean`.
- A subgroup-equality bridge between `stabilizerGroup` and
  `stabilizerCode.toStabilizerGroup` is usually needed; package it as
  `<CodeName>StabilizerCode_subgroup_eq_homological`.
-/

/-!
## End-of-file checklist

Before declaring a CSS-code formalization complete, verify:

- [ ] `lake build QEC.Stabilizer.Codes.<CodeName>` succeeds (no errors, no
  `sorry` warnings).
- [ ] No `set_option linter.* false` in the file (project-wide policy).
- [ ] §1–§6 and §10–§13 are present (§14 may be in a separate distance
  file); §7–§9 only for a parametric family on the CSS route.
- [ ] `stabilizerGroup_toSubgroup_eq` exposed, so downstream files can get
  from the bundled group to the explicit generating set.
- [ ] Module imported in `QEC/Stabilizer/Codes.lean` umbrella (otherwise
  orphan-module trap — see CLAUDE.md).
- [ ] Doc-comment header references the original paper.
- [ ] Logical-operator (anti)commutation pattern matches the codeword basis from
  the original paper (Stage-3 review point).

## See also

- `Steane7.lean` — canonical k = 1 instantiation of this template (decide
  route); `Steane7Distance.lean` / `Steane7TransversalGates.lean` show how
  downstream files consume `stabilizerGroup_toSubgroup_eq`
- `Shor9.lean` — k = 1, n = 9, the largest literal instance
- `FiveQubit_5_1_3.lean` — non-CSS; same §2–§6, general distance closer
- `Repetition/N.lean`, `Iceberg/N.lean` — parametric families on the CSS
  route (§7–§9)
- `RepetitionCode3.lean`, `RepetitionCodeN.lean` — degenerate small-distance
  cases (d = 1)
- `RotatedSurfaceCodeN*.lean` — parametric L family
- `ToricCodeN*.lean` — parametric family with trimmed-generator packaging
- `.claude/agents/qec-skeleton-drafter.md` — Stage-2 agent that uses this
  template to draft new code skeletons
- CLAUDE.md — project-wide naming, tactics, linter conventions
-/

end _Template
end StabilizerGroup
end Quantum
