import QEC.Stabilizer.Framework.Symplectic.SymplecticImage

/-!
# Presenting a stabilizer code by a generator list

`StabilizerCode n k` (`Core/Stabilizer/StabilizerCode.lean`) is a specification
on the stabilizer group alone: a stabilizer group with `2 ^ (n - k)` elements.
Concrete codes are written down as a list of generators, and
`StabilizerCode.Presentation n k` bundles such a list with the obligations
that make it present an `[[n, k]]` code:

- `generators_length` — the list has `n − k` entries;
- `generators_phaseZero` — each generator has phase `+1`;
- `generators_independent` — the check-matrix rows are linearly independent
  over `𝔽₂` (`rowsLinearIndependent`);
- `generators_commute` — the generators pairwise commute;
- `closure_no_neg_identity` — `−I` is not generated (filled in by default from
  the three previous fields, via
  `negIdentity_not_mem_of_indep_phase_zero_commute`).

Row independence is what ties the length to `k`. It is strictly stronger than
the set-level `GeneratorsIndependent` (which it implies), and in particular it
excludes a repeated generator (`Presentation.nodup`): with a set-level
condition a duplicated generator would be counted by the length but invisible
to every other obligation, so the claimed `k` would only be a lower bound on
the number of logical qubits of the generated group.

`Presentation.toCode` is the soundness map into the specification: its
stabilizer group is the closure of the list (`toCode_toSubgroup`, by `rfl`),
and its cardinality `2 ^ (n - k)` comes from
`card_closure_eq_two_pow_length`.

## Migration recipe

A concrete code defines its presentation with the same fields the bare code
used to carry, then takes the code from it. The one field whose type changed is
`generators_independent`: it is now the check-matrix row independence itself
(`rowsLinearIndependent_generatorsList`, closed by `decide` for a literal
list) rather than `GeneratorsIndependent`, which row independence implies:

```lean
def presentation : StabilizerCode.Presentation 7 1 where
  hk := by decide
  generatorsList := generatorsList
  generators_length := rfl
  generators_phaseZero := AllPhaseZero_generatorsList
  generators_independent := rowsLinearIndependent_generatorsList
  generators_commute := generators_commute
  closure_no_neg_identity := negIdentity_not_mem

noncomputable def stabilizerCode : Code[[7, 1]] := presentation.toCode
```

`stabilizerCode.toStabilizerGroup` is still definitionally
`mkStabilizerFromGenerators 7 generatorsList …`, so the `rfl` subgroup
equations and the logical bases typed against the code's own
`stabilizerGroup` are unchanged. `closure_no_neg_identity` may be omitted (it
defaults to the `−I` lemma applied to the other fields), and a presentation
whose generator list is `noncomputable` must be marked `noncomputable` itself.
-/

namespace Quantum
namespace StabilizerGroup

open NQubitPauliGroupElement

variable {n k : ℕ}

/-- A presentation of an `[[n, k]]` stabilizer code by a list of generators:
`n − k` phase-zero, pairwise commuting generators whose check-matrix rows are
linearly independent over `𝔽₂` and whose closure avoids `−I` (the last field
follows from the others and is filled in by default). `toCode` turns a
presentation into the code it presents. -/
structure StabilizerCode.Presentation (n k : ℕ) where
  /-- We need `k ≤ n` so that the generator count `n - k` is meaningful. -/
  hk : k ≤ n
  /-- The generators; their closure is the stabilizer group of `toCode`. -/
  generatorsList : List (NQubitPauliGroupElement n)
  /-- There are exactly `n - k` generators. -/
  generators_length : generatorsList.length = n - k
  /-- Every generator has phase power `0`. -/
  generators_phaseZero : AllPhaseZero generatorsList
  /-- The check-matrix rows are linearly independent over `𝔽₂` (in particular,
  no generator is repeated: `Presentation.nodup`). -/
  generators_independent : rowsLinearIndependent generatorsList
  /-- The generators pairwise commute. -/
  generators_commute : ∀ g ∈ listToSet generatorsList, ∀ h ∈ listToSet generatorsList,
    g * h = h * g
  /-- The closure of the generators does not contain `−I`. -/
  closure_no_neg_identity : negIdentity n ∉ Subgroup.closure (listToSet generatorsList) :=
    negIdentity_not_mem_of_indep_phase_zero_commute generatorsList generators_phaseZero
      generators_independent generators_commute

namespace StabilizerCode.Presentation

variable (P : StabilizerCode.Presentation n k)

/-- A presentation has no repeated generator: its check-matrix rows are linearly
independent, hence pairwise distinct. -/
theorem nodup : P.generatorsList.Nodup :=
  P.generators_independent.nodup

/-- The generators of a presentation are independent in the subgroup sense: no
generator lies in the closure of the others. -/
theorem independentGenerators :
    Subgroup.IndependentGenerators (listToSet P.generatorsList) :=
  rowsLinearIndependent_implies_independentGenerators _ P.generators_independent

/-- The generator list of a presentation is `GeneratorsIndependent`. -/
theorem generatorsIndependent : GeneratorsIndependent n P.generatorsList :=
  P.independentGenerators

/-- **Size of the presented group.** The generators of a presentation generate a
group with exactly `2 ^ (n - k)` elements. -/
theorem card_closure :
    Nat.card (Subgroup.closure (listToSet P.generatorsList)) = 2 ^ (n - k) := by
  rw [← P.generators_length]
  exact card_closure_eq_two_pow_length P.generatorsList P.generators_independent
    P.generators_commute P.closure_no_neg_identity

/-- **Soundness of a presentation.** The `[[n, k]]` stabilizer code presented by
`P`: its stabilizer group is the closure of the generator list, which has
`2 ^ (n - k)` elements by `card_closure`. -/
noncomputable def toCode : StabilizerCode n k where
  toStabilizerGroup :=
    mkStabilizerFromGenerators n P.generatorsList P.generators_commute P.closure_no_neg_identity
  hk := P.hk
  card_eq := P.card_closure

/-- The stabilizer group of the presented code is built from the generator list
by `mkStabilizerFromGenerators`. -/
theorem toCode_toStabilizerGroup :
    P.toCode.toStabilizerGroup =
      mkStabilizerFromGenerators n P.generatorsList P.generators_commute
        P.closure_no_neg_identity :=
  rfl

/-- The stabilizer subgroup of the presented code is the closure of the
generator list. -/
@[simp] theorem toCode_toSubgroup :
    P.toCode.toStabilizerGroup.toSubgroup = Subgroup.closure (listToSet P.generatorsList) :=
  rfl

end StabilizerCode.Presentation

end StabilizerGroup
end Quantum
