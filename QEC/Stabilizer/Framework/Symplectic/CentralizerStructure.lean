import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Tactic
import QEC.Stabilizer.Foundations.BinarySymplectic.Core
import QEC.Stabilizer.Foundations.BinarySymplectic.SymplecticInner
import QEC.Stabilizer.Foundations.BinarySymplectic.CheckMatrix
import QEC.Stabilizer.Framework.Symplectic.SymplecticSpan
import QEC.Stabilizer.Framework.Symplectic.SymplecticOrthogonal
import QEC.Stabilizer.Framework.Core.Stabilizer.StabilizerGroup
import QEC.Stabilizer.Framework.Core.Stabilizer.Centralizer
import QEC.Stabilizer.Framework.Core.Stabilizer.StabilizerCode
import QEC.Stabilizer.Framework.Core.Logical.LogicalOperators
import QEC.Stabilizer.Foundations.PauliGroup.NQubitElement

/-!
# Inner-centralizer classification (Milestone M4)

Milestone **M4** of the CSS concatenation plan
(`pipeline/attempts/concat_css_general/plan.md`) — the long pole of the distance
argument. For a `k = 1` stabilizer code, the centralizer of the stabilizer is
`stabilizer ⊔ ⟨X̄₁, Z̄₁⟩`; the distance proof needs to read off, per block, whether
a centralizing operator is "stabilizer-like" or a genuine logical.

This module assembles the `SymplecticSpan` bridge into two results:

- **`centralizer_classify_of_k1`** (the *weak dichotomy*, proven here) — every
  centralizing element either has its operator part realized by a stabilizer
  element, or is a nontrivial logical. This is the per-block split the distance
  argument applies to each `restrictBlock b L`.

  **Note on the statement.** The plan's draft phrased the "trivial" branch as
  `g ∈ stabilizer`. That over-claims: `g` may differ from a stabilizer element by
  a global phase (`i`, `-1`, `-i`), and such a phased element is neither in the
  stabilizer (no `-I`) nor a *nontrivial* logical (its operator part coincides
  with a stabilizer's). The phase-clean, downstream-usable form — and the one the
  repo's `no_weight_w_logical_of_centralizer_in_span` already uses — states the
  trivial branch in **operator-part** terms: `∃ s ∈ stabilizer, s.operators =
  g.operators`. That is exactly what the weight/distance argument consumes.

- **`operators_eq_stab_of_commutes_both_logicals`** (the *decisive direction* —
  still `sorry`) — a centralizing element that commutes with *both* inner
  logicals has its operator part realized by a stabilizer element. This is the
  genuine content of M4 and the one place the weak dichotomy is insufficient: it
  is the `k = 1` "dimension-2 quotient" fact `sympOrthogonal(span{stab rows,
  X̄, Z̄}) = span{stab rows}`. See its doc-comment for the precise scoped goal.
-/

namespace Quantum.StabilizerGroup

open NQubitPauliGroupElement

variable {n k : ℕ}

/-- **(M4, weak dichotomy.)** Any element of the centralizer of a stabilizer code's
stabilizer group is, in operator-part terms, either *stabilizer-like* (some stabilizer
element shares its operator part) or a *nontrivial logical*.

Proof: split on whether the symplectic vector of `g.operators` lies in the row span
`sympSpan C.generatorsList`. If it does, `exists_mem_closure_of_symp_in_span` realizes
the operator part by a closure (= stabilizer) element. If it does not, all three clauses
of `IsNontrivialLogicalOperator` hold — centralizer membership is the hypothesis, and the
"not a stabilizer / operator-part distinct from every stabilizer" clauses follow because
any stabilizer element's symplectic vector *does* lie in `sympSpan` (the generators are
phase-0, so `mem_closure_implies_symp_in_span` applies). No dimension count, no `k = 1`. -/
theorem centralizer_classify_of_k1 (C : StabilizerCode n k)
    (g : NQubitPauliGroupElement n) (hg : g ∈ centralizer C.toStabilizerGroup) :
    (∃ s ∈ C.toStabilizerGroup.toSubgroup, s.operators = g.operators) ∨
      IsNontrivialLogicalOperator g C.toStabilizerGroup := by
  classical
  by_cases hin : NQubitPauliOperator.toSymplectic g.operators ∈ sympSpan C.generatorsList
  · exact Or.inl (exists_mem_closure_of_symp_in_span C.generatorsList g.operators hin)
  · refine Or.inr ((IsNontrivialLogicalOperator_iff g C.toStabilizerGroup).mpr ⟨hg, ?_, ?_⟩)
    · intro hmem
      exact hin (mem_closure_implies_symp_in_span C.generatorsList C.generators_phaseZero g hmem)
    · intro s hs heq
      refine hin ?_
      have hs' := mem_closure_implies_symp_in_span C.generatorsList C.generators_phaseZero s hs
      rwa [heq] at hs'

/-- **(M4, decisive direction — the long pole, still `sorry`.)** For a `k = 1` code, a
centralizing element that commutes with *both* inner logicals `X̄₁`, `Z̄₁` has its operator
part realized by a stabilizer element.

The proof reduces (via `exists_mem_closure_of_symp_in_span`) to the symplectic core:

  `toSymplectic g.operators ∈ sympSpan C.generatorsList`.

That is the `k = 1` *dimension-2 quotient* fact. With `L = C.generatorsList`:
`g ∈ centralizer` gives `symp(g) ⊥ rows(L)`; commuting with `X̄₁`, `Z̄₁` gives
`symp(g) ⊥ symp(X̄₁)`, `symp(g) ⊥ symp(Z̄₁)`. So `symp(g) ∈ sympOrthogonal(span{rows(L),
X̄₁, Z̄₁})`. Because the form is nondegenerate on `F₂^{2n}`, the stabilizer rows are
independent (`n - 1` of them), and `X̄₁, Z̄₁` are independent logicals (in the centralizer
but not the stabilizer, and mutually anticommuting), `span{rows(L), X̄₁, Z̄₁}` has dimension
`n + 1`, its orthogonal has dimension `n - 1`, and that orthogonal *equals* `span(rows L)`
(the stabilizer span is contained in it and has the same dimension). Hence `symp(g) ∈
sympSpan L`.

Formalizing this needs symplectic-form nondegeneracy + `dim(W^⊥) = 2n - dim(W)` (no repo
machinery yet; mathlib's `LinearMap.BilinForm` API) **and** row-independence of the inner
generators (which `StabilizerCode` does not currently carry — it only provides subgroup
`GeneratorsIndependent`, strictly weaker than `rowsLinearIndependent`). Both are scoped as
follow-on work; see `pipeline/attempts/concat_css_general/progress.md` (Session 9). -/
theorem operators_eq_stab_of_commutes_both_logicals (C : StabilizerCode n 1)
    (g : NQubitPauliGroupElement n) (hg : g ∈ centralizer C.toStabilizerGroup)
    (hX : g * (C.logicalOps 0).xOp = (C.logicalOps 0).xOp * g)
    (hZ : g * (C.logicalOps 0).zOp = (C.logicalOps 0).zOp * g) :
    ∃ s ∈ C.toStabilizerGroup.toSubgroup, s.operators = g.operators := by
  apply exists_mem_closure_of_symp_in_span C.generatorsList g.operators
  -- Remaining goal: `toSymplectic g.operators ∈ sympSpan C.generatorsList`, fed by the
  -- orthogonality facts from `hg`, `hX`, `hZ` via the k=1 dimension-2 quotient argument.
  -- TODO(concat-m4): symplectic dimension count —
  -- sympOrthogonal(span{rows, X̄, Z̄}) = span rows for k=1.
  sorry

end Quantum.StabilizerGroup
