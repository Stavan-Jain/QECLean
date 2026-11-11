import QEC.Stabilizer.Framework.Core.Stabilizer.StabilizerGroup
import QEC.Stabilizer.Framework.Core.Stabilizer.Centralizer
import QEC.Stabilizer.Foundations.PauliGroup.NQubitOperator

/-!
# Logical operators as cosets

A logical operator of a stabilizer group `S` is a coset of `S` in its
centralizer: two elements of the centralizer that differ by an element of `S`
act identically on the codespace.

For code distance only the nontrivial cosets count. A coset is trivial when it
is `φ • S` for a phase `φ`, i.e. when its representatives share their operator
part with some element of `S`; such an element acts on the codespace as a
scalar. Excluding all of them, and not only `S` itself, ensures that `-Z` for
`Z ∈ S` does not lower the distance.

This file defines the element-level predicate `RepresentsNontrivialCoset g S`:
`g` is in the centralizer of `S` and no element of `S` has the operator part of
`g`. The quotient `centralizer S ⧸ S` is not constructed.
-/

namespace Quantum
namespace StabilizerGroup

variable {n : ℕ}

open NQubitPauliGroupElement

/-- The Pauli element `g` represents a nontrivial coset of `S`: it is in the
centralizer of `S`, and no element of `S` has the same operator part as `g`.
The second condition excludes the cosets `φ • S` for every phase `φ`; in
particular it gives `g ∉ S.toSubgroup` (`RepresentsNontrivialCoset.not_mem`). -/
def RepresentsNontrivialCoset (g : NQubitPauliGroupElement n) (S : StabilizerGroup n) : Prop :=
  g ∈ centralizer S ∧ ∀ s ∈ S.toSubgroup, s.operators ≠ g.operators

/-- An element representing a nontrivial coset is in the centralizer. -/
lemma RepresentsNontrivialCoset.mem_centralizer {g : NQubitPauliGroupElement n}
    {S : StabilizerGroup n} (h : RepresentsNontrivialCoset g S) : g ∈ centralizer S :=
  h.1

/-- An element representing a nontrivial coset is not in the stabilizer. -/
lemma RepresentsNontrivialCoset.not_mem {g : NQubitPauliGroupElement n} {S : StabilizerGroup n}
    (h : RepresentsNontrivialCoset g S) : g ∉ S.toSubgroup :=
  fun hg => h.2 g hg rfl

/-- If `g` represents a nontrivial coset, then no stabilizer element has the
same operator part as `g`. -/
lemma RepresentsNontrivialCoset.operators_ne_of_mem {g : NQubitPauliGroupElement n}
    {S : StabilizerGroup n} (h : RepresentsNontrivialCoset g S) (s : NQubitPauliGroupElement n)
    (hs : s ∈ S.toSubgroup) : s.operators ≠ g.operators :=
  h.2 s hs

/-- `RepresentsNontrivialCoset` depends only on the underlying subgroup of the
stabilizer group. -/
theorem RepresentsNontrivialCoset_of_toSubgroup_eq (g : NQubitPauliGroupElement n)
    {S T : StabilizerGroup n} (h : S.toSubgroup = T.toSubgroup) :
    (RepresentsNontrivialCoset g S ↔ RepresentsNontrivialCoset g T) := by
  rw [RepresentsNontrivialCoset, RepresentsNontrivialCoset,
    centralizer_eq_of_toSubgroup_eq S T h, h]

end StabilizerGroup
end Quantum
