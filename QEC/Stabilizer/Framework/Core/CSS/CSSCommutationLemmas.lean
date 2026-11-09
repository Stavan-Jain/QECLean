import Mathlib.Tactic
import QEC.Stabilizer.Framework.Core.CSS.CSSNoNegI
import QEC.Stabilizer.Foundations.PauliGroup.Commutation

/-!
# Commutation of typed elements

Two Pauli group elements of the same type commute, because single-qubit Paulis
drawn from `{I, Z}` (or from `{I, X}`) do:

- `NQubitPauliGroupElement.IsZTypeElement.commute`: Z-type elements commute;
- `NQubitPauliGroupElement.IsXTypeElement.commute`: X-type elements commute.

So the Z-type generators of a CSS code commute among themselves, as do the
X-type generators, and only the commutation of a Z-type generator with an
X-type generator depends on the code.
-/

namespace Quantum
namespace NQubitPauliGroupElement

variable {n : ℕ}

/-- Any two Z-type elements commute. -/
lemma IsZTypeElement.commute {g h : NQubitPauliGroupElement n}
    (hg : IsZTypeElement g) (hh : IsZTypeElement h) :
    g * h = h * g :=
  commutes_of_componentwise_commutes g h fun i => by
    rcases hg.2 i with h₁ | h₁ <;> rcases hh.2 i with h₂ | h₂ <;> rw [h₁, h₂] <;> rfl

/-- Any two X-type elements commute. -/
lemma IsXTypeElement.commute {g h : NQubitPauliGroupElement n}
    (hg : IsXTypeElement g) (hh : IsXTypeElement h) :
    g * h = h * g :=
  commutes_of_componentwise_commutes g h fun i => by
    rcases hg.2 i with h₁ | h₁ <;> rcases hh.2 i with h₂ | h₂ <;> rw [h₁, h₂] <;> rfl

end NQubitPauliGroupElement
end Quantum
