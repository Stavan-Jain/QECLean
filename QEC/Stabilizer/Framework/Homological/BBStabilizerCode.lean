import QEC.Stabilizer.Framework.Homological.BBChainComplex
import QEC.Stabilizer.Framework.Homological.ToCode

/-!
# The bivariate bicycle code as a `StabilizerCode`

A bivariate bicycle code is determined by two cycle lengths `ℓ, m` and two
polynomials `A, B ∈ 𝔽₂[x, y] / (xˡ − 1, yᵐ − 1)`, written here as
`ZMod 2`-valued functions on the group `ZMod ℓ × ZMod m` (the `poly[…]`
literal of `BBChainComplex.lean` builds them from a polynomial expression).
`bbChainComplex A B` is the corresponding length-3 chain complex, and the
hypothesis-free `HomologicalCode.toStabilizerCode` (`ToCode.lean`) turns any
chain complex into a stabilizer code whose number of logical qubits is
`dim H₁`.

This file names the composite:

```
bbStabilizerCode ℓ m A B :
    StabilizerCode (bbNumQubits (ZMod ℓ × ZMod m))
      (Module.finrank (ZMod 2) (bbChainComplex A B).H1)
```

together with the simp lemma `bbNumQubits_zmod` that rewrites the qubit
count to `2 * (ℓ * m)`, and the `rfl` lemmas identifying its stabilizer
group with the closure of the face checks `[A | B]` and vertex checks
`[Bᵀ | Aᵀ]`.

The number of logical qubits is left symbolic: it is a theorem about the
particular `A, B`, not part of the construction. For the gross code
(`Codes/BivariateBicycle/Gross/`) the hand-built `grossStabilizerCode`
exhibits `k = 12`.
-/

namespace Quantum
namespace Stabilizer
namespace Homological
namespace BB

/-- The number of qubits of a bivariate bicycle code on `ZMod ℓ × ZMod m` is
`2ℓm`. -/
@[simp] theorem bbNumQubits_zmod (ℓ m : ℕ) [NeZero ℓ] [NeZero m] :
    bbNumQubits (ZMod ℓ × ZMod m) = 2 * (ℓ * m) := by
  simp [bbNumQubits, Fintype.card_prod, ZMod.card]

/-- **The bivariate bicycle code** with cycle lengths `ℓ, m` and polynomials
`A, B` on `ZMod ℓ × ZMod m`: the stabilizer code of `bbChainComplex A B`,
on `2ℓm` qubits (`bbNumQubits_zmod`), with `dim H₁` logical qubits. Its
stabilizer group is the closure of all face and vertex checks, with no
independence hypothesis on them. -/
noncomputable def bbStabilizerCode (ℓ m : ℕ) [NeZero ℓ] [NeZero m]
    (A B : ZMod ℓ × ZMod m → ZMod 2) :
    StabilizerGroup.StabilizerCode (bbNumQubits (ZMod ℓ × ZMod m))
      (Module.finrank (ZMod 2) (bbChainComplex A B).H1) :=
  (bbChainComplex A B).toStabilizerCode

variable {ℓ m : ℕ} [NeZero ℓ] [NeZero m] (A B : ZMod ℓ × ZMod m → ZMod 2)

/-- `bbStabilizerCode` is `toStabilizerCode` of the BB chain complex. -/
@[simp] theorem bbStabilizerCode_eq :
    bbStabilizerCode ℓ m A B = (bbChainComplex A B).toStabilizerCode :=
  rfl

/-- The stabilizer group of a bivariate bicycle code is the homological
stabilizer group of its chain complex. -/
@[simp] theorem bbStabilizerCode_toStabilizerGroup :
    (bbStabilizerCode ℓ m A B).toStabilizerGroup =
      (bbChainComplex A B).homologicalStabilizerGroup :=
  rfl

/-- The stabilizer subgroup of a bivariate bicycle code is the closure of the
face checks (`X`-type, rows of `[A | B]`) and vertex checks (`Z`-type, rows
of `[Bᵀ | Aᵀ]`). -/
@[simp] theorem bbStabilizerCode_toSubgroup :
    (bbStabilizerCode ℓ m A B).toStabilizerGroup.toSubgroup =
      Subgroup.closure (bbChainComplex A B).homologicalGenerators :=
  rfl

/-! ## Example: the gross code parameters

`ℓ = 12`, `m = 6`, `A = x³ + y + y²`, `B = y³ + x + x²` give a code on
`144` qubits. -/

example : bbNumQubits (ZMod 12 × ZMod 6) = 144 := by simp

noncomputable example :
    StabilizerGroup.StabilizerCode (bbNumQubits (ZMod 12 × ZMod 6))
      (Module.finrank (ZMod 2)
        (bbChainComplex (poly[x^3 + y + y^2] : ZMod 12 × ZMod 6 → ZMod 2)
          (poly[y^3 + x + x^2] : ZMod 12 × ZMod 6 → ZMod 2)).H1) :=
  bbStabilizerCode 12 6 poly[x^3 + y + y^2] poly[y^3 + x + x^2]

end BB
end Homological
end Stabilizer
end Quantum
