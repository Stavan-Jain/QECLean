import QEC.Stabilizer.Framework.Homological.BBChainComplex
import QEC.Stabilizer.Framework.Homological.ToCode
import QEC.Stabilizer.Framework.Homological.BBLogicalQubits

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

This file names the composite, with the logical-qubit count of
`BBLogicalQubits.lean` in its type:

```
bbStabilizerCode ℓ m A B :
    StabilizerCode (2 * (ℓ * m)) (2 * Module.finrank (ZMod 2) ↥(ker A ⊓ ker B))
```

`bbChainComplex` counts its qubits as `bbNumQubits G = 2 * Fintype.card G`,
which is only propositionally `2 * (ℓ * m)` (`bbNumQubits_zmod`). Since
`numQubits` is a field of `HomologicalCode` chosen by each instance,
`bbHomologicalCode ℓ m A B` is the same chain complex with its qubit count
written as `2 * (ℓ * m)` (`HomologicalCode.withNumQubits`), so that the
stabilizer code lives on `2ℓm` qubits definitionally. The `rfl` lemmas
identify its stabilizer group with the closure of the face checks `[A | B]`
and vertex checks `[Bᵀ | Aᵀ]`.

The number of logical qubits is `2 · dim (ker A ⊓ ker B)`, where `A` and `B`
act on `ZMod ℓ × ZMod m → ZMod 2` by convolution and `ker a` is the scoped
notation for the kernel of convolution by `a` (`BBLogicalQubits.lean`): the
generic code has `dim H₁` logical qubits, and `finrank_H1_bbChainComplex`
is `dim H₁ = 2 · dim (ker A ⊓ ker B)`. A numeral `k`
is then a kernel computation for the particular `A, B`; for the gross code it
is `12` (`Codes/BivariateBicycle/Gross/HomologicalToCode.lean`, read off the
hand-built `grossStabilizerCode`).
-/

namespace Quantum
namespace Stabilizer
namespace Homological

namespace HomologicalCode

variable (X : HomologicalCode)

/-- The same chain complex with its qubit count rewritten to a propositionally
equal `n`. Cells and boundary maps are unchanged, so cycles, boundaries, and
`H₁` are definitionally those of `X`; only `numQubits` and the qubit indexing
`edgeEquiv` (composed with `finCongr h`) change. -/
def withNumQubits (n : ℕ) (h : X.numQubits = n) : HomologicalCode :=
  { X with
    numQubits := n
    numQubits_eq := X.numQubits_eq.trans h
    edgeEquiv := X.edgeEquiv.trans (finCongr h) }

variable (n : ℕ) (h : X.numQubits = n)

@[simp] theorem withNumQubits_numQubits : (X.withNumQubits n h).numQubits = n := rfl

@[simp] theorem withNumQubits_boundary1 :
    (X.withNumQubits n h).boundary1 = X.boundary1 := rfl

@[simp] theorem withNumQubits_boundary2 :
    (X.withNumQubits n h).boundary2 = X.boundary2 := rfl

@[simp] theorem withNumQubits_cycles : (X.withNumQubits n h).cycles = X.cycles := rfl

@[simp] theorem withNumQubits_boundaries :
    (X.withNumQubits n h).boundaries = X.boundaries := rfl

/-- `H₁` is untouched by renumbering the qubits. -/
@[simp] theorem withNumQubits_finrank_H1 :
    Module.finrank (ZMod 2) (X.withNumQubits n h).H1 = Module.finrank (ZMod 2) X.H1 := rfl

end HomologicalCode

namespace BB

/-- The number of qubits of a bivariate bicycle code on `ZMod ℓ × ZMod m` is
`2ℓm`. -/
@[simp] theorem bbNumQubits_zmod (ℓ m : ℕ) [NeZero ℓ] [NeZero m] :
    bbNumQubits (ZMod ℓ × ZMod m) = 2 * (ℓ * m) := by
  simp [bbNumQubits, Fintype.card_prod, ZMod.card]

/-- The bivariate bicycle chain complex on `ZMod ℓ × ZMod m`, with its qubit
count written as `2 * (ℓ * m)`. Same cells, boundary maps, and `H₁` as
`bbChainComplex A B`. -/
noncomputable def bbHomologicalCode (ℓ m : ℕ) [NeZero ℓ] [NeZero m]
    (A B : ZMod ℓ × ZMod m → ZMod 2) : HomologicalCode :=
  (bbChainComplex A B).withNumQubits (2 * (ℓ * m)) (bbNumQubits_zmod ℓ m)

/-- **The bivariate bicycle code** with cycle lengths `ℓ, m` and polynomials
`A, B` on `ZMod ℓ × ZMod m`: the stabilizer code of the BB chain complex, on
`2ℓm` qubits, with `2 · dim (ker A ⊓ ker B)` logical qubits
(`finrank_H1_bbChainComplex`). Its stabilizer group is the closure of all
face and vertex checks, with no independence hypothesis on them. -/
noncomputable def bbStabilizerCode (ℓ m : ℕ) [NeZero ℓ] [NeZero m]
    (A B : ZMod ℓ × ZMod m → ZMod 2) :
    StabilizerGroup.StabilizerCode (2 * (ℓ * m))
      (2 * Module.finrank (ZMod 2) ↥(ker A ⊓ ker B)) where
  toStabilizerGroup := (bbHomologicalCode ℓ m A B).homologicalStabilizerGroup
  hk := by
    have h : Module.finrank (ZMod 2) (bbChainComplex A B).H1 ≤ 2 * (ℓ * m) :=
      (bbHomologicalCode ℓ m A B).toStabilizerCode.hk
    rwa [finrank_H1_bbChainComplex] at h
  card_eq := by
    have h : Nat.card (bbHomologicalCode ℓ m A B).homologicalStabilizerGroup.toSubgroup =
        2 ^ (2 * (ℓ * m) - Module.finrank (ZMod 2) (bbChainComplex A B).H1) :=
      (bbHomologicalCode ℓ m A B).toStabilizerCode.card_eq
    rwa [finrank_H1_bbChainComplex] at h

variable {ℓ m : ℕ} [NeZero ℓ] [NeZero m] (A B : ZMod ℓ × ZMod m → ZMod 2)

@[simp] theorem bbHomologicalCode_numQubits :
    (bbHomologicalCode ℓ m A B).numQubits = 2 * (ℓ * m) := rfl

@[simp] theorem bbHomologicalCode_boundary1 :
    (bbHomologicalCode ℓ m A B).boundary1 = bbBoundary1 A B := rfl

@[simp] theorem bbHomologicalCode_boundary2 :
    (bbHomologicalCode ℓ m A B).boundary2 = bbBoundary2 A B := rfl

/-- `H₁` of the renumbered complex is `H₁` of `bbChainComplex A B`. -/
@[simp] theorem bbHomologicalCode_finrank_H1 :
    Module.finrank (ZMod 2) (bbHomologicalCode ℓ m A B).H1 =
      Module.finrank (ZMod 2) (bbChainComplex A B).H1 := rfl

/-- The logical-qubit count of `bbStabilizerCode` is `dim H₁` of the BB chain
complex: it has the stabilizer group of `toStabilizerCode` of the chain
complex, and differs from it only in how `k` is written. -/
theorem bbStabilizerCode_k_eq_finrank_H1 :
    2 * Module.finrank (ZMod 2) ↥(ker A ⊓ ker B) =
      Module.finrank (ZMod 2) (bbChainComplex A B).H1 :=
  (finrank_H1_bbChainComplex A B).symm

/-- The stabilizer group of a bivariate bicycle code is the homological
stabilizer group of its chain complex. -/
@[simp] theorem bbStabilizerCode_toStabilizerGroup :
    (bbStabilizerCode ℓ m A B).toStabilizerGroup =
      (bbHomologicalCode ℓ m A B).homologicalStabilizerGroup :=
  rfl

/-- The stabilizer subgroup of a bivariate bicycle code is the closure of the
face checks (`X`-type, rows of `[A | B]`) and vertex checks (`Z`-type, rows
of `[Bᵀ | Aᵀ]`). -/
@[simp] theorem bbStabilizerCode_toSubgroup :
    (bbStabilizerCode ℓ m A B).toStabilizerGroup.toSubgroup =
      Subgroup.closure (bbHomologicalCode ℓ m A B).homologicalGenerators :=
  rfl

/-! ## Example: the gross code parameters

`ℓ = 12`, `m = 6`, `A = x³ + y + y²`, `B = y³ + x + x²` give a code on
`144` qubits, definitionally; `Gross/HomologicalToCode.lean` shows that the
logical count is `12`. -/

noncomputable example :
    StabilizerGroup.StabilizerCode 144
      (2 * Module.finrank (ZMod 2)
        ↥(ker (poly[x^3 + y + y^2] : ZMod 12 × ZMod 6 → ZMod 2) ⊓
          ker (poly[y^3 + x + x^2] : ZMod 12 × ZMod 6 → ZMod 2))) :=
  bbStabilizerCode 12 6 poly[x^3 + y + y^2] poly[y^3 + x + x^2]

end BB
end Homological
end Stabilizer
end Quantum
