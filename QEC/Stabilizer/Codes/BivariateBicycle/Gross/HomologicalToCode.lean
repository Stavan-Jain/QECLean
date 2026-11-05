/-
# The gross code through the generic constructions

`grossStabilizerCode` (`StabilizerCode.lean`) is built from generated data:
trimmed generators, decoder identities for their independence, and an explicit
symplectic basis of 12 logical pairs. The generic
`HomologicalCode.toStabilizerCode` (`Framework/Homological/ToCode.lean`) builds
a code from `grossComplex` with no such data, encoding `dim H₁` logical qubits,
and the family constructor `bbStabilizerCode 12 6 grossA grossB`
(`Framework/Homological/BBStabilizerCode.lean`) writes that count as
`2 · dim (ker A ∩ ker B)`.

This file links the three. The packaged code and the generic code have the same
stabilizer subgroup (`grossStabilizerCode_toSubgroup_eq`), and `k` is a
function of the subgroup (`StabilizerCode.k_eq_of_toSubgroup_eq`), so

* `grossComplex_finrank_H1_eq_12`: `dim H₁(grossComplex) = 12`;
* `finrank_commonKernel_gross`: `dim (ker grossA ∩ ker grossB) = 6`, by the
  generic count `dim H₁ = 2 · dim (ker A ∩ ker B)`;
* `grossStabilizerCodeOfBB : StabilizerCode 144 12`, the family constructor's
  code with its parameters read off.

No new computation is involved: the `12` is the one exhibited by the generated
symplectic basis, transported along the subgroup equality. What the link
provides is that the distance results on `grossStabilizerCode` are results
about the object written down from the BB definition, `bbChainComplex grossA
grossB`, and a check that the generic logical-qubit count agrees with the
hand-built one.
-/

import QEC.Stabilizer.Codes.BivariateBicycle.Gross.StabilizerCode
import QEC.Stabilizer.Framework.Homological.BBStabilizerCode

namespace Quantum.Stabilizer.Homological.BB

open Quantum.StabilizerGroup

/-- The generic construction and the packaged code have the same stabilizer
subgroup: both are the closure of all face and vertex checks. -/
theorem grossComplex_toStabilizerCode_subgroup_eq :
    grossComplex.toStabilizerCode.toStabilizerGroup.toSubgroup =
      grossStabilizerCode.toStabilizerGroup.toSubgroup :=
  grossStabilizerCode_toSubgroup_eq.symm

/-- `dim H₁ = 12` for the gross chain complex, read off the generic code: it
shares its stabilizer subgroup with the `[[144, 12]]` code
`grossStabilizerCode`, and `k` is a function of the subgroup. -/
theorem grossComplex_finrank_H1_eq_12 :
    Module.finrank (ZMod 2) grossComplex.H1 = 12 :=
  StabilizerCode.k_eq_of_toSubgroup_eq grossComplex.toStabilizerCode grossStabilizerCode
    grossComplex_toStabilizerCode_subgroup_eq

/-- `dim (ker A ∩ ker B) = 6` for the gross polynomials, from
`dim H₁ = 2 · dim (ker A ∩ ker B)` and `dim H₁ = 12`. -/
theorem finrank_commonKernel_gross :
    Module.finrank (ZMod 2) (commonKernel grossA grossB) = 6 := by
  have h := finrank_H1_bbChainComplex grossA grossB
  rw [show bbChainComplex grossA grossB = grossComplex from rfl,
    grossComplex_finrank_H1_eq_12] at h
  omega

/-- The gross code as the family constructor's code `bbStabilizerCode 12 6 A B`
with `A = x³ + y + y²`, `B = y³ + x + x²`, and its parameters `[[144, 12]]`
read off: `2 · 12 · 6 = 144` definitionally, and `k = 2 · 6 = 12` by
`finrank_commonKernel_gross`. -/
noncomputable def grossStabilizerCodeOfBB : StabilizerCode 144 12 where
  toStabilizerGroup := (bbStabilizerCode 12 6 grossA grossB).toStabilizerGroup
  hk := by norm_num
  card_eq :=
    (bbStabilizerCode 12 6 grossA grossB).card_eq.trans
      (congrArg (2 ^ ·) (by rw [finrank_commonKernel_gross]))

end Quantum.Stabilizer.Homological.BB
