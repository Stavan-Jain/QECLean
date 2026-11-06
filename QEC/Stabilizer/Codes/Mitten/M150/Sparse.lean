/-
# Sparse check maps for the mitten code

The canonical check enumeration addresses the packed decoder tables.
The two check-entry functions are identified with the boundary maps on
point masses by symbolic convolution identities. Linearity extends those
identities to arbitrary chains.
-/

import QEC.Stabilizer.Codes.Mitten.M150.Defs
import QEC.Stabilizer.Framework.Homological.LogicalCorrespondence


set_option maxRecDepth 65536

namespace Quantum
namespace Stabilizer
namespace Homological
namespace LP
namespace M150

open scoped BigOperators
open NQubitPauliGroupElement

/-! ## §1  Canonical cell indexing

Both check types (`C2` = X-checks and `C0` = Z-checks) are `Fin 2 × M150G`;
the canonical index of a cell is `30·i + g` (`checkOf` from `Data.lean`).
The bijection lets the packed-Nat decoder tables address cells by index. -/

/-- Canonical cell of a `Fin 60` index. -/
def checkOfF (p : Fin 60) : Fin 2 × M150G := checkOf p.val

/-- The canonical enumeration bijects the sixty check cells. -/
lemma checkOfF_bijective : Function.Bijective checkOfF := by
  rw [Fintype.bijective_iff_injective_and_card]
  exact ⟨by decide, by decide⟩

/-! ## §2  Sparse boundary terms and their bridges

`d2term c q` is the `H_X` entry at X-check `c = (β, h)`, qubit `q = (m, x)`
(grid block `m < 4`: `[m%2 = β]·[h·x⁻¹ ∈ a_{m/2}]`; shared block `m = 4`:
`[x⁻¹·h ∈ b_β]`), and `cmTerm p q` the `H_Z` entry at Z-check `p = (α, y)`
(grid: `[m/2 = α]·[y⁻¹·x ∈ b_{m%2}]`; shared: `[x·y⁻¹ ∈ a_α]`).  The
pointwise bridges follow from the translated point-mass formulas for
left and right convolution; linearity then gives the chain-level bridges. -/

/-- `H_X` entry at X-check `c`, qubit `q` (the `(c, q)` entry of `∂₂`'s
matrix). -/
def d2term (c : Fin 2 × M150G) (q : Fin 5 × M150G) : ZMod 2 :=
  if q.1.val = 4 then m150B c.1 (q.2⁻¹ * c.2)
  else if blockCol q.1 = c.1 then m150A (blockRow q.1) (c.2 * q.2⁻¹) else 0

/-- `H_Z` entry at Z-check `p`, qubit `q` (the `(p, q)` entry of `∂₁`'s
matrix, i.e. of `cutMap`'s columns). -/
def cmTerm (p : Fin 2 × M150G) (q : Fin 5 × M150G) : ZMod 2 :=
  if q.1.val = 4 then m150A p.1 (q.2 * p.2⁻¹)
  else if blockRow q.1 = p.1 then m150B (blockCol q.1) (p.2⁻¹ * q.2) else 0

/-- The face-boundary map on point masses has the sparse check entries. -/
lemma lpBoundary2Fn_single_eq_d2term :
    ∀ (c : Fin 2 × M150G) (q : Fin 5 × M150G),
      lpBoundary2Fn m150A m150B (fun e => if e = c then 1 else 0) q
        = d2term c q := by
  rintro ⟨c, x⟩ ⟨q, y⟩
  fin_cases c <;> fin_cases q <;>
    simp [-lconv_apply, -rconv_apply, lpBoundary2Fn, d2term, blockRow, blockCol, lconv_delta,
      rconv_delta, antipode] <;> simp [lconv, rconv]


/-- The primal-boundary map on point masses has the sparse check entries. -/
lemma lpBoundary1Fn_single_eq_cmTerm :
    ∀ (q : Fin 5 × M150G) (p : Fin 2 × M150G),
      lpBoundary1Fn m150A m150B (fun e => if e = q then 1 else 0) p
        = cmTerm p q := by
  rintro ⟨q, x⟩ ⟨p, y⟩
  fin_cases p <;> fin_cases q <;>
    simp [-lconv_apply, -rconv_apply, lpBoundary1Fn, cmTerm, gridIdx, sharedIdx, blockRow, blockCol,
      lconv_delta, rconv_delta, antipode] <;> simp [lconv, rconv]


/-- The face-boundary identity in the homological cell types. -/
lemma boundary2_single_apply (c : m150Complex.C2) (q : m150Complex.C1) :
    m150Complex.boundary2 (Pi.single c 1) q = d2term c q := by
  have hpt : (Pi.single c (1 : ZMod 2))
      = (fun e => if e = c then (1 : ZMod 2) else 0) := by
    funext e
    exact Pi.single_apply c 1 e
  rw [hpt]
  exact lpBoundary2Fn_single_eq_d2term c q

/-- `∂₁(δ_q)` evaluated at a Z-check is the sparse `cmTerm`. -/
lemma boundary1_single_apply (q : m150Complex.C1) (p : m150Complex.C0) :
    m150Complex.boundary1 (Pi.single q 1) p = cmTerm p q := by
  have hpt : (Pi.single q (1 : ZMod 2))
      = (fun e => if e = q then (1 : ZMod 2) else 0) := by
    funext e
    exact Pi.single_apply q 1 e
  rw [hpt]
  exact lpBoundary1Fn_single_eq_cmTerm q p

/-- Expand a face boundary in point-mass images. -/
private lemma boundary2_apply_eq_sum_single (f : m150Complex.C2 → ZMod 2)
    (q : m150Complex.C1) :
    m150Complex.boundary2 f q
      = ∑ c : m150Complex.C2, f c * m150Complex.boundary2 (Pi.single c 1) q := by
  have hf : f = ∑ c : m150Complex.C2, f c • Pi.single c (1 : ZMod 2) := by
    ext e
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hf]
  simp [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

/-- **(L1, X)** Basis expansion of `∂₂` in the sparse `d2term` form. -/
lemma boundary2_apply_eq_sum_d2term (f : m150Complex.C2 → ZMod 2)
    (q : m150Complex.C1) :
    m150Complex.boundary2 f q = ∑ c : m150Complex.C2, f c * d2term c q := by
  rw [boundary2_apply_eq_sum_single]
  exact Finset.sum_congr rfl fun c _ => by rw [boundary2_single_apply]

/-- **(L1, Z)** `cutMap` in the sparse `cmTerm` form. -/
lemma cutMap_apply_eq_sum_cmTerm (s : m150Complex.C0 → ZMod 2)
    (q : m150Complex.C1) :
    m150Complex.cutMap s q = ∑ p : m150Complex.C0, s p * cmTerm p q := by
  rw [HomologicalCode.cutMap_apply]
  exact Finset.sum_congr rfl fun p _ => by rw [boundary1_single_apply]

/-- Computable transpose boundary, expressed using sparse check entries. -/
def dualBfn (c : Fin 5 × M150G → ZMod 2) (p : Fin 2 × M150G) : ZMod 2 :=
  ∑ q : Fin 5 × M150G, c q * d2term p q

/-- The sparse transpose agrees with the homological dual boundary. -/
lemma dualBoundary_eq_dualBfn (c : Fin 5 × M150G → ZMod 2) (p : Fin 2 × M150G) :
    m150Complex.dualBoundary c p = dualBfn c p := by
  rw [HomologicalCode.dualBoundary_apply]
  exact Finset.sum_congr rfl fun q _ => by rw [boundary2_single_apply]

end M150
end LP
end Homological
end Stabilizer
end Quantum
