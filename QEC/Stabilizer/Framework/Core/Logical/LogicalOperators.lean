import QEC.Foundations.Basic
import QEC.Stabilizer.Framework.Core.Stabilizer.StabilizerGroup
import QEC.Stabilizer.Framework.Core.Stabilizer.Centralizer
import QEC.Stabilizer.Framework.Core.Logical.LogicalOperatorCoset
import QEC.Stabilizer.Framework.Core.Stabilizer.Codespace
import QEC.Stabilizer.Framework.Core.Logical.LogicalGates
import QEC.Stabilizer.Framework.Core.Logical.LogicalGateGroup
import QEC.Stabilizer.Foundations.PauliGroup
import QEC.Stabilizer.Foundations.PauliGroup.Representation
import QEC.Stabilizer.Foundations.PauliGroup.NQubitElement
import QEC.Stabilizer.Foundations.PauliGroup.Commutation

/-!
# Logical operators

A Pauli logical operator of a stabilizer group `S` is a Pauli group element
whose gate maps the codespace to itself.

Main definitions and results:

- `IsPauliLogicalOperator g S`: the gate of `g` is a logical gate for `S`;
- `isPauliLogicalOperator_iff_mem_centralizer`: the Pauli logical operators are
  exactly the elements of the centralizer of `S`;
- `IsNontrivialLogicalOperator g S`: `g` is in the centralizer and no element of
  `S` has the same operator part, i.e. `g` represents a coset of `S` other than
  the cosets `φ • S` of pure phases. These are the operators that code distance
  minimizes over;
- `isNontrivialLogicalOperator_of_anticommute_centralizer`: a centralizer
  element that anticommutes with another centralizer element is nontrivial;
- `IsNontrivialLogicalOperator.weight_pos`: a nontrivial logical operator has
  positive weight;
- `LogicalQubitOps n S`: an anticommuting pair of logical `X` and `Z`
  operators, both of which are nontrivial logical operators;
- `SameLogicalOperator L L' S`: `L` and `L'` lie in the same coset of `S`, an
  equivalence relation.
-/

namespace Quantum
namespace StabilizerGroup

variable {n : ℕ}
open Matrix
open scoped BigOperators

/-!
## Pauli logical operators and the centralizer
-/

/-- A Pauli logical operator is a Pauli group element whose gate maps the
codespace to itself. Equivalently, it lies in the centralizer of `S`
(`isPauliLogicalOperator_iff_mem_centralizer`). -/
def IsPauliLogicalOperator (g : NQubitPauliGroupElement n) (S : StabilizerGroup n) : Prop :=
  IsLogicalGate (g.toGate) S

/-- A Pauli operator that anticommutes with an element `s` of the stabilizer
group is not a Pauli logical operator: on a codespace state `ψ` it would give
`g ψ = s g ψ = -g s ψ = -g ψ`, forcing `ψ = 0`. -/
lemma anticommutes_imp_not_isPauliLogicalOperator (g : NQubitPauliGroupElement n)
    (S : StabilizerGroup n) (s : NQubitPauliGroupElement n) (hs : s ∈ S.toSubgroup)
    (h_anti : NQubitPauliGroupElement.Anticommute s g) : ¬IsPauliLogicalOperator g S := by
  intro hg
  obtain ⟨ψ, hψ⟩ := exists_codespace_state S
  have hsψ : s.toMatrix *ᵥ ψ.val = ψ.val := hψ s hs
  have h_fix : s.toMatrix *ᵥ (g.toMatrix *ᵥ ψ.val) = g.toMatrix *ᵥ ψ.val := by
    have h := (mem_logicalGateGroup_iff_forall_mem _ S).mp hg ψ.val hψ s hs
    rwa [NQubitPauliGroupElement.toGate_val] at h
  rw [mulVec_mulVec, NQubitPauliGroupElement.Anticommute.toMatrix_mul_neg s g h_anti,
    smul_mulVec, ← mulVec_mulVec, hsψ, neg_one_smul] at h_fix
  have h_zero : g.toMatrix *ᵥ ψ.val = 0 :=
    funext fun i => CharZero.eq_neg_self_iff.mp (congrFun h_fix.symm i)
  have h_norm := ψ.2
  rw [← one_mulVec ψ.val, ← NQubitPauliGroupElement.toMatrix_one, ← inv_mul_cancel g,
    NQubitPauliGroupElement.toMatrix_mul, ← mulVec_mulVec, h_zero, mulVec_zero,
    Quantum.norm_zero] at h_norm
  exact zero_ne_one h_norm

/-- A Pauli group element is a logical operator iff it lies in the centralizer
of `S`. -/
theorem isPauliLogicalOperator_iff_mem_centralizer (g : NQubitPauliGroupElement n)
    (S : StabilizerGroup n) : IsPauliLogicalOperator g S ↔ g ∈ centralizer S := by
  refine ⟨fun hg => (mem_centralizer_iff g S).mpr fun s hs => ?_,
    fun hg => (mem_logicalGateGroup_iff_forall_mem _ S).mpr fun v hv s hs => ?_⟩
  · exact (NQubitPauliGroupElement.commute_or_anticommute s g).resolve_right fun h =>
      anticommutes_imp_not_isPauliLogicalOperator g S s hs h hg
  · rw [NQubitPauliGroupElement.toGate_val, mulVec_mulVec,
      ← NQubitPauliGroupElement.toMatrix_mul, hg s hs, NQubitPauliGroupElement.toMatrix_mul,
      ← mulVec_mulVec, hv s hs]

/-- A Pauli group element is a logical operator iff it commutes with every
element of a generating set of the stabilizer. -/
theorem isPauliLogicalOperator_iff_commutes_generators (g : NQubitPauliGroupElement n)
    (S : StabilizerGroup n) (genSet : Set (NQubitPauliGroupElement n))
    (h_closure : S.toSubgroup = Subgroup.closure genSet) :
    IsPauliLogicalOperator g S ↔ ∀ s ∈ genSet, s * g = g * s := by
  rw [isPauliLogicalOperator_iff_mem_centralizer, mem_centralizer_iff_closure g S genSet h_closure]

/-- Every element of the stabilizer group is a Pauli logical operator. -/
lemma IsPauliLogicalOperator_of_mem_stabilizer (S : StabilizerGroup n)
    {g : NQubitPauliGroupElement n} (hg : g ∈ S.toSubgroup) :
    IsPauliLogicalOperator g S :=
  (isPauliLogicalOperator_iff_mem_centralizer g S).2 (stabilizer_le_centralizer S hg)

/-- Being a Pauli logical operator depends only on the underlying subgroup of
the stabilizer group. -/
theorem IsPauliLogicalOperator_of_toSubgroup_eq (g : NQubitPauliGroupElement n)
    {S T : StabilizerGroup n} (h : S.toSubgroup = T.toSubgroup) :
    (IsPauliLogicalOperator g S ↔ IsPauliLogicalOperator g T) :=
  isLogicalGate_iff_toSubgroup_eq (g.toGate) S T h

/-!
## Nontrivial logical operators
-/

/-- A nontrivial logical operator is a Pauli logical operator that represents a
nontrivial coset: `g` is in the centralizer, and no `s ∈ S` has the same
operator part as `g`. So the coset of `g` is not `φ • S` for any phase `φ`, and
in particular `g ∉ S`. -/
def IsNontrivialLogicalOperator (g : NQubitPauliGroupElement n) (S : StabilizerGroup n) : Prop :=
  RepresentsNontrivialCoset g S

/-- A nontrivial logical operator is a centralizer element whose operator part
is not shared by any element of the stabilizer. -/
theorem IsNontrivialLogicalOperator_iff (g : NQubitPauliGroupElement n) (S : StabilizerGroup n) :
    IsNontrivialLogicalOperator g S ↔
      g ∈ centralizer S ∧ ∀ s ∈ S.toSubgroup, s.operators ≠ g.operators :=
  Iff.rfl

/-- Being a nontrivial logical operator depends only on the underlying subgroup
of the stabilizer group. -/
theorem IsNontrivialLogicalOperator_of_toSubgroup_eq (g : NQubitPauliGroupElement n)
    {S T : StabilizerGroup n} (h : S.toSubgroup = T.toSubgroup) :
    (IsNontrivialLogicalOperator g S ↔ IsNontrivialLogicalOperator g T) :=
  RepresentsNontrivialCoset_of_toSubgroup_eq g h

/-- A centralizer element that anticommutes with some other centralizer element
is a nontrivial logical operator. No stabilizer element can share its operator
part: the stabilizer commutes with the whole centralizer, and anticommutation
only sees operator parts (`anticommute_congr_left`). This certifies a
low-weight representative `X̄ * s` (`s` a stabilizer) as nontrivial: it still
anticommutes with `Z̄`. -/
theorem isNontrivialLogicalOperator_of_anticommute_centralizer (S : StabilizerGroup n)
    {g h : NQubitPauliGroupElement n} (hg : g ∈ centralizer S) (hh : h ∈ centralizer S)
    (hgh : NQubitPauliGroupElement.Anticommute g h) : IsNontrivialLogicalOperator g S :=
  ⟨hg, fun s hs h_ops =>
    not_mem_stabilizer_of_anticommutes_centralizer S s h hh
      ((NQubitPauliGroupElement.anticommute_congr_left h_ops).mpr hgh) hs⟩

/-- A nontrivial logical operator has positive weight: an element of weight `0`
has the operator part of the identity, which is in the stabilizer group. -/
lemma IsNontrivialLogicalOperator.weight_pos {g : NQubitPauliGroupElement n}
    {S : StabilizerGroup n} (hg : IsNontrivialLogicalOperator g S) :
    0 < NQubitPauliGroupElement.weight g :=
  Nat.pos_of_ne_zero fun h =>
    hg.2 1 S.one_mem ((NQubitPauliGroupElement.weight_eq_zero_iff g).mp h).symm

/-!
## Logical `X` and `Z` of one logical qubit
-/

/-- Data for one logical qubit: logical `X` and `Z` operators that commute with
the stabilizer and anticommute with each other. -/
structure LogicalQubitOps (n : ℕ) (S : StabilizerGroup n) where
  /-- Logical X operator. -/
  xOp : NQubitPauliGroupElement n
  /-- Logical Z operator. -/
  zOp : NQubitPauliGroupElement n
  /-- Logical X is in the centralizer of S. -/
  x_mem_centralizer : xOp ∈ centralizer S
  /-- Logical Z is in the centralizer of S. -/
  z_mem_centralizer : zOp ∈ centralizer S
  /-- X̄ and Z̄ anticommute. -/
  anticommute : NQubitPauliGroupElement.Anticommute xOp zOp

namespace LogicalQubitOps

/-- The logical X operator is a Pauli logical operator. -/
theorem xOp_IsPauliLogicalOperator {S : StabilizerGroup n} (ops : LogicalQubitOps n S) :
    IsPauliLogicalOperator ops.xOp S :=
  (isPauliLogicalOperator_iff_mem_centralizer ops.xOp S).2 ops.x_mem_centralizer

/-- The logical Z operator is a Pauli logical operator. -/
theorem zOp_IsPauliLogicalOperator {S : StabilizerGroup n} (ops : LogicalQubitOps n S) :
    IsPauliLogicalOperator ops.zOp S :=
  (isPauliLogicalOperator_iff_mem_centralizer ops.zOp S).2 ops.z_mem_centralizer

/-- The logical X operator is a nontrivial logical operator. -/
theorem xOp_nontrivial {S : StabilizerGroup n} (ops : LogicalQubitOps n S) :
    IsNontrivialLogicalOperator ops.xOp S :=
  isNontrivialLogicalOperator_of_anticommute_centralizer S ops.x_mem_centralizer
    ops.z_mem_centralizer ops.anticommute

/-- The logical Z operator is a nontrivial logical operator. -/
theorem zOp_nontrivial {S : StabilizerGroup n} (ops : LogicalQubitOps n S) :
    IsNontrivialLogicalOperator ops.zOp S :=
  isNontrivialLogicalOperator_of_anticommute_centralizer S ops.z_mem_centralizer
    ops.x_mem_centralizer
    (NQubitPauliGroupElement.anticommute_symm ops.xOp ops.zOp ops.anticommute)

/-- The logical X operator is not in the stabilizer. -/
theorem xOp_not_mem {S : StabilizerGroup n} (ops : LogicalQubitOps n S) :
    ops.xOp ∉ S.toSubgroup :=
  RepresentsNontrivialCoset.not_mem ops.xOp_nontrivial

/-- The logical Z operator is not in the stabilizer. -/
theorem zOp_not_mem {S : StabilizerGroup n} (ops : LogicalQubitOps n S) :
    ops.zOp ∉ S.toSubgroup :=
  RepresentsNontrivialCoset.not_mem ops.zOp_nontrivial

/-- No stabilizer element has the same operator part as logical X. -/
theorem xOp_operators_ne_of_mem {S : StabilizerGroup n} (ops : LogicalQubitOps n S)
    (s : NQubitPauliGroupElement n) (hs : s ∈ S.toSubgroup) :
    s.operators ≠ ops.xOp.operators :=
  ops.xOp_nontrivial.2 s hs

/-- No stabilizer element has the same operator part as logical Z. -/
theorem zOp_operators_ne_of_mem {S : StabilizerGroup n} (ops : LogicalQubitOps n S)
    (s : NQubitPauliGroupElement n) (hs : s ∈ S.toSubgroup) :
    s.operators ≠ ops.zOp.operators :=
  ops.zOp_nontrivial.2 s hs

end LogicalQubitOps

/-!
## Equality of logical operators
-/

/-- Two Pauli elements represent the same logical operator if they differ by an
element of the stabilizer, i.e. lie in the same coset of `S`. -/
def SameLogicalOperator (L L' : NQubitPauliGroupElement n) (S : StabilizerGroup n) : Prop :=
  L⁻¹ * L' ∈ S.toSubgroup

namespace SameLogicalOperator

/-- Every Pauli element is the same logical operator as itself. -/
theorem refl (L : NQubitPauliGroupElement n) (S : StabilizerGroup n) :
    SameLogicalOperator L L S := by
  rw [SameLogicalOperator, inv_mul_cancel]
  exact S.one_mem

/-- If `L` and `L'` represent the same logical operator, so do `L'` and `L`. -/
theorem symm (S : StabilizerGroup n) {L L' : NQubitPauliGroupElement n}
    (h : SameLogicalOperator L L' S) : SameLogicalOperator L' L S := by
  have h_inv := S.inv_mem h
  rwa [_root_.mul_inv_rev, inv_inv] at h_inv

/-- Representing the same logical operator is transitive. -/
theorem trans (S : StabilizerGroup n) {L L' L'' : NQubitPauliGroupElement n}
    (h₁ : SameLogicalOperator L L' S) (h₂ : SameLogicalOperator L' L'' S) :
    SameLogicalOperator L L'' S := by
  have h_mul := S.mul_mem h₁ h₂
  rwa [_root_.mul_assoc, mul_inv_cancel_left] at h_mul

/-- Representing the same logical operator is an equivalence relation. -/
theorem equivalence (S : StabilizerGroup n) :
    Equivalence (fun L L' => SameLogicalOperator L L' S) where
  refl L := refl L S
  symm := symm S
  trans := trans S

end SameLogicalOperator

end StabilizerGroup
end Quantum
