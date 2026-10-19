import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.SetTheory.Cardinal.Finite
import QEC.Stabilizer.Foundations.BinarySymplectic.CheckMatrix
import QEC.Stabilizer.Framework.Core.Stabilizer.Codespace
import QEC.Stabilizer.Framework.Core.Stabilizer.StabilizerCode
import QEC.Stabilizer.Framework.Symplectic.SymplecticSpan

/-!
# The symplectic image of a stabilizer group, and its size

The map `g ↦ toSymplectic g.operators` forgets the phase of a Pauli group
element. On a stabilizer group it forgets nothing: two elements of `S` with the
same operator part differ by a phase lying in `S`, and `−I ∉ S` rules out every
phase but `1` (the phases `±i` square to `−1`). So the map is injective on `S`
(`toSymplectic_injOn`), its image is an `𝔽₂`-subspace (`sympImage`), and

  `Nat.card S = 2 ^ finrank (sympImage S)`   (`card_eq_two_pow_finrank`).

This is the bridge between the group-level definition of a stabilizer code
(`StabilizerCode n k`: `Nat.card S = 2 ^ (n - k)`) and the check-matrix view:

- `StabilizerCode.finrank_sympImage`: the `𝔽₂`-rank of the symplectic image of
  a `[[n, k]]` code's stabilizer is `n − k`;
- `NQubitPauliGroupElement.card_closure_eq_two_pow_length`: commuting
  generators with linearly independent check-matrix rows and `−I` outside their
  closure generate a group with exactly `2 ^ L.length` elements — the soundness
  input of `StabilizerCode.Presentation.toCode`;
- `NQubitPauliGroupElement.rowsLinearIndependent.nodup`: linearly independent
  rows are pairwise distinct, so such a list has no repeated generator.
-/

namespace Quantum

open NQubitPauliGroupElement NQubitPauliOperator

variable {n : ℕ}

namespace StabilizerGroup

/-- The symplectic map is injective on a stabilizer group: two elements with the
same operator part differ by `g * h⁻¹ ∈ S`, whose operator part is the identity,
so `g * h⁻¹ = 1` — its phase can be neither `−1` (that is `−I`) nor `±i` (whose
square is `−I`); see `eq_one_of_mem_stabilizer_and_is_scalar`. -/
lemma toSymplectic_injOn (S : StabilizerGroup n) :
    Set.InjOn (fun g : NQubitPauliGroupElement n => toSymplectic g.operators)
      (S.toSubgroup : Set (NQubitPauliGroupElement n)) := by
  intro g hg h hh hgh
  have hops : g.operators = h.operators := toSymplectic_injective hgh
  have h1 : g * h⁻¹ = 1 := eq_one_of_mem_stabilizer_and_is_scalar S (g * h⁻¹)
    (S.mul_mem hg (S.inv_mem hh)) (mul_inv_operators_identity_of_eq_operators g h hops)
  exact mul_inv_eq_one.mp h1

/-- The symplectic image of a stabilizer group: the `𝔽₂`-span of the symplectic
vectors of its elements. The image is already closed under addition and
scalars (`mem_sympImage_iff`), so the span adds nothing. -/
def sympImage (S : StabilizerGroup n) : Submodule (ZMod 2) (Fin (n + n) → ZMod 2) :=
  Submodule.span (ZMod 2)
    ((fun g : NQubitPauliGroupElement n => toSymplectic g.operators) '' S.toSubgroup)

/-- A vector lies in the symplectic image of `S` iff it is the symplectic vector
of an element of `S`: the image of a subgroup is closed under `+` (products),
contains `0` (the identity), and over `𝔽₂` scalars are `0` or `1`. -/
lemma mem_sympImage_iff (S : StabilizerGroup n) (v : Fin (n + n) → ZMod 2) :
    v ∈ S.sympImage ↔ ∃ g ∈ S.toSubgroup, toSymplectic g.operators = v := by
  constructor
  · intro hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, hg, rfl⟩ := hx
      exact ⟨g, hg, rfl⟩
    | zero => exact ⟨1, S.one_mem, toSymplectic_one_operators⟩
    | add x y _ _ hx hy =>
      obtain ⟨g, hg, rfl⟩ := hx
      obtain ⟨h, hh, rfl⟩ := hy
      exact ⟨g * h, S.mul_mem hg hh, funext (toSymplectic_mul g h)⟩
    | smul a x _ hx =>
      obtain ⟨g, hg, rfl⟩ := hx
      rcases (by decide : ∀ b : ZMod 2, b = 0 ∨ b = 1) a with rfl | rfl
      · exact ⟨1, S.one_mem, by rw [toSymplectic_one_operators, zero_smul]⟩
      · exact ⟨g, hg, (one_smul _ _).symm⟩
  · rintro ⟨g, hg, rfl⟩
    exact Submodule.subset_span ⟨g, hg, rfl⟩

/-- As a set, the symplectic image of `S` is the image of `S` under the
symplectic map. -/
lemma coe_sympImage (S : StabilizerGroup n) :
    (S.sympImage : Set (Fin (n + n) → ZMod 2)) =
      (fun g : NQubitPauliGroupElement n => toSymplectic g.operators) '' S.toSubgroup := by
  ext v
  rw [SetLike.mem_coe, mem_sympImage_iff]
  rfl

/-- **Size of a stabilizer group.** A stabilizer group has `2 ^ r` elements,
where `r` is the `𝔽₂`-rank of its symplectic image: the symplectic map is a
bijection from `S` onto that subspace (`toSymplectic_injOn`,
`coe_sympImage`). -/
theorem card_eq_two_pow_finrank (S : StabilizerGroup n) :
    Nat.card S.toSubgroup = 2 ^ Module.finrank (ZMod 2) S.sympImage := by
  have h1 := Nat.card_image_of_injOn (toSymplectic_injOn S)
  rw [← coe_sympImage] at h1
  have h2 : Nat.card S.sympImage = 2 ^ Module.finrank (ZMod 2) S.sympImage := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  rw [← h2]
  exact h1.symm

/-- The symplectic image of the stabilizer group generated by a list is the row
span of the list's check matrix. -/
lemma sympImage_mkStabilizerFromGenerators (L : List (NQubitPauliGroupElement n))
    (hC : ∀ g ∈ listToSet L, ∀ h ∈ listToSet L, g * h = h * g)
    (hN : negIdentity n ∉ Subgroup.closure (listToSet L)) :
    (mkStabilizerFromGenerators n L hC hN).sympImage = sympSpan L := by
  apply le_antisymm
  · rw [sympImage, Submodule.span_le]
    rintro _ ⟨g, hg, rfl⟩
    rw [SetLike.mem_coe, sympSpan_eq_span_listToSet]
    exact Quantum.toSymplectic_mem_span_of_mem_closure hg
  · rw [sympSpan, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact Submodule.subset_span ⟨L.get i, Subgroup.subset_closure (List.get_mem L i), rfl⟩

/-- **The rank characterization of `k`.** The symplectic image of a
`[[n, k]]` code's stabilizer has `𝔽₂`-rank exactly `n − k`: compare
`card_eq_two_pow_finrank` with `StabilizerCode.card_eq`. -/
theorem StabilizerCode.finrank_sympImage {k : ℕ} (C : StabilizerCode n k) :
    Module.finrank (ZMod 2) C.toStabilizerGroup.sympImage = n - k := by
  have h := card_eq_two_pow_finrank C.toStabilizerGroup
  rw [C.card_eq] at h
  exact (Nat.pow_right_injective le_rfl h).symm

end StabilizerGroup

namespace NQubitPauliGroupElement

/-- Linearly independent check-matrix rows are pairwise distinct, so a list with
linearly independent rows has no repeated element. -/
theorem rowsLinearIndependent.nodup {L : List (NQubitPauliGroupElement n)}
    (h : rowsLinearIndependent L) : L.Nodup := by
  rw [List.nodup_iff_injective_get]
  intro i j hij
  apply h.injective
  funext c
  simp only [checkMatrix, hij]

/-- **Size of the group generated by a presentation.** Pairwise commuting
generators with linearly independent check-matrix rows, whose closure avoids
`−I`, generate a group with exactly `2 ^ L.length` elements. -/
theorem card_closure_eq_two_pow_length (L : List (NQubitPauliGroupElement n))
    (hIndep : rowsLinearIndependent L)
    (hC : ∀ g ∈ listToSet L, ∀ h ∈ listToSet L, g * h = h * g)
    (hN : StabilizerGroup.negIdentity n ∉ Subgroup.closure (listToSet L)) :
    Nat.card (Subgroup.closure (listToSet L)) = 2 ^ L.length := by
  have h := StabilizerGroup.card_eq_two_pow_finrank
    (StabilizerGroup.mkStabilizerFromGenerators n L hC hN)
  rw [StabilizerGroup.sympImage_mkStabilizerFromGenerators, sympSpan,
    finrank_span_eq_card hIndep, Fintype.card_fin] at h
  exact h

end NQubitPauliGroupElement

end Quantum
