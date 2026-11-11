import QEC.Stabilizer.Codes.Toric.H1Dimension

/-!
# Wrapping numbers of toric cycles

A 1-chain `c` on the `L × L` torus has a horizontal-edge parity
`hAt L x c = ∑ y, c (EdgeIdx.h x y)` in every column `x`, and a vertical-edge
parity `vAt L y c = ∑ x, c (EdgeIdx.v x y)` in every row `y`.

* On a cycle these parities do not depend on the column or the row
  (`hAt_independent_on_cycles`, `vAt_independent_on_cycles`); `hWrap L c` and
  `vWrap L c` are their values at the column and the row `zeroCoord L`: the
  wrapping numbers of the cycle `c`.
* The wrapping numbers vanish on boundaries (`h_boundary_zero`,
  `v_boundary_zero`), so they define a linear map
  `phi L : H₁ L →ₗ[ZMod 2] ZMod 2 × ZMod 2`.
* `phi L` is bijective (`phi_bijective`; the linear equivalence is
  `phiEquiv L`): it is onto because the cycles `loopChain L a b` realise all
  four values, and `dim H₁ = 2`. Equivalently, a cycle is a boundary iff both
  of its wrapping numbers vanish (`mem_toricBoundaries_iff_wrap_eq_zero`).
-/

namespace Quantum
namespace Stabilizer
namespace Lattice

open scoped Homology
open scoped ToricChain

variable (L : ℕ)

/-! ## Column and row parities -/

/-- The coordinate `0 : Fin L` of a nonempty lattice. -/
def zeroCoord [Fact (0 < L)] : Fin L := ⟨0, Fact.out⟩

/-- The parity of the horizontal edges of `c` in the column `x0`. -/
def hAt (x0 : Fin L) (c : C1 L) : ZMod 2 :=
  ∑ y : Fin L, c (EdgeIdx.h x0 y)

/-- The parity of the vertical edges of `c` in the row `y0`. -/
def vAt (y0 : Fin L) (c : C1 L) : ZMod 2 :=
  ∑ x : Fin L, c (EdgeIdx.v x y0)

/-- `hAt L x0` as a linear map. -/
def hAtLinear (x0 : Fin L) : C1 L →ₗ[ZMod 2] ZMod 2 where
  toFun := hAt L x0
  map_add' c d := by simp [hAt, Finset.sum_add_distrib]
  map_smul' a c := by simp [hAt, Finset.mul_sum]

/-- `vAt L y0` as a linear map. -/
def vAtLinear (y0 : Fin L) : C1 L →ₗ[ZMod 2] ZMod 2 where
  toFun := vAt L y0
  map_add' c d := by simp [vAt, Finset.sum_add_distrib]
  map_smul' a c := by simp [vAt, Finset.mul_sum]

variable [Fact (0 < L)]

/-- The sum of `∂₁ c` over the vertices of the column `x` is the sum of the
horizontal-edge parities of `c` in the columns `x` and `prev L x`. -/
lemma sum_toricBoundary1_column (c : C1 L) (x : Fin L) :
    ∑ y, ∂₁ L c (x, y) = hAt L x c + hAt L (prev L x) c := by
  simp only [toricBoundary1_apply, Finset.sum_add_distrib, hAt]
  rw [sum_comp_prev L fun y => c (EdgeIdx.v x y), add_assoc, CharTwo.add_self_eq_zero, add_zero]

/-- The sum of `∂₁ c` over the vertices of the row `y` is the sum of the
vertical-edge parities of `c` in the rows `y` and `prev L y`. -/
lemma sum_toricBoundary1_row (c : C1 L) (y : Fin L) :
    ∑ x, ∂₁ L c (x, y) = vAt L y c + vAt L (prev L y) c := by
  simp only [toricBoundary1_apply, Finset.sum_add_distrib, vAt]
  rw [sum_comp_prev L fun x => c (EdgeIdx.h x y), CharTwo.add_self_eq_zero, zero_add]

/-- On a cycle, the horizontal-edge parity is the same in every column. -/
theorem hAt_independent_on_cycles (c : Z₁ L) (x0 x1 : Fin L) :
    hAt L x0 c.1 = hAt L x1 c.1 := by
  refine eq_of_forall_next_eq L (fun x => hAt L x c.1) (fun x => ?_) x0 x1
  have h := sum_toricBoundary1_column L c.1 (next L x)
  rw [prev_next, show ∂₁ L c.1 = 0 from c.2] at h
  exact CharTwo.add_eq_zero.1 (h.symm.trans Finset.sum_const_zero)

/-- On a cycle, the vertical-edge parity is the same in every row. -/
theorem vAt_independent_on_cycles (c : Z₁ L) (y0 y1 : Fin L) :
    vAt L y0 c.1 = vAt L y1 c.1 := by
  refine eq_of_forall_next_eq L (fun y => vAt L y c.1) (fun y => ?_) y0 y1
  have h := sum_toricBoundary1_row L c.1 (next L y)
  rw [prev_next, show ∂₁ L c.1 = 0 from c.2] at h
  exact CharTwo.add_eq_zero.1 (h.symm.trans Finset.sum_const_zero)

/-- The boundary of a 2-chain has even horizontal-edge parity in every
column: each face of the column meets it in two horizontal edges. -/
lemma hAt_toricBoundary2 (x0 : Fin L) (f : C2 L) : hAt L x0 (∂₂ L f) = 0 := by
  simp only [hAt, toricBoundary2_apply_h, Finset.sum_add_distrib]
  rw [sum_comp_prev L fun y => f (x0, y)]
  exact CharTwo.add_self_eq_zero _

/-- The boundary of a 2-chain has even vertical-edge parity in every row. -/
lemma vAt_toricBoundary2 (y0 : Fin L) (f : C2 L) : vAt L y0 (∂₂ L f) = 0 := by
  simp only [vAt, toricBoundary2_apply_v, Finset.sum_add_distrib]
  rw [sum_comp_prev L fun x => f (x, y0)]
  exact CharTwo.add_self_eq_zero _

/-! ## Wrapping numbers -/

/-- The horizontal wrapping number of a cycle: its horizontal-edge parity in
the column `zeroCoord L`. -/
def hWrap (c : Z₁ L) : ZMod 2 :=
  hAt L (zeroCoord L) c.1

/-- The vertical wrapping number of a cycle: its vertical-edge parity in the
row `zeroCoord L`. -/
def vWrap (c : Z₁ L) : ZMod 2 :=
  vAt L (zeroCoord L) c.1

/-- The horizontal wrapping number vanishes on boundaries. -/
theorem h_boundary_zero (b : B₁ L) : hAt L (zeroCoord L) b.1 = 0 := by
  obtain ⟨f, hf⟩ := b.2
  rw [← hf]
  exact hAt_toricBoundary2 L _ f

/-- The vertical wrapping number vanishes on boundaries. -/
theorem v_boundary_zero (b : B₁ L) : vAt L (zeroCoord L) b.1 = 0 := by
  obtain ⟨f, hf⟩ := b.2
  rw [← hf]
  exact vAt_toricBoundary2 L _ f

/-- The wrapping map `H₁ → (ZMod 2)²`, sending the class of a cycle `c` to its
wrapping numbers `(hWrap L c, vWrap L c)`. -/
noncomputable def phi : H₁ L →ₗ[ZMod 2] ZMod 2 × ZMod 2 :=
  Submodule.liftQ _
    (((hAtLinear L (zeroCoord L)).prod (vAtLinear L (zeroCoord L))).comp (Z₁ L).subtype)
    fun c hc => Prod.ext (h_boundary_zero L ⟨c.1, hc⟩) (v_boundary_zero L ⟨c.1, hc⟩)

/-- `phi` on the class of a cycle. -/
theorem phi_mk (c : Z₁ L) :
    phi L (Submodule.Quotient.mk c) = (hWrap L c, vWrap L c) := rfl

/-! ## The wrapping map is an isomorphism -/

/-- The 1-chain that is `a` on the horizontal edges of the row `zeroCoord L`
and `b` on the vertical edges of the column `zeroCoord L`: `a` times the
horizontal loop plus `b` times the vertical loop. -/
def loopChain (a b : ZMod 2) : C1 L
  | EdgeIdx.h _ y => if y = zeroCoord L then a else 0
  | EdgeIdx.v x _ => if x = zeroCoord L then b else 0

/-- `loopChain L a b` is a cycle. -/
lemma loopChain_mem_toricCycles (a b : ZMod 2) : loopChain L a b ∈ Z₁ L := by
  have key : ∀ s t : ZMod 2, s + s + t + t = 0 := by decide
  ext v
  exact key _ _

/-- The wrapping map is surjective: `loopChain L a b` has wrapping numbers
`(a, b)`. -/
theorem phi_surjective : Function.Surjective (phi L) := fun ⟨a, b⟩ =>
  ⟨Submodule.Quotient.mk ⟨loopChain L a b, loopChain_mem_toricCycles L a b⟩,
    Prod.ext (by simp [phi_mk, hWrap, hAt, loopChain])
      (by simp [phi_mk, vWrap, vAt, loopChain])⟩

/-- The wrapping map is injective: it is a surjection between spaces of the
same dimension `2`. -/
theorem phi_injective : Function.Injective (phi L) :=
  (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (by rw [toric_finrank_H1_eq_two, Module.finrank_prod, Module.finrank_self])).2
    (phi_surjective L)

/-- The wrapping numbers classify the homology of the torus: the wrapping map
`phi L : H₁ L → (ZMod 2)²` is bijective. -/
theorem phi_bijective : Function.Bijective (phi L) :=
  ⟨phi_injective L, phi_surjective L⟩

/-- The wrapping map as a linear equivalence `H₁ ≃ (ZMod 2)²`. -/
noncomputable def phiEquiv : H₁ L ≃ₗ[ZMod 2] ZMod 2 × ZMod 2 :=
  LinearEquiv.ofBijective (phi L) (phi_bijective L)

/-- A cycle is a boundary iff both of its wrapping numbers vanish. -/
theorem mem_toricBoundaries_iff_wrap_eq_zero (c : Z₁ L) :
    c.1 ∈ B₁ L ↔ hWrap L c = 0 ∧ vWrap L c = 0 := by
  rw [← Prod.mk_eq_zero, ← phi_mk, map_eq_zero_iff _ (phi_injective L),
    Submodule.Quotient.mk_eq_zero]
  rfl

end Lattice
end Stabilizer
end Quantum
