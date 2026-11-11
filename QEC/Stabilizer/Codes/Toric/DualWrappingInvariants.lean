import QEC.Stabilizer.Codes.Toric.WrappingInvariants

/-!
# The dual toric complex and its wrapping numbers

The dual of the toric chain complex `C2 →∂₂ C1 →∂₁ C0` is the complex
`C0 →δ⁰ C1 →∂₂ᵀ C2` of the transposed maps:

* `toricDualBoundary L : C1 L →ₗ[ZMod 2] C2 L` is the transpose of `∂₂`: a face
  receives the sum of the values on the four edges around it;
* `toricDualCycles L` (notation `Z¹ L`) is its kernel, and
  `toricDualBoundaries L` (notation `B¹ L`) is the range of the vertex cut map
  `δ⁰`; `toricDualH1 L` is the quotient.

These are the dual complex of `toricHomologicalCode L`
(`toricHomologicalCode_dualBoundary_eq`, `toricHomologicalCode_dualCycles_eq`,
`toricHomologicalCode_dualBoundaries_eq`).

The dual lattice of the periodic square lattice is again a periodic square
lattice: every edge is crossed by exactly one edge of the dual lattice
(`edgeDual L`). Relabelling 1-chains along this bijection is a linear
equivalence `toricDuality L` that carries the chain complex to its dual:
`toricDualCycles_eq_map` and `toricDualBoundaries_eq_map`. It preserves the
weight of a chain (`edgeWeight_toricDuality`), so statements about dual cycles
follow from the statements about cycles.

In particular the wrapping numbers `hWrap` and `vWrap` of a cycle have dual
counterparts: the row parity `hRowAt L y c = ∑ x, c (EdgeIdx.h x y)` of the
horizontal edges and the column parity `vColAt L x c = ∑ y, c (EdgeIdx.v x y)`
of the vertical edges. On dual cycles they do not depend on the row or the
column, they vanish on dual boundaries, and they define a linear bijection
`phiDual L : toricDualH1 L →ₗ[ZMod 2] ZMod 2 × ZMod 2` (`phiDual_bijective`;
the linear equivalence is `phiDualEquiv L`): a dual cycle is a dual boundary
iff both parities vanish (`mem_toricDualBoundaries_iff_wrap_eq_zero`). The
chains `dualLoopChain L a b` realise all four values.
-/

namespace Quantum
namespace Stabilizer
namespace Lattice

open scoped Homology
open scoped ToricChain

variable (L : ℕ)

section Complex

variable [Fact (0 < L)]

/-! ## The dual complex -/

/-- The dual boundary map `C1 → C2`, the transpose of `∂₂`: a face receives the
sum of the values on the four edges around it. -/
def toricDualBoundary : C1 L →ₗ[ZMod 2] C2 L where
  toFun c :=
    fun p =>
      c (EdgeIdx.h p.1 p.2) + c (EdgeIdx.h p.1 (next L p.2)) +
      c (EdgeIdx.v p.1 p.2) + c (EdgeIdx.v (next L p.1) p.2)
  map_add' c d := by
    ext p
    simp only [Pi.add_apply]
    ring
  map_smul' a c := by
    ext p
    simp [mul_add]

lemma toricDualBoundary_apply (c : C1 L) (p : FaceIdx L) :
    toricDualBoundary L c p =
      c (EdgeIdx.h p.1 p.2) + c (EdgeIdx.h p.1 (next L p.2)) +
      c (EdgeIdx.v p.1 p.2) + c (EdgeIdx.v (next L p.1) p.2) := rfl

/-- The dual 1-cycles: the kernel of `toricDualBoundary`. -/
def toricDualCycles : Submodule (ZMod 2) (C1 L) :=
  LinearMap.ker (toricDualBoundary L)

/-- The dual 1-boundaries: the range of the vertex cut map `δ⁰`. -/
def toricDualBoundaries : Submodule (ZMod 2) (C1 L) :=
  LinearMap.range (δ⁰ L)

/-- `Z¹ L` is the toric dual 1-cycle submodule `toricDualCycles L`. Scoped:
`open scoped ToricChain`. -/
scoped[ToricChain] notation "Z¹" => Quantum.Stabilizer.Lattice.toricDualCycles

/-- `B¹ L` is the toric dual 1-boundary submodule `toricDualBoundaries L`.
Scoped: `open scoped ToricChain`. -/
scoped[ToricChain] notation "B¹" => Quantum.Stabilizer.Lattice.toricDualBoundaries

/-- Every dual boundary is a dual cycle: each of the four vertices of a face is
counted twice. -/
theorem toricDualBoundaries_le_toricDualCycles : B¹ L ≤ Z¹ L := by
  have key : ∀ a b c d : ZMod 2, a + b + (c + d) + (a + c) + (b + d) = 0 := by decide
  rintro _ ⟨s, rfl⟩
  ext p
  exact key _ _ _ _

/-- The dual first homology: dual cycles modulo dual boundaries. -/
abbrev toricDualH1 : Type :=
  Z¹ L ⧸ Submodule.comap (Z¹ L).subtype (B¹ L)

/-! ## The dual complex of `toricHomologicalCode` -/

/-- On indicator chains, `toricDualBoundary` is the transpose of `∂₂`: the
boundary of the face `p` at the edge `e` is the dual boundary of `e` at `p`. -/
private lemma toricBoundary2_single_apply (e : EdgeIdx L) (p : FaceIdx L) (a : ZMod 2) :
    a * ∂₂ L (Pi.single p 1) e = toricDualBoundary L (Pi.single e a) p := by
  cases e with
  | h x y =>
    rw [toricBoundary2_apply_h, toricDualBoundary_apply]
    simp [Pi.single_apply, mul_add, Prod.ext_iff, eq_comm]
  | v x y =>
    rw [toricBoundary2_apply_v, toricDualBoundary_apply]
    simp [Pi.single_apply, mul_add, Prod.ext_iff, eq_comm]

/-- The dual boundary map of `toricHomologicalCode L`, defined as the transpose
of `∂₂`, is `toricDualBoundary L`. -/
theorem toricHomologicalCode_dualBoundary_eq :
    (toricHomologicalCode L).dualBoundary = toricDualBoundary L := by
  refine LinearMap.pi_ext fun e a => funext fun p => ?_
  refine Eq.trans ?_ (toricBoundary2_single_apply L e p a)
  change ∑ e' : EdgeIdx L, (Pi.single e a : C1 L) e' * ∂₂ L (Pi.single p 1) e' = _
  simp [Pi.single_apply]

/-- The dual cycles of `toricHomologicalCode L` are `Z¹ L`. -/
theorem toricHomologicalCode_dualCycles_eq :
    (toricHomologicalCode L).dualCycles = Z¹ L :=
  congrArg LinearMap.ker (toricHomologicalCode_dualBoundary_eq L)

/-- The dual boundaries of `toricHomologicalCode L` are `B¹ L`. -/
theorem toricHomologicalCode_dualBoundaries_eq :
    (toricHomologicalCode L).dualBoundaries = B¹ L :=
  congrArg LinearMap.range (toricHomologicalCode_cutMap_eq L)

/-! ## Duality of the square lattice

The faces of the lattice are the vertices of the dual lattice, the face
`(x, y)` being the dual vertex `(x, y)`. The dual edge crossing a vertical
edge is then horizontal, the one crossing a horizontal edge is vertical, and
the vertex `(x, y)` is the dual face `(prev L x, prev L y)`. -/

/-- The edge of the dual lattice that crosses a given edge, in the coordinates
of the dual lattice: the horizontal edge `h x y` is crossed by the dual
vertical edge `v x (prev L y)`, and the vertical edge `v x y` by the dual
horizontal edge `h (prev L x) y`. -/
def edgeDual : EdgeIdx L ≃ EdgeIdx L where
  toFun
    | EdgeIdx.h x y => EdgeIdx.v x (prev L y)
    | EdgeIdx.v x y => EdgeIdx.h (prev L x) y
  invFun
    | EdgeIdx.h x y => EdgeIdx.v (next L x) y
    | EdgeIdx.v x y => EdgeIdx.h x (next L y)
  left_inv e := by cases e <;> simp
  right_inv e := by cases e <;> simp

/-- Duality on 1-chains: `toricDuality L c` is the chain `c` of the dual
lattice read on the edges of the lattice, its value on an edge being the value
of `c` on the dual edge crossing it. -/
def toricDuality : C1 L ≃ₗ[ZMod 2] C1 L :=
  LinearEquiv.funCongrLeft (ZMod 2) (ZMod 2) (edgeDual L)

lemma toricDuality_apply_h (c : C1 L) (x y : Fin L) :
    toricDuality L c (EdgeIdx.h x y) = c (EdgeIdx.v x (prev L y)) := rfl

lemma toricDuality_apply_v (c : C1 L) (x y : Fin L) :
    toricDuality L c (EdgeIdx.v x y) = c (EdgeIdx.h (prev L x) y) := rfl

/-- Duality turns `∂₁` into the dual boundary map: the dual boundary of
`toricDuality L c` at the face `p` is the boundary of `c` at the vertex `p`. -/
lemma toricDualBoundary_toricDuality (c : C1 L) :
    toricDualBoundary L (toricDuality L c) = ∂₁ L c := by
  ext p
  simp only [toricDualBoundary_apply, toricDuality_apply_h, toricDuality_apply_v, prev_next,
    toricBoundary1_apply]
  ring

/-- Duality turns `∂₂` into the vertex cut map, the vertex `p` being the dual
face `(prev L p.1, prev L p.2)`. -/
lemma toricDuality_toricBoundary2 (f : C2 L) :
    toricDuality L (∂₂ L f) = δ⁰ L fun p => f (prev L p.1, prev L p.2) := by
  ext e
  cases e with
  | h x y =>
    rw [toricDuality_apply_h, toricBoundary2_apply_v, toricVertexCutMap_apply_h, prev_next,
      add_comm]
  | v x y =>
    rw [toricDuality_apply_v, toricBoundary2_apply_h, toricVertexCutMap_apply_v, prev_next,
      add_comm]

variable {L} in
/-- `toricDuality L c` is a dual cycle iff `c` is a cycle. -/
lemma toricDuality_mem_toricDualCycles_iff {c : C1 L} :
    toricDuality L c ∈ Z¹ L ↔ c ∈ Z₁ L := by
  rw [toricDualCycles, LinearMap.mem_ker, toricDualBoundary_toricDuality]
  rfl

variable {L} in
/-- `toricDuality L c` is a dual boundary iff `c` is a boundary. -/
lemma toricDuality_mem_toricDualBoundaries_iff {c : C1 L} :
    toricDuality L c ∈ B¹ L ↔ c ∈ B₁ L := by
  constructor
  · rintro ⟨s, hs⟩
    refine ⟨fun p => s (next L p.1, next L p.2), (toricDuality L).injective ?_⟩
    simp only [← hs, toricDuality_toricBoundary2, next_prev]
  · rintro ⟨f, rfl⟩
    exact ⟨_, (toricDuality_toricBoundary2 L f).symm⟩

/-- The dual cycles are the image of the cycles under duality. -/
theorem toricDualCycles_eq_map :
    Z¹ L = (Z₁ L).map (toricDuality L : C1 L →ₗ[ZMod 2] C1 L) := by
  ext c
  rw [Submodule.mem_map_equiv, ← toricDuality_mem_toricDualCycles_iff,
    LinearEquiv.apply_symm_apply]

/-- The dual boundaries are the image of the boundaries under duality. -/
theorem toricDualBoundaries_eq_map :
    B¹ L = (B₁ L).map (toricDuality L : C1 L →ₗ[ZMod 2] C1 L) := by
  ext c
  rw [Submodule.mem_map_equiv, ← toricDuality_mem_toricDualBoundaries_iff,
    LinearEquiv.apply_symm_apply]

/-- Duality preserves the weight of a chain. -/
lemma edgeWeight_toricDuality (c : C1 L) :
    edgeWeight (toricDuality L c) = edgeWeight c :=
  Finset.card_equiv (edgeDual L) fun e => by
    simp only [mem_edgeSupport]
    rfl

/-- The dual cycle space has dimension `L² + 1`. -/
theorem toric_finrank_dualCycles : dim₂ (Z¹ L) = L * L + 1 := by
  rw [toricDualCycles_eq_map, LinearEquiv.finrank_map_eq, toric_finrank_cycles]

/-- The dual boundary space has dimension `L² - 1`. -/
theorem toric_finrank_dualBoundaries : dim₂ (B¹ L) = L * L - 1 :=
  (toric_rank_boundary1_eq_rank_cutMap L).symm.trans (toric_rank_boundary1 L)

end Complex

/-! ## Row and column parities -/

/-- The parity of the horizontal edges of `c` in the row `y0`. -/
def hRowAt (y0 : Fin L) (c : C1 L) : ZMod 2 :=
  ∑ x : Fin L, c (EdgeIdx.h x y0)

/-- The parity of the vertical edges of `c` in the column `x0`. -/
def vColAt (x0 : Fin L) (c : C1 L) : ZMod 2 :=
  ∑ y : Fin L, c (EdgeIdx.v x0 y)

/-- `hRowAt L y0` as a linear map. -/
def hRowAtLinear (y0 : Fin L) : C1 L →ₗ[ZMod 2] ZMod 2 where
  toFun := hRowAt L y0
  map_add' c d := by simp [hRowAt, Finset.sum_add_distrib]
  map_smul' a c := by simp [hRowAt, Finset.mul_sum]

/-- `vColAt L x0` as a linear map. -/
def vColAtLinear (x0 : Fin L) : C1 L →ₗ[ZMod 2] ZMod 2 where
  toFun := vColAt L x0
  map_add' c d := by simp [vColAt, Finset.sum_add_distrib]
  map_smul' a c := by simp [vColAt, Finset.mul_sum]

variable [Fact (0 < L)]

/-- The row parity of `toricDuality L c` is a vertical-edge parity of `c`. -/
lemma hRowAt_toricDuality (y0 : Fin L) (c : C1 L) :
    hRowAt L y0 (toricDuality L c) = vAt L (prev L y0) c := rfl

/-- The column parity of `toricDuality L c` is a horizontal-edge parity of
`c`. -/
lemma vColAt_toricDuality (x0 : Fin L) (c : C1 L) :
    vColAt L x0 (toricDuality L c) = hAt L (prev L x0) c := rfl

/-- On a dual cycle, the row parity of the horizontal edges is the same in
every row. -/
theorem hRowAt_independent_on_dualCycles (c : Z¹ L) (y0 y1 : Fin L) :
    hRowAt L y0 c.1 = hRowAt L y1 c.1 := by
  obtain ⟨c, hc⟩ := c
  obtain ⟨c, rfl⟩ := (toricDuality L).surjective c
  exact vAt_independent_on_cycles L ⟨c, toricDuality_mem_toricDualCycles_iff.1 hc⟩ _ _

/-- On a dual cycle, the column parity of the vertical edges is the same in
every column. -/
theorem vColAt_independent_on_dualCycles (c : Z¹ L) (x0 x1 : Fin L) :
    vColAt L x0 c.1 = vColAt L x1 c.1 := by
  obtain ⟨c, hc⟩ := c
  obtain ⟨c, rfl⟩ := (toricDuality L).surjective c
  exact hAt_independent_on_cycles L ⟨c, toricDuality_mem_toricDualCycles_iff.1 hc⟩ _ _

/-- The cut of a 0-chain has even row parity in every row: each vertex of the
row meets it in two horizontal edges. -/
lemma hRowAt_toricVertexCutMap (y0 : Fin L) (s : C0 L) : hRowAt L y0 (δ⁰ L s) = 0 := by
  simp only [hRowAt, toricVertexCutMap_apply_h, Finset.sum_add_distrib]
  rw [sum_comp_next L fun x => s (x, y0)]
  exact CharTwo.add_self_eq_zero _

/-- The cut of a 0-chain has even column parity in every column. -/
lemma vColAt_toricVertexCutMap (x0 : Fin L) (s : C0 L) : vColAt L x0 (δ⁰ L s) = 0 := by
  simp only [vColAt, toricVertexCutMap_apply_v, Finset.sum_add_distrib]
  rw [sum_comp_next L fun y => s (x0, y)]
  exact CharTwo.add_self_eq_zero _

/-- The row parity vanishes on dual boundaries. -/
theorem hRowAt_dualBoundary_zero (b : B¹ L) : hRowAt L (zeroCoord L) b.1 = 0 := by
  obtain ⟨s, hs⟩ := b.2
  rw [← hs]
  exact hRowAt_toricVertexCutMap L _ s

/-- The column parity vanishes on dual boundaries. -/
theorem vColAt_dualBoundary_zero (b : B¹ L) : vColAt L (zeroCoord L) b.1 = 0 := by
  obtain ⟨s, hs⟩ := b.2
  rw [← hs]
  exact vColAt_toricVertexCutMap L _ s

/-- A dual cycle is a dual boundary iff its row parity and its column parity
vanish. -/
theorem mem_toricDualBoundaries_iff_wrap_eq_zero (c : Z¹ L) :
    c.1 ∈ B¹ L ↔ hRowAt L (zeroCoord L) c.1 = 0 ∧ vColAt L (zeroCoord L) c.1 = 0 := by
  obtain ⟨c, hc⟩ := c
  obtain ⟨c, rfl⟩ := (toricDuality L).surjective c
  have hc' : c ∈ Z₁ L := toricDuality_mem_toricDualCycles_iff.1 hc
  rw [toricDuality_mem_toricDualBoundaries_iff, mem_toricBoundaries_iff_wrap_eq_zero L ⟨c, hc'⟩,
    and_comm, hRowAt_toricDuality, vColAt_toricDuality,
    vAt_independent_on_cycles L ⟨c, hc'⟩ _ (zeroCoord L),
    hAt_independent_on_cycles L ⟨c, hc'⟩ _ (zeroCoord L)]
  rfl

/-! ## The dual wrapping map -/

/-- The dual wrapping map `toricDualH1 L → (ZMod 2)²`, sending the class of a
dual cycle `c` to its row and column parities. -/
noncomputable def phiDual : toricDualH1 L →ₗ[ZMod 2] ZMod 2 × ZMod 2 :=
  Submodule.liftQ _
    (((hRowAtLinear L (zeroCoord L)).prod (vColAtLinear L (zeroCoord L))).comp (Z¹ L).subtype)
    fun c hc => Prod.ext (hRowAt_dualBoundary_zero L ⟨c.1, hc⟩)
      (vColAt_dualBoundary_zero L ⟨c.1, hc⟩)

/-- `phiDual` on the class of a dual cycle. -/
theorem phiDual_mk (c : Z¹ L) :
    phiDual L (Submodule.Quotient.mk c) =
      (hRowAt L (zeroCoord L) c.1, vColAt L (zeroCoord L) c.1) := rfl

/-- The 1-chain that is `a` on the horizontal edges of the column `zeroCoord L`
and `b` on the vertical edges of the row `zeroCoord L`: the image of
`loopChain L b a` under duality. -/
def dualLoopChain (a b : ZMod 2) : C1 L
  | EdgeIdx.h x _ => if x = zeroCoord L then a else 0
  | EdgeIdx.v _ y => if y = zeroCoord L then b else 0

lemma toricDuality_loopChain (a b : ZMod 2) :
    toricDuality L (loopChain L a b) = dualLoopChain L b a := by
  funext e
  cases e <;> rfl

/-- `dualLoopChain L a b` is a dual cycle. -/
lemma dualLoopChain_mem_toricDualCycles (a b : ZMod 2) : dualLoopChain L a b ∈ Z¹ L := by
  rw [← toricDuality_loopChain]
  exact toricDuality_mem_toricDualCycles_iff.2 (loopChain_mem_toricCycles L b a)

/-- The dual wrapping map is surjective: `dualLoopChain L a b` has parities
`(a, b)`. -/
theorem phiDual_surjective : Function.Surjective (phiDual L) := fun ⟨a, b⟩ =>
  ⟨Submodule.Quotient.mk ⟨dualLoopChain L a b, dualLoopChain_mem_toricDualCycles L a b⟩,
    Prod.ext (by simp [phiDual_mk, hRowAt, dualLoopChain])
      (by simp [phiDual_mk, vColAt, dualLoopChain])⟩

/-- The dual wrapping map is injective: a dual cycle with vanishing parities is
a dual boundary. -/
theorem phiDual_injective : Function.Injective (phiDual L) := by
  refine (injective_iff_map_eq_zero _).2 fun q hq => ?_
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  rw [phiDual_mk, Prod.mk_eq_zero] at hq
  exact (Submodule.Quotient.mk_eq_zero _).2 ((mem_toricDualBoundaries_iff_wrap_eq_zero L c).2 hq)

/-- The row and column parities classify the dual homology of the torus: the
dual wrapping map `phiDual L : toricDualH1 L → (ZMod 2)²` is bijective. -/
theorem phiDual_bijective : Function.Bijective (phiDual L) :=
  ⟨phiDual_injective L, phiDual_surjective L⟩

/-- The dual wrapping map as a linear equivalence. -/
noncomputable def phiDualEquiv : toricDualH1 L ≃ₗ[ZMod 2] ZMod 2 × ZMod 2 :=
  LinearEquiv.ofBijective (phiDual L) (phiDual_bijective L)

end Lattice
end Stabilizer
end Quantum
