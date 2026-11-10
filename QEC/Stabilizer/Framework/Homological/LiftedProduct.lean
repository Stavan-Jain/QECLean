import QEC.Stabilizer.Framework.Homological.Distance

/-!
# Non-abelian lifted product as a `HomologicalCode`

The 1×2 lifted product over the group algebra `𝔽₂[G]` of a finite, possibly
non-abelian group `G`: base rows `A = [a₀ a₁]`, `B = [b₀ b₁]`, five qubit
blocks (a 2×2 grid and one shared block), two X-check blocks and two Z-check
blocks, with check matrices

```
H_X = [ L(a₀)   0     L(a₁)   0     R(b₀*) ]
      [  0     L(a₀)   0     L(a₁)  R(b₁*) ]

H_Z = [ R(b₀)  R(b₁)   0      0     L(a₀*) ]
      [  0      0     R(b₀)  R(b₁)  L(a₁*) ]
```

where `L`/`R` are left/right regular-representation sums and `*` is the
antipode `g ↦ g⁻¹`. The chain-complex law is left/right commutation: left and
right convolution commute because group multiplication is associative
(`rconv_lconv`), and the two occurrences of each mixed term cancel in
characteristic 2.

This file provides:

* `lconv a f`, `rconv f b`: the one-sided convolutions on `G → ZMod 2`, and
  `antipode`;
* `rconv_lconv`: left and right convolution commute;
* `lpBoundary1`, `lpBoundary2`: the boundary maps, with X-checks
  `C2 = Fin 2 × G`, qubits `C1 = Fin 5 × G` and Z-checks `C0 = Fin 2 × G`; the
  grid block `m < 4` is `(α, β) = (blockRow m, blockCol m)`;
* `mittenChainComplex A B : HomologicalCode`: the packaged complex.
-/

namespace Quantum
namespace Stabilizer
namespace Homological
namespace LP

open scoped BigOperators

variable {G : Type} [Fintype G] [Group G]

/-! ## One-sided convolutions and the antipode -/

/-- Left convolution: `(a ⋆ₗ f) y = ∑ h, a h · f (h⁻¹ y)` — the action of
the left regular-representation sum `L(a)` on chains. -/
def lconv (a f : G → ZMod 2) : G → ZMod 2 :=
  fun y => ∑ h : G, a h * f (h⁻¹ * y)

/-- Right convolution: `(f ⋆ᵣ b) y = ∑ h, f (y h⁻¹) · b h` — the action of
the right-translate sum (matrix `R(b*)`) on chains. -/
def rconv (f b : G → ZMod 2) : G → ZMod 2 :=
  fun y => ∑ h : G, f (y * h⁻¹) * b h

/-- The antipode `a* g = a g⁻¹`. -/
def antipode (a : G → ZMod 2) : G → ZMod 2 := fun g => a g⁻¹

/-- Left convolution evaluated at a group element. -/
@[simp] lemma lconv_apply (a f : G → ZMod 2) (y : G) :
    lconv a f y = ∑ h : G, a h * f (h⁻¹ * y) := rfl

/-- Right convolution evaluated at a group element. -/
@[simp] lemma rconv_apply (f b : G → ZMod 2) (y : G) :
    rconv f b y = ∑ h : G, f (y * h⁻¹) * b h := rfl

omit [Fintype G] in
/-- The antipode evaluates a coefficient at the inverse element. -/
@[simp] lemma antipode_apply (a : G → ZMod 2) (g : G) :
    antipode a g = a g⁻¹ := rfl

/-- Left and right convolution commute, by associativity of the group
multiplication. This is what makes the lifted product a chain complex. -/
lemma rconv_lconv (a f b : G → ZMod 2) :
    rconv (lconv a f) b = lconv a (rconv f b) := by
  funext y
  simp only [lconv, rconv, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun h _ => Finset.sum_congr rfl fun k _ => ?_
  rw [mul_assoc (a h) _ (b k), mul_assoc h⁻¹ y k⁻¹]

/-- `lconv` is additive in the chain argument. -/
lemma lconv_add (a f₁ f₂ : G → ZMod 2) :
    lconv a (f₁ + f₂) = lconv a f₁ + lconv a f₂ := by
  funext y
  simp only [lconv_apply, Pi.add_apply, mul_add, Finset.sum_add_distrib]

/-- `rconv` is additive in the chain argument. -/
lemma rconv_add (f₁ f₂ b : G → ZMod 2) :
    rconv (f₁ + f₂) b = rconv f₁ b + rconv f₂ b := by
  funext y
  simp only [rconv_apply, Pi.add_apply, add_mul, Finset.sum_add_distrib]

/-- `lconv` commutes with scalars in the chain argument. -/
lemma lconv_smul (s : ZMod 2) (a f : G → ZMod 2) :
    lconv a (s • f) = s • lconv a f := by
  funext y
  simp only [lconv_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun h _ => ?_
  ring

/-- `rconv` commutes with scalars in the chain argument. -/
lemma rconv_smul (s : ZMod 2) (f b : G → ZMod 2) :
    rconv (s • f) b = s • rconv f b := by
  funext y
  simp only [rconv_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun h _ => ?_
  ring

/-! The same lemmas with the sum or scalar multiple written pointwise, the
form that the block restrictions `fun g => f (m, g)` of a sum take after
`Pi.add_apply` / `Pi.smul_apply`. -/

/-- Left convolution distributes over pointwise addition. -/
lemma lconv_add' (a f₁ f₂ : G → ZMod 2) :
    lconv a (fun g => f₁ g + f₂ g) = lconv a f₁ + lconv a f₂ :=
  lconv_add a f₁ f₂

/-- Right convolution distributes over pointwise addition. -/
lemma rconv_add' (f₁ f₂ b : G → ZMod 2) :
    rconv (fun g => f₁ g + f₂ g) b = rconv f₁ b + rconv f₂ b :=
  rconv_add f₁ f₂ b

/-- Left convolution commutes with pointwise scalar multiplication. -/
lemma lconv_smul' (s : ZMod 2) (a f : G → ZMod 2) :
    lconv a (fun g => s * f g) = s • lconv a f :=
  lconv_smul s a f

/-- Right convolution commutes with pointwise scalar multiplication. -/
lemma rconv_smul' (s : ZMod 2) (f b : G → ZMod 2) :
    rconv (fun g => s * f g) b = s • rconv f b :=
  rconv_smul s f b

section PointMass
variable [DecidableEq G]

/-- Left convolution with a point mass is a translated coefficient. -/
lemma lconv_delta (a : G → ZMod 2) (c x : G) :
    lconv a (fun g => if g = c then 1 else 0) x = a (x * c⁻¹) := by
  simp only [lconv_apply, mul_ite, mul_one, mul_zero, inv_mul_eq_iff_eq_mul,
    ← mul_inv_eq_iff_eq_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

/-- Right convolution of a point mass is a translated coefficient. -/
lemma rconv_delta (b : G → ZMod 2) (c x : G) :
    rconv (fun g => if g = c then 1 else 0) b x = b (c⁻¹ * x) := by
  simp only [rconv_apply, ite_mul, one_mul, zero_mul, mul_inv_eq_iff_eq_mul,
    ← inv_mul_eq_iff_eq_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

end PointMass

/-! ## Boundary maps

Cells: `C2 = Fin 2 × G` (X-checks), `C1 = Fin 5 × G` (qubits: the grid
blocks `m < 4` carry `(α, β) = (blockRow m, blockCol m)`, block `4` is
the shared block), `C0 = Fin 2 × G` (Z-checks). -/

variable (A B : Fin 2 → G → ZMod 2)

/-- Grid-block index `(α, β) ↦ 2α + β`. -/
def gridIdx (α β : Fin 2) : Fin 5 := ⟨2 * α.val + β.val, by omega⟩

/-- The shared (fifth) block. -/
def sharedIdx : Fin 5 := ⟨4, by omega⟩

/-- Row `α` of a grid block. The value at the shared block is not used. -/
def blockRow (m : Fin 5) : Fin 2 := if m.val < 2 then 0 else 1

/-- Column `β` of a grid block. The value at the shared block is not used. -/
def blockCol (m : Fin 5) : Fin 2 := if m.val % 2 = 0 then 0 else 1

omit [Fintype G] [Group G] in
/-- The row of a grid index is its first coordinate. -/
@[simp] lemma blockRow_grid (α β : Fin 2) : blockRow (gridIdx α β) = α := by
  revert α β
  decide

omit [Fintype G] [Group G] in
/-- The column of a grid index is its second coordinate. -/
@[simp] lemma blockCol_grid (α β : Fin 2) : blockCol (gridIdx α β) = β := by
  revert α β
  decide

/-- Underlying function of `∂₂` (columns of `H_X`): grid block `(α, β)`
receives `L(a_α*)` of the `β`-th X-check chain; the shared block receives
the `R(b_β*)` of both X-check chains. -/
def lpBoundary2Fn (f : Fin 2 × G → ZMod 2) : Fin 5 × G → ZMod 2 :=
  fun q =>
    if q.1.val = 4 then
      rconv (fun g => f (0, g)) (antipode (B 0)) q.2
        + rconv (fun g => f (1, g)) (antipode (B 1)) q.2
    else
      lconv (antipode (A (blockRow q.1))) (fun g => f (blockCol q.1, g)) q.2

/-- Underlying function of `∂₁` (rows of `H_Z`): Z-check block `α` reads
its two grid blocks through `R(b_β)` and the shared block through
`L(a_α*)`. -/
def lpBoundary1Fn (u : Fin 5 × G → ZMod 2) : Fin 2 × G → ZMod 2 :=
  fun p =>
    rconv (fun g => u (gridIdx p.1 0, g)) (antipode (B 0)) p.2
      + rconv (fun g => u (gridIdx p.1 1, g)) (antipode (B 1)) p.2
      + lconv (antipode (A p.1)) (fun g => u (sharedIdx, g)) p.2

omit [Fintype G] [Group G] in
/-- A grid index is distinct from the shared block. -/
lemma gridIdx_val_ne_four (α β : Fin 2) : ¬((gridIdx α β).val = 4) := by
  revert α β
  decide

/-- `∂₂` evaluated on a grid block. -/
lemma lpBoundary2Fn_grid (f : Fin 2 × G → ZMod 2) (α β : Fin 2) (x : G) :
    lpBoundary2Fn A B f (gridIdx α β, x)
      = lconv (antipode (A α)) (fun g => f (β, g)) x := by
  simp only [lpBoundary2Fn, if_neg (gridIdx_val_ne_four α β), blockRow_grid,
    blockCol_grid]

/-- `∂₂` evaluated on the shared block. -/
lemma lpBoundary2Fn_shared (f : Fin 2 × G → ZMod 2) (x : G) :
    lpBoundary2Fn A B f (sharedIdx, x)
      = rconv (fun g => f (0, g)) (antipode (B 0)) x
          + rconv (fun g => f (1, g)) (antipode (B 1)) x := rfl

/-- The chain-complex law on the underlying functions: `∂₁ (∂₂ f) = 0`. Each
mixed term `L(a_α*) ∘ R(b_β*)` arises once through grid block `(α, β)` and once
through the shared block; `rconv_lconv` aligns the two and characteristic 2
cancels them. -/
lemma lpBoundaryFn_comp (f : Fin 2 × G → ZMod 2) :
    lpBoundary1Fn A B (lpBoundary2Fn A B f) = 0 := by
  funext p
  obtain ⟨α, y⟩ := p
  have hgrid : ∀ β, (fun g => lpBoundary2Fn A B f (gridIdx α β, g))
      = lconv (antipode (A α)) (fun g => f (β, g)) :=
    fun β => funext fun g => lpBoundary2Fn_grid A B f α β g
  have hshared : (fun g => lpBoundary2Fn A B f (sharedIdx, g))
      = rconv (fun g => f (0, g)) (antipode (B 0))
          + rconv (fun g => f (1, g)) (antipode (B 1)) := rfl
  simp only [lpBoundary1Fn, hgrid, hshared, lconv_add, rconv_lconv, Pi.add_apply,
    Pi.zero_apply]
  exact CharTwo.add_self_eq_zero _

/-- `∂₂` as a `ZMod 2`-linear map. -/
noncomputable def lpBoundary2 :
    (Fin 2 × G → ZMod 2) →ₗ[ZMod 2] (Fin 5 × G → ZMod 2) where
  toFun := lpBoundary2Fn A B
  map_add' f₁ f₂ := by
    ext ⟨m, x⟩
    simp only [lpBoundary2Fn, Pi.add_apply]
    split
    · simp only [rconv_add', Pi.add_apply]
      ring
    · simp only [lconv_add', Pi.add_apply]
  map_smul' s f := by
    ext ⟨m, x⟩
    simp only [lpBoundary2Fn, RingHom.id_apply, Pi.smul_apply, smul_eq_mul]
    split
    · simp only [rconv_smul', Pi.smul_apply, smul_eq_mul]
      ring
    · simp only [lconv_smul', Pi.smul_apply, smul_eq_mul]

/-- `∂₁` as a `ZMod 2`-linear map. -/
noncomputable def lpBoundary1 :
    (Fin 5 × G → ZMod 2) →ₗ[ZMod 2] (Fin 2 × G → ZMod 2) where
  toFun := lpBoundary1Fn A B
  map_add' u₁ u₂ := by
    ext ⟨α, y⟩
    simp only [lpBoundary1Fn, Pi.add_apply, rconv_add', lconv_add']
    ring
  map_smul' s u := by
    ext ⟨α, y⟩
    simp only [lpBoundary1Fn, RingHom.id_apply, Pi.smul_apply, smul_eq_mul,
      rconv_smul', lconv_smul']
    ring

/-- The linear map `∂₂` applies its underlying function. -/
@[simp] lemma lpBoundary2_apply (f : Fin 2 × G → ZMod 2) :
    lpBoundary2 A B f = lpBoundary2Fn A B f := rfl

/-- The linear map `∂₁` applies its underlying function. -/
@[simp] lemma lpBoundary1_apply (u : Fin 5 × G → ZMod 2) :
    lpBoundary1 A B u = lpBoundary1Fn A B u := rfl

/-- The chain-complex law `∂₁ ∘ ∂₂ = 0`. -/
lemma lpBoundary_comp : (lpBoundary1 A B).comp (lpBoundary2 A B) = 0 :=
  LinearMap.ext (lpBoundaryFn_comp A B)

/-! ## Packaging as a `HomologicalCode` -/

/-- Number of qubits: `5 · |G|`. -/
def lpNumQubits (G : Type) [Fintype G] : ℕ := 5 * Fintype.card G

omit [Group G] in
/-- The qubit-cell cardinality is five times the group cardinality. -/
lemma lpCard_C1 : Fintype.card (Fin 5 × G) = lpNumQubits G := by
  rw [lpNumQubits, Fintype.card_prod, Fintype.card_fin]

/-- A numbering of the qubit cells by `Fin (5 |G|)`. -/
noncomputable def lpEdgeEquiv : (Fin 5 × G) ≃ Fin (lpNumQubits G) :=
  ((Equiv.refl (Fin 5)).prodCongr (Fintype.equivFin G)).trans
    (finProdFinEquiv.trans (finCongr rfl))

/-- The 1×2 non-abelian lifted product as a `HomologicalCode`: `n = 5|G|`
qubits, X-checks `Fin 2 × G`, Z-checks `Fin 2 × G`, boundary maps
`lpBoundary1` and `lpBoundary2`. -/
noncomputable def mittenChainComplex [DecidableEq G] (A B : Fin 2 → G → ZMod 2) :
    HomologicalCode where
  C0 := Fin 2 × G
  C1 := Fin 5 × G
  C2 := Fin 2 × G
  decEq0 := inferInstance
  decEq1 := inferInstance
  decEq2 := inferInstance
  fin0 := inferInstance
  fin1 := inferInstance
  fin2 := inferInstance
  boundary1 := lpBoundary1 A B
  boundary2 := lpBoundary2 A B
  boundary_comp := lpBoundary_comp A B
  numQubits := lpNumQubits G
  numQubits_eq := lpCard_C1
  edgeEquiv := lpEdgeEquiv

end LP
end Homological
end Stabilizer
end Quantum
