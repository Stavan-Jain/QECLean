/-
# BB Chain Complex (Bivariate Bicycle CSS code) as a `HomologicalCode`

Given polynomial coefficient functions
`A B : (ZMod ℓ × ZMod m) → ZMod 2` representing elements of
`F_2[Z_ℓ × Z_m]`, we construct the length-3 chain complex underlying
the CSS code with check matrices

  H_X = [A | B]      (X-checks; matrix indexed by face-group entries × qubits)
  H_Z = [B^T | A^T]  (Z-checks; transposed)

In our convolution convention (defined below), the resulting code's
Z-checks are *reflected* compared to the literal transpose
(`b(g-h)` instead of `b(h-g)`).  Since the BB code is invariant under
the relabeling `g ↦ -g` on the group, this gives the same code up to
qubit relabeling — i.e. same parameters `(n, k, d)`.

The chain-complex law `∂₁ ∘ ∂₂ = 0` reduces to commutativity of
convolution on the abelian group `Z_ℓ × Z_m` combined with `char F_2 = 2`:
in char 2, `(a * b) + (b * a) = 2(a * b) = 0`.  Clean, no
transpose-juggling.

## What this file provides

* `conv (a b : G → ZMod 2) : G → ZMod 2` — convolution on abelian `G`
* `conv_comm`, `conv_assoc` — algebraic properties
* `bbBoundary1`, `bbBoundary2` — concrete boundary maps
* `bbChainComplex ℓ m A B : HomologicalCode` — the CSS chain complex
-/

import QEC.Stabilizer.Framework.Homological.Distance

namespace Quantum
namespace Stabilizer
namespace Homological
namespace BB

open scoped BigOperators

/-! ## Convolution on a finite abelian group

We work over `G = ZMod ℓ × ZMod m`, but for generality the convolution
definition only needs `G` to be a `Fintype` with `Sub`. -/

variable {G : Type} [Fintype G] [AddCommGroup G]

/-- Convolution of two `ZMod 2`-valued functions on a finite group `G`:
`(a * b)(g) = ∑_h a(h) · b(g - h)`. -/
def conv (a b : G → ZMod 2) : G → ZMod 2 :=
  fun g => ∑ h : G, a h * b (g - h)

@[simp] lemma conv_apply (a b : G → ZMod 2) (g : G) :
    conv a b g = ∑ h : G, a h * b (g - h) := rfl

/-- Convolution is commutative on an abelian group. -/
lemma conv_comm (a b : G → ZMod 2) : conv a b = conv b a := by
  funext g
  simp only [conv_apply]
  -- ∑_h a h * b (g - h) = ∑_h b h * a (g - h)
  -- reindex via h ↦ g - h
  refine Finset.sum_bij' (fun h _ => g - h) (fun h _ => g - h)
    (fun h _ => Finset.mem_univ _) (fun h _ => Finset.mem_univ _)
    ?_ ?_ ?_
  · intro h _; simp
  · intro h _; simp
  · intro h _
    have : g - (g - h) = h := by simp
    rw [this, mul_comm]

/-- Convolution is associative. -/
lemma conv_assoc (a b c : G → ZMod 2) : conv (conv a b) c = conv a (conv b c) := by
  funext g
  -- We'll show both sides equal `∑_h ∑_k, a h * b k * c (g - h - k)`.
  -- LHS = ∑_h (conv a b) h * c (g - h) = ∑_h (∑_k a k * b (h - k)) * c (g - h)
  -- Reindex inner sum k ↦ h - k' so that the argument of b becomes k', and
  -- of a becomes h - k'.  Then renaming the outer variable to h_new = h - k'
  -- to align with RHS.  Cleanest: reindex jointly via the bijection
  -- (h, k) ↦ (h - k, k) on G × G.
  have lhs_expand :
      conv (conv a b) c g = ∑ h : G, ∑ k : G, a h * b k * c (g - h - k) := by
    simp only [conv_apply, Finset.sum_mul]
    -- LHS now: ∑ h, ∑ k, (a k * b (h - k)) * c (g - h)
    -- Goal: ∑ h, ∑ k, a h * b k * c (g - h - k)
    -- Reindex per outer h by k' = h - k, so a k = a (h - k'), b (h - k) = b k'
    -- Then swap outer/inner via sum_comm.
    rw [Finset.sum_comm]
    -- ∑ k, ∑ h, (a k * b (h - k)) * c (g - h)
    -- Now reindex inner h ↦ h + k:  (h - k) ↦ h, (g - h) ↦ g - h - k
    have step : ∀ k : G, (∑ h : G, a k * b (h - k) * c (g - h)) =
        ∑ h : G, a k * b h * c (g - k - h) := by
      intro k
      refine Finset.sum_bij' (fun h _ => h - k) (fun h _ => h + k)
        (fun _ _ => Finset.mem_univ _) (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_
      · intro h _
        change h - k + k = h
        abel
      · intro h _
        change h + k - k = h
        abel
      · intro h _
        have h1 : g - h = g - k - (h - k) := by abel
        rw [h1]
    rw [Finset.sum_congr rfl (fun k _ => step k)]
  have rhs_expand :
      conv a (conv b c) g = ∑ h : G, ∑ k : G, a h * b k * c (g - h - k) := by
    simp only [conv_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun h _ => ?_)
    refine Finset.sum_congr rfl (fun k _ => ?_)
    have : (g - h) - k = g - h - k := by abel
    rw [← this]
    ring
  rw [lhs_expand, rhs_expand]

/-- Convolution distributes over addition (left). -/
lemma conv_add_left (a b c : G → ZMod 2) :
    conv (a + b) c = conv a c + conv b c := by
  funext g
  simp only [conv_apply, Pi.add_apply, add_mul, Finset.sum_add_distrib]

/-- Convolution distributes over addition (right). -/
lemma conv_add_right (a b c : G → ZMod 2) :
    conv a (b + c) = conv a b + conv a c := by
  funext g
  simp only [conv_apply, Pi.add_apply, mul_add, Finset.sum_add_distrib]

/-- Convolution scales (left). -/
lemma conv_smul_left (s : ZMod 2) (a b : G → ZMod 2) :
    conv (s • a) b = s • conv a b := by
  funext g
  simp only [conv_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

/-- Convolution scales (right). -/
lemma conv_smul_right (s : ZMod 2) (a b : G → ZMod 2) :
    conv a (s • b) = s • conv a b := by
  funext g
  simp only [conv_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  congr 1; funext h
  ring

/-- In char 2, for any commuting `a, b`, `conv a b + conv b a = 0`.
By commutativity of `conv`, this is just `2 (conv a b) = 0`. -/
lemma conv_add_swap_eq_zero (a b : G → ZMod 2) :
    conv a b + conv b a = 0 := by
  rw [conv_comm a b]
  ext g
  simp [Pi.add_apply, CharTwo.add_self_eq_zero]

/-- Convolving with a point mass on the left translates: `δ_a ⋆ b = b (· - a)`. -/
lemma conv_single_left [DecidableEq G] (a : G) (b : G → ZMod 2) :
    conv (Pi.single a 1) b = fun g => b (g - a) := by
  funext g
  rw [conv_apply, Finset.sum_eq_single a]
  · simp
  · intro h _ hne
    rw [Pi.single_eq_of_ne hne, zero_mul]
  · intro habs
    exact absurd (Finset.mem_univ a) habs

/-- Pointwise form of `conv_single_left` (avoids beta-redex residue when
rewriting at an applied occurrence). -/
@[simp] lemma conv_single_left_apply [DecidableEq G] (a : G) (b : G → ZMod 2)
    (g : G) :
    conv (Pi.single a 1) b g = b (g - a) := by
  rw [conv_single_left]

/-! ## Boundary maps for BB chain complex

Cells:
* `C0 := G` (Z-stabilizer positions = "vertices")
* `C1 := G × Fin 2` (qubits, indexed by group element and L/R block)
* `C2 := G` (X-stabilizer positions = "faces")

Boundary maps:
* `∂₂(f) (h, 0) := conv A f h`,  `∂₂(f) (h, 1) := conv B f h`
* `∂₁(c) (g)    := conv B c_L g + conv A c_R g`
  where `c_L h = c (h, 0)`, `c_R h = c (h, 1)`.

Then `∂₁ ∘ ∂₂ = 0` reduces to `conv B (conv A f) + conv A (conv B f) = 0`
via `conv_assoc` and `conv_add_swap_eq_zero` (char 2 + commutativity). -/

variable (A B : G → ZMod 2)

/-- The "left half" of a 1-chain. -/
def leftHalf (c : G × Fin 2 → ZMod 2) : G → ZMod 2 := fun g => c (g, 0)

/-- The "right half" of a 1-chain. -/
def rightHalf (c : G × Fin 2 → ZMod 2) : G → ZMod 2 := fun g => c (g, 1)

/-- Underlying function of `∂₂`. -/
def bbBoundary2Fn (f : G → ZMod 2) : G × Fin 2 → ZMod 2 :=
  fun ⟨h, j⟩ => if j = 0 then conv A f h else conv B f h

/-- Underlying function of `∂₁`. -/
def bbBoundary1Fn (c : G × Fin 2 → ZMod 2) : G → ZMod 2 :=
  fun g => conv B (leftHalf c) g + conv A (rightHalf c) g

/-- `∂₂` as a `ZMod 2`-linear map. -/
noncomputable def bbBoundary2 :
    (G → ZMod 2) →ₗ[ZMod 2] (G × Fin 2 → ZMod 2) where
  toFun := bbBoundary2Fn A B
  map_add' f₁ f₂ := by
    ext ⟨h, j⟩
    have key : ∀ (p : G → ZMod 2),
        (∑ x : G, p x * ((f₁ + f₂) (h - x))) =
          (∑ x : G, p x * f₁ (h - x)) + (∑ x : G, p x * f₂ (h - x)) := by
      intro p
      simp [Pi.add_apply, mul_add, Finset.sum_add_distrib]
    by_cases hj : j = 0
    · simp only [bbBoundary2Fn, hj, if_true, Pi.add_apply, conv_apply]
      exact key A
    · simp only [bbBoundary2Fn, hj, if_false, Pi.add_apply, conv_apply]
      exact key B
  map_smul' s f := by
    ext ⟨h, j⟩
    have key : ∀ (p : G → ZMod 2),
        (∑ x : G, p x * ((s • f) (h - x))) = s * (∑ x : G, p x * f (h - x)) := by
      intro p
      simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun x _ => ?_); ring
    by_cases hj : j = 0
    · simp only [bbBoundary2Fn, hj, if_true, RingHom.id_apply, Pi.smul_apply,
        smul_eq_mul, conv_apply]
      exact key A
    · simp only [bbBoundary2Fn, hj, if_false, RingHom.id_apply, Pi.smul_apply,
        smul_eq_mul, conv_apply]
      exact key B

/-- `∂₁` as a `ZMod 2`-linear map. -/
noncomputable def bbBoundary1 :
    (G × Fin 2 → ZMod 2) →ₗ[ZMod 2] (G → ZMod 2) where
  toFun := bbBoundary1Fn A B
  map_add' c₁ c₂ := by
    ext g
    -- Goal: bbBoundary1Fn A B (c₁ + c₂) g = bbBoundary1Fn A B c₁ g + bbBoundary1Fn A B c₂ g
    -- Both sides expand via `conv` definition; reduces to ring arithmetic
    -- in `ZMod 2` after splitting sums.
    simp only [bbBoundary1Fn, leftHalf, rightHalf, conv_apply, Pi.add_apply]
    -- Now goal is a `(∑ + ∑) = (∑ + ∑) + (∑ + ∑)` shape — split sums.
    have hL : ∀ p : G → ZMod 2,
        (∑ h : G, p h * (c₁ (g - h, 0) + c₂ (g - h, 0))) =
        (∑ h : G, p h * c₁ (g - h, 0)) + (∑ h : G, p h * c₂ (g - h, 0)) := by
      intro p
      simp [mul_add, Finset.sum_add_distrib]
    have hR : ∀ p : G → ZMod 2,
        (∑ h : G, p h * (c₁ (g - h, 1) + c₂ (g - h, 1))) =
        (∑ h : G, p h * c₁ (g - h, 1)) + (∑ h : G, p h * c₂ (g - h, 1)) := by
      intro p
      simp [mul_add, Finset.sum_add_distrib]
    rw [hL B, hR A]
    ring
  map_smul' s c := by
    ext g
    simp only [bbBoundary1Fn, leftHalf, rightHalf, conv_apply, RingHom.id_apply,
      Pi.smul_apply, smul_eq_mul]
    have hL : (∑ h : G, B h * (s * c (g - h, 0))) =
        s * (∑ h : G, B h * c (g - h, 0)) := by
      simp only [Finset.mul_sum]; refine Finset.sum_congr rfl (fun x _ => ?_); ring
    have hR : (∑ h : G, A h * (s * c (g - h, 1))) =
        s * (∑ h : G, A h * c (g - h, 1)) := by
      simp only [Finset.mul_sum]; refine Finset.sum_congr rfl (fun x _ => ?_); ring
    rw [hL, hR]
    ring

/-- `rfl` bridge from the LinearMap `∂₂` to its computable underlying function. -/
@[simp] lemma bbBoundary2_apply (f : G → ZMod 2) :
    bbBoundary2 A B f = bbBoundary2Fn A B f := rfl

/-- `rfl` bridge from the LinearMap `∂₁` to its computable underlying function. -/
@[simp] lemma bbBoundary1_apply (c : G × Fin 2 → ZMod 2) :
    bbBoundary1 A B c = bbBoundary1Fn A B c := rfl

/-- The chain-complex law `∂₁ ∘ ∂₂ = 0`. -/
lemma bbBoundary_comp : (bbBoundary1 A B).comp (bbBoundary2 A B) = 0 := by
  refine LinearMap.ext (fun f => ?_)
  ext g
  simp only [LinearMap.comp_apply, LinearMap.zero_apply, Pi.zero_apply]
  change bbBoundary1Fn A B (bbBoundary2Fn A B f) g = 0
  unfold bbBoundary1Fn bbBoundary2Fn leftHalf rightHalf
  -- ∂₁(∂₂ f)(g) = conv B (h ↦ conv A f h) g + conv A (h ↦ conv B f h) g
  have hL : (fun h => (if (0 : Fin 2) = 0 then conv A f h else conv B f h)) =
      conv A f := by funext h; simp
  have hR : (fun h => (if (1 : Fin 2) = 0 then conv A f h else conv B f h)) =
      conv B f := by funext h; simp
  rw [hL, hR]
  -- Goal: conv B (conv A f) g + conv A (conv B f) g = 0
  -- Use conv_assoc (right-to-left) to fold: conv B (conv A f) = conv (conv B A) f
  rw [← conv_assoc B A f, ← conv_assoc A B f]
  -- Goal: conv (conv B A) f g + conv (conv A B) f g = 0
  rw [conv_comm B A]
  -- Goal: conv (conv A B) f g + conv (conv A B) f g = 0
  -- That's `x + x = 0` in `ZMod 2` (i.e. `char F_2 = 2`).
  exact CharTwo.add_self_eq_zero _

/-! ## Packaging as a `HomologicalCode`

Given `[Fintype G] [DecidableEq G] [AddCommGroup G]` and polynomials
`A, B : G → ZMod 2`, build the chain complex
`C0 = G,  C1 = G × Fin 2,  C2 = G`
with `bbBoundary1`, `bbBoundary2`. -/

variable [DecidableEq G]

/-- Number of qubits = `2 * Fintype.card G`. -/
def bbNumQubits (G : Type) [Fintype G] : ℕ := 2 * Fintype.card G

/-- Bijection between `G × Fin 2` and `Fin (bbNumQubits G)`. -/
noncomputable def bbEdgeEquiv :
    (G × Fin 2) ≃ Fin (bbNumQubits G) := by
  classical
  -- Use the equiv G × Fin 2 ≃ Fin (card G) × Fin 2 ≃ Fin (2 * card G)
  refine (((Fintype.equivFin G).prodCongr (Equiv.refl (Fin 2))).trans
    (finProdFinEquiv (m := Fintype.card G) (n := 2))).trans ?_
  -- Fin (card G * 2) → Fin (2 * card G)
  exact finCongr (by unfold bbNumQubits; ring)

omit [AddCommGroup G] [DecidableEq G] in
lemma bbCard_C1 :
    Fintype.card (G × Fin 2) = bbNumQubits G := by
  unfold bbNumQubits
  rw [Fintype.card_prod, Fintype.card_fin, mul_comm]

/-- The BB chain complex packaged as a `HomologicalCode`. -/
noncomputable def bbChainComplex (A B : G → ZMod 2) : HomologicalCode where
  C0 := G
  C1 := G × Fin 2
  C2 := G
  decEq0 := inferInstance
  decEq1 := inferInstance
  decEq2 := inferInstance
  fin0 := inferInstance
  fin1 := inferInstance
  fin2 := inferInstance
  boundary1 := bbBoundary1 A B
  boundary2 := bbBoundary2 A B
  boundary_comp := bbBoundary_comp A B
  numQubits := bbNumQubits G
  numQubits_eq := bbCard_C1
  edgeEquiv := bbEdgeEquiv

end BB
end Homological
end Stabilizer
end Quantum
