import QEC.Stabilizer.Framework.Homological.BBChainComplex

/-!
# Pushforward and pullback of `ZMod 2`-chains along a covering

Transfer of chains along a map of index types, in four layers.

1. **Fiber summation.** `fiberSumFn f u` is the pushforward
   `(f_* u) j = ∑ i ∈ f⁻¹ j, u i` of a chain along an arbitrary map
   `f : I → J` of finite types; `fiberSum f` is the same as a linear map. It is
   the transpose of the pullback `u ↦ u ∘ f` (`sum_fiberSumFn_mul`).
2. **Convolution.** Along an additive homomorphism `π : G →+ H` the pushforward
   is multiplicative (`fiberSum_conv`), and convolution against a pulled-back
   chain is the pullback of a convolution (`conv_pullback`). Neither needs `π`
   to be injective or surjective.
3. **Double covers.** A double cover is a map `f : I → J` with a
   fixed-point-free map `σ : I → I` whose orbits are the fibers of `f`:
   `f i' = f i ↔ i' = i ∨ i' = σ i`. Then `σ` is an involution
   (`sigma_involutive`), `(f_* v) (f i) = v i + v (σ i)` (`fiberSumFn_pair`),
   the pushforward kills pullbacks (`fiberSumFn_pullback`), is onto when `f` has
   a section (`fiberSumFn_lift0`) and has the pullbacks as its kernel
   (`fiberSumFn_eq_zero_iff`). Supports satisfy
   `|supp v| = |supp (f_* v)| + |{i | v i ≠ 0 ∧ v (σ i) ≠ 0}|`
   (`card_support_fiberSum_add_overlap`), the overlap set has twice the size of
   its image (`card_overlap_eq_two_mul`), and a pullback has twice the support
   of its base chain (`card_support_pullback`).
4. **Bivariate bicycle complexes.** If `π_* A_cov = A_base` and
   `π_* B_cov = B_base`, then pushforward and pullback along `π` are chain maps
   between the two bivariate bicycle complexes (`fiberSum_bbBoundary1Fn`,
   `fiberSum_bbBoundary2Fn`, `pullback_bbBoundary1Fn`,
   `pullback_bbBoundary2Fn`).
-/

namespace Quantum
namespace Stabilizer
namespace Homological
namespace BB

open scoped BigOperators

/-! ## Fiber summation along a map of finite index types -/

section FiberSum

variable {I J : Type} [Fintype I] [DecidableEq J]

/-- Pushforward (fiber summation) of a `ZMod 2`-chain along `f : I → J`:
`(f_* u) j = ∑ i ∈ f⁻¹ j, u i`. -/
def fiberSumFn (f : I → J) (u : I → ZMod 2) : J → ZMod 2 :=
  fun j => ∑ i : I, if f i = j then u i else 0

@[simp] lemma fiberSumFn_apply (f : I → J) (u : I → ZMod 2) (j : J) :
    fiberSumFn f u j = ∑ i : I, if f i = j then u i else 0 := rfl

/-- The pushforward is additive. -/
lemma fiberSumFn_add (f : I → J) (u v : I → ZMod 2) :
    fiberSumFn f (u + v) = fiberSumFn f u + fiberSumFn f v := by
  funext j
  simp only [fiberSumFn_apply, ← Finset.sum_filter, Pi.add_apply, Finset.sum_add_distrib]

/-- `fiberSumFn` as a `ZMod 2`-linear map. -/
noncomputable def fiberSum (f : I → J) :
    (I → ZMod 2) →ₗ[ZMod 2] (J → ZMod 2) where
  toFun := fiberSumFn f
  map_add' := fiberSumFn_add f
  map_smul' s u := by
    funext j
    simp only [fiberSumFn_apply, ← Finset.sum_filter, Pi.smul_apply, smul_eq_mul,
      Finset.mul_sum, RingHom.id_apply]

@[simp] lemma fiberSum_apply (f : I → J) (u : I → ZMod 2) :
    fiberSum f u = fiberSumFn f u := rfl

/-- The pushforward is the transpose of the pullback: pairing `f_* u` with `F`
is pairing `u` with `F ∘ f`. -/
lemma sum_fiberSumFn_mul [Fintype J] (f : I → J) (u : I → ZMod 2) (F : J → ZMod 2) :
    ∑ j, fiberSumFn f u j * F j = ∑ i, u i * F (f i) := by
  simp only [fiberSumFn_apply, Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  simp

/-- Fiber summation along `Prod.map f id` acts blockwise: at `(j, b)` it is
fiber summation along `f` of the `b`-slice. -/
lemma fiberSumFn_prodMap {B : Type} [Fintype B] [DecidableEq B]
    (f : I → J) (c : I × B → ZMod 2) (j : J) (b : B) :
    fiberSumFn (Prod.map f id) c (j, b) = fiberSumFn f (fun i => c (i, b)) j := by
  simp only [fiberSumFn_apply, Fintype.sum_prod_type, Prod.map_apply, id, Prod.mk.injEq,
    ite_and]
  exact Finset.sum_congr rfl fun i _ => by split_ifs <;> simp

end FiberSum

/-! ## Convolution and group homomorphisms -/

section ConvTransfer

variable {G H : Type} [Fintype G] [AddCommGroup G]
  [Fintype H] [AddCommGroup H] [DecidableEq H]
variable (π : G →+ H)

/-- The pushforward is multiplicative: `π_* (a ⋆ b) = π_* a ⋆ π_* b`. -/
lemma fiberSum_conv (a b : G → ZMod 2) :
    fiberSumFn ⇑π (a ⋆ b) = fiberSumFn ⇑π a ⋆ fiberSumFn ⇑π b := by
  funext j
  rw [conv_apply, sum_fiberSumFn_mul ⇑π a fun k => fiberSumFn ⇑π b (j - k)]
  calc fiberSumFn ⇑π (a ⋆ b) j
      = ∑ h, ∑ g, if π g = j then a h * b (g - h) else 0 := by
        rw [Finset.sum_comm]
        simp only [fiberSumFn_apply, conv_apply, Finset.sum_ite_irrel, Finset.sum_const_zero]
    _ = ∑ h, a h * fiberSumFn ⇑π b (j - π h) := Finset.sum_congr rfl fun h _ => by
        -- reindex the inner sum by `g ↦ g + h`
        rw [fiberSumFn_apply, Finset.mul_sum, ← Equiv.sum_comp (Equiv.addRight h)]
        simp [eq_sub_iff_add_eq]

/-- Convolving against a pulled-back chain pushes the left factor forward:
`a ⋆ (u ∘ π) = (π_* a ⋆ u) ∘ π`. -/
lemma conv_pullback (a : G → ZMod 2) (u : H → ZMod 2) :
    a ⋆ (u ∘ ⇑π) = (fiberSumFn ⇑π a ⋆ u) ∘ ⇑π := by
  funext g
  simp only [Function.comp_apply, conv_apply, map_sub]
  exact (sum_fiberSumFn_mul ⇑π a fun k => u (π g - k)).symm

end ConvTransfer

/-! ## Double covers

A double cover is a map `f : I → J` together with `σ : I → I` such that `σ` has
no fixed points and the fibers of `f` are exactly the `σ`-orbits:
`f i' = f i ↔ i' = i ∨ i' = σ i`. -/

section DoubleCover

variable {I J : Type} {f : I → J} {σ : I → I}

/-- The deck map of a double cover is an involution. -/
lemma sigma_involutive (hσne : ∀ i, σ i ≠ i)
    (hfiber : ∀ i i', f i' = f i ↔ i' = i ∨ i' = σ i) (i : I) :
    σ (σ i) = i :=
  (((hfiber (σ i) i).mp ((hfiber i (σ i)).mpr (Or.inr rfl)).symm).resolve_left
    fun h => hσne i h.symm).symm

/-- The fiber of `f` through `i`, as a `Finset`, is the pair `{i, σ i}`. -/
lemma fiber_filter_eq [Fintype I] [DecidableEq I] [DecidableEq J]
    (hfiber : ∀ i i', f i' = f i ↔ i' = i ∨ i' = σ i) (i : I) :
    Finset.univ.filter (fun i' => f i' = f i) = {i, σ i} := by
  ext i'
  simp [hfiber i i']

/-- Two-point fiber formula: `(f_* v) (f i) = v i + v (σ i)`. -/
lemma fiberSumFn_pair [Fintype I] [DecidableEq J] (hσne : ∀ i, σ i ≠ i)
    (hfiber : ∀ i i', f i' = f i ↔ i' = i ∨ i' = σ i)
    (v : I → ZMod 2) (i : I) :
    fiberSumFn f v (f i) = v i + v (σ i) := by
  classical
  rw [fiberSumFn_apply, ← Finset.sum_filter, fiber_filter_eq hfiber i,
    Finset.sum_pair (Ne.symm (hσne i))]

/-- The pushforward annihilates pullbacks: `f_* (u ∘ f) = 0`, each fiber
contributing `u j + u j = 0`. -/
lemma fiberSumFn_pullback [Fintype I] [DecidableEq J] (hσne : ∀ i, σ i ≠ i)
    (hfiber : ∀ i i', f i' = f i ↔ i' = i ∨ i' = σ i)
    (u : J → ZMod 2) :
    fiberSumFn f (u ∘ f) = 0 := by
  funext j
  by_cases hj : ∃ i, f i = j
  · obtain ⟨i, rfl⟩ := hj
    rw [fiberSumFn_pair hσne hfiber, Function.comp_apply, Function.comp_apply,
      (hfiber i (σ i)).mpr (Or.inr rfl)]
    exact CharTwo.add_self_eq_zero _
  · exact Finset.sum_eq_zero fun i _ => if_neg fun h => hj ⟨i, h⟩

/-- The lift of a base chain along a section `sec` of `f`: supported on the
image of `sec`, where it takes the base values. -/
def lift0 [DecidableEq I] (f : I → J) (sec : J → I) (u : J → ZMod 2) :
    I → ZMod 2 :=
  fun i => if i = sec (f i) then u (f i) else 0

/-- The pushforward of `lift0 f sec u` is `u`; in particular `fiberSumFn f` is
surjective whenever `f` has a section. -/
lemma fiberSumFn_lift0 [Fintype I] [DecidableEq I] [DecidableEq J]
    {sec : J → I} (hsec : ∀ j, f (sec j) = j)
    (u : J → ZMod 2) :
    fiberSumFn f (lift0 f sec u) = u := by
  funext j
  rw [fiberSumFn_apply, Fintype.sum_eq_single (sec j)]
  · simp [lift0, hsec j]
  · intro i hne
    by_cases hfi : f i = j
    · rw [if_pos hfi, lift0, if_neg (by rwa [hfi])]
    · rw [if_neg hfi]

/-- The kernel of the pushforward is the image of the pullback: the chains
with zero pushforward are the deck-invariant ones, which descend. -/
lemma fiberSumFn_eq_zero_iff [Fintype I] [DecidableEq J] (hσne : ∀ i, σ i ≠ i)
    (hfiber : ∀ i i', f i' = f i ↔ i' = i ∨ i' = σ i)
    {sec : J → I} (hsec : ∀ j, f (sec j) = j)
    (v : I → ZMod 2) :
    fiberSumFn f v = 0 ↔ ∃ u : J → ZMod 2, v = u ∘ f := by
  refine ⟨fun h0 => ⟨v ∘ sec, funext fun i => ?_⟩, ?_⟩
  · have hpair : v i = v (σ i) := by
      have hi := congrFun h0 (f i)
      rwa [fiberSumFn_pair hσne hfiber, Pi.zero_apply, CharTwo.add_eq_zero] at hi
    rcases (hfiber i (sec (f i))).mp (hsec (f i)) with h | h
    · rw [Function.comp_apply, Function.comp_apply, h]
    · rw [Function.comp_apply, Function.comp_apply, h, ← hpair]
  · rintro ⟨u, rfl⟩
    exact fiberSumFn_pullback hσne hfiber u

/-! ### Supports

For a double cover, `|supp v| = |supp (f_* v)| + |overlap|`, where the overlap
is the set of points of `supp v` whose deck partner is also in `supp v`. The
overlap is a union of fibers, so it has twice as many points as its image. -/

/-- Support-weight identity for a double cover: the support of `v` splits into
the points whose deck partner is outside the support, which `f` maps
bijectively onto the support of `f_* v`, and the overlap. -/
theorem card_support_fiberSum_add_overlap [Fintype I] [Fintype J] [DecidableEq J]
    (hσne : ∀ i, σ i ≠ i)
    (hfiber : ∀ i i', f i' = f i ↔ i' = i ∨ i' = σ i)
    (v : I → ZMod 2) :
    (Finset.univ.filter fun i => v i ≠ 0).card
      = (Finset.univ.filter fun j => fiberSumFn f v j ≠ 0).card
        + (Finset.univ.filter fun i => v i ≠ 0 ∧ v (σ i) ≠ 0).card := by
  classical
  rw [← Finset.card_filter_add_card_filter_not (s := Finset.univ.filter fun i => v i ≠ 0)
    fun i => v (σ i) = 0, Finset.filter_filter, Finset.filter_filter]
  congr 1
  refine Finset.card_bij (fun i _ => f i) ?_ ?_ ?_
  · intro i hi
    obtain ⟨-, hvi, hvσ⟩ := Finset.mem_filter.mp hi
    rw [Finset.mem_filter, fiberSumFn_pair hσne hfiber, hvσ, add_zero]
    exact ⟨Finset.mem_univ _, hvi⟩
  · intro i₁ h₁ i₂ h₂ heq
    rcases (hfiber i₁ i₂).mp heq.symm with rfl | rfl
    · rfl
    · exact absurd (Finset.mem_filter.mp h₁).2.2 (Finset.mem_filter.mp h₂).2.1
  · intro j hj
    rw [Finset.mem_filter] at hj
    obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hj.2
    obtain ⟨rfl, -⟩ := ite_ne_right_iff.mp hi
    have hne := hj.2
    rw [fiberSumFn_pair hσne hfiber] at hne
    by_cases hσi : v (σ i) = 0
    · exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rwa [hσi, add_zero] at hne, hσi⟩,
        rfl⟩
    · refine ⟨σ i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hσi, ?_⟩,
        (hfiber i (σ i)).mpr (Or.inr rfl)⟩
      rw [sigma_involutive hσne hfiber]
      by_contra hi0
      rw [zmod2_ne_zero_iff.mp hi0, zmod2_ne_zero_iff.mp hσi] at hne
      exact hne (CharTwo.add_self_eq_zero 1)

/-- Pushing forward along a double cover can only shrink the support. -/
theorem card_support_fiberSum_le [Fintype I] [Fintype J] [DecidableEq J]
    (hσne : ∀ i, σ i ≠ i)
    (hfiber : ∀ i i', f i' = f i ↔ i' = i ∨ i' = σ i)
    (v : I → ZMod 2) :
    (Finset.univ.filter fun j => fiberSumFn f v j ≠ 0).card
      ≤ (Finset.univ.filter fun i => v i ≠ 0).card := by
  rw [card_support_fiberSum_add_overlap hσne hfiber v]
  exact Nat.le_add_right _ _

/-- A deck-invariant set upstairs is a union of fibers, so it has twice as many
points as there are base points whose fiber it contains. -/
lemma card_filter_eq_two_mul_of_deck_invariant [Fintype I] [Fintype J]
    (hσne : ∀ i, σ i ≠ i)
    (hfiber : ∀ i i', f i' = f i ↔ i' = i ∨ i' = σ i)
    {sec : J → I} (hsec : ∀ j, f (sec j) = j)
    (P : I → Prop) [DecidablePred P] (hP : ∀ i, P (σ i) ↔ P i) :
    (Finset.univ.filter P).card = 2 * (Finset.univ.filter fun j => P (sec j)).card := by
  classical
  -- the fiber over `j` is the pair `{sec j, σ (sec j)}`
  have hfib : ∀ i j, i ∈ ({sec j, σ (sec j)} : Finset I) ↔ f i = j := fun i j => by
    rw [Finset.mem_insert, Finset.mem_singleton, ← hfiber, hsec]
  have hU : Finset.univ.filter P
      = (Finset.univ.filter fun j => P (sec j)).biUnion fun j => {sec j, σ (sec j)} := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_biUnion, Finset.mem_univ, true_and, hfib,
      exists_eq_right']
    rcases (hfiber i (sec (f i))).mp (hsec (f i)) with h | h
    · rw [h]
    · rw [h, hP]
  rw [hU, Finset.card_biUnion fun j₁ _ j₂ _ hne => Finset.disjoint_left.mpr fun i h₁ h₂ =>
      hne (((hfib i j₁).mp h₁).symm.trans ((hfib i j₂).mp h₂)),
    Finset.sum_congr rfl fun j _ => Finset.card_pair (hσne (sec j)).symm, Finset.sum_const,
    smul_eq_mul, mul_comm]

/-- The deck-overlap set upstairs has exactly twice the cardinality of the
overlapping fibers downstairs: overlap points come in deck pairs. -/
theorem card_overlap_eq_two_mul [Fintype I] [Fintype J]
    (hσne : ∀ i, σ i ≠ i)
    (hfiber : ∀ i i', f i' = f i ↔ i' = i ∨ i' = σ i)
    {sec : J → I} (hsec : ∀ j, f (sec j) = j)
    (v : I → ZMod 2) :
    (Finset.univ.filter fun i => v i ≠ 0 ∧ v (σ i) ≠ 0).card
      = 2 * (Finset.univ.filter fun j =>
          v (sec j) ≠ 0 ∧ v (σ (sec j)) ≠ 0).card :=
  card_filter_eq_two_mul_of_deck_invariant hσne hfiber hsec _ fun i => by
    rw [sigma_involutive hσne hfiber, and_comm]

/-- The support of a pullback along a double cover is exactly twice the base
support: each base point in the support contributes its full two-point fiber. -/
theorem card_support_pullback [Fintype I] [Fintype J]
    (hσne : ∀ i, σ i ≠ i)
    (hfiber : ∀ i i', f i' = f i ↔ i' = i ∨ i' = σ i)
    {sec : J → I} (hsec : ∀ j, f (sec j) = j)
    (u : J → ZMod 2) :
    (Finset.univ.filter fun i => u (f i) ≠ 0).card
      = 2 * (Finset.univ.filter fun j => u j ≠ 0).card := by
  have h := card_filter_eq_two_mul_of_deck_invariant hσne hfiber hsec (fun i => u (f i) ≠ 0)
    fun i => by simp only [(hfiber i (σ i)).mpr (Or.inr rfl)]
  simpa only [hsec] using h

end DoubleCover

/-! ## Chain maps between bivariate bicycle complexes

Given `π : G →+ H` with `π_* A_cov = A_base` and `π_* B_cov = B_base`, the
pushforward (`fiberSumFn` along `π` on `C₀` and `C₂`, along `Prod.map π id` on
`C₁`) and the pullback (composition with `π`, respectively `Prod.map π id`) are
chain maps between the two bivariate bicycle complexes. -/

section BBChainMaps

variable {G H : Type} [Fintype G] [AddCommGroup G]
  [Fintype H] [AddCommGroup H] [DecidableEq H]
variable (π : G →+ H) (Ac Bc : G → ZMod 2) (Ab Bb : H → ZMod 2)

omit [Fintype H] in
/-- Pushforward on 1-chains acts on the left half by pushforward on `G`. -/
lemma leftHalf_fiberSumFn_prodMap (c : G × Fin 2 → ZMod 2) :
    leftHalf (fiberSumFn (Prod.map ⇑π id) c) = fiberSumFn ⇑π (leftHalf c) :=
  funext fun j => fiberSumFn_prodMap ⇑π c j 0

omit [Fintype H] in
/-- Pushforward on 1-chains acts on the right half by pushforward on `G`. -/
lemma rightHalf_fiberSumFn_prodMap (c : G × Fin 2 → ZMod 2) :
    rightHalf (fiberSumFn (Prod.map ⇑π id) c) = fiberSumFn ⇑π (rightHalf c) :=
  funext fun j => fiberSumFn_prodMap ⇑π c j 1

omit [Fintype G] [Fintype H] [DecidableEq H] in
/-- Pullback on 1-chains acts on the left half by pullback on `G`. -/
lemma leftHalf_pullback_prodMap (u : H × Fin 2 → ZMod 2) :
    leftHalf (u ∘ Prod.map ⇑π id) = (leftHalf u) ∘ ⇑π := rfl

omit [Fintype G] [Fintype H] [DecidableEq H] in
/-- Pullback on 1-chains acts on the right half by pullback on `G`. -/
lemma rightHalf_pullback_prodMap (u : H × Fin 2 → ZMod 2) :
    rightHalf (u ∘ Prod.map ⇑π id) = (rightHalf u) ∘ ⇑π := rfl

/-- The pushforward commutes with `∂₁`. -/
lemma fiberSum_bbBoundary1Fn
    (hA : fiberSumFn ⇑π Ac = Ab) (hB : fiberSumFn ⇑π Bc = Bb)
    (c : G × Fin 2 → ZMod 2) :
    fiberSumFn ⇑π (bbBoundary1Fn Ac Bc c)
      = bbBoundary1Fn Ab Bb (fiberSumFn (Prod.map ⇑π id) c) := by
  rw [bbBoundary1Fn_eq, bbBoundary1Fn_eq, fiberSumFn_add, fiberSum_conv, fiberSum_conv, hA, hB,
    leftHalf_fiberSumFn_prodMap, rightHalf_fiberSumFn_prodMap]

/-- The pushforward commutes with `∂₂`. -/
lemma fiberSum_bbBoundary2Fn
    (hA : fiberSumFn ⇑π Ac = Ab) (hB : fiberSumFn ⇑π Bc = Bb)
    (f2 : G → ZMod 2) :
    fiberSumFn (Prod.map ⇑π id) (bbBoundary2Fn Ac Bc f2)
      = bbBoundary2Fn Ab Bb (fiberSumFn ⇑π f2) := by
  rw [halves_ext_iff, leftHalf_fiberSumFn_prodMap, rightHalf_fiberSumFn_prodMap,
    leftHalf_bbBoundary2Fn, rightHalf_bbBoundary2Fn, fiberSum_conv, fiberSum_conv, hA, hB]
  exact ⟨rfl, rfl⟩

/-- The pullback commutes with `∂₁`. -/
lemma pullback_bbBoundary1Fn
    (hA : fiberSumFn ⇑π Ac = Ab) (hB : fiberSumFn ⇑π Bc = Bb)
    (u : H × Fin 2 → ZMod 2) :
    bbBoundary1Fn Ac Bc (u ∘ Prod.map ⇑π id)
      = (bbBoundary1Fn Ab Bb u) ∘ ⇑π := by
  rw [bbBoundary1Fn_eq, leftHalf_pullback_prodMap, rightHalf_pullback_prodMap, conv_pullback,
    conv_pullback, hA, hB]
  rfl

/-- The pullback commutes with `∂₂`. -/
lemma pullback_bbBoundary2Fn
    (hA : fiberSumFn ⇑π Ac = Ab) (hB : fiberSumFn ⇑π Bc = Bb)
    (f2 : H → ZMod 2) :
    bbBoundary2Fn Ac Bc (f2 ∘ ⇑π)
      = (bbBoundary2Fn Ab Bb f2) ∘ Prod.map ⇑π id := by
  rw [halves_ext_iff, leftHalf_bbBoundary2Fn, rightHalf_bbBoundary2Fn, conv_pullback,
    conv_pullback, hA, hB]
  exact ⟨rfl, rfl⟩

end BBChainMaps

end BB
end Homological
end Stabilizer
end Quantum
