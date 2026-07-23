/-
# A23 seam floor, layer 1: the z-fiber site structure of `F₂[Z₅×Z₁₅]`

The `[[150,8,8]]` base group `G150 = Z₅(x)×Z₁₅(y)` fibers over the 15
**sites** `(x, y mod 3)` with 5-point fibers (the `z = y³` cosets).  This
file builds the combinatorial layer of the analytic seam-coset floor:

* the fiber partition of chain weight (`wt150_eq_sum_fwt`);
* fiber parities and the **parity link**: the site parities of `A⋆f` at
  `s` and of `B⋆f` at `s + x̄` agree (the ε-component identity
  `B̄ = x̄·Ā` of the A22 CRT fibering), and `e₀` is ε-free;
* the δ-**type** of a fiber by weight alone (`0,5 ↦ O`, `1,4 ↦ M`,
  `2,3 ↦ D` — the CRT `F₂⁵ ≅ F₂ × GF(16)` classification), the site cost
  table, and the **per-site bound**: two parity-linked fibers weigh at
  least the cost of their type pair (`site_bound`);
* δ-coordinates (`dcoord`, fiber mod the all-ones vector) and the packed
  δ-data vector `wOf f : WIdx → ZMod 2` consumed by the sweep layer;
* `translate` algebra and the block-weight split used by the reduction.

Everything finite is discharged by `decide`/`native_decide`; the
provenance and numeric validation is
`qec-lab:experiments/bb_lab/scripts/a23_site_sweep.py` (V0–V6).
-/

import QEC.Stabilizer.Codes.BivariateBicycle.Z5Z15F2A6.SeamSweepData

namespace Quantum
namespace Stabilizer
namespace Homological
namespace BB
namespace Z5Z15F2A6

open scoped BigOperators

set_option maxRecDepth 4096

/-! ## Sites and fibers -/

/-- The site group: `x`-coordinate × (`y mod 3`). -/
abbrev Sites : Type := ZMod 5 × ZMod 3

/-- Site linear index `3x + (y mod 3) ∈ [0, 15)`. -/
def siteIdx (s : Sites) : ℕ := 3 * s.1.val + s.2.val

/-- The site of a cell. -/
def siteOf (g : G150) : Sites := (g.1, (g.2.val : ZMod 3))

/-- The `k`-th fiber point over a site (no wrap: `c + 3k ≤ 14`). -/
def fpt (s : Sites) (k : Fin 5) : G150 :=
  (s.1, ((s.2.val + 3 * k.val : ℕ) : ZMod 15))

/-- The fiber coordinate of a cell. -/
def fidx (g : G150) : Fin 5 :=
  ⟨g.2.val / 3, by have := g.2.val_lt; omega⟩

lemma fpt_siteOf_fidx : ∀ g : G150, fpt (siteOf g) (fidx g) = g := by decide

lemma siteOf_fpt : ∀ (s : Sites) (k : Fin 5), siteOf (fpt s k) = s := by decide

lemma fidx_fpt : ∀ (s : Sites) (k : Fin 5), fidx (fpt s k) = k := by decide

/-! ## Chain weight and its fiber partition -/

/-- Hamming weight of a 2-chain / 75-cell vector. -/
def wt150 (v : G150 → ZMod 2) : ℕ :=
  (Finset.univ.filter fun g => v g ≠ 0).card

/-- Fiber weight of `v` at a site. -/
def fwt (v : G150 → ZMod 2) (s : Sites) : ℕ :=
  (Finset.univ.filter fun k : Fin 5 => v (fpt s k) ≠ 0).card

lemma fwt_le_five (v : G150 → ZMod 2) (s : Sites) : fwt v s ≤ 5 := by
  calc fwt v s ≤ (Finset.univ : Finset (Fin 5)).card := Finset.card_filter_le _ _
  _ = 5 := by simp

/-- Per-site slice of the weight: cells of `v`'s support at site `b`. -/
lemma card_site_slice (v : G150 → ZMod 2) (b : Sites) :
    ((Finset.univ.filter fun g => v g ≠ 0).filter fun g => siteOf g = b).card
      = fwt v b := by
  refine Finset.card_bij' (fun g _ => fidx g) (fun k _ => fpt b k) ?_ ?_ ?_ ?_
  · intro g hg
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg ⊢
    obtain ⟨hv, hs⟩ := hg
    rwa [← hs, fpt_siteOf_fidx]
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
    exact ⟨hk, siteOf_fpt b k⟩
  · intro g hg
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg
    have h := fpt_siteOf_fidx g
    rwa [hg.2] at h
  · intro k _
    exact fidx_fpt b k

/-- **The fiber partition**: `|v| = Σ_s |fiber_s v|`. -/
theorem wt150_eq_sum_fwt (v : G150 → ZMod 2) :
    wt150 v = ∑ s : Sites, fwt v s := by
  have h : wt150 v = ∑ b : Sites,
      ((Finset.univ.filter fun g => v g ≠ 0).filter fun g => siteOf g = b).card :=
    Finset.card_eq_sum_card_fiberwise fun g _ => Finset.mem_univ _
  rw [h]
  exact Finset.sum_congr rfl fun b _ => card_site_slice v b

/-! ## Fiber parity -/

/-- Fiber parity of `v` at a site. -/
def fparity (v : G150 → ZMod 2) (s : Sites) : ZMod 2 :=
  ∑ k : Fin 5, v (fpt s k)

lemma sum_fin5_eq_card (p : Fin 5 → ZMod 2) :
    (∑ k, p k) = ((Finset.univ.filter fun k : Fin 5 => p k ≠ 0).card : ZMod 2) := by
  revert p; decide

/-- Parity is the weight mod 2. -/
lemma fparity_eq_fwt (v : G150 → ZMod 2) (s : Sites) :
    fparity v s = (fwt v s : ZMod 2) :=
  sum_fin5_eq_card fun k => v (fpt s k)

/-- **The parity link on the δ-basis**: at every cell `g` and site `s`,
the `A`-image parity at `s` equals the `B`-image parity at `s + x̄`.
(The ε-identity `B̄ = x̄·Ā` of the CRT fibering, checked cell-wise.) -/
lemma parity_link_basis :
    ∀ (g : G150) (s : Sites),
      fparity (conv a150 (Pi.single g 1)) s
        = fparity (conv b150 (Pi.single g 1)) (s + (1, 0)) := by
  native_decide

lemma conv_zero_right (P : G150 → ZMod 2) : conv P (0 : G150 → ZMod 2) = 0 := by
  funext g
  simp [conv_apply]

lemma fparity_conv_zero (P : G150 → ZMod 2) (s : Sites) :
    fparity (conv P (0 : G150 → ZMod 2)) s = 0 := by
  rw [conv_zero_right]
  simp [fparity]

lemma fparity_conv_add (P : G150 → ZMod 2) (a b : G150 → ZMod 2) (s : Sites) :
    fparity (conv P (a + b)) s = fparity (conv P a) s + fparity (conv P b) s := by
  rw [fparity, fparity, fparity, conv_add_right, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun k _ => rfl

/-- The parity link for every `f` (basis lift of `parity_link_basis`). -/
theorem parity_link (f : G150 → ZMod 2) (s : Sites) :
    fparity (conv a150 f) s = fparity (conv b150 f) (s + (1, 0)) := by
  have h := funLiftF2
    (M := fun f : G150 → ZMod 2 => fun s : Sites => fparity (conv a150 f) s)
    (N := fun f : G150 → ZMod 2 => fun s : Sites =>
      fparity (conv b150 f) (s + (1, 0)))
    (by funext s; exact fparity_conv_zero a150 s)
    (by funext s; exact fparity_conv_zero b150 (s + (1, 0)))
    (by
      intro a b
      funext s
      exact fparity_conv_add a150 a b s)
    (by
      intro a b
      funext s
      exact fparity_conv_add b150 a b (s + (1, 0)))
    (by
      intro g
      funext s
      exact parity_link_basis g s)
    f
  exact congrFun h s

/-- `e₀` is ε-free: every fiber parity vanishes. -/
lemma e0_fparity : ∀ s : Sites, fparity e0f s = 0 := by native_decide

/-! ## δ-types and the site cost table -/

/-- δ-type of a fiber weight: `0,5 ↦ O(0)`, `1,4 ↦ M(1)`, `2,3 ↦ D(2)`.
(The CRT `F₂⁵ ≅ F₂ × GF(16)`: weight-`{0,5}` fibers are the ε-only ones,
weight-`{1,4}` reduce to `μ₅`-scalars, the rest to `GF(16) ∖ (μ₅ ∪ 0)`.) -/
def ftype (w : ℕ) : Fin 3 :=
  if w = 0 ∨ w = 5 then 0 else if w = 1 ∨ w = 4 then 1 else 2

/-- The per-site cost table `c(t₁, t₂)` — the minimum total weight of a
parity-linked fiber pair with δ-types `(t₁, t₂)`. -/
def siteCost : Fin 3 → Fin 3 → ℕ :=
  ![![0, 4, 2], ![4, 2, 4], ![2, 4, 4]]

/-- **The per-site bound**: parity-linked fiber weights are bounded below
by the cost of their type pair. -/
lemma site_bound : ∀ wp wq : Fin 6, wp.val % 2 = wq.val % 2 →
    siteCost (ftype wp.val) (ftype wq.val) ≤ wp.val + wq.val := by decide

/-- `site_bound` over `ℕ` (stated with abstract variables so that heavy
weight terms are never unfolded by unification). -/
lemma site_bound' (wp wq : ℕ) (hp : wp ≤ 5) (hq : wq ≤ 5)
    (h : wp % 2 = wq % 2) : siteCost (ftype wp) (ftype wq) ≤ wp + wq :=
  site_bound ⟨wp, Nat.lt_succ_of_le hp⟩ ⟨wq, Nat.lt_succ_of_le hq⟩ h

/-- Every active (non-`(O,O)`) type pair costs at least 2. -/
lemma siteCost_active : ∀ t₁ t₂ : Fin 3, ¬(t₁ = 0 ∧ t₂ = 0) →
    2 ≤ siteCost t₁ t₂ := by decide

/-! ## δ-coordinates and the packed δ-data vector -/

/-- δ-coordinates of the fiber of `v` at `s`: the fiber mod the all-ones
vector, in the basis `pᵢ + p₄`. -/
def dcoord (v : G150 → ZMod 2) (s : Sites) (i : Fin 4) : ZMod 2 :=
  v (fpt s i.castSucc) + v (fpt s 4)

/-- δ-type from δ-coordinates (nibble `d₀ + 2d₁ + 4d₂ + 8d₃`; the five
`M`-nibbles are the images of the fiber monomials). -/
def dTypeOf (d : Fin 4 → ZMod 2) : Fin 3 :=
  let n := (d 0).val + 2 * (d 1).val + 4 * (d 2).val + 8 * (d 3).val
  if n = 0 then 0
  else if n = 1 ∨ n = 2 ∨ n = 4 ∨ n = 8 ∨ n = 15 then 1 else 2

/-- The δ-type of a fiber's δ-coordinates is the δ-type of its weight. -/
lemma dTypeOf_dcoord_eq_ftype : ∀ p : Fin 5 → ZMod 2,
    dTypeOf (fun i => p i.castSucc + p 4)
      = ftype (Finset.univ.filter fun k : Fin 5 => p k ≠ 0).card := by
  decide

/-- Zero δ-type means zero δ-coordinates. -/
lemma dTypeOf_eq_zero : ∀ d : Fin 4 → ZMod 2, dTypeOf d = 0 → ∀ i, d i = 0 := by
  decide

/-- The δ-data index space: 15 sites × (4 `A`-side + 4 `B`-side) bits. -/
abbrev WIdx : Type := Sites × Fin 8

/-- Linear index `8·siteIdx + r ∈ [0, 120)`. -/
def widxNat (p : WIdx) : ℕ := 8 * siteIdx p.1 + p.2.val

/-- Decode a linear index. -/
def wIdxOf (n : ℕ) : WIdx :=
  ((((n / 8 / 3 : ℕ) : ZMod 5), ((n / 8 : ℕ) : ZMod 3)), ⟨n % 8, Nat.mod_lt _ (by omega)⟩)

lemma widxNat_wIdxOf : ∀ n : Fin 120, widxNat (wIdxOf n.val) = n.val := by decide

lemma wIdxOf_widxNat : ∀ p : WIdx, wIdxOf (widxNat p) = p := by decide

/-- The δ-data vector of `f`: `A`-side δ-coords of `e₀ + A⋆f` at `s`
(`r < 4`), `B`-side δ-coords of `B⋆f` at `s + x̄` (`r ≥ 4`). -/
def wOf (f : G150 → ZMod 2) : WIdx → ZMod 2 := fun p =>
  if h : p.2.val < 4 then dcoord (e0f + conv a150 f) p.1 ⟨p.2.val, h⟩
  else dcoord (conv b150 f) (p.1 + (1, 0)) ⟨p.2.val - 4, by omega⟩

/-- `A`-side δ-type of a δ-data vector at a site. -/
def tU (w : WIdx → ZMod 2) (s : Sites) : Fin 3 :=
  dTypeOf fun i => w (s, ⟨i.val, by omega⟩)

/-- `B`-side δ-type of a δ-data vector at a site. -/
def tV (w : WIdx → ZMod 2) (s : Sites) : Fin 3 :=
  dTypeOf fun i => w (s, ⟨i.val + 4, by omega⟩)

/-- Low half of `wOf`: the `A`-side δ-coordinates. -/
lemma wOf_lo (f : G150 → ZMod 2) (s : Sites) (i : Fin 4) :
    wOf f (s, ⟨i.val, by omega⟩) = dcoord (e0f + conv a150 f) s i := by
  unfold wOf
  rw [dif_pos (show ((s, ⟨i.val, by omega⟩) : WIdx).2.val < 4 from i.isLt)]

/-- High half of `wOf`: the `B`-side δ-coordinates. -/
lemma wOf_hi (f : G150 → ZMod 2) (s : Sites) (i : Fin 4) :
    wOf f (s, ⟨i.val + 4, by omega⟩) = dcoord (conv b150 f) (s + (1, 0)) i := by
  unfold wOf
  rw [dif_neg (show ¬ ((s, ⟨i.val + 4, by omega⟩) : WIdx).2.val < 4 by
    simp)]
  exact congrArg (dcoord (conv b150 f) (s + (1, 0))) (Fin.ext (by simp))

/-- δ-type from δ-coordinates equals δ-type from the fiber weight. -/
lemma dTypeOf_dcoord (u : G150 → ZMod 2) (s : Sites) :
    dTypeOf (fun i => dcoord u s i) = ftype (fwt u s) :=
  dTypeOf_dcoord_eq_ftype fun k => u (fpt s k)

/-- `tU (wOf f)` is the fiber-weight type of `e₀ + A⋆f`. -/
lemma tU_wOf (f : G150 → ZMod 2) (s : Sites) :
    tU (wOf f) s = ftype (fwt (e0f + conv a150 f) s) := by
  unfold tU
  rw [show (fun i : Fin 4 => wOf f (s, ⟨i.val, by omega⟩))
      = fun i => dcoord (e0f + conv a150 f) s i from funext fun i => wOf_lo f s i]
  exact dTypeOf_dcoord (e0f + conv a150 f) s

/-- `tV (wOf f)` is the fiber-weight type of `B⋆f` at the shifted site. -/
lemma tV_wOf (f : G150 → ZMod 2) (s : Sites) :
    tV (wOf f) s = ftype (fwt (conv b150 f) (s + (1, 0))) := by
  unfold tV
  rw [show (fun i : Fin 4 => wOf f (s, ⟨i.val + 4, by omega⟩))
      = fun i => dcoord (conv b150 f) (s + (1, 0)) i
    from funext fun i => wOf_hi f s i]
  exact dTypeOf_dcoord (conv b150 f) (s + (1, 0))

/-! ## The per-site chain: weight ≥ site-cost sum -/

/-- Reindexing a site sum by a shift. -/
lemma sum_fwt_shift (v : G150 → ZMod 2) (c : Sites) :
    (∑ s : Sites, fwt v (s + c)) = ∑ s : Sites, fwt v s :=
  Equiv.sum_comp (Equiv.addRight c) (fwt v)

/-- **The site-cost lower bound**: for any `f`, the total weight of the
pair `(e₀ + A⋆f, B⋆f)` dominates the site-cost sum of its δ-data. -/
theorem weight_ge_cost_sum (f : G150 → ZMod 2) :
    (∑ s : Sites, siteCost (tU (wOf f) s) (tV (wOf f) s))
      ≤ wt150 (e0f + conv a150 f) + wt150 (conv b150 f) := by
  have hre : wt150 (conv b150 f) = ∑ s : Sites, fwt (conv b150 f) (s + (1, 0)) := by
    rw [wt150_eq_sum_fwt, sum_fwt_shift]
  rw [wt150_eq_sum_fwt (e0f + conv a150 f), hre, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun s _ => ?_
  have hpar : fwt (e0f + conv a150 f) s % 2 = fwt (conv b150 f) (s + (1, 0)) % 2 := by
    have h1 : fparity (e0f + conv a150 f) s = fparity (conv b150 f) (s + (1, 0)) := by
      have hadd : fparity (e0f + conv a150 f) s
          = fparity e0f s + fparity (conv a150 f) s := by
        rw [fparity, fparity, fparity, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun k _ => rfl
      rw [hadd, e0_fparity, zero_add]
      exact parity_link f s
    rw [fparity_eq_fwt, fparity_eq_fwt] at h1
    exact (ZMod.natCast_eq_natCast_iff' _ _ _).mp h1
  have hb := site_bound' _ _ (fwt_le_five (e0f + conv a150 f) s)
    (fwt_le_five (conv b150 f) (s + (1, 0))) hpar
  rw [tU_wOf, tV_wOf]
  exact hb

/-! ## `translate` algebra and the block-weight split -/

lemma translate_comp (a b : G150) (v : G150 → ZMod 2) :
    translate a (translate b v) = translate (a + b) v := by
  funext g
  change v (g + a + b) = v (g + (a + b))
  rw [add_assoc]

lemma translate_zero' (v : G150 → ZMod 2) : translate (0 : G150) v = v := by
  funext g
  change v (g + 0) = v g
  rw [add_zero]

lemma translate_add_dist (c : G150) (u v : G150 → ZMod 2) :
    translate c (u + v) = translate c u + translate c v := rfl

/-- Translation preserves weight. -/
lemma wt150_translate (c : G150) (v : G150 → ZMod 2) :
    wt150 (translate c v) = wt150 v := by
  refine Finset.card_bij' (fun g _ => g + c) (fun g _ => g - c) ?_ ?_ ?_ ?_
  · intro g hg
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      translate_apply] at hg
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hg
  · intro g hg
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, translate_apply,
      sub_add_cancel]
    exact hg
  · intro g _
    exact add_sub_cancel_right g c
  · intro g _
    exact sub_add_cancel g c

/-- Weight of a two-block 1-chain splits as the block weights. -/
lemma card_two_blocks (u v : G150 → ZMod 2) :
    (Finset.univ.filter fun p : G150 × Fin 2 =>
        (if p.2 = 0 then u p.1 else v p.1) ≠ 0).card
      = wt150 u + wt150 v := by
  rw [(Finset.card_filter_add_card_filter_not
    (s := Finset.univ.filter fun p : G150 × Fin 2 =>
      (if p.2 = 0 then u p.1 else v p.1) ≠ 0)
    (p := fun p : G150 × Fin 2 => p.2 = 0)).symm]
  congr 1
  · refine Finset.card_bij' (fun p _ => p.1) (fun g _ => (g, 0)) ?_ ?_ ?_ ?_
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
      rw [if_pos hp.2] at hp
      exact hp.1
    · intro g hg
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg ⊢
      exact ⟨by simpa using hg, trivial⟩
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
      exact Prod.ext rfl hp.2.symm
    · intro g _
      rfl
  · refine Finset.card_bij' (fun p _ => p.1) (fun g _ => (g, 1)) ?_ ?_ ?_ ?_
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
      rw [if_neg hp.2] at hp
      exact hp.1
    · intro g hg
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg ⊢
      refine ⟨by simpa using hg, by simp⟩
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
      have h2 : p.2 = 1 := by omega
      exact Prod.ext rfl h2.symm
    · intro g _
      rfl

end Z5Z15F2A6
end BB
end Homological
end Stabilizer
end Quantum
