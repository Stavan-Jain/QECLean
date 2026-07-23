/-
# A22: the (ε,δ) site geometry of the `Z₅×Z₁₅` base — semantic layer

The F₂-ified fibering behind the analytic `LightClassification` proof
(`qec-lab:experiments/bb_lab/notes/A22_analytic_classification.md`): the
150 cells of a 1-chain pair regroup into 15 *sites* × 2 blocks × 5-cell
*fibers* (fiber = coset of `⟨y³⟩`; site = (x-coordinate, w-coordinate)
with `w = y⁵`), with the u-fiber of site `s` paired to the v-fiber of
site `s + x̄` (the `x̄`-pairing that shares the ε-coordinate on
boundaries).

Per fiber, the pair (ε = bit sum, δ = the four bits `tₙ + t₄`, i.e.
reduction mod `q(z) = 1+z+z²+z³+z⁴`) is a *bijection* on `𝔽₂⁵` with
explicit inverse `σbit`, so every chain is pointwise reconstructed from
its (ε, δ)-data (`recon_eq`); the chain weight is the sum of 30 fiber
weights (`chainWeight_eq_sum_sites`); δ-active site pairs weigh ≥ 2 and
δ-inactive ε-flipped pairs weigh exactly 10 (`active_card_le`,
`flip_card_le`).  All per-fiber facts are ≤ 1024-case `decide`s; no
field theory appears anywhere.
-/

import QEC.Stabilizer.Codes.BivariateBicycle.Z5Z15F2A6.Defs

namespace Quantum
namespace Stabilizer
namespace Homological
namespace BB
namespace Z5Z15F2A6

open scoped BigOperators

set_option maxRecDepth 4096

/-! ## Sites, fibers, cells -/

/-- The `x`-coordinate of site `s` (`s = 3·i + b`). -/
def siteI (s : Fin 15) : ZMod 5 := (s.val / 3 : ℕ)

/-- The `w`-coordinate of site `s`. -/
def siteB (s : Fin 15) : ℕ := s.val % 3

/-- The u-block cell of site `s`, fiber coordinate `a` (`y = 3a + 5b`). -/
def uCell (s : Fin 15) (a : Fin 5) : G150 × Fin 2 :=
  ((siteI s, ((3 * a.val + 5 * siteB s : ℕ) : ZMod 15)), 0)

/-- The paired v-block cell: site `s + x̄`, same fiber coordinate. -/
def vCell (s : Fin 15) (a : Fin 5) : G150 × Fin 2 :=
  ((siteI s + 1, ((3 * a.val + 5 * siteB s : ℕ) : ZMod 15)), 1)

/-- Site-fiber coordinates of a cell (inverse direction). -/
def siteFibOf (p : G150 × Fin 2) : Fin 15 × Fin 2 × Fin 5 :=
  let x : ZMod 5 := if p.2 = 0 then p.1.1 else p.1.1 - 1
  (⟨(3 * x.val + 2 * p.1.2.val % 3) % 15, Nat.mod_lt _ (by norm_num)⟩,
    p.2, ⟨2 * p.1.2.val % 5, Nat.mod_lt _ (by norm_num)⟩)

/-- The cell of site-fiber coordinates. -/
def cellOf (q : Fin 15 × Fin 2 × Fin 5) : G150 × Fin 2 :=
  if q.2.1 = 0 then uCell q.1 q.2.2 else vCell q.1 q.2.2

lemma cellOf_siteFibOf : ∀ p : G150 × Fin 2, cellOf (siteFibOf p) = p := by
  decide

lemma siteFibOf_cellOf : ∀ q : Fin 15 × Fin 2 × Fin 5,
    siteFibOf (cellOf q) = q := by
  decide

/-- The site-fiber regrouping as an `Equiv`. -/
def siteEquiv : Fin 15 × Fin 2 × Fin 5 ≃ G150 × Fin 2 where
  toFun := cellOf
  invFun := siteFibOf
  left_inv := siteFibOf_cellOf
  right_inv := cellOf_siteFibOf

/-! ## (ε, δ)-data of a chain -/

/-- ε-coordinate of the u-fiber at site `s` (the shared `h`). -/
def hU (b : G150 × Fin 2 → ZMod 2) (s : Fin 15) : ZMod 2 :=
  ∑ a : Fin 5, b (uCell s a)

/-- ε-coordinate of the paired v-fiber at site `s`. -/
def hV (b : G150 × Fin 2 → ZMod 2) (s : Fin 15) : ZMod 2 :=
  ∑ a : Fin 5, b (vCell s a)

/-- δ-bit `n` of the u-fiber at site `s`. -/
def dU (b : G150 × Fin 2 → ZMod 2) (s : Fin 15) (n : Fin 4) : ZMod 2 :=
  b (uCell s ⟨n.val, by omega⟩) + b (uCell s 4)

/-- δ-bit `n` of the paired v-fiber at site `s`. -/
def dV (b : G150 × Fin 2 → ZMod 2) (s : Fin 15) (n : Fin 4) : ZMod 2 :=
  b (vCell s ⟨n.val, by omega⟩) + b (vCell s 4)

/-- The packed (α, β′)-data: position `p = 8s + 4t + n`. -/
def deltaData (b : G150 × Fin 2 → ZMod 2) : Fin 120 → ZMod 2 := fun p =>
  if p.val / 4 % 2 = 0 then dU b ⟨p.val / 8, by omega⟩ ⟨p.val % 4, by omega⟩
  else dV b ⟨p.val / 8, by omega⟩ ⟨p.val % 4, by omega⟩

lemma deltaData_apply_u (b : G150 × Fin 2 → ZMod 2) (s : Fin 15) (n : Fin 4)
    (p : Fin 120) (hp : p.val = 8 * s.val + n.val) :
    deltaData b p = dU b s n := by
  have hs : p.val / 8 = s.val := by omega
  have hn : p.val % 4 = n.val := by omega
  have ht : p.val / 4 % 2 = 0 := by omega
  simp only [deltaData, hs, hn, ht, Fin.eta]
  norm_num

lemma deltaData_apply_v (b : G150 × Fin 2 → ZMod 2) (s : Fin 15) (n : Fin 4)
    (p : Fin 120) (hp : p.val = 8 * s.val + 4 + n.val) :
    deltaData b p = dV b s n := by
  have hs : p.val / 8 = s.val := by omega
  have hn : p.val % 4 = n.val := by omega
  have ht : p.val / 4 % 2 = 1 := by omega
  simp only [deltaData, hs, hn, ht, Fin.eta]
  norm_num

/-! ## The σ-reconstruction -/

/-- Fiber bit `a` of the unique fiber with ε-coordinate `h` and δ-bits
`d`: `t₄ = h + Σd`, `tₙ = dₙ + t₄`. -/
def σbit (h : ZMod 2) (d : Fin 4 → ZMod 2) (a : Fin 5) : ZMod 2 :=
  (if ha : a.val < 4 then d ⟨a.val, ha⟩ else 0) + (h + d 0 + d 1 + d 2 + d 3)

/-- Reconstruction at site-fiber coordinates. -/
def reconAt (h : Fin 15 → ZMod 2) (y : Fin 120 → ZMod 2)
    (q : Fin 15 × Fin 2 × Fin 5) : ZMod 2 :=
  σbit (h q.1)
    (fun n => y ⟨8 * q.1.val + 4 * q.2.1.val + n.val, by
      have h1 := q.1.isLt
      have h2 := q.2.1.isLt
      have h3 := n.isLt
      omega⟩)
    q.2.2

/-- The reconstruction of a 1-chain pair from (h, αβ)-data. -/
def reconFn (h : Fin 15 → ZMod 2) (y : Fin 120 → ZMod 2) :
    G150 × Fin 2 → ZMod 2 := fun p => reconAt h y (siteFibOf p)

/-- **The fiber tautology**: `σbit` inverts the (ε, δ)-extraction on every
5-bit fiber. -/
lemma σbit_eps_delta : ∀ t : Fin 5 → ZMod 2, ∀ a : Fin 5,
    σbit (∑ j : Fin 5, t j)
      (fun n : Fin 4 => t ⟨n.val, by omega⟩ + t 4) a = t a := by
  decide

/-- **Reconstruction**: a chain whose paired fibers share ε-coordinates
is `reconFn` of its own (h, αβ)-data. -/
theorem recon_eq (b : G150 × Fin 2 → ZMod 2)
    (hEps : ∀ s : Fin 15, hV b s = hU b s) :
    b = reconFn (hU b) (deltaData b) := by
  funext p
  conv_lhs => rw [← cellOf_siteFibOf p]
  show b (cellOf (siteFibOf p)) = reconAt (hU b) (deltaData b) (siteFibOf p)
  generalize siteFibOf p = q
  obtain ⟨s, t, a⟩ := q
  have hdu : (fun n : Fin 4 => deltaData b
      ⟨8 * s.val + 4 * (0 : Fin 2).val + n.val, by
        have := s.isLt; have := n.isLt; omega⟩)
      = dU b s := by
    funext n
    exact deltaData_apply_u b s n _ (by simp)
  have hdv : (fun n : Fin 4 => deltaData b
      ⟨8 * s.val + 4 * (1 : Fin 2).val + n.val, by
        have := s.isLt; have := n.isLt; omega⟩)
      = dV b s := by
    funext n
    exact deltaData_apply_v b s n _ (by simp)
  fin_cases t
  · show b (uCell s a) = reconAt (hU b) (deltaData b) (s, 0, a)
    show b (uCell s a)
      = σbit (hU b s) (fun n : Fin 4 => deltaData b
          ⟨8 * s.val + 4 * (0 : Fin 2).val + n.val, _⟩) a
    rw [hdu]
    have hkey := σbit_eps_delta (fun j => b (uCell s j)) a
    have hdueq : dU b s = fun n : Fin 4 =>
        (fun j => b (uCell s j)) ⟨n.val, by omega⟩
          + (fun j => b (uCell s j)) 4 := by
      funext n
      rfl
    rw [hdueq]
    exact hkey.symm
  · show b (vCell s a) = reconAt (hU b) (deltaData b) (s, 1, a)
    show b (vCell s a)
      = σbit (hU b s) (fun n : Fin 4 => deltaData b
          ⟨8 * s.val + 4 * (1 : Fin 2).val + n.val, _⟩) a
    rw [hdv]
    have hkey := σbit_eps_delta (fun j => b (vCell s j)) a
    have hdveq : dV b s = fun n : Fin 4 =>
        (fun j => b (vCell s j)) ⟨n.val, by omega⟩
          + (fun j => b (vCell s j)) 4 := by
      funext n
      rfl
    rw [hdveq, ← hEps s]
    exact hkey.symm

/-! ## Weight regrouping -/

/-- u-fiber weight at a site. -/
def wU (b : G150 × Fin 2 → ZMod 2) (s : Fin 15) : ℕ :=
  ∑ a : Fin 5, if b (uCell s a) ≠ 0 then 1 else 0

/-- Paired v-fiber weight at a site. -/
def wV (b : G150 × Fin 2 → ZMod 2) (s : Fin 15) : ℕ :=
  ∑ a : Fin 5, if b (vCell s a) ≠ 0 then 1 else 0

/-- **The site regrouping of chain weight.** -/
theorem chainWeight_eq_sum_sites (b : G150 × Fin 2 → ZMod 2) :
    (Finset.univ.filter fun j : G150 × Fin 2 => b j ≠ 0).card
      = ∑ s : Fin 15, (wU b s + wV b s) := by
  rw [Finset.card_filter]
  rw [← Equiv.sum_comp siteEquiv
    (fun j : G150 × Fin 2 => if b j ≠ 0 then (1 : ℕ) else 0)]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Fintype.sum_prod_type, Fin.sum_univ_two]
  rfl

/-! ## Per-site pair bounds (paired fibers share ε) -/

/-- δ-activity of a site: some δ-bit of either paired fiber is set. -/
def siteActive (b : G150 × Fin 2 → ZMod 2) (s : Fin 15) : Prop :=
  (∃ n, dU b s n ≠ 0) ∨ (∃ n, dV b s n ≠ 0)

instance (b : G150 × Fin 2 → ZMod 2) (s : Fin 15) :
    Decidable (siteActive b s) := by
  unfold siteActive
  infer_instance

/-- Fiber-pair core: a δ-active ε-matched pair weighs at least 2. -/
lemma pair_active_ge_two : ∀ tu tv : Fin 5 → ZMod 2,
    (∑ j : Fin 5, tu j) = (∑ j : Fin 5, tv j) →
    ((∃ n : Fin 4, tu ⟨n.val, by omega⟩ + tu 4 ≠ 0) ∨
     (∃ n : Fin 4, tv ⟨n.val, by omega⟩ + tv 4 ≠ 0)) →
    2 ≤ (∑ a : Fin 5, if tu a ≠ 0 then (1 : ℕ) else 0)
        + (∑ a : Fin 5, if tv a ≠ 0 then (1 : ℕ) else 0) := by
  decide

/-- Fiber-pair core: a δ-inactive ε-matched pair with ε = 1 weighs
exactly 10 (both fibers are the full `N`-fiber). -/
lemma pair_flip_eq_ten : ∀ tu tv : Fin 5 → ZMod 2,
    (∑ j : Fin 5, tu j) = (∑ j : Fin 5, tv j) →
    (∀ n : Fin 4, tu ⟨n.val, by omega⟩ + tu 4 = 0) →
    (∀ n : Fin 4, tv ⟨n.val, by omega⟩ + tv 4 = 0) →
    (∑ j : Fin 5, tu j) ≠ 0 →
    (∑ a : Fin 5, if tu a ≠ 0 then (1 : ℕ) else 0)
        + (∑ a : Fin 5, if tv a ≠ 0 then (1 : ℕ) else 0) = 10 := by
  decide

/-- Site instantiation: an active site weighs ≥ 2. -/
lemma site_active_ge_two (b : G150 × Fin 2 → ZMod 2)
    (hEps : ∀ s : Fin 15, hV b s = hU b s) (s : Fin 15)
    (hact : siteActive b s) : 2 ≤ wU b s + wV b s :=
  pair_active_ge_two (fun j => b (uCell s j)) (fun j => b (vCell s j))
    (hEps s).symm hact

/-- Site instantiation: an inactive flipped site weighs 10. -/
lemma site_flip_eq_ten (b : G150 × Fin 2 → ZMod 2)
    (hEps : ∀ s : Fin 15, hV b s = hU b s) (s : Fin 15)
    (hinact : ¬ siteActive b s) (hflip : hU b s ≠ 0) :
    wU b s + wV b s = 10 := by
  rw [siteActive, not_or] at hinact
  push Not at hinact
  exact pair_flip_eq_ten (fun j => b (uCell s j)) (fun j => b (vCell s j))
    (hEps s).symm hinact.1 hinact.2 hflip

/-- Generic counting step: if `k` sites each weigh ≥ `m` and the total
weight is ≤ `W`, then `k·m ≤ W`. -/
lemma card_mul_le_of_site_bound (b : G150 × Fin 2 → ZMod 2)
    (P : Fin 15 → Prop) [DecidablePred P] (m : ℕ)
    (hsite : ∀ s, P s → m ≤ wU b s + wV b s) {W : ℕ}
    (hW : (Finset.univ.filter fun j : G150 × Fin 2 => b j ≠ 0).card ≤ W) :
    (Finset.univ.filter P).card * m ≤ W := by
  have h1 : (Finset.univ.filter P).card * m
      ≤ ∑ s ∈ Finset.univ.filter P, (wU b s + wV b s) := by
    rw [← smul_eq_mul]
    refine Finset.card_nsmul_le_sum _ _ _ fun s hs => ?_
    exact hsite s (Finset.mem_filter.mp hs).2
  have h2 : ∑ s ∈ Finset.univ.filter P, (wU b s + wV b s)
      ≤ ∑ s : Fin 15, (wU b s + wV b s) :=
    Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
  have h3 := chainWeight_eq_sum_sites b
  omega

/-- **Active-site bound**: a weight-≤14 ε-matched chain has ≤ 7 δ-active
sites. -/
theorem active_card_le (b : G150 × Fin 2 → ZMod 2)
    (hEps : ∀ s : Fin 15, hV b s = hU b s)
    (h14 : (Finset.univ.filter fun j : G150 × Fin 2 => b j ≠ 0).card ≤ 14) :
    (Finset.univ.filter (siteActive b)).card ≤ 7 := by
  have := card_mul_le_of_site_bound b (siteActive b) 2
    (site_active_ge_two b hEps) h14
  omega

/-- **Outside-flip bound**: a weight-≤14 ε-matched chain has ≤ 1
δ-inactive site with ε = 1. -/
theorem flip_card_le (b : G150 × Fin 2 → ZMod 2)
    (hEps : ∀ s : Fin 15, hV b s = hU b s)
    (h14 : (Finset.univ.filter fun j : G150 × Fin 2 => b j ≠ 0).card ≤ 14) :
    (Finset.univ.filter fun s => ¬ siteActive b s ∧ hU b s ≠ 0).card ≤ 1 := by
  have := card_mul_le_of_site_bound b
    (fun s => ¬ siteActive b s ∧ hU b s ≠ 0) 10
    (fun s hs => le_of_eq (site_flip_eq_ten b hEps s hs.1 hs.2).symm) h14
  omega

/-! ## The per-fiber weight table -/

/-- Fiber weights by (ε, δ-nibble): index `16·h + (d₀ + 2d₁ + 4d₂ + 8d₃)`. -/
def W5TAB : Array Nat :=
  #[0, 4, 4, 2, 4, 2, 2, 2, 4, 2, 2, 2, 2, 2, 2, 4,
    5, 1, 1, 3, 1, 3, 3, 3, 1, 3, 3, 3, 3, 3, 3, 1]

/-- Nibble value of four δ-bits. -/
def nibVal (d : Fin 4 → ZMod 2) : ℕ :=
  (if d 0 = 1 then 1 else 0) + 2 * (if d 1 = 1 then 1 else 0)
    + 4 * (if d 2 = 1 then 1 else 0) + 8 * (if d 3 = 1 then 1 else 0)

/-- The weight of a fiber is the table entry at its (ε, δ)-index. -/
lemma fiber_weight_eq_table : ∀ t : Fin 5 → ZMod 2,
    (∑ a : Fin 5, if t a ≠ 0 then (1 : ℕ) else 0)
      = W5TAB.getD ((if (∑ j : Fin 5, t j) = 1 then 16 else 0)
          + nibVal (fun n : Fin 4 => t ⟨n.val, by omega⟩ + t 4)) 0 := by
  decide

end Z5Z15F2A6
end BB
end Homological
end Stabilizer
end Quantum
