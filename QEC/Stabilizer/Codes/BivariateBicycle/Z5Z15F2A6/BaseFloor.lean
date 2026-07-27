/-
# A21: the logical base floor `LogicalFloor 8` for the `[[150,8,8]]` base

Discharges the `hbase : coverData.LogicalFloor 8` hypothesis of
`cover300_pauli_distance_eq_16_of_classification` (`Distance.lean`) —
the `d(base) ≥ 8` half of `d(base) = 8`, previously certified offline by
CaDiCaL `UNSAT@7` and now kernel/`native_decide`-checked end to end.

Proof architecture (the split map of
`qec-lab:experiments/bb_lab/notes/A21_analytic_base_floor.md` §3–§4):

* **weights 1,3,5,7** — parity (PAR): `ε(A) = ε(B) = 1` forces
  `|u_L| ≡ |u_R| (mod 2)`;
* **weights 2,4** — the parametric small-cycle bundle
  (`SmallCycleData`, obligations in `BaseFloorChecks.lean`);
* **weight 6** — `weight6_cycle_is_boundary`: every weight-6 cycle is a
  boundary (in fact a generator column `∂₂ δ_t`).  Split map on
  `(|u_L|, |u_R|)`:
  - `(0,6)/(6,0)`: `u_R` (resp. `u_L`) lies in the shared kernel
    `Ann(A) = Ann(B)` (`kerA_classify`/`kerB_classify`,
    `BaseFloorKernel.lean`), whose 15 nonzero elements weigh 40
    (`kerElt_card_ne_six`);
  - `1 ≤ |u_L| ≤ 3`: translation-normalize a left support cell to the
    origin; the coset structure `u_R ∈ wAB ⋆ u_L + kerElt`
    (`rightHalf_coset`) reduces each class to 16 explicit candidates,
    killed (weights 5/4) or classified into the generator column
    (weight 3) by the sweeps `sweepA1/A2/A3` (`BaseFloorSweep.lean`);
  - `|u_R| ∈ {1,2}`: mirror through `u_L ∈ wBA ⋆ u_R + kerElt`
    (`leftHalf_coset`) and `sweepB1/B2`.

The engineering-grade sweeps replace the §3 analytic arguments leaf-for-
leaf (the two-grade doctrine); the analytic flip can land later without
touching this assembly.
-/

import QEC.Stabilizer.Codes.BivariateBicycle.Z5Z15F2A6.BaseFloorChecks
import QEC.Stabilizer.Codes.BivariateBicycle.Z5Z15F2A6.BaseFloorSweep

namespace Quantum
namespace Stabilizer
namespace Homological
namespace BB
namespace Z5Z15F2A6

set_option maxRecDepth 4096

/-! ## The small-cycle bundle (weights 2 and 4) -/

/-- The small-cycle bundle for the `[[150,8,8]]` base (obligations in
`BaseFloorChecks.lean`). -/
def floorData : SmallCycleData G150 where
  A := a150
  B := b150
  epsA := epsA_holds
  epsB := epsB_holds
  check_two := check_two_holds
  check_four := check_four_holds

lemma floorData_complex : floorData.complex = base150Complex := rfl

/-- **Strong small-cycle floor**: every nonzero 1-cycle of the base
complex has weight ≥ 6 — boundaries included.  (Sharp: the generator
columns have weight exactly 6.) -/
theorem strong_floor (u : G150 × Fin 2 → ZMod 2)
    (hcyc : bbBoundary1Fn a150 b150 u = 0) (hne : u ≠ 0) :
    6 ≤ (Finset.univ.filter fun p => u p ≠ 0).card :=
  floorData.cycle_weight_ge_6 u hcyc hne

/-! ## Support bookkeeping -/

/-- A support of size zero means the zero chain. -/
private lemma support_eq_zero (v : G150 → ZMod 2)
    (h : (Finset.univ.filter fun g => v g ≠ 0).card = 0) : v = 0 := by
  funext g
  change v g = 0
  by_contra hg
  have hmem : g ∈ Finset.univ.filter fun g => v g ≠ 0 :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hg⟩
  rw [Finset.card_eq_zero] at h
  rw [h] at hmem
  exact absurd hmem (Finset.notMem_empty _)

/-- A weight-1 chain supported at the origin is the origin indicator. -/
private lemma support_extract₁ (v : G150 → ZMod 2)
    (h1 : (Finset.univ.filter fun g => v g ≠ 0).card = 1) (h0 : v 0 ≠ 0) :
    v = fun g => if g = 0 then 1 else 0 := by
  have hdichot : ∀ a : ZMod 2, a ≠ 0 → a = 1 := by decide
  obtain ⟨x, hS⟩ := Finset.card_eq_one.mp h1
  have h0mem : (0 : G150) ∈ Finset.univ.filter fun g => v g ≠ 0 :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, h0⟩
  rw [hS, Finset.mem_singleton] at h0mem
  funext g
  by_cases hg : g = 0
  · subst hg
    rw [if_pos rfl]
    exact hdichot _ h0
  · rw [if_neg hg]
    by_contra hvg
    have hmem : g ∈ Finset.univ.filter fun g => v g ≠ 0 :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hvg⟩
    rw [hS, Finset.mem_singleton] at hmem
    exact hg (hmem.trans h0mem.symm)

/-- A weight-2 chain through the origin is a two-point indicator. -/
private lemma support_extract₂ (v : G150 → ZMod 2)
    (h2 : (Finset.univ.filter fun g => v g ≠ 0).card = 2) (h0 : v 0 ≠ 0) :
    ∃ t : G150, t ≠ 0 ∧ v = fun g => if g = 0 ∨ g = t then 1 else 0 := by
  have hdichot : ∀ a : ZMod 2, a ≠ 0 → a = 1 := by decide
  obtain ⟨x, y, hxy, hS⟩ := Finset.card_eq_two.mp h2
  have hmem_iff : ∀ g : G150, v g ≠ 0 ↔ (g = x ∨ g = y) := by
    intro g
    constructor
    · intro hg
      have hmem : g ∈ Finset.univ.filter fun g => v g ≠ 0 :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hg⟩
      rw [hS] at hmem
      simpa using hmem
    · intro hg
      have hmem : g ∈ ({x, y} : Finset G150) := by simpa using hg
      rw [← hS] at hmem
      exact (Finset.mem_filter.mp hmem).2
  have build : ∀ a : G150, a ≠ 0 →
      (∀ g : G150, v g ≠ 0 ↔ (g = 0 ∨ g = a)) →
      ∃ t : G150, t ≠ 0 ∧ v = fun g => if g = 0 ∨ g = t then 1 else 0 := by
    intro a ha hiff
    refine ⟨a, ha, ?_⟩
    funext g
    by_cases hcond : g = 0 ∨ g = a
    · rw [if_pos hcond]
      exact hdichot _ ((hiff g).mpr hcond)
    · rw [if_neg hcond]
      by_contra hvg
      exact hcond ((hiff g).mp hvg)
  rcases (hmem_iff 0).mp h0 with h | h
  · subst h
    exact build y (Ne.symm hxy) hmem_iff
  · subst h
    exact build x hxy fun g => (hmem_iff g).trans (by tauto)

/-- A weight-3 chain through the origin is a three-point indicator. -/
private lemma support_extract₃ (v : G150 → ZMod 2)
    (h3 : (Finset.univ.filter fun g => v g ≠ 0).card = 3) (h0 : v 0 ≠ 0) :
    ∃ t₁ t₂ : G150, t₁ ≠ 0 ∧ t₂ ≠ 0 ∧ t₁ ≠ t₂
      ∧ v = fun g => if g = 0 ∨ g = t₁ ∨ g = t₂ then 1 else 0 := by
  have hdichot : ∀ a : ZMod 2, a ≠ 0 → a = 1 := by decide
  obtain ⟨x, y, z, hxy, hxz, hyz, hS⟩ := Finset.card_eq_three.mp h3
  have hmem_iff : ∀ g : G150, v g ≠ 0 ↔ (g = x ∨ g = y ∨ g = z) := by
    intro g
    constructor
    · intro hg
      have hmem : g ∈ Finset.univ.filter fun g => v g ≠ 0 :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hg⟩
      rw [hS] at hmem
      simpa using hmem
    · intro hg
      have hmem : g ∈ ({x, y, z} : Finset G150) := by simpa using hg
      rw [← hS] at hmem
      exact (Finset.mem_filter.mp hmem).2
  have build : ∀ a b : G150, a ≠ 0 → b ≠ 0 → a ≠ b →
      (∀ g : G150, v g ≠ 0 ↔ (g = 0 ∨ g = a ∨ g = b)) →
      ∃ t₁ t₂ : G150, t₁ ≠ 0 ∧ t₂ ≠ 0 ∧ t₁ ≠ t₂
        ∧ v = fun g => if g = 0 ∨ g = t₁ ∨ g = t₂ then 1 else 0 := by
    intro a b ha hb hab hiff
    refine ⟨a, b, ha, hb, hab, ?_⟩
    funext g
    by_cases hcond : g = 0 ∨ g = a ∨ g = b
    · rw [if_pos hcond]
      exact hdichot _ ((hiff g).mpr hcond)
    · rw [if_neg hcond]
      by_contra hvg
      exact hcond ((hiff g).mp hvg)
  rcases (hmem_iff 0).mp h0 with h | h | h
  · subst h
    exact build y z (Ne.symm hxy) (Ne.symm hxz) hyz hmem_iff
  · subst h
    exact build x z hxy (Ne.symm hyz) hxz
      fun g => (hmem_iff g).trans (by tauto)
  · subst h
    exact build x y hxz hyz hxy
      fun g => (hmem_iff g).trans (by tauto)

/-- Chain weight splits over the two blocks. -/
lemma card_support_split (u : G150 × Fin 2 → ZMod 2) :
    (Finset.univ.filter fun p => u p ≠ 0).card
      = (Finset.univ.filter fun g => leftHalf u g ≠ 0).card
        + (Finset.univ.filter fun g => rightHalf u g ≠ 0).card := by
  rw [Finset.card_filter, Finset.card_filter, Finset.card_filter,
    Fintype.sum_prod_type, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [Fin.sum_univ_two]
  rfl

/-! ## The coset structure of a cycle -/

private lemma conv_zero_right (a : G150 → ZMod 2) :
    conv a (0 : G150 → ZMod 2) = 0 := by
  funext g
  simp [conv_apply]

/-- On any cycle, `u_R` lies in the 16-element coset
`wAB ⋆ u_L + kerElt` (the solution set of `A ⋆ u_R = B ⋆ u_L`). -/
lemma rightHalf_coset (u : G150 × Fin 2 → ZMod 2)
    (hcyc : bbBoundary1Fn a150 b150 u = 0) :
    ∃ e1 e2 e3 e4 : ZMod 2,
      rightHalf u = fun g =>
        conv wABf (leftHalf u) g + kerElt e1 e2 e3 e4 g := by
  have hker : conv a150 (rightHalf u + conv wABf (leftHalf u)) = 0 := by
    rw [conv_add_right]
    have hkey : conv a150 (conv wABf (leftHalf u))
        = conv b150 (leftHalf u) := by
      calc conv a150 (conv wABf (leftHalf u))
          = conv (conv a150 wABf) (leftHalf u) :=
            (conv_assoc a150 wABf (leftHalf u)).symm
        _ = conv b150 (leftHalf u) := by rw [conv_a150_wABf]
    rw [hkey]
    funext r
    have hr : conv b150 (leftHalf u) r + conv a150 (rightHalf u) r = 0 :=
      congrFun hcyc r
    change conv a150 (rightHalf u) r + conv b150 (leftHalf u) r = 0
    rw [add_comm]
    exact hr
  have hcls := kerA_classify (rightHalf u + conv wABf (leftHalf u)) hker
  refine ⟨(rightHalf u + conv wABf (leftHalf u)) fc1,
    (rightHalf u + conv wABf (leftHalf u)) fc2,
    (rightHalf u + conv wABf (leftHalf u)) fc3,
    (rightHalf u + conv wABf (leftHalf u)) fc4, ?_⟩
  funext g
  have hg' : rightHalf u g + conv wABf (leftHalf u) g
      = kerElt ((rightHalf u + conv wABf (leftHalf u)) fc1)
          ((rightHalf u + conv wABf (leftHalf u)) fc2)
          ((rightHalf u + conv wABf (leftHalf u)) fc3)
          ((rightHalf u + conv wABf (leftHalf u)) fc4) g :=
    congrFun hcls g
  calc rightHalf u g
      = rightHalf u g
          + (conv wABf (leftHalf u) g + conv wABf (leftHalf u) g) := by
        rw [CharTwo.add_self_eq_zero, add_zero]
    _ = (rightHalf u g + conv wABf (leftHalf u) g)
          + conv wABf (leftHalf u) g := by ring
    _ = kerElt ((rightHalf u + conv wABf (leftHalf u)) fc1)
          ((rightHalf u + conv wABf (leftHalf u)) fc2)
          ((rightHalf u + conv wABf (leftHalf u)) fc3)
          ((rightHalf u + conv wABf (leftHalf u)) fc4) g
          + conv wABf (leftHalf u) g := by rw [hg']
    _ = _ := add_comm _ _

/-- Mirror: on any cycle, `u_L` lies in `wBA ⋆ u_R + kerElt`. -/
lemma leftHalf_coset (u : G150 × Fin 2 → ZMod 2)
    (hcyc : bbBoundary1Fn a150 b150 u = 0) :
    ∃ e1 e2 e3 e4 : ZMod 2,
      leftHalf u = fun g =>
        conv wBAf (rightHalf u) g + kerElt e1 e2 e3 e4 g := by
  have hker : conv b150 (leftHalf u + conv wBAf (rightHalf u)) = 0 := by
    rw [conv_add_right]
    have hkey : conv b150 (conv wBAf (rightHalf u))
        = conv a150 (rightHalf u) := by
      calc conv b150 (conv wBAf (rightHalf u))
          = conv (conv b150 wBAf) (rightHalf u) :=
            (conv_assoc b150 wBAf (rightHalf u)).symm
        _ = conv a150 (rightHalf u) := by rw [conv_b150_wBAf]
    rw [hkey]
    exact hcyc
  have hcls := kerB_classify (leftHalf u + conv wBAf (rightHalf u)) hker
  refine ⟨(leftHalf u + conv wBAf (rightHalf u)) fc1,
    (leftHalf u + conv wBAf (rightHalf u)) fc2,
    (leftHalf u + conv wBAf (rightHalf u)) fc3,
    (leftHalf u + conv wBAf (rightHalf u)) fc4, ?_⟩
  funext g
  have hg' : leftHalf u g + conv wBAf (rightHalf u) g
      = kerElt ((leftHalf u + conv wBAf (rightHalf u)) fc1)
          ((leftHalf u + conv wBAf (rightHalf u)) fc2)
          ((leftHalf u + conv wBAf (rightHalf u)) fc3)
          ((leftHalf u + conv wBAf (rightHalf u)) fc4) g :=
    congrFun hcls g
  calc leftHalf u g
      = leftHalf u g
          + (conv wBAf (rightHalf u) g + conv wBAf (rightHalf u) g) := by
        rw [CharTwo.add_self_eq_zero, add_zero]
    _ = (leftHalf u g + conv wBAf (rightHalf u) g)
          + conv wBAf (rightHalf u) g := by ring
    _ = kerElt ((leftHalf u + conv wBAf (rightHalf u)) fc1)
          ((leftHalf u + conv wBAf (rightHalf u)) fc2)
          ((leftHalf u + conv wBAf (rightHalf u)) fc3)
          ((leftHalf u + conv wBAf (rightHalf u)) fc4) g
          + conv wBAf (rightHalf u) g := by rw [hg']
    _ = _ := add_comm _ _

/-! ## Translation and boundary transfer -/

set_option maxHeartbeats 1000000 in
-- the `rfl` unfolds `base150Complex` through the `bbChainComplex`
-- structure literal and the `LinearMap` coercion — a long but finite
-- definitional chain past the default heartbeat budget
/-- `∂₂` of the packaged complex is the computable `bbBoundary2Fn`
(definitional bridge, stated once so downstream uses can `rw`). -/
private lemma base150_boundary2_eq (f : G150 → ZMod 2) :
    base150Complex.boundary2 f = bbBoundary2Fn a150 b150 f := rfl

/-- Boundaries are stable under chain translation. -/
lemma translate1_mem_boundaries (c : G150) (v : G150 × Fin 2 → ZMod 2)
    (hv : v ∈ base150Complex.boundaries) :
    translate1 c v ∈ base150Complex.boundaries := by
  obtain ⟨f, hf⟩ := (base150Complex.mem_boundaries_iff v).mp hv
  have hf' : bbBoundary2Fn a150 b150 (show G150 → ZMod 2 from f) = v := hf
  refine (base150Complex.mem_boundaries_iff _).mpr
    ⟨show G150 → ZMod 2 from translate c (show G150 → ZMod 2 from f), ?_⟩
  rw [base150_boundary2_eq, bbBoundary2Fn_translate, hf']

/-! ## The weight-6 split map -/

private lemma case_left0 (u : G150 × Fin 2 → ZMod 2)
    (hcyc : bbBoundary1Fn a150 b150 u = 0)
    (hL : (Finset.univ.filter fun g => leftHalf u g ≠ 0).card = 0)
    (hR : (Finset.univ.filter fun g => rightHalf u g ≠ 0).card = 6) :
    False := by
  have hL0 : leftHalf u = 0 := support_eq_zero _ hL
  have hker : conv a150 (rightHalf u) = 0 := by
    funext r
    have hr : conv b150 (leftHalf u) r + conv a150 (rightHalf u) r = 0 :=
      congrFun hcyc r
    rw [hL0, conv_zero_right] at hr
    simpa using hr
  have hcls := kerA_classify (rightHalf u) hker
  have hR6 : (Finset.univ.filter fun g : G150 =>
      kerElt (rightHalf u fc1) (rightHalf u fc2) (rightHalf u fc3)
        (rightHalf u fc4) g ≠ 0).card = 6 := by
    have hset : (Finset.univ.filter fun g : G150 =>
          kerElt (rightHalf u fc1) (rightHalf u fc2) (rightHalf u fc3)
            (rightHalf u fc4) g ≠ 0)
        = Finset.univ.filter fun g => rightHalf u g ≠ 0 := by
      apply Finset.filter_congr
      intro g _
      rw [← hcls]
    rw [hset]
    exact hR
  exact kerElt_card_ne_six _ _ _ _ hR6

private lemma case_left6 (u : G150 × Fin 2 → ZMod 2)
    (hcyc : bbBoundary1Fn a150 b150 u = 0)
    (hL : (Finset.univ.filter fun g => leftHalf u g ≠ 0).card = 6)
    (hR : (Finset.univ.filter fun g => rightHalf u g ≠ 0).card = 0) :
    False := by
  have hR0 : rightHalf u = 0 := support_eq_zero _ hR
  have hker : conv b150 (leftHalf u) = 0 := by
    funext r
    have hr : conv b150 (leftHalf u) r + conv a150 (rightHalf u) r = 0 :=
      congrFun hcyc r
    rw [hR0, conv_zero_right] at hr
    simpa using hr
  have hcls := kerB_classify (leftHalf u) hker
  have hL6 : (Finset.univ.filter fun g : G150 =>
      kerElt (leftHalf u fc1) (leftHalf u fc2) (leftHalf u fc3)
        (leftHalf u fc4) g ≠ 0).card = 6 := by
    have hset : (Finset.univ.filter fun g : G150 =>
          kerElt (leftHalf u fc1) (leftHalf u fc2) (leftHalf u fc3)
            (leftHalf u fc4) g ≠ 0)
        = Finset.univ.filter fun g => leftHalf u g ≠ 0 := by
      apply Finset.filter_congr
      intro g _
      rw [← hcls]
    rw [hset]
    exact hL
  exact kerElt_card_ne_six _ _ _ _ hL6

private lemma case_left1 (u : G150 × Fin 2 → ZMod 2)
    (hcyc : bbBoundary1Fn a150 b150 u = 0)
    (hL : (Finset.univ.filter fun g => leftHalf u g ≠ 0).card = 1)
    (hR : (Finset.univ.filter fun g => rightHalf u g ≠ 0).card = 5) :
    False := by
  obtain ⟨g₀, hg₀mem⟩ := Finset.card_pos.mp
    (show 0 < (Finset.univ.filter fun g => leftHalf u g ≠ 0).card by omega)
  have hg₀ : leftHalf u g₀ ≠ 0 := (Finset.mem_filter.mp hg₀mem).2
  have hcyc' : bbBoundary1Fn a150 b150 (translate1 g₀ u) = 0 := by
    rw [bbBoundary1Fn_translate1, hcyc]
    rfl
  have hL' : (Finset.univ.filter
      fun g => leftHalf (translate1 g₀ u) g ≠ 0).card = 1 := by
    have htrans : (Finset.univ.filter
          fun g => leftHalf (translate1 g₀ u) g ≠ 0).card
        = (Finset.univ.filter fun g => leftHalf u g ≠ 0).card :=
      card_filter_comp_equiv (Equiv.addRight g₀) (fun g => leftHalf u g ≠ 0)
    rw [htrans]
    exact hL
  have hR' : (Finset.univ.filter
      fun g => rightHalf (translate1 g₀ u) g ≠ 0).card = 5 := by
    have htrans : (Finset.univ.filter
          fun g => rightHalf (translate1 g₀ u) g ≠ 0).card
        = (Finset.univ.filter fun g => rightHalf u g ≠ 0).card :=
      card_filter_comp_equiv (Equiv.addRight g₀) (fun g => rightHalf u g ≠ 0)
    rw [htrans]
    exact hR
  have h0' : leftHalf (translate1 g₀ u) 0 ≠ 0 := by
    change u ((0 : G150) + g₀, 0) ≠ 0
    rw [zero_add]
    exact hg₀
  have hind := support_extract₁ (leftHalf (translate1 g₀ u)) hL' h0'
  obtain ⟨e1, e2, e3, e4, hcand⟩ := rightHalf_coset (translate1 g₀ u) hcyc'
  rw [hind, conv_indicator₁] at hcand
  have hR5 : (Finset.univ.filter fun g : G150 =>
      wABf g + kerElt e1 e2 e3 e4 g ≠ 0).card = 5 := by
    have hset : (Finset.univ.filter
          fun g => rightHalf (translate1 g₀ u) g ≠ 0)
        = Finset.univ.filter fun g : G150 =>
            wABf g + kerElt e1 e2 e3 e4 g ≠ 0 := by
      apply Finset.filter_congr
      intro g _
      rw [hcand]
    rw [← hset]
    exact hR'
  exact sweepA1 e1 e2 e3 e4 hR5

private lemma case_left2 (u : G150 × Fin 2 → ZMod 2)
    (hcyc : bbBoundary1Fn a150 b150 u = 0)
    (hL : (Finset.univ.filter fun g => leftHalf u g ≠ 0).card = 2)
    (hR : (Finset.univ.filter fun g => rightHalf u g ≠ 0).card = 4) :
    False := by
  obtain ⟨g₀, hg₀mem⟩ := Finset.card_pos.mp
    (show 0 < (Finset.univ.filter fun g => leftHalf u g ≠ 0).card by omega)
  have hg₀ : leftHalf u g₀ ≠ 0 := (Finset.mem_filter.mp hg₀mem).2
  have hcyc' : bbBoundary1Fn a150 b150 (translate1 g₀ u) = 0 := by
    rw [bbBoundary1Fn_translate1, hcyc]
    rfl
  have hL' : (Finset.univ.filter
      fun g => leftHalf (translate1 g₀ u) g ≠ 0).card = 2 := by
    have htrans : (Finset.univ.filter
          fun g => leftHalf (translate1 g₀ u) g ≠ 0).card
        = (Finset.univ.filter fun g => leftHalf u g ≠ 0).card :=
      card_filter_comp_equiv (Equiv.addRight g₀) (fun g => leftHalf u g ≠ 0)
    rw [htrans]
    exact hL
  have hR' : (Finset.univ.filter
      fun g => rightHalf (translate1 g₀ u) g ≠ 0).card = 4 := by
    have htrans : (Finset.univ.filter
          fun g => rightHalf (translate1 g₀ u) g ≠ 0).card
        = (Finset.univ.filter fun g => rightHalf u g ≠ 0).card :=
      card_filter_comp_equiv (Equiv.addRight g₀) (fun g => rightHalf u g ≠ 0)
    rw [htrans]
    exact hR
  have h0' : leftHalf (translate1 g₀ u) 0 ≠ 0 := by
    change u ((0 : G150) + g₀, 0) ≠ 0
    rw [zero_add]
    exact hg₀
  obtain ⟨t, ht, hind⟩ := support_extract₂ (leftHalf (translate1 g₀ u)) hL' h0'
  obtain ⟨e1, e2, e3, e4, hcand⟩ := rightHalf_coset (translate1 g₀ u) hcyc'
  rw [hind, conv_indicator₂ wABf t ht] at hcand
  have hR4 : (Finset.univ.filter fun g : G150 =>
      wABf g + wABf (g - t) + kerElt e1 e2 e3 e4 g ≠ 0).card = 4 := by
    have hset : (Finset.univ.filter
          fun g => rightHalf (translate1 g₀ u) g ≠ 0)
        = Finset.univ.filter fun g : G150 =>
            wABf g + wABf (g - t) + kerElt e1 e2 e3 e4 g ≠ 0 := by
      apply Finset.filter_congr
      intro g _
      rw [hcand]
    rw [← hset]
    exact hR'
  exact sweepA2 t e1 e2 e3 e4 hR4

private lemma case_left3 (u : G150 × Fin 2 → ZMod 2)
    (hcyc : bbBoundary1Fn a150 b150 u = 0)
    (hL : (Finset.univ.filter fun g => leftHalf u g ≠ 0).card = 3)
    (hR : (Finset.univ.filter fun g => rightHalf u g ≠ 0).card = 3) :
    u ∈ base150Complex.boundaries := by
  obtain ⟨g₀, hg₀mem⟩ := Finset.card_pos.mp
    (show 0 < (Finset.univ.filter fun g => leftHalf u g ≠ 0).card by omega)
  have hg₀ : leftHalf u g₀ ≠ 0 := (Finset.mem_filter.mp hg₀mem).2
  have hcyc' : bbBoundary1Fn a150 b150 (translate1 g₀ u) = 0 := by
    rw [bbBoundary1Fn_translate1, hcyc]
    rfl
  have hL' : (Finset.univ.filter
      fun g => leftHalf (translate1 g₀ u) g ≠ 0).card = 3 := by
    have htrans : (Finset.univ.filter
          fun g => leftHalf (translate1 g₀ u) g ≠ 0).card
        = (Finset.univ.filter fun g => leftHalf u g ≠ 0).card :=
      card_filter_comp_equiv (Equiv.addRight g₀) (fun g => leftHalf u g ≠ 0)
    rw [htrans]
    exact hL
  have hR' : (Finset.univ.filter
      fun g => rightHalf (translate1 g₀ u) g ≠ 0).card = 3 := by
    have htrans : (Finset.univ.filter
          fun g => rightHalf (translate1 g₀ u) g ≠ 0).card
        = (Finset.univ.filter fun g => rightHalf u g ≠ 0).card :=
      card_filter_comp_equiv (Equiv.addRight g₀) (fun g => rightHalf u g ≠ 0)
    rw [htrans]
    exact hR
  have h0' : leftHalf (translate1 g₀ u) 0 ≠ 0 := by
    change u ((0 : G150) + g₀, 0) ≠ 0
    rw [zero_add]
    exact hg₀
  obtain ⟨t₁, t₂, ht1, ht2, ht12, hind⟩ :=
    support_extract₃ (leftHalf (translate1 g₀ u)) hL' h0'
  obtain ⟨e1, e2, e3, e4, hcand⟩ := rightHalf_coset (translate1 g₀ u) hcyc'
  rw [hind, conv_indicator₃ wABf t₁ t₂ ht1 ht2 ht12] at hcand
  have hR3 : (Finset.univ.filter fun g : G150 =>
      wABf g + wABf (g - t₁) + wABf (g - t₂)
        + kerElt e1 e2 e3 e4 g ≠ 0).card = 3 := by
    have hset : (Finset.univ.filter
          fun g => rightHalf (translate1 g₀ u) g ≠ 0)
        = Finset.univ.filter fun g : G150 =>
            wABf g + wABf (g - t₁) + wABf (g - t₂)
              + kerElt e1 e2 e3 e4 g ≠ 0 := by
      apply Finset.filter_congr
      intro g _
      rw [hcand]
    rw [← hset]
    exact hR'
  obtain ⟨t, hgenL, hgenR⟩ := sweepA3 t₁ t₂ e1 e2 e3 e4 hR3
  -- the normalized cycle is the generator column `∂₂ δ_t`
  have hbd : translate1 g₀ u = bbBoundary2Fn a150 b150 (Pi.single t 1) := by
    funext p
    obtain ⟨h, j⟩ := p
    have hAh : conv a150 (Pi.single t 1) h = a150 (h - t) := by
      rw [conv_comm a150 (Pi.single t 1)]
      exact conv_single_left_apply t a150 h
    have hBh : conv b150 (Pi.single t 1) h = b150 (h - t) := by
      rw [conv_comm b150 (Pi.single t 1)]
      exact conv_single_left_apply t b150 h
    by_cases hj : j = 0
    · subst hj
      have hLh : leftHalf (translate1 g₀ u) h = a150 (h - t) := by
        rw [hind]
        exact hgenL h
      change leftHalf (translate1 g₀ u) h = conv a150 (Pi.single t 1) h
      rw [hLh, hAh]
    · have hj1 : j = 1 := by omega
      subst hj1
      have hRh : rightHalf (translate1 g₀ u) h = b150 (h - t) := by
        rw [hcand]
        exact hgenR h
      change rightHalf (translate1 g₀ u) h = conv b150 (Pi.single t 1) h
      rw [hRh, hBh]
  have hmem : translate1 g₀ u ∈ base150Complex.boundaries := by
    refine (base150Complex.mem_boundaries_iff _).mpr
      ⟨show G150 → ZMod 2 from Pi.single t 1, ?_⟩
    rw [base150_boundary2_eq, hbd]
  have hu : u = translate1 (-g₀) (translate1 g₀ u) := by
    funext p
    change u p = u (p.1 + -g₀ + g₀, p.2)
    rw [show p.1 + -g₀ + g₀ = p.1 from by abel]
  rw [hu]
  exact translate1_mem_boundaries (-g₀) (translate1 g₀ u) hmem

private lemma case_left4 (u : G150 × Fin 2 → ZMod 2)
    (hcyc : bbBoundary1Fn a150 b150 u = 0)
    (hL : (Finset.univ.filter fun g => leftHalf u g ≠ 0).card = 4)
    (hR : (Finset.univ.filter fun g => rightHalf u g ≠ 0).card = 2) :
    False := by
  obtain ⟨g₀, hg₀mem⟩ := Finset.card_pos.mp
    (show 0 < (Finset.univ.filter fun g => rightHalf u g ≠ 0).card by omega)
  have hg₀ : rightHalf u g₀ ≠ 0 := (Finset.mem_filter.mp hg₀mem).2
  have hcyc' : bbBoundary1Fn a150 b150 (translate1 g₀ u) = 0 := by
    rw [bbBoundary1Fn_translate1, hcyc]
    rfl
  have hL' : (Finset.univ.filter
      fun g => leftHalf (translate1 g₀ u) g ≠ 0).card = 4 := by
    have htrans : (Finset.univ.filter
          fun g => leftHalf (translate1 g₀ u) g ≠ 0).card
        = (Finset.univ.filter fun g => leftHalf u g ≠ 0).card :=
      card_filter_comp_equiv (Equiv.addRight g₀) (fun g => leftHalf u g ≠ 0)
    rw [htrans]
    exact hL
  have hR' : (Finset.univ.filter
      fun g => rightHalf (translate1 g₀ u) g ≠ 0).card = 2 := by
    have htrans : (Finset.univ.filter
          fun g => rightHalf (translate1 g₀ u) g ≠ 0).card
        = (Finset.univ.filter fun g => rightHalf u g ≠ 0).card :=
      card_filter_comp_equiv (Equiv.addRight g₀) (fun g => rightHalf u g ≠ 0)
    rw [htrans]
    exact hR
  have h0' : rightHalf (translate1 g₀ u) 0 ≠ 0 := by
    change u ((0 : G150) + g₀, 1) ≠ 0
    rw [zero_add]
    exact hg₀
  obtain ⟨t, ht, hind⟩ := support_extract₂ (rightHalf (translate1 g₀ u)) hR' h0'
  obtain ⟨e1, e2, e3, e4, hcand⟩ := leftHalf_coset (translate1 g₀ u) hcyc'
  rw [hind, conv_indicator₂ wBAf t ht] at hcand
  have hL4 : (Finset.univ.filter fun g : G150 =>
      wBAf g + wBAf (g - t) + kerElt e1 e2 e3 e4 g ≠ 0).card = 4 := by
    have hset : (Finset.univ.filter
          fun g => leftHalf (translate1 g₀ u) g ≠ 0)
        = Finset.univ.filter fun g : G150 =>
            wBAf g + wBAf (g - t) + kerElt e1 e2 e3 e4 g ≠ 0 := by
      apply Finset.filter_congr
      intro g _
      rw [hcand]
    rw [← hset]
    exact hL'
  exact sweepB2 t e1 e2 e3 e4 hL4

private lemma case_left5 (u : G150 × Fin 2 → ZMod 2)
    (hcyc : bbBoundary1Fn a150 b150 u = 0)
    (hL : (Finset.univ.filter fun g => leftHalf u g ≠ 0).card = 5)
    (hR : (Finset.univ.filter fun g => rightHalf u g ≠ 0).card = 1) :
    False := by
  obtain ⟨g₀, hg₀mem⟩ := Finset.card_pos.mp
    (show 0 < (Finset.univ.filter fun g => rightHalf u g ≠ 0).card by omega)
  have hg₀ : rightHalf u g₀ ≠ 0 := (Finset.mem_filter.mp hg₀mem).2
  have hcyc' : bbBoundary1Fn a150 b150 (translate1 g₀ u) = 0 := by
    rw [bbBoundary1Fn_translate1, hcyc]
    rfl
  have hL' : (Finset.univ.filter
      fun g => leftHalf (translate1 g₀ u) g ≠ 0).card = 5 := by
    have htrans : (Finset.univ.filter
          fun g => leftHalf (translate1 g₀ u) g ≠ 0).card
        = (Finset.univ.filter fun g => leftHalf u g ≠ 0).card :=
      card_filter_comp_equiv (Equiv.addRight g₀) (fun g => leftHalf u g ≠ 0)
    rw [htrans]
    exact hL
  have hR' : (Finset.univ.filter
      fun g => rightHalf (translate1 g₀ u) g ≠ 0).card = 1 := by
    have htrans : (Finset.univ.filter
          fun g => rightHalf (translate1 g₀ u) g ≠ 0).card
        = (Finset.univ.filter fun g => rightHalf u g ≠ 0).card :=
      card_filter_comp_equiv (Equiv.addRight g₀) (fun g => rightHalf u g ≠ 0)
    rw [htrans]
    exact hR
  have h0' : rightHalf (translate1 g₀ u) 0 ≠ 0 := by
    change u ((0 : G150) + g₀, 1) ≠ 0
    rw [zero_add]
    exact hg₀
  have hind := support_extract₁ (rightHalf (translate1 g₀ u)) hR' h0'
  obtain ⟨e1, e2, e3, e4, hcand⟩ := leftHalf_coset (translate1 g₀ u) hcyc'
  rw [hind, conv_indicator₁] at hcand
  have hL5 : (Finset.univ.filter fun g : G150 =>
      wBAf g + kerElt e1 e2 e3 e4 g ≠ 0).card = 5 := by
    have hset : (Finset.univ.filter
          fun g => leftHalf (translate1 g₀ u) g ≠ 0)
        = Finset.univ.filter fun g : G150 =>
            wBAf g + kerElt e1 e2 e3 e4 g ≠ 0 := by
      apply Finset.filter_congr
      intro g _
      rw [hcand]
    rw [← hset]
    exact hL'
  exact sweepB1 e1 e2 e3 e4 hL5

/-- **Weight-6 classification**: every weight-6 1-cycle of the base
complex is a boundary (in fact a generator column `∂₂ δ_t`). -/
theorem weight6_cycle_is_boundary (u : G150 × Fin 2 → ZMod 2)
    (hcyc : bbBoundary1Fn a150 b150 u = 0)
    (hw : (Finset.univ.filter fun p => u p ≠ 0).card = 6) :
    u ∈ base150Complex.boundaries := by
  have hsplit := card_support_split u
  rw [hw] at hsplit
  have hcases :
      ((Finset.univ.filter fun g => leftHalf u g ≠ 0).card = 0
        ∧ (Finset.univ.filter fun g => rightHalf u g ≠ 0).card = 6)
      ∨ ((Finset.univ.filter fun g => leftHalf u g ≠ 0).card = 1
        ∧ (Finset.univ.filter fun g => rightHalf u g ≠ 0).card = 5)
      ∨ ((Finset.univ.filter fun g => leftHalf u g ≠ 0).card = 2
        ∧ (Finset.univ.filter fun g => rightHalf u g ≠ 0).card = 4)
      ∨ ((Finset.univ.filter fun g => leftHalf u g ≠ 0).card = 3
        ∧ (Finset.univ.filter fun g => rightHalf u g ≠ 0).card = 3)
      ∨ ((Finset.univ.filter fun g => leftHalf u g ≠ 0).card = 4
        ∧ (Finset.univ.filter fun g => rightHalf u g ≠ 0).card = 2)
      ∨ ((Finset.univ.filter fun g => leftHalf u g ≠ 0).card = 5
        ∧ (Finset.univ.filter fun g => rightHalf u g ≠ 0).card = 1)
      ∨ ((Finset.univ.filter fun g => leftHalf u g ≠ 0).card = 6
        ∧ (Finset.univ.filter fun g => rightHalf u g ≠ 0).card = 0) := by
    omega
  rcases hcases with h | h | h | h | h | h | h
  · exact (case_left0 u hcyc h.1 h.2).elim
  · exact (case_left1 u hcyc h.1 h.2).elim
  · exact (case_left2 u hcyc h.1 h.2).elim
  · exact case_left3 u hcyc h.1 h.2
  · exact (case_left4 u hcyc h.1 h.2).elim
  · exact (case_left5 u hcyc h.1 h.2).elim
  · exact (case_left6 u hcyc h.1 h.2).elim

/-! ## Assembly: the logical floor -/

/-- `chainWeight` on the cover bundle's base complex, in raw `Finset`
form (definitional; the `maxRecDepth` bump covers the projection
chain). -/
lemma baseComplex_chainWeight_eq (u : G150 × Fin 2 → ZMod 2) :
    coverData.baseComplex.chainWeight u
      = (Finset.univ.filter fun p : G150 × Fin 2 => u p ≠ 0).card := rfl

/-- **The logical base floor**: every non-boundary 1-cycle of the
`[[150,8,8]]` base complex has weight ≥ 8.  This is the
`hbase` hypothesis of `cover300_pauli_distance_eq_16_of_classification`.

Proof: parity kills odd weights; the strong small-cycle floor kills
nonzero weights ≤ 5; the weight-6 classification shows weight-6 cycles
are boundaries; hence a non-boundary cycle weighs ≥ 8. -/
theorem logicalFloor_8 : coverData.LogicalFloor 8 := by
  intro u hcyc hnb
  rw [baseComplex_chainWeight_eq]
  by_contra hlt
  push Not at hlt
  have hne : u ≠ 0 := by
    rintro rfl
    exact hnb (zero_mem _)
  have hcyc' : bbBoundary1Fn a150 b150 u = 0 := hcyc
  have h6 : 6 ≤ (Finset.univ.filter fun p => u p ≠ 0).card :=
    strong_floor u hcyc' hne
  have hpar : (Finset.univ.filter fun p => u p ≠ 0).card % 2 = 0 :=
    floorData.cycle_weight_even u hcyc'
  have hw : (Finset.univ.filter fun p => u p ≠ 0).card = 6 := by omega
  -- `coverData.baseComplex = base150Complex` is definitional, so the
  -- boundary memberships coincide (no `rw` — the membership type depends
  -- on the complex, which breaks the rewrite motive).
  exact hnb (show u ∈ coverData.baseComplex.boundaries from
    weight6_cycle_is_boundary u hcyc' hw)

end Z5Z15F2A6
end BB
end Homological
end Stabilizer
end Quantum
