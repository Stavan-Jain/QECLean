/-
# Phase 2 (tier 1): d(base) ≥ 6 — discharging `BaseDistanceGe6`

The small-cycle theorem for the bb72 base complex, in its strong form:
**every nonzero 1-cycle has weight ≥ 6** (A4 Theorem A).  Consequences
assembled here:

* `base_distance_ge_6 : BaseDistanceGe6` — the Phase-1 hypothesis (A) is a
  theorem;
* `base_chain_distance_eq_6` — chain-level d(base) = 6 (Corollary A′; the
  weight-6 witness is `u*` from `Witness.lean`);
* **unconditional d(gross) ≥ 6** at the chain, dual-chain, and Pauli levels
  (A4 Theorem B): the safe and nonzero-dangerous sectors bound by 6 via the
  strong small-cycle theorem applied to `p(v)`, and the `b = 0` sector by 12
  via the Phase-1 rung.

## Proof shape (tier 1: verified-finite leaf, analytic frame)

Two analytic inputs are formalized here: the translation symmetry (`∂₁` is
translation-equivariant, so any small cycle can be normalized to put a
support point at group-origin) and **the parity lemma (PAR)** of A4 §4 —
cycles have even weight, by applying the augmentation `ε` to the cycle
condition (`ε(A) = ε(B) = 1`).  Parity kills all odd-weight supports, so
the normalized finite sweep only covers `((0,0), b)` plus exactly 1 or 3
further qubits — `2·(C(71,1) + C(71,3)) ≈ 1.2·10⁵` cases, swept by
`native_decide` (`smallCycleCheckAux_*`) with the boundary evaluated
through the sparse syndrome form `syndAt` (the hand-proven bridge
`bbBoundary1Fn_indicator` turns `∂₁(χ_S) = 0` into 36 few-term sums).
Replacing this finite leaf with the per-split CRT-engine analysis of
A4 §§3–4 (the fully analytic Theorem A) is the tier-2 upgrade; the
statement `base_distance_ge_6` is already in its final form, so the
upgrade is invisible downstream.

## Convention bridge (lab notes → repo)

Repo convention: `∂₂ f = (A⋆f | B⋆f)`, `∂₁ c = B⋆c_L + A⋆c_R`; cycle
condition `B⋆v_L = A⋆v_R`.  **Repo-left = lab-right.**
-/

import QEC.Stabilizer.Codes.BivariateBicycle.Assembly

namespace Quantum
namespace Stabilizer
namespace Homological
namespace BB

open scoped BigOperators

/-! ## Support plumbing -/

/-- A `ZMod 2` chain is the indicator function of its support. -/
lemma eq_indicator_support {I : Type} [Fintype I] [DecidableEq I]
    (u : I → ZMod 2) :
    u = fun p => if p ∈ (Finset.univ.filter fun q => u q ≠ 0) then 1 else 0 := by
  have hdichot : ∀ a : ZMod 2, a ≠ 0 → a = 1 := by decide
  funext p
  by_cases h : u p = 0
  · simp [h]
  · simp [hdichot _ h]

/-- Translation preserves support size (1-chains over the base group). -/
lemma card_support_translate1 (c : BaseGroup) (u : BaseGroup × Fin 2 → ZMod 2) :
    (Finset.univ.filter fun p => translate1 c u p ≠ 0).card
      = (Finset.univ.filter fun p => u p ≠ 0).card :=
  card_filter_comp_equiv ((Equiv.addRight c).prodCongr (Equiv.refl (Fin 2)))
    (fun p => u p ≠ 0)

/-! ## The sparse syndrome form

For an indicator chain `χ_S`, the boundary `∂₁(χ_S)(h)` is the
`|S|`-term sum `syndAt S h` — far cheaper to evaluate than the
convolution form during the `native_decide` sweep. -/

/-- The syndrome contribution of a single qubit at a check position. -/
def termAt (q : BaseGroup × Fin 2) (h : BaseGroup) : ZMod 2 :=
  if q.2 = 0 then baseB (h - q.1) else baseA (h - q.1)

/-- Sparse syndrome of a support set at a check position. -/
def syndAt (S : Finset (BaseGroup × Fin 2)) (h : BaseGroup) : ZMod 2 :=
  ∑ q ∈ S, termAt q h

/-- `∂₁` of a point mass, in either block. -/
lemma bbBoundary1Fn_single_point (q : BaseGroup × Fin 2) (h : BaseGroup) :
    bbBoundary1Fn baseA baseB (Pi.single q 1) h = termAt q h := by
  obtain ⟨g, j⟩ := q
  by_cases hj : j = 0
  · subst hj
    exact bbBoundary1Fn_single_left baseA baseB g h
  · have hj1 : j = 1 := by omega
    subst hj1
    exact bbBoundary1Fn_single_right baseA baseB g h

/-- Indicator of `insert` decomposes as indicator plus a point mass. -/
lemma indicator_insert {I : Type} [DecidableEq I] (a : I) (S : Finset I)
    (ha : a ∉ S) :
    (fun p => if p ∈ insert a S then (1 : ZMod 2) else 0)
      = (fun p => if p ∈ S then 1 else 0) + Pi.single a 1 := by
  funext p
  by_cases hp : p = a
  · subst hp
    simp [Finset.mem_insert, ha]
  · simp [Finset.mem_insert, hp]

/-- **The sparse-syndrome bridge**: on indicator chains, `∂₁` evaluates to
`syndAt`. -/
lemma bbBoundary1Fn_indicator (S : Finset (BaseGroup × Fin 2)) :
    ∀ h : BaseGroup,
      bbBoundary1Fn baseA baseB (fun q => if q ∈ S then 1 else 0) h
        = syndAt S h := by
  classical
  induction S using Finset.induction with
  | empty =>
      intro h
      have hzero : (fun q : BaseGroup × Fin 2 =>
          if q ∈ (∅ : Finset (BaseGroup × Fin 2)) then (1 : ZMod 2) else 0)
          = 0 := by
        funext q
        simp
      rw [hzero]
      simp [bbBoundary1Fn, leftHalf, rightHalf, conv_apply, syndAt]
  | insert a S ha ih =>
      intro h
      rw [indicator_insert a S ha, bbBoundary1Fn_add, Pi.add_apply, ih h,
        bbBoundary1Fn_single_point]
      simp only [syndAt]
      rw [Finset.sum_insert ha]
      ring

/-! ## The parity lemma (PAR)

Every cycle has even weight: applying the augmentation `ε(w) = Σ_g w(g)`
to `B⋆u_L + A⋆u_R = 0` gives `ε(u_L) + ε(u_R) = 0` since
`ε(A) = ε(B) = 1`.  This kills all odd-weight supports analytically, so the
finite sweep below only needs the (normalized) weight-2 and weight-4
configurations. -/

/-- The augmentation is multiplicative on convolutions. -/
lemma sum_conv {G : Type} [Fintype G] [AddCommGroup G] (a b : G → ZMod 2) :
    ∑ g : G, conv a b g = (∑ h : G, a h) * (∑ g : G, b g) := by
  simp only [conv_apply]
  rw [Finset.sum_comm]
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [← Finset.mul_sum]
  congr 1
  exact Equiv.sum_comp (Equiv.subRight h) b

/-- **(PAR)**: cycles of the base complex have zero total parity. -/
lemma cycle_total_parity (u : BaseGroup × Fin 2 → ZMod 2)
    (hcyc : bbBoundary1Fn baseA baseB u = 0) :
    ∑ p : BaseGroup × Fin 2, u p = 0 := by
  have h0 : ∑ g : BaseGroup, bbBoundary1Fn baseA baseB u g = 0 := by
    rw [hcyc]
    simp
  have hexp : ∑ g : BaseGroup, bbBoundary1Fn baseA baseB u g
      = (∑ h : BaseGroup, baseB h) * (∑ g : BaseGroup, leftHalf u g)
        + (∑ h : BaseGroup, baseA h) * (∑ g : BaseGroup, rightHalf u g) := by
    rw [show (fun g => bbBoundary1Fn baseA baseB u g)
        = fun g => conv baseB (leftHalf u) g + conv baseA (rightHalf u) g
      from rfl]
    rw [Finset.sum_add_distrib, sum_conv, sum_conv]
  have hA : (∑ h : BaseGroup, baseA h) = 1 := by native_decide
  have hB : (∑ h : BaseGroup, baseB h) = 1 := by native_decide
  rw [hexp, hA, hB, one_mul, one_mul] at h0
  rw [Fintype.sum_prod_type]
  calc ∑ g : BaseGroup, ∑ j : Fin 2, u (g, j)
      = ∑ g : BaseGroup, (u (g, 0) + u (g, 1)) := by
        refine Finset.sum_congr rfl fun g _ => ?_
        exact Fin.sum_univ_two _
    _ = (∑ g : BaseGroup, leftHalf u g) + (∑ g : BaseGroup, rightHalf u g) :=
        Finset.sum_add_distrib
    _ = 0 := h0

/-- Cycles have even weight. -/
lemma cycle_weight_even (u : BaseGroup × Fin 2 → ZMod 2)
    (hcyc : bbBoundary1Fn baseA baseB u = 0) :
    (Finset.univ.filter fun p => u p ≠ 0).card % 2 = 0 := by
  have hdichot : ∀ a : ZMod 2, a ≠ 0 → a = 1 := by decide
  have hcast : (((Finset.univ.filter fun p => u p ≠ 0).card : ℕ) : ZMod 2)
      = ∑ p : BaseGroup × Fin 2, u p := by
    rw [← Finset.sum_filter_ne_zero Finset.univ]
    rw [Finset.sum_congr rfl fun p hp => hdichot (u p)
      (Finset.mem_filter.mp hp).2]
    rw [Finset.sum_const, nsmul_eq_mul, mul_one]
  have h0 := cycle_total_parity u hcyc
  rw [← hcast] at h0
  have heven := ZMod.natCast_eq_zero_iff_even.mp h0
  exact Nat.even_iff.mp heven

/-! ## The normalized finite check

Every normalized configuration — `((0,0), b)` plus one or three further
qubits (by (PAR) those are the only sizes a small cycle could have) — has a
nonzero syndrome.  Quantified over plain tuples (no `Finset.powersetCard`
in the decided statement: its compiled decision procedure is prohibitively
expensive), so repeated/colliding tuples are allowed; the statements remain
true since any such chain is nonzero of weight ≤ 4. -/

/-- No normalized weight-2 chain is a cycle. -/
lemma smallCycleCheck_two : ∀ b : Fin 2, ∀ q : BaseGroup × Fin 2,
    q ≠ (((0, 0) : BaseGroup), b) →
    ∃ h : BaseGroup,
      termAt ((((0, 0) : BaseGroup)), b) h + termAt q h ≠ 0 := by
  native_decide

/-- No normalized weight-≤4 chain containing the origin qubit is a cycle
(disjunctive form: the hypotheses `qᵢ ≠ origin` are folded into the
conclusion so the `Decidable` instance synthesizes structurally). -/
lemma smallCycleCheck_four : ∀ b : Fin 2, ∀ q₁ q₂ q₃ : BaseGroup × Fin 2,
    q₁ = (((0, 0) : BaseGroup), b) ∨ q₂ = (((0, 0) : BaseGroup), b) ∨
    q₃ = (((0, 0) : BaseGroup), b) ∨
    ∃ h : BaseGroup,
      termAt ((((0, 0) : BaseGroup)), b) h + termAt q₁ h + termAt q₂ h
        + termAt q₃ h ≠ 0 := by
  native_decide

/-! ## The small-cycle theorem (strong form) -/

/-- **Small-cycle theorem** (A4 Theorem A, repo form): every nonzero 1-cycle
of the bb72 base complex has weight ≥ 6 — boundaries included. -/
theorem base_cycle_weight_ge_6
    (u : BaseGroup × Fin 2 → ZMod 2)
    (hcyc : bbBoundary1Fn baseA baseB u = 0) (hne : u ≠ 0) :
    6 ≤ (Finset.univ.filter fun p => u p ≠ 0).card := by
  by_contra hlt
  push Not at hlt
  -- a support point
  have hex : ∃ p, u p ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hne (funext hall)
  obtain ⟨p, hp⟩ := hex
  -- normalize its group coordinate to the origin
  have hp' : translate1 p.1 u ((0, 0), p.2) ≠ 0 := by
    change u ((0 : BaseGroup) + p.1, p.2) ≠ 0
    rw [zero_add]
    exact hp
  have hcyc' : bbBoundary1Fn baseA baseB (translate1 p.1 u) = 0 := by
    rw [bbBoundary1Fn_translate1, hcyc]
    rfl
  have hcard' :
      (Finset.univ.filter fun q => translate1 p.1 u q ≠ 0).card ≤ 5 := by
    rw [card_support_translate1]
    omega
  -- decompose the normalized support
  have hxS : (((0, 0) : BaseGroup), p.2)
      ∈ Finset.univ.filter fun q => translate1 p.1 u q ≠ 0 :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp'⟩
  have hxs : (((0, 0) : BaseGroup), p.2)
      ∉ (Finset.univ.filter fun q => translate1 p.1 u q ≠ 0).erase
          (((0, 0) : BaseGroup), p.2) :=
    Finset.notMem_erase _ _
  have hins : insert ((((0, 0) : BaseGroup)), p.2)
      ((Finset.univ.filter fun q => translate1 p.1 u q ≠ 0).erase
        (((0, 0) : BaseGroup), p.2))
      = Finset.univ.filter fun q => translate1 p.1 u q ≠ 0 :=
    Finset.insert_erase hxS
  -- (PAR): the normalized support has even size, and it is nonempty
  have hpar := cycle_weight_even (translate1 p.1 u) hcyc'
  have hpos : 0 < (Finset.univ.filter fun q => translate1 p.1 u q ≠ 0).card :=
    Finset.card_pos.mpr ⟨_, hxS⟩
  have hscard :
      ((Finset.univ.filter fun q => translate1 p.1 u q ≠ 0).erase
        (((0, 0) : BaseGroup), p.2)).card = 1
      ∨ ((Finset.univ.filter fun q => translate1 p.1 u q ≠ 0).erase
        (((0, 0) : BaseGroup), p.2)).card = 3 := by
    rw [Finset.card_erase_of_mem hxS]
    omega
  -- the normalized chain is the indicator of `insert x s`
  have hind : translate1 p.1 u
      = fun q => if q ∈ insert ((((0, 0) : BaseGroup)), p.2)
          ((Finset.univ.filter fun q => translate1 p.1 u q ≠ 0).erase
            (((0, 0) : BaseGroup), p.2)) then 1 else 0 := by
    rw [hins]
    exact eq_indicator_support (translate1 p.1 u)
  -- contradict the finite check
  have hcheck : ∃ h : BaseGroup, syndAt (insert ((((0, 0) : BaseGroup)), p.2)
      ((Finset.univ.filter fun q => translate1 p.1 u q ≠ 0).erase
        (((0, 0) : BaseGroup), p.2))) h ≠ 0 := by
    rcases hscard with hk | hk
    · obtain ⟨q, hq⟩ := Finset.card_eq_one.mp hk
      rw [hq] at hxs
      rw [Finset.mem_singleton] at hxs
      obtain ⟨h, hh⟩ := smallCycleCheck_two p.2 q (Ne.symm hxs)
      refine ⟨h, ?_⟩
      rw [hq, syndAt,
        Finset.sum_insert (by rw [Finset.mem_singleton]; exact hxs),
        Finset.sum_singleton]
      exact hh
    · obtain ⟨q₁, q₂, q₃, h12, h13, h23, hs3⟩ := Finset.card_eq_three.mp hk
      rw [hs3, Finset.mem_insert, Finset.mem_insert,
        Finset.mem_singleton] at hxs
      push Not at hxs
      obtain ⟨hx1, hx2, hx3⟩ := hxs
      have hfour := smallCycleCheck_four p.2 q₁ q₂ q₃
      rcases hfour with hc | hc | hc | ⟨h, hh⟩
      · exact absurd hc.symm hx1
      · exact absurd hc.symm hx2
      · exact absurd hc.symm hx3
      refine ⟨h, ?_⟩
      rw [hs3, syndAt,
        Finset.sum_insert (by
          rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton]
          push Not
          exact ⟨hx1, hx2, hx3⟩),
        Finset.sum_insert (by
          rw [Finset.mem_insert, Finset.mem_singleton]
          push Not
          exact ⟨h12, h13⟩),
        Finset.sum_insert (by rw [Finset.mem_singleton]; exact h23),
        Finset.sum_singleton, ← add_assoc, ← add_assoc]
      exact hh
  obtain ⟨h, hsynd⟩ := hcheck
  apply hsynd
  rw [← bbBoundary1Fn_indicator, ← hind]
  exact congrFun hcyc' h

/-! ## `BaseDistanceGe6` is a theorem -/

/-- The Phase-1 hypothesis (A): chain-level d(base) ≥ 6. -/
theorem base_distance_ge_6 : BaseDistanceGe6 := by
  intro u hu hnb
  have hne : u ≠ 0 := by
    rintro rfl
    exact hnb ⟨0, map_zero _⟩
  have hcyc : bbBoundary1Fn baseA baseB u = 0 := hu
  have h6 := base_cycle_weight_ge_6 u hcyc hne
  rw [bb72Complex_chainWeight_eq]
  exact h6

/-- `u*` is not a base boundary (else its pullback `τ(u*)` would be a gross
boundary, contradicting the Phase-0 dual-witness certificate). -/
theorem uStar_not_mem_base_boundaries : uStar ∉ bb72Complex.boundaries :=
  fun h => tauUStar_not_mem_boundaries (coverPull1_mem_boundaries h)

/-- **Chain-level d(base) = 6** (Corollary A′): 6 is attained (by `u*`) and
minimal. -/
theorem base_chain_distance_eq_6 :
    IsLeast {w : ℕ | ∃ u : BaseGroup × Fin 2 → ZMod 2,
      u ∈ bb72Complex.cycles ∧ u ∉ bb72Complex.boundaries ∧
      bb72Complex.chainWeight u = w} 6 := by
  constructor
  · exact ⟨uStar, uStar_mem_cycles, uStar_not_mem_base_boundaries,
      chainWeight_uStar⟩
  · rintro w ⟨u, hu, hnb, rfl⟩
    exact base_distance_ge_6 u hu hnb

/-! ## Unconditional d(gross) ≥ 6 (A4 Theorem B)

Sector split on `b := p(v)`: if `b ≠ 0` then `b` is a nonzero base *cycle*
(boundary or not), so `|v| ≥ |b| ≥ 6` by the strong small-cycle theorem;
if `b = 0` the Phase-1 rung gives `|v| ≥ 12`. -/

/-- Every nontrivial cycle of the gross complex has chain weight ≥ 6 —
**unconditionally**. -/
theorem gross_chainWeight_ge_6 :
    ∀ v : GrossGroup × Fin 2 → ZMod 2,
      v ∈ grossComplex.cycles → v ∉ grossComplex.boundaries →
      6 ≤ grossComplex.chainWeight v := by
  intro v hv hnb
  by_cases h0 : coverPush1 v = 0
  · have h12 := gross_chainWeight_ge_12_of_coverPush_eq_zero
      base_distance_ge_6 hv hnb h0
    omega
  · have hcyc : bbBoundary1Fn baseA baseB (coverPush1 v) = 0 :=
      coverPush1_mem_cycles hv
    have h6 := base_cycle_weight_ge_6 (coverPush1 v) hcyc h0
    have hle := chainWeight_coverPush_le v
    rw [bb72Complex_chainWeight_eq] at hle
    omega

/-- Dual-side mirror, via the Φ duality. -/
theorem gross_dual_chainWeight_ge_6 :
    ∀ c ∈ grossComplex.dualCycles, c ∉ grossComplex.dualBoundaries →
      6 ≤ grossComplex.chainWeight c := by
  have hX : ∀ c ∈ (bbChainComplex grossA grossB).cycles,
      c ∉ (bbChainComplex grossA grossB).boundaries →
      6 ≤ (bbChainComplex grossA grossB).chainWeight c := fun c hc hnb =>
    gross_chainWeight_ge_6 c hc hnb
  exact (bb_cycle_bound_iff_dual_bound grossA grossB 6).mp hX

/-- **Unconditional d(gross) ≥ 6 at the Pauli level** (A4 Theorem B): every
nontrivial logical operator of the gross homological stabilizer group has
weight ≥ 6 — triple the published Lin–Pryadko floor of 2. -/
theorem gross_logical_weight_ge_6
    (g : NQubitPauliGroupElement grossComplex.numQubits)
    (hg : Quantum.StabilizerGroup.IsNontrivialLogicalOperator g
      grossComplex.homologicalStabilizerGroup) :
    6 ≤ NQubitPauliGroupElement.weight g :=
  HomologicalCode.chainWeight_lower_bound_transfers grossComplex 6
    (fun c hc hnb => gross_chainWeight_ge_6 c hc hnb)
    gross_dual_chainWeight_ge_6 g hg

/-! ## The narrowed Phase-1 interface

With (A) discharged, the conditional `d(gross) = 12` needs only the two
sector inputs. -/

/-- Conditional Pauli-level `d(gross) = 12`, now from the two remaining
sector hypotheses (A4 Theorems C and D; Phases 3–4). -/
theorem gross_pauli_distance_eq_12_of_two_sectors
    (hM : DangerousSectorGe12) (hMim : SafeSectorGe12) :
    IsLeast {w : ℕ | ∃ g : NQubitPauliGroupElement grossComplex.numQubits,
      Quantum.StabilizerGroup.IsNontrivialLogicalOperator g
        grossComplex.homologicalStabilizerGroup ∧
      NQubitPauliGroupElement.weight g = w} 12 :=
  gross_pauli_distance_eq_12_of_sectors base_distance_ge_6 hM hMim

end BB
end Homological
end Stabilizer
end Quantum
