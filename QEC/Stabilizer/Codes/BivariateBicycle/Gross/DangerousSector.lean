/-
# Phase 3: the dangerous sector — (M) modulo the light-stabilizer classification

The dangerous-sector bound (`DangerousSectorGe12`, A4 Theorem C) reduced to a
single named hypothesis, `LightStabilizerClassification` (A4 §6.3: every
nonzero base boundary of weight ≤ 11 is a hexagon `∂₂δ_g` or a D-pair
`∂₂(δ_g + δ_{g+d})`, `d ∈ pairDirections`). The sheet identities and
logical-floor rungs are applications of `BBCover` and `BBDoubling`; the
shape weights, support certificates, and classification dispatch are specific
to Gross:

* the **sheet decomposition** of cover chains (`sheet0`, `sheet1`) and the
  refined slice identity `|v| = |b| + 2·|supp(sheet0 v) ∖ supp b|`
  (`gross_chainWeight_sheet_eq`);
* the **m-rungs** (A4 §6.4), from the small-cycle theorem:
  - `m(hexagon) ≥ 3` — a dangerous cycle over a hexagon with ≤ 2 off-support
    qubits descends (after subtracting the lifted stabilizer) to a base cycle
    that, after an `u ↦ u + b` flip, has weight ≤ 5, hence is a
    boundary — trivializing `v`;
  - `m(D-pair) ≥ 1` — over a D-pair with zero off-support overlap, the
    descended cycle lives in the 11-qubit union; its four translates by
    `{0, b₁, b₂, b₁+b₂}` have total weight `2·11 = 22 < 4·6`, so one of them
    is a small cycle, again trivializing `v`;
* the assembly `dangerous_sector_of_classification`.

## Convention bridge (lab notes → repo)

Repo convention: `∂₂ f = (A⋆f | B⋆f)`, `∂₁ c = B⋆c_L + A⋆c_R`.
**Repo-left = lab-right.**  Sheet 0 = the `coverSec` image (`x ∈ {0..5}`).
-/

import QEC.Stabilizer.Codes.BivariateBicycle.Gross.BaseDistance

namespace Quantum
namespace Stabilizer
namespace Homological
namespace BB

open scoped BigOperators

-- Defeq checks through `coverPush1`/`coverPull1` and the lifted-stabilizer
-- bridges unfold deep `Prod`/`ZMod` instance chains (same as
-- `CoverTransfer.lean`).
set_option maxRecDepth 4096

/-! ## Sheet decomposition of cover 1-chains -/

/-- Sheet-0 restriction of a cover 1-chain (via the section `coverSec1`). -/
def sheet0 (v : GrossGroup × Fin 2 → ZMod 2) : BaseGroup × Fin 2 → ZMod 2 :=
  fun q => v (coverSec1 q)

/-- Sheet-1 restriction of a cover 1-chain (deck partner of sheet 0). -/
def sheet1 (v : GrossGroup × Fin 2 → ZMod 2) : BaseGroup × Fin 2 → ZMod 2 :=
  fun q => v (deckSigma1 (coverSec1 q))

@[simp] lemma sheet0_apply (v : GrossGroup × Fin 2 → ZMod 2)
    (q : BaseGroup × Fin 2) : sheet0 v q = v (coverSec1 q) := rfl

@[simp] lemma sheet1_apply (v : GrossGroup × Fin 2 → ZMod 2)
    (q : BaseGroup × Fin 2) : sheet1 v q = v (deckSigma1 (coverSec1 q)) := rfl

lemma sheet0_add (v w : GrossGroup × Fin 2 → ZMod 2) :
    sheet0 (v + w) = sheet0 v + sheet0 w := rfl

lemma sheet1_add (v w : GrossGroup × Fin 2 → ZMod 2) :
    sheet1 (v + w) = sheet1 v + sheet1 w := rfl

/-- The two sheets sum to the pushforward. -/
lemma sheet0_add_sheet1 (v : GrossGroup × Fin 2 → ZMod 2)
    (j : BaseGroup × Fin 2) :
    sheet0 v j + sheet1 v j = coverPush1 v j :=
  grossCoverData.sheet0_add_sheet1 v j

/-- Sheet-0 restriction inverts the pullback. -/
lemma sheet0_coverPull1 (u : BaseGroup × Fin 2 → ZMod 2) :
    sheet0 (coverPull1 u) = u :=
  grossCoverData.sheet0_pull1 u

/-! ## The refined slice identity -/

/-- The deck-overlap of `v` counts twice the overlapping fibers. -/
lemma overlapCount_eq_two_mul_sheets (v : GrossGroup × Fin 2 → ZMod 2) :
    overlapCount v
      = 2 * (Finset.univ.filter fun j =>
          sheet0 v j ≠ 0 ∧ sheet1 v j ≠ 0).card :=
  grossCoverData.overlapCount_eq_two_mul_sheets v

/-- **Refined slice identity**: `|v| = |p(v)| + 2·|supp(sheet0 v) ∖ supp p(v)|`.
-/
theorem gross_chainWeight_sheet_eq (v : GrossGroup × Fin 2 → ZMod 2) :
    grossComplex.chainWeight v
      = bb72Complex.chainWeight (coverPush1 v)
        + 2 * (Finset.univ.filter fun j =>
            sheet0 v j ≠ 0 ∧ coverPush1 v j = 0).card :=
  grossCoverData.chainWeight_sheet_eq v

/-! ## The lifted stabilizer -/

/-- Sheet-0 lift of a base 2-chain to the cover. -/
def liftC2 (ξ : BaseGroup → ZMod 2) : GrossGroup → ZMod 2 :=
  lift0 ⇑coverPi coverSec ξ

lemma coverPush0_liftC2 (ξ : BaseGroup → ZMod 2) :
    fiberSumFn ⇑coverPi (liftC2 ξ) = ξ :=
  grossCoverData.push0_liftC2 ξ

/-- The lifted stabilizer of a base 2-chain: `∂₂(gross) (lift ξ)`. -/
def liftStab (ξ : BaseGroup → ZMod 2) : GrossGroup × Fin 2 → ZMod 2 :=
  bbBoundary2Fn grossA grossB (liftC2 ξ)

lemma liftStab_mem_boundaries (ξ : BaseGroup → ZMod 2) :
    liftStab ξ ∈ grossComplex.boundaries :=
  grossCoverData.liftStab_mem_boundaries ξ

/-- The lifted stabilizer pushes forward to the base stabilizer. -/
lemma coverPush1_liftStab (ξ : BaseGroup → ZMod 2) :
    coverPush1 (liftStab ξ) = bbBoundary2Fn baseA baseB ξ :=
  grossCoverData.push1_liftStab ξ

/-- The generic sheet-0 restriction is the Gross sheet-0 restriction. -/
lemma grossCoverData_sheet0 : grossCoverData.sheet0 = sheet0 := rfl

/-- The generic sheet-1 restriction is the Gross sheet-1 restriction. -/
lemma grossCoverData_sheet1 : grossCoverData.sheet1 = sheet1 := rfl

/-- The generic lift agrees with the Gross certificate interface. -/
lemma grossCoverData_liftC2 : grossCoverData.liftC2 = liftC2 := rfl

/-- The generic lifted stabilizer agrees with the Gross certificate interface.
-/
lemma grossCoverData_liftStab : grossCoverData.liftStab = liftStab := rfl

/-! ## Plumbing for the rung proofs -/

/-- The descended chain of a dangerous normalization is a base cycle. -/
lemma descend_cycle {u : BaseGroup × Fin 2 → ZMod 2}
    (h : coverPull1 u ∈ grossComplex.cycles) :
    bbBoundary1Fn baseA baseB u = 0 :=
  grossCoverData.descend_cycle h

/-- Support split of a chain by an indicator set: `|u| = |u on s| + |u off s|`
for any decidable predicate `s`. -/
lemma card_filter_split {I : Type} [Fintype I] (u : I → ZMod 2)
    (P : I → Prop) [DecidablePred P] :
    (Finset.univ.filter fun j => u j ≠ 0).card
      = ((Finset.univ.filter fun j => u j ≠ 0).filter P).card
        + ((Finset.univ.filter fun j => u j ≠ 0).filter fun j => ¬ P j).card :=
  XDoubleCoverData.card_filter_split u P

/-! ### Pointwise `∂₂` plumbing (kernel-decide support)

The rung side conditions below are finite checks over `∂₂` of point masses.
Evaluating the convolution sums inside a kernel `decide` is too slow, so each
check is first reduced to the pointwise form
`∂₂(δ_c)(h, j) = if j = 0 then A (h - c) else B (h - c)`
(`bbBoundary2Fn_single_pt`), the lifted stabilizer of a point mass to a gross
point mass at the section (`liftC2_single`), and the D-pair statements to their
`g = 0` translates (`card_filter_comp_equiv`); only the reduced forms are swept
by `decide +kernel`. -/

/-- Pair-argument form of `bbBoundary2Fn_single`. -/
private lemma bbBoundary2Fn_single_pt {G : Type} [Fintype G] [AddCommGroup G]
    [DecidableEq G] (A B : G → ZMod 2) (c : G) (p : G × Fin 2) :
    bbBoundary2Fn A B (Pi.single c 1) p
      = if p.2 = 0 then A (p.1 - c) else B (p.1 - c) := by
  obtain ⟨h, j⟩ := p
  exact bbBoundary2Fn_single A B c h j

/-- Sheet-0 lift of a base point mass is the gross point mass at the section
point. -/
private lemma liftC2_single : ∀ g : BaseGroup,
    liftC2 (Pi.single g 1) = Pi.single (coverSec g) 1 := by
  decide +kernel

private lemma liftC2_add (f f' : BaseGroup → ZMod 2) :
    liftC2 (f + f') = liftC2 f + liftC2 f' :=
  grossCoverData.liftC2_add f f'

/-! ## The hexagon rung (`m(hexagon) ≥ 3`) -/

private lemma hexagon_weight_check : ∀ g : BaseGroup,
    (Finset.univ.filter fun j : BaseGroup × Fin 2 =>
      (if j.2 = 0 then baseA (j.1 - g) else baseB (j.1 - g)) ≠ 0).card = 6 := by
  decide +kernel

/-- Hexagons have weight 6. -/
lemma hexagon_weight : ∀ g : BaseGroup,
    (Finset.univ.filter fun j : BaseGroup × Fin 2 =>
      bbBoundary2Fn baseA baseB (Pi.single g 1) j ≠ 0).card = 6 := by
  intro g
  have hfil : (Finset.univ.filter fun j : BaseGroup × Fin 2 =>
      bbBoundary2Fn baseA baseB (Pi.single g 1) j ≠ 0)
      = Finset.univ.filter fun j : BaseGroup × Fin 2 =>
          (if j.2 = 0 then baseA (j.1 - g) else baseB (j.1 - g)) ≠ 0 := by
    apply Finset.filter_congr
    intro j _
    rw [bbBoundary2Fn_single_pt]
  rw [hfil]
  exact hexagon_weight_check g

private lemma hexagon_seam_check : ∀ g : BaseGroup, ∀ j : BaseGroup × Fin 2,
    (if j.2 = 0 then grossA (coverSec j.1 - coverSec g)
      else grossB (coverSec j.1 - coverSec g)) ≠ 0 →
    (if j.2 = 0 then baseA (j.1 - g) else baseB (j.1 - g)) ≠ 0 := by
  decide +kernel

/-- The sheet-0 seam part of a lifted hexagon is supported in the hexagon. -/
lemma hexagon_seam_subset : ∀ g : BaseGroup, ∀ j : BaseGroup × Fin 2,
    sheet0 (liftStab (Pi.single g 1)) j ≠ 0 →
    bbBoundary2Fn baseA baseB (Pi.single g 1) j ≠ 0 := by
  intro g j hne
  have e1 : sheet0 (liftStab (Pi.single g 1)) j
      = if j.2 = 0 then grossA (coverSec j.1 - coverSec g)
        else grossB (coverSec j.1 - coverSec g) := by
    change bbBoundary2Fn grossA grossB (liftC2 (Pi.single g 1)) (coverSec1 j) = _
    rw [liftC2_single g, bbBoundary2Fn_single_pt]
    rfl
  rw [e1] at hne
  rw [bbBoundary2Fn_single_pt]
  exact hexagon_seam_check g j hne

/-- **The hexagon rung**: a nontrivial dangerous cycle over a hexagon has weight
≥ 12. -/
theorem dangerous_hexagon_bound (g : BaseGroup)
    {v : GrossGroup × Fin 2 → ZMod 2}
    (hv : v ∈ grossComplex.cycles) (hnb : v ∉ grossComplex.boundaries)
    (hb : coverPush1 v = bbBoundary2Fn baseA baseB (Pi.single g 1)) :
    12 ≤ grossComplex.chainWeight v := by
  refine grossCoverData.dangerous_bound_of_single_shape_of_logicalFloor
    grossCoverData_logicalFloor (t := 3) (by decide) (Pi.single g 1) ?_
    (hexagon_seam_subset g) hv hnb hb
  change (Finset.univ.filter fun j : BaseGroup × Fin 2 =>
    bbBoundary2Fn baseA baseB (Pi.single g 1) j ≠ 0).card + 2 * 3 = 2 * 6
  rw [hexagon_weight]

/-! ## The D-pair rung (`m(D-pair) ≥ 1`) -/

/-- The twelve D-pair directions `dA ∪ dB`. -/
def pairDirections : Finset BaseGroup :=
  {(0, 1), (0, 5), (3, 1), (3, 2), (3, 4), (3, 5),
   (1, 0), (1, 3), (2, 3), (4, 3), (5, 0), (5, 3)}

private lemma dpair_weight_check : ∀ d ∈ pairDirections,
    (Finset.univ.filter fun j : BaseGroup × Fin 2 =>
      (if j.2 = 0 then baseA j.1 + baseA (j.1 - d)
        else baseB j.1 + baseB (j.1 - d)) ≠ 0).card = 10 := by
  decide +kernel

/-- D-pairs have weight 10. -/
lemma dpair_weight : ∀ g : BaseGroup, ∀ d ∈ pairDirections,
    (Finset.univ.filter fun j : BaseGroup × Fin 2 =>
      bbBoundary2Fn baseA baseB
        (Pi.single g 1 + Pi.single (g + d) 1) j ≠ 0).card = 10 := by
  intro g d hd
  have hfil : (Finset.univ.filter fun j : BaseGroup × Fin 2 =>
      bbBoundary2Fn baseA baseB (Pi.single g 1 + Pi.single (g + d) 1) j ≠ 0)
      = Finset.univ.filter fun j : BaseGroup × Fin 2 =>
          (if j.2 = 0 then baseA (j.1 - g) + baseA (j.1 - g - d)
            else baseB (j.1 - g) + baseB (j.1 - g - d)) ≠ 0 := by
    apply Finset.filter_congr
    intro j _
    rw [bbBoundary2Fn_add, Pi.add_apply, bbBoundary2Fn_single_pt,
      bbBoundary2Fn_single_pt, sub_add_eq_sub_sub]
    by_cases hj : j.2 = 0
    · rw [if_pos hj, if_pos hj, if_pos hj]
    · rw [if_neg hj, if_neg hj, if_neg hj]
  have htrans : (Finset.univ.filter fun j : BaseGroup × Fin 2 =>
      (if j.2 = 0 then baseA (j.1 - g) + baseA (j.1 - g - d)
        else baseB (j.1 - g) + baseB (j.1 - g - d)) ≠ 0).card
      = (Finset.univ.filter fun j : BaseGroup × Fin 2 =>
          (if j.2 = 0 then baseA j.1 + baseA (j.1 - d)
            else baseB j.1 + baseB (j.1 - d)) ≠ 0).card :=
    card_filter_comp_equiv ((Equiv.subRight g).prodCongr (Equiv.refl (Fin 2)))
      (fun j : BaseGroup × Fin 2 =>
        (if j.2 = 0 then baseA j.1 + baseA (j.1 - d)
          else baseB j.1 + baseB (j.1 - d)) ≠ 0)
  rw [hfil, htrans]
  exact dpair_weight_check d hd

private lemma dpair_union_check : ∀ d ∈ pairDirections,
    (Finset.univ.filter fun j : BaseGroup × Fin 2 =>
      (if j.2 = 0 then baseA j.1 else baseB j.1) ≠ 0 ∨
      (if j.2 = 0 then baseA (j.1 - d) else baseB (j.1 - d)) ≠ 0).card
      ≤ 11 := by
  decide +kernel

/-- The 11-qubit union: the two hexagons of a D-pair overlap. -/
lemma dpair_union_card : ∀ g : BaseGroup, ∀ d ∈ pairDirections,
    (Finset.univ.filter fun j : BaseGroup × Fin 2 =>
      bbBoundary2Fn baseA baseB (Pi.single g 1) j ≠ 0 ∨
      bbBoundary2Fn baseA baseB (Pi.single (g + d) 1) j ≠ 0).card ≤ 11 := by
  intro g d hd
  have hfil : (Finset.univ.filter fun j : BaseGroup × Fin 2 =>
      bbBoundary2Fn baseA baseB (Pi.single g 1) j ≠ 0 ∨
      bbBoundary2Fn baseA baseB (Pi.single (g + d) 1) j ≠ 0)
      = Finset.univ.filter fun j : BaseGroup × Fin 2 =>
          (if j.2 = 0 then baseA (j.1 - g) else baseB (j.1 - g)) ≠ 0 ∨
          (if j.2 = 0 then baseA (j.1 - g - d)
            else baseB (j.1 - g - d)) ≠ 0 := by
    apply Finset.filter_congr
    intro j _
    rw [bbBoundary2Fn_single_pt, bbBoundary2Fn_single_pt, sub_add_eq_sub_sub]
  have htrans : (Finset.univ.filter fun j : BaseGroup × Fin 2 =>
      (if j.2 = 0 then baseA (j.1 - g) else baseB (j.1 - g)) ≠ 0 ∨
      (if j.2 = 0 then baseA (j.1 - g - d)
        else baseB (j.1 - g - d)) ≠ 0).card
      = (Finset.univ.filter fun j : BaseGroup × Fin 2 =>
          (if j.2 = 0 then baseA j.1 else baseB j.1) ≠ 0 ∨
          (if j.2 = 0 then baseA (j.1 - d) else baseB (j.1 - d)) ≠ 0).card :=
    card_filter_comp_equiv ((Equiv.subRight g).prodCongr (Equiv.refl (Fin 2)))
      (fun j : BaseGroup × Fin 2 =>
        (if j.2 = 0 then baseA j.1 else baseB j.1) ≠ 0 ∨
        (if j.2 = 0 then baseA (j.1 - d) else baseB (j.1 - d)) ≠ 0)
  rw [hfil, htrans]
  exact dpair_union_check d hd

/-- The sheet-0 seam part of a lifted D-pair is supported in the union
(analytic: the lifted stabilizer is additive, and a nonzero `ZMod 2` sum has a
nonzero summand, so the hexagon seam lemma applies to each half). -/
lemma dpair_seam_subset : ∀ g : BaseGroup, ∀ d ∈ pairDirections,
    ∀ j : BaseGroup × Fin 2,
    sheet0 (liftStab (Pi.single g 1 + Pi.single (g + d) 1)) j ≠ 0 →
    (bbBoundary2Fn baseA baseB (Pi.single g 1) j ≠ 0 ∨
     bbBoundary2Fn baseA baseB (Pi.single (g + d) 1) j ≠ 0) := by
  intro g d _hd j hne
  have hsplit : liftStab (Pi.single g 1 + Pi.single (g + d) 1)
      = liftStab (Pi.single g 1) + liftStab (Pi.single (g + d) 1) := by
    unfold liftStab
    rw [liftC2_add, bbBoundary2Fn_add]
  rw [hsplit, sheet0_add] at hne
  have hcases : sheet0 (liftStab (Pi.single g 1)) j ≠ 0 ∨
      sheet0 (liftStab (Pi.single (g + d) 1)) j ≠ 0 := by
    by_contra hcon
    push Not at hcon
    rw [Pi.add_apply, hcon.1, hcon.2, add_zero] at hne
    exact hne rfl
  rcases hcases with h | h
  · exact Or.inl (hexagon_seam_subset g j h)
  · exact Or.inr (hexagon_seam_subset (g + d) j h)

/-- **The D-pair rung**: a nontrivial dangerous cycle over a D-pair has weight ≥
12. -/
theorem dangerous_dpair_bound (g d : BaseGroup) (hd : d ∈ pairDirections)
    {v : GrossGroup × Fin 2 → ZMod 2}
    (hv : v ∈ grossComplex.cycles) (hnb : v ∉ grossComplex.boundaries)
    (hb : coverPush1 v
      = bbBoundary2Fn baseA baseB (Pi.single g 1 + Pi.single (g + d) 1)) :
    12 ≤ grossComplex.chainWeight v := by
  have hb' : grossCoverData.push1 v
      = bbBoundary2Fn baseA baseB (Pi.single g 1)
        + bbBoundary2Fn baseA baseB (Pi.single (g + d) 1) := by
    rw [← bbBoundary2Fn_add]
    exact hb
  refine grossCoverData.dangerous_bound_of_pair_shape_of_logicalFloor
    grossCoverData_logicalFloor (t := 1) (by decide)
    (Pi.single g 1) (Pi.single (g + d) 1) ?_ ?_
    (dpair_seam_subset g d hd) hv hnb hb'
  · change (Finset.univ.filter fun j : BaseGroup × Fin 2 =>
      (bbBoundary2Fn baseA baseB (Pi.single g 1)
        + bbBoundary2Fn baseA baseB (Pi.single (g + d) 1)) j ≠ 0).card
      + 2 * 1 = 2 * 6
    rw [← bbBoundary2Fn_add, dpair_weight g d hd]
  · simpa only [Nat.sub_self, Nat.mul_zero, Nat.add_zero] using dpair_union_card g d hd

/-! ## The classification hypothesis and the assembly -/

/-- **The light-stabilizer classification** (A4 §6.3, Theorem "light
stabilizers"): every nonzero base boundary of weight ≤ 11 is a hexagon or a
D-pair. This is the single remaining analytic input for the dangerous sector;
its paper proof is the CRT-engine analysis of A4 §§6.2–6.3. -/
def LightStabilizerClassification : Prop :=
  ∀ f : BaseGroup → ZMod 2,
    bbBoundary2Fn baseA baseB f ≠ 0 →
    (Finset.univ.filter fun j : BaseGroup × Fin 2 =>
      bbBoundary2Fn baseA baseB f j ≠ 0).card ≤ 11 →
    (∃ g : BaseGroup, bbBoundary2Fn baseA baseB f
        = bbBoundary2Fn baseA baseB (Pi.single g 1)) ∨
    (∃ g : BaseGroup, ∃ d ∈ pairDirections, bbBoundary2Fn baseA baseB f
        = bbBoundary2Fn baseA baseB (Pi.single g 1 + Pi.single (g + d) 1))

/-- **The dangerous sector, conditional only on the classification**: (M) holds,
i.e. `DangerousSectorGe12`. -/
theorem dangerous_sector_of_classification
    (hC : LightStabilizerClassification) : DangerousSectorGe12 := by
  intro v hv hnb hbmem hbne
  obtain ⟨f, hf⟩ := hbmem
  have hf' : bbBoundary2Fn baseA baseB f = coverPush1 v := hf
  by_cases hw : 12 ≤ bb72Complex.chainWeight (coverPush1 v)
  · exact le_trans hw (chainWeight_coverPush_le v)
  · push Not at hw
    have hne : bbBoundary2Fn baseA baseB f ≠ 0 := by
      rw [hf']
      exact hbne
    have hle : (Finset.univ.filter fun j : BaseGroup × Fin 2 =>
        bbBoundary2Fn baseA baseB f j ≠ 0).card ≤ 11 := by
      have heq : (Finset.univ.filter fun j : BaseGroup × Fin 2 =>
          bbBoundary2Fn baseA baseB f j ≠ 0).card
          = bb72Complex.chainWeight (coverPush1 v) := by
        rw [bb72Complex_chainWeight_eq, hf']
      omega
    rcases hC f hne hle with ⟨g, hg⟩ | ⟨g, d, hd, hgd⟩
    · exact dangerous_hexagon_bound g hv hnb (by rw [← hf', hg])
    · exact dangerous_dpair_bound g d hd hv hnb (by rw [← hf', hgd])

end BB
end Homological
end Stabilizer
end Quantum
