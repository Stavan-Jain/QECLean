import Mathlib.Tactic
import QEC.Stabilizer.Codes.RotatedSurfaceCodeNDistanceX
import QEC.Stabilizer.Codes.RotatedSurfaceCodeNDistanceZ
import QEC.Stabilizer.Codes.RotatedSurfaceCodeNStabilizerCode
import QEC.Stabilizer.Homological.Distance
import QEC.Stabilizer.Core.CodeDistance

/-!
# Stage 7 — Combined rotated-surface-code distance = `L`

Combines the X-distance ≥ L (`RotatedSurfaceCodeNDistanceX`) and the
Z-distance ≥ L (`RotatedSurfaceCodeNDistanceZ`) via the CSS bridge
`HomologicalCode.not_both_boundary_of_nontrivial` to obtain
`HasCodeDistance (rotatedSurfaceStabilizerCode L) L`.

The argument mirrors `ToricCodeNDistance`:

* For a non-trivial logical `g`, its X-chain `xChainOf g` is always a
  cycle and its Z-chain `zChainOf g` is always a dual cycle (because `g`
  commutes with every stabilizer generator).
* The CSS bridge guarantees that the two chains cannot **both** be
  boundaries.
* Whichever side is *not* a boundary gives a non-trivial X-type
  (resp. Z-type) logical via `chainXOperator` (resp. `chainZOperator`),
  whose weight is ≥ L by Stage 5 (resp. Stage 6).
* The qubit-wise inclusion `weight g ≥ chainWeight (xChainOf g)`
  (`HomologicalCode.weight_ge_chainWeight_xChainOf`) then transfers the
  bound to `weight g`.
-/

namespace Quantum
namespace StabilizerGroup
namespace RotatedSurfaceCodeN

open scoped BigOperators
open NQubitPauliGroupElement Stabilizer.Lattice.RotatedSurface
  Quantum.Stabilizer.Homological.HomologicalCode

variable (L : ℕ) [Fact (Odd L)] [Fact (3 ≤ L)]

/-! ### Qubit-wise anticommutation bridges

For any qubit `i`, the anticommutation pattern of `g` against a
Z-type (resp. X-type) stabilizer generator depends only on `g`'s
X-content (resp. Z-content) at `i`.  These are the rotated-surface
analogues of `ToricCodeNDistance.anticommutesAt_vertexStab_g_iff_xChain`
/ `anticommutesAt_faceStab_g_iff_zChain`. -/

/-- Against the Z-type vertex stabilizer, qubit-wise anticommutation of
`g` matches that of `chainXOperator (xChainOf g)` (the "X-only encoding"
of `g`). -/
private lemma anticommutesAt_vertexStabOf_iff_xChainOf
    (g : NQubitPauliGroupElement (rotatedSurfaceHomologicalCode L).numQubits)
    (v : (rotatedSurfaceHomologicalCode L).C0)
    (i : Fin (rotatedSurfaceHomologicalCode L).numQubits) :
    NQubitPauliGroupElement.anticommutesAt
        ((rotatedSurfaceHomologicalCode L).vertexStabOf v).operators
        g.operators i ↔
      NQubitPauliGroupElement.anticommutesAt
        ((rotatedSurfaceHomologicalCode L).vertexStabOf v).operators
        ((rotatedSurfaceHomologicalCode L).chainXOperator
          ((rotatedSurfaceHomologicalCode L).xChainOf g)).operators i := by
  have hZ :
      ((rotatedSurfaceHomologicalCode L).vertexStabOf v).operators i =
        PauliOperator.I ∨
      ((rotatedSurfaceHomologicalCode L).vertexStabOf v).operators i =
        PauliOperator.Z :=
    (Quantum.Stabilizer.Homological.HomologicalCode.vertexStabOf_isZType
      (X := rotatedSurfaceHomologicalCode L) v).2 i
  have heq :=
    Quantum.Stabilizer.Homological.HomologicalCode.chainXOperator_xChainOf_op_at
      (X := rotatedSurfaceHomologicalCode L) g i
  rcases hZ with hI | hZ
  · simp only [NQubitPauliGroupElement.anticommutesAt, hI]
    cases hgi : g.operators i <;>
      cases hxi :
        ((rotatedSurfaceHomologicalCode L).chainXOperator
          ((rotatedSurfaceHomologicalCode L).xChainOf g)).operators i <;>
      simp [PauliOperator.mulOp]
  · simp only [NQubitPauliGroupElement.anticommutesAt, hZ, heq]
    cases hgi : g.operators i <;>
      simp [PauliOperator.mulOp]

/-- Against the X-type face stabilizer, qubit-wise anticommutation of `g`
matches that of `chainZOperator (zChainOf g)` (the "Z-only encoding"
of `g`). -/
private lemma anticommutesAt_faceStabOf_iff_zChainOf
    (g : NQubitPauliGroupElement (rotatedSurfaceHomologicalCode L).numQubits)
    (f : (rotatedSurfaceHomologicalCode L).C2)
    (i : Fin (rotatedSurfaceHomologicalCode L).numQubits) :
    NQubitPauliGroupElement.anticommutesAt
        ((rotatedSurfaceHomologicalCode L).faceStabOf f).operators
        g.operators i ↔
      NQubitPauliGroupElement.anticommutesAt
        ((rotatedSurfaceHomologicalCode L).faceStabOf f).operators
        ((rotatedSurfaceHomologicalCode L).chainZOperator
          ((rotatedSurfaceHomologicalCode L).zChainOf g)).operators i := by
  have hX :
      ((rotatedSurfaceHomologicalCode L).faceStabOf f).operators i =
        PauliOperator.I ∨
      ((rotatedSurfaceHomologicalCode L).faceStabOf f).operators i =
        PauliOperator.X :=
    (Quantum.Stabilizer.Homological.HomologicalCode.faceStabOf_isXType
      (X := rotatedSurfaceHomologicalCode L) f).2 i
  have heq :=
    Quantum.Stabilizer.Homological.HomologicalCode.chainZOperator_zChainOf_op_at
      (X := rotatedSurfaceHomologicalCode L) g i
  rcases hX with hI | hX
  · simp only [NQubitPauliGroupElement.anticommutesAt, hI]
    cases hgi : g.operators i <;>
      cases hzi :
        ((rotatedSurfaceHomologicalCode L).chainZOperator
          ((rotatedSurfaceHomologicalCode L).zChainOf g)).operators i <;>
      simp [PauliOperator.mulOp]
  · simp only [NQubitPauliGroupElement.anticommutesAt, hX, heq]
    cases hgi : g.operators i <;>
      simp [PauliOperator.mulOp]

/-! ### Centralizer → cycle bridges -/

/-- For `g ∈ centralizer`, `xChainOf g` is a 1-cycle. -/
private lemma xChainOf_mem_cycles_of_centralizer
    (g : NQubitPauliGroupElement (rotatedSurfaceHomologicalCode L).numQubits)
    (hg : g ∈ StabilizerGroup.centralizer
            (rotatedSurfaceHomologicalCode L).homologicalStabilizerGroup) :
    (rotatedSurfaceHomologicalCode L).xChainOf g ∈
      (rotatedSurfaceHomologicalCode L).cycles := by
  apply (chainXOperator_mem_centralizer_iff_mem_cycles
      (X := rotatedSurfaceHomologicalCode L)
      ((rotatedSurfaceHomologicalCode L).xChainOf g)).mp
  intro s hs
  refine Subgroup.closure_induction
    (p := fun y _ => y *
        (rotatedSurfaceHomologicalCode L).chainXOperator
          ((rotatedSurfaceHomologicalCode L).xChainOf g) =
      (rotatedSurfaceHomologicalCode L).chainXOperator
        ((rotatedSurfaceHomologicalCode L).xChainOf g) * y) ?_ ?_ ?_ ?_ hs
  · rintro y (⟨v, rfl⟩ | ⟨f, rfl⟩)
    · -- y = vertexStabOf v (Z-type generator)
      have hmem : (rotatedSurfaceHomologicalCode L).vertexStabOf v ∈
          (rotatedSurfaceHomologicalCode L).homologicalStabilizerGroup.toSubgroup :=
        Subgroup.subset_closure (Or.inl ⟨v, rfl⟩)
      have hcomm_g :
          (rotatedSurfaceHomologicalCode L).vertexStabOf v * g =
            g * (rotatedSurfaceHomologicalCode L).vertexStabOf v :=
        (Quantum.StabilizerGroup.mem_centralizer_iff g _).mp hg _ hmem
      rw [NQubitPauliGroupElement.commutes_iff_even_anticommutes] at hcomm_g ⊢
      classical
      have hfilter_eq :
          Finset.univ.filter (NQubitPauliGroupElement.anticommutesAt
              ((rotatedSurfaceHomologicalCode L).vertexStabOf v).operators
              ((rotatedSurfaceHomologicalCode L).chainXOperator
                ((rotatedSurfaceHomologicalCode L).xChainOf g)).operators) =
            Finset.univ.filter (NQubitPauliGroupElement.anticommutesAt
              ((rotatedSurfaceHomologicalCode L).vertexStabOf v).operators
              g.operators) := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact (anticommutesAt_vertexStabOf_iff_xChainOf L g v i).symm
      rw [hfilter_eq]
      exact hcomm_g
    · -- y = faceStabOf f (X-type generator) — X-type / X-type commute trivially
      exact Quantum.Stabilizer.Homological.HomologicalCode.chainXOperator_commutes_faceStabOf
        (X := rotatedSurfaceHomologicalCode L)
        ((rotatedSurfaceHomologicalCode L).xChainOf g) f
  · -- one
    change (1 : NQubitPauliGroupElement (rotatedSurfaceHomologicalCode L).numQubits) *
        (rotatedSurfaceHomologicalCode L).chainXOperator
          ((rotatedSurfaceHomologicalCode L).xChainOf g) =
        (rotatedSurfaceHomologicalCode L).chainXOperator
          ((rotatedSurfaceHomologicalCode L).xChainOf g) * 1
    rw [_root_.one_mul, _root_.mul_one]
  · -- mul
    intros y₁ y₂ _ _ hy₁ hy₂
    calc (y₁ * y₂) *
            (rotatedSurfaceHomologicalCode L).chainXOperator
              ((rotatedSurfaceHomologicalCode L).xChainOf g)
        = y₁ * (y₂ *
            (rotatedSurfaceHomologicalCode L).chainXOperator
              ((rotatedSurfaceHomologicalCode L).xChainOf g)) := _root_.mul_assoc _ _ _
      _ = y₁ * ((rotatedSurfaceHomologicalCode L).chainXOperator
              ((rotatedSurfaceHomologicalCode L).xChainOf g) * y₂) := by rw [hy₂]
      _ = (y₁ * (rotatedSurfaceHomologicalCode L).chainXOperator
              ((rotatedSurfaceHomologicalCode L).xChainOf g)) * y₂ :=
        (_root_.mul_assoc _ _ _).symm
      _ = ((rotatedSurfaceHomologicalCode L).chainXOperator
              ((rotatedSurfaceHomologicalCode L).xChainOf g) * y₁) * y₂ := by rw [hy₁]
      _ = (rotatedSurfaceHomologicalCode L).chainXOperator
              ((rotatedSurfaceHomologicalCode L).xChainOf g) * (y₁ * y₂) :=
        _root_.mul_assoc _ _ _
  · -- inv
    intros y _ hy
    exact (show Commute y _ from hy).inv_left.eq

/-- For `g ∈ centralizer`, `zChainOf g` is a dual cycle. -/
private lemma zChainOf_mem_dualCycles_of_centralizer
    (g : NQubitPauliGroupElement (rotatedSurfaceHomologicalCode L).numQubits)
    (hg : g ∈ StabilizerGroup.centralizer
            (rotatedSurfaceHomologicalCode L).homologicalStabilizerGroup) :
    (rotatedSurfaceHomologicalCode L).zChainOf g ∈
      (rotatedSurfaceHomologicalCode L).dualCycles := by
  apply (chainZOperator_mem_centralizer_iff_mem_dualCycles
      (X := rotatedSurfaceHomologicalCode L)
      ((rotatedSurfaceHomologicalCode L).zChainOf g)).mp
  intro s hs
  refine Subgroup.closure_induction
    (p := fun y _ => y *
        (rotatedSurfaceHomologicalCode L).chainZOperator
          ((rotatedSurfaceHomologicalCode L).zChainOf g) =
      (rotatedSurfaceHomologicalCode L).chainZOperator
        ((rotatedSurfaceHomologicalCode L).zChainOf g) * y) ?_ ?_ ?_ ?_ hs
  · rintro y (⟨v, rfl⟩ | ⟨f, rfl⟩)
    · -- y = vertexStabOf v (Z-type generator) — Z-type / Z-type commute trivially
      exact Quantum.Stabilizer.Homological.HomologicalCode.chainZOperator_commutes_vertexStabOf
        (X := rotatedSurfaceHomologicalCode L)
        ((rotatedSurfaceHomologicalCode L).zChainOf g) v
    · -- y = faceStabOf f (X-type generator)
      have hmem : (rotatedSurfaceHomologicalCode L).faceStabOf f ∈
          (rotatedSurfaceHomologicalCode L).homologicalStabilizerGroup.toSubgroup :=
        Subgroup.subset_closure (Or.inr ⟨f, rfl⟩)
      have hcomm_g :
          (rotatedSurfaceHomologicalCode L).faceStabOf f * g =
            g * (rotatedSurfaceHomologicalCode L).faceStabOf f :=
        (Quantum.StabilizerGroup.mem_centralizer_iff g _).mp hg _ hmem
      rw [NQubitPauliGroupElement.commutes_iff_even_anticommutes] at hcomm_g ⊢
      classical
      have hfilter_eq :
          Finset.univ.filter (NQubitPauliGroupElement.anticommutesAt
              ((rotatedSurfaceHomologicalCode L).faceStabOf f).operators
              ((rotatedSurfaceHomologicalCode L).chainZOperator
                ((rotatedSurfaceHomologicalCode L).zChainOf g)).operators) =
            Finset.univ.filter (NQubitPauliGroupElement.anticommutesAt
              ((rotatedSurfaceHomologicalCode L).faceStabOf f).operators
              g.operators) := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact (anticommutesAt_faceStabOf_iff_zChainOf L g f i).symm
      rw [hfilter_eq]
      exact hcomm_g
  · -- one
    change (1 : NQubitPauliGroupElement (rotatedSurfaceHomologicalCode L).numQubits) *
        (rotatedSurfaceHomologicalCode L).chainZOperator
          ((rotatedSurfaceHomologicalCode L).zChainOf g) =
        (rotatedSurfaceHomologicalCode L).chainZOperator
          ((rotatedSurfaceHomologicalCode L).zChainOf g) * 1
    rw [_root_.one_mul, _root_.mul_one]
  · -- mul
    intros y₁ y₂ _ _ hy₁ hy₂
    calc (y₁ * y₂) *
            (rotatedSurfaceHomologicalCode L).chainZOperator
              ((rotatedSurfaceHomologicalCode L).zChainOf g)
        = y₁ * (y₂ *
            (rotatedSurfaceHomologicalCode L).chainZOperator
              ((rotatedSurfaceHomologicalCode L).zChainOf g)) := _root_.mul_assoc _ _ _
      _ = y₁ * ((rotatedSurfaceHomologicalCode L).chainZOperator
              ((rotatedSurfaceHomologicalCode L).zChainOf g) * y₂) := by rw [hy₂]
      _ = (y₁ * (rotatedSurfaceHomologicalCode L).chainZOperator
              ((rotatedSurfaceHomologicalCode L).zChainOf g)) * y₂ :=
        (_root_.mul_assoc _ _ _).symm
      _ = ((rotatedSurfaceHomologicalCode L).chainZOperator
              ((rotatedSurfaceHomologicalCode L).zChainOf g) * y₁) * y₂ := by rw [hy₁]
      _ = (rotatedSurfaceHomologicalCode L).chainZOperator
              ((rotatedSurfaceHomologicalCode L).zChainOf g) * (y₁ * y₂) :=
        _root_.mul_assoc _ _ _
  · -- inv
    intros y _ hy
    exact (show Commute y _ from hy).inv_left.eq

/-! ### Weight bridge: `weight (chain*Operator c) = chainWeight c`

Local versions of the equalities `weight (chainXOperator c) = chainWeight c`
and `weight (chainZOperator c) = chainWeight c`, proved via the same
`rscQubitEquiv` bijection used in
`RotatedSurfaceCodeNDistanceX.weight_chainXOperator_eq_chainSupport_card`. -/

private lemma weight_chainXOperator_eq_chainWeight
    (c : (rotatedSurfaceHomologicalCode L).C1 → ZMod 2) :
    NQubitPauliGroupElement.weight
        ((rotatedSurfaceHomologicalCode L).chainXOperator c) =
      (rotatedSurfaceHomologicalCode L).chainWeight c := by
  classical
  unfold NQubitPauliGroupElement.weight NQubitPauliOperator.weight
    Quantum.Stabilizer.Homological.HomologicalCode.chainWeight
    Quantum.Stabilizer.Homological.HomologicalCode.chainSupport
  symm
  apply Finset.card_bij
    (fun v _ => (rotatedSurfaceHomologicalCode L).edgeEquiv v)
  · intro v hv
    rw [Finset.mem_filter] at hv
    have h_ne : c v ≠ 0 := hv.2
    have h1 : c v = 1 := by
      rcases Fin.exists_fin_two.mp ⟨c v, rfl⟩ with h0 | h1
      · exact absurd h0 h_ne
      · exact h1
    exact (Quantum.Stabilizer.Homological.HomologicalCode.mem_support_chainXOperator_iff
      (X := rotatedSurfaceHomologicalCode L) c v).mpr h1
  · intros v₁ _ v₂ _ heq
    exact (rotatedSurfaceHomologicalCode L).edgeEquiv.injective heq
  · intros q hq
    set v := (rotatedSurfaceHomologicalCode L).edgeEquiv.symm q with hv_def
    have h_q : (rotatedSurfaceHomologicalCode L).edgeEquiv v = q :=
      Equiv.apply_symm_apply _ _
    refine ⟨v, ?_, h_q⟩
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    have h_iff :=
      Quantum.Stabilizer.Homological.HomologicalCode.mem_support_chainXOperator_iff
        (X := rotatedSurfaceHomologicalCode L) c v
    rw [h_q] at h_iff
    have hcv : c v = 1 := h_iff.mp hq
    rw [hcv]; decide

private lemma weight_chainZOperator_eq_chainWeight
    (c : (rotatedSurfaceHomologicalCode L).C1 → ZMod 2) :
    NQubitPauliGroupElement.weight
        ((rotatedSurfaceHomologicalCode L).chainZOperator c) =
      (rotatedSurfaceHomologicalCode L).chainWeight c := by
  classical
  unfold NQubitPauliGroupElement.weight NQubitPauliOperator.weight
    Quantum.Stabilizer.Homological.HomologicalCode.chainWeight
    Quantum.Stabilizer.Homological.HomologicalCode.chainSupport
  symm
  apply Finset.card_bij
    (fun v _ => (rotatedSurfaceHomologicalCode L).edgeEquiv v)
  · intro v hv
    rw [Finset.mem_filter] at hv
    have h_ne : c v ≠ 0 := hv.2
    have h1 : c v = 1 := by
      rcases Fin.exists_fin_two.mp ⟨c v, rfl⟩ with h0 | h1
      · exact absurd h0 h_ne
      · exact h1
    exact (Quantum.Stabilizer.Homological.HomologicalCode.mem_support_chainZOperator_iff
      (X := rotatedSurfaceHomologicalCode L) c v).mpr h1
  · intros v₁ _ v₂ _ heq
    exact (rotatedSurfaceHomologicalCode L).edgeEquiv.injective heq
  · intros q hq
    set v := (rotatedSurfaceHomologicalCode L).edgeEquiv.symm q with hv_def
    have h_q : (rotatedSurfaceHomologicalCode L).edgeEquiv v = q :=
      Equiv.apply_symm_apply _ _
    refine ⟨v, ?_, h_q⟩
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    have h_iff :=
      Quantum.Stabilizer.Homological.HomologicalCode.mem_support_chainZOperator_iff
        (X := rotatedSurfaceHomologicalCode L) c v
    rw [h_q] at h_iff
    have hcv : c v = 1 := h_iff.mp hq
    rw [hcv]; decide

/-! ### Main theorem -/

/-- **Stage 7 endpoint.**  The rotated surface code on an `L × L` lattice
has code distance exactly `L`. -/
theorem rotatedSurfaceCodeN_distance_eq_L :
    HasCodeDistance (rotatedSurfaceStabilizerCode L) L := by
  have hL_pos : 0 < L := by have h3 : 3 ≤ L := Fact.out; omega
  -- Bridge: the StabilizerCode subgroup equals the homological one.
  have h_sub_eq := rotatedSurfaceStabilizerCode_subgroup_eq_homological L
  -- Bridge `IsNontrivialLogicalOperator` between the two groups.
  have h_iff_NL : ∀ g,
      Quantum.StabilizerGroup.IsNontrivialLogicalOperator g
          (rotatedSurfaceStabilizerCode L).toStabilizerGroup ↔
        Quantum.StabilizerGroup.IsNontrivialLogicalOperator g
          (rotatedSurfaceHomologicalCode L).homologicalStabilizerGroup :=
    fun g => Quantum.StabilizerGroup.IsNontrivialLogicalOperator_of_toSubgroup_eq g h_sub_eq
  refine ⟨hL_pos, ?_, ?_⟩
  · -- Lower bound: every non-trivial logical has weight ≥ L.
    intro g hgLogical _hgwpos
    have hg_hom := (h_iff_NL g).mp hgLogical
    have hg_cent_hom :
        g ∈ Quantum.StabilizerGroup.centralizer
          (rotatedSurfaceHomologicalCode L).homologicalStabilizerGroup :=
      ((Quantum.StabilizerGroup.IsNontrivialLogicalOperator_iff g _).mp hg_hom).1
    -- Apply the abstract CSS bridge: not both boundary.
    have h_not_both :=
      Quantum.Stabilizer.Homological.HomologicalCode.not_both_boundary_of_nontrivial
        (X := rotatedSurfaceHomologicalCode L) g hg_hom
    -- xChainOf g ∈ cycles, zChainOf g ∈ dualCycles
    have hxCyc := xChainOf_mem_cycles_of_centralizer L g hg_cent_hom
    have hzCyc := zChainOf_mem_dualCycles_of_centralizer L g hg_cent_hom
    -- Case on whether xChainOf g is a boundary.
    by_cases hxBnd : (rotatedSurfaceHomologicalCode L).xChainOf g ∈
        (rotatedSurfaceHomologicalCode L).boundaries
    · -- Then zChainOf g ∉ dualBoundaries — use Z-distance bound.
      have hzBnd : (rotatedSurfaceHomologicalCode L).zChainOf g ∉
          (rotatedSurfaceHomologicalCode L).dualBoundaries := by
        intro h; exact h_not_both ⟨hxBnd, h⟩
      -- chainZOperator (zChainOf g) is a Z-type non-trivial logical.
      set gZ : NQubitPauliGroupElement (numQubits L) :=
        (rotatedSurfaceHomologicalCode L).chainZOperator
          ((rotatedSurfaceHomologicalCode L).zChainOf g) with hgZ_def
      have hgZ_isZType : NQubitPauliGroupElement.IsZTypeElement gZ :=
        Quantum.Stabilizer.Homological.HomologicalCode.chainZOperator_isZType
          (X := rotatedSurfaceHomologicalCode L) _
      have hgZ_nl_hom :
          Quantum.StabilizerGroup.IsNontrivialLogicalOperator gZ
            (rotatedSurfaceHomologicalCode L).homologicalStabilizerGroup :=
        (Quantum.Stabilizer.Homological.HomologicalCode.chainZOperator_isNontrivialLogical_iff
          (X := rotatedSurfaceHomologicalCode L)
          ((rotatedSurfaceHomologicalCode L).zChainOf g)).mpr ⟨hzCyc, hzBnd⟩
      have hgZ_nl :
          Quantum.StabilizerGroup.IsNontrivialLogicalOperator gZ
            (rotatedSurfaceStabilizerCode L).toStabilizerGroup :=
        (h_iff_NL gZ).mpr hgZ_nl_hom
      have hwZ : L ≤ NQubitPauliGroupElement.weight gZ :=
        weight_ge_L_of_nontrivial_Z_logical L hgZ_isZType hgZ_nl
      -- weight g ≥ chainWeight (zChainOf g) = weight gZ ≥ L.
      have h_step1 :
          (rotatedSurfaceHomologicalCode L).chainWeight
              ((rotatedSurfaceHomologicalCode L).zChainOf g) ≤
            NQubitPauliGroupElement.weight g :=
        Quantum.Stabilizer.Homological.HomologicalCode.weight_ge_chainWeight_zChainOf
          (X := rotatedSurfaceHomologicalCode L) g
      have h_step2 :
          NQubitPauliGroupElement.weight gZ =
            (rotatedSurfaceHomologicalCode L).chainWeight
              ((rotatedSurfaceHomologicalCode L).zChainOf g) :=
        weight_chainZOperator_eq_chainWeight L _
      omega
    · -- xChainOf g ∉ boundaries — use X-distance bound.
      set gX : NQubitPauliGroupElement (numQubits L) :=
        (rotatedSurfaceHomologicalCode L).chainXOperator
          ((rotatedSurfaceHomologicalCode L).xChainOf g) with hgX_def
      have hgX_isXType : NQubitPauliGroupElement.IsXTypeElement gX :=
        Quantum.Stabilizer.Homological.HomologicalCode.chainXOperator_isXType
          (X := rotatedSurfaceHomologicalCode L) _
      have hgX_nl_hom :
          Quantum.StabilizerGroup.IsNontrivialLogicalOperator gX
            (rotatedSurfaceHomologicalCode L).homologicalStabilizerGroup :=
        (Quantum.Stabilizer.Homological.HomologicalCode.chainXOperator_isNontrivialLogical_iff
          (X := rotatedSurfaceHomologicalCode L)
          ((rotatedSurfaceHomologicalCode L).xChainOf g)).mpr ⟨hxCyc, hxBnd⟩
      have hgX_nl :
          Quantum.StabilizerGroup.IsNontrivialLogicalOperator gX
            (rotatedSurfaceStabilizerCode L).toStabilizerGroup :=
        (h_iff_NL gX).mpr hgX_nl_hom
      have hwX : L ≤ NQubitPauliGroupElement.weight gX :=
        weight_ge_L_of_nontrivial_X_logical L hgX_isXType hgX_nl
      have h_step1 :
          (rotatedSurfaceHomologicalCode L).chainWeight
              ((rotatedSurfaceHomologicalCode L).xChainOf g) ≤
            NQubitPauliGroupElement.weight g :=
        Quantum.Stabilizer.Homological.HomologicalCode.weight_ge_chainWeight_xChainOf
          (X := rotatedSurfaceHomologicalCode L) g
      have h_step2 :
          NQubitPauliGroupElement.weight gX =
            (rotatedSurfaceHomologicalCode L).chainWeight
              ((rotatedSurfaceHomologicalCode L).xChainOf g) :=
        weight_chainXOperator_eq_chainWeight L _
      omega
  · -- Witness: `logicalX L` has weight exactly L.
    refine ⟨logicalX L, ?_, ?_⟩
    · -- IsNontrivialLogicalOperator (logicalX L) (rotatedSurfaceStabilizerCode L).toStabilizerGroup
      have hlogX_nl_hom :
          Quantum.StabilizerGroup.IsNontrivialLogicalOperator (logicalX L)
            (rotatedSurfaceHomologicalCode L).homologicalStabilizerGroup := by
        change Quantum.StabilizerGroup.IsNontrivialLogicalOperator
          ((rotatedSurfaceHomologicalCode L).chainXOperator (middleColChain L)) _
        exact (Quantum.Stabilizer.Homological.HomologicalCode.chainXOperator_isNontrivialLogical_iff
          (X := rotatedSurfaceHomologicalCode L) (middleColChain L)).mpr
          ⟨middleColChain_mem_cycles L, middleColChain_not_mem_boundaries L⟩
      exact (h_iff_NL (logicalX L)).mpr hlogX_nl_hom
    · exact logicalX_weight_eq_L L

end RotatedSurfaceCodeN
end StabilizerGroup
end Quantum
