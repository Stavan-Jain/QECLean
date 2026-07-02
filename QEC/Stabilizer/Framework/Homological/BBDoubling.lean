/-
# The parametric free-ℤ₂ doubling template for BB codes

Consumes an `XDoubleCoverData G H` bundle (`BBCover.lean`) and packages the
gross-proof doubling architecture (docs/gross-distance-extensibility.md §3)
as generic theorems.  Everything the gross development proved for the
specific `Z₁₂×Z₆ → Z₆×Z₆` cover in `DeckHomotopy.lean`, `Assembly.lean`,
`DangerousSector.lean` (rungs) and `SafeSector.lean` (reduction) is proved
here once, parametrically; what remains per instance are the five *inputs*:

* `StrongBaseFloor d` — the base small-cycle theorem (Theorem A);
* `DeckTrivialOnH1` — the homotopy (R), from a finite matrix certificate
  (`deckTrivial_of_homotopy_certificate`; the gross polynomial identity
  `(1+x²)B² = 1+x⁶` is one way to produce such a certificate);
* `DangerousFloorNZ (2d)` — assembled per instance from the generic rungs
  (`dangerous_bound_of_single_shape`, `dangerous_bound_of_pair_shape`)
  dispatched over that code's light-boundary classification;
* `SeamCosetFloor (2d)` — the (M-im) analog, per-class coset sweeps;
* the tight witness `u*` with `pull1 u* ∉ boundaries`.

Given those, `chain_distance_eq_double` and `pauli_distance_eq_double`
deliver `d(cover) = 2·d(base)` at the chain and Pauli levels, and
`chainWeight_ge_of_strongBaseFloor` delivers the unconditional Theorem-B
floor `d(cover) ≥ d(base)` from the base floor alone.

## Name map (parametric ↔ gross instantiation)

| here                                    | gross                                  |
|-----------------------------------------|----------------------------------------|
| `StrongBaseFloor d`                     | `base_cycle_weight_ge_6` (shape)       |
| `DeckTrivialOnH1`                       | `deck_add_mem_boundaries`              |
| `DangerousFloorNZ (2d)`                 | `DangerousSectorGe12`                  |
| `SafeFloor (2d)`                        | `SafeSectorGe12`                       |
| `SeamCosetFloor (2d)`                   | `MImBound`                             |
| `dangerous_zero_rung`                   | `gross_chainWeight_ge_12_of_coverPush_eq_zero` |
| `dangerous_bound_of_single_shape`       | `dangerous_hexagon_bound`              |
| `dangerous_bound_of_pair_shape`         | `dangerous_dpair_bound`                |
| `safeFloor_of_seamCosetFloor`           | `safe_sector_of_mim`                   |
| `chain_distance_eq_double`              | `gross_chain_distance_eq_12_of_sectors`|
| `pauli_distance_eq_double`              | `gross_pauli_distance_eq_12_of_sectors`|
-/

import QEC.Stabilizer.Framework.Homological.BBCover

namespace Quantum
namespace Stabilizer
namespace Homological
namespace BB

open scoped BigOperators

set_option maxRecDepth 4096

/-! ## A basis-lift combinator for `𝔽₂`-chain identities

Generic form of the `funLift` pattern used throughout the gross
development: an additive identity between two maps out of a finite
`𝔽₂`-function space holds everywhere once it holds on the `δ`-basis.
(Named `funLiftF2`/`indF2` to avoid clashing with the `BaseGroup`-specific
`funLift`/`ind` in `Codes/BivariateBicycle/LightStabClassify.lean`.) -/

section FunLift

variable {I : Type} [DecidableEq I]

/-- Indicator chain of a finite set. -/
def indF2 (S : Finset I) : I → ZMod 2 := fun i => if i ∈ S then 1 else 0

lemma indF2_empty : indF2 (∅ : Finset I) = 0 := by
  funext i
  simp [indF2]

lemma indF2_insert {a : I} {S : Finset I} (ha : a ∉ S) :
    indF2 (insert a S) = Pi.single a 1 + indF2 S := by
  funext i
  by_cases hi : i = a
  · subst hi
    simp [indF2, ha]
  · simp [indF2, Finset.mem_insert, hi]

lemma self_eq_indF2_filter [Fintype I] (f : I → ZMod 2) :
    f = indF2 (Finset.univ.filter fun i => f i ≠ 0) := by
  funext i
  have key : ∀ a : ZMod 2, a = if a ≠ 0 then 1 else 0 := by decide
  simp only [indF2, Finset.mem_filter, Finset.mem_univ, true_and]
  exact key (f i)

/-- Two additive maps out of `I → ZMod 2` agreeing on the `δ`-basis agree
everywhere. -/
theorem funLiftF2 [Finite I] {W : Type} [AddCommMonoid W]
    (M N : (I → ZMod 2) → W)
    (hM0 : M 0 = 0) (hN0 : N 0 = 0)
    (hMadd : ∀ a b, M (a + b) = M a + M b)
    (hNadd : ∀ a b, N (a + b) = N a + N b)
    (hbasis : ∀ i, M (Pi.single i 1) = N (Pi.single i 1))
    (f : I → ZMod 2) : M f = N f := by
  cases nonempty_fintype I
  have key : ∀ S : Finset I, M (indF2 S) = N (indF2 S) := by
    intro S
    induction S using Finset.induction with
    | empty => rw [indF2_empty, hM0, hN0]
    | @insert p S hp ih => rw [indF2_insert hp, hMadd, hNadd, hbasis p, ih]
  rw [self_eq_indF2_filter f]
  exact key _

end FunLift

namespace XDoubleCoverData

/-- Support split of a chain by a decidable predicate:
`|u| = |u on P| + |u off P|`.  (Lives in this namespace to avoid clashing
with the identical `BB.card_filter_split` in
`Codes/BivariateBicycle/DangerousSector.lean`.) -/
lemma card_filter_split {I : Type} [Fintype I] (u : I → ZMod 2)
    (P : I → Prop) [DecidablePred P] :
    (Finset.univ.filter fun j => u j ≠ 0).card
      = ((Finset.univ.filter fun j => u j ≠ 0).filter P).card
        + ((Finset.univ.filter fun j => u j ≠ 0).filter fun j => ¬ P j).card :=
  (Finset.card_filter_add_card_filter_not
    (s := Finset.univ.filter fun j => u j ≠ 0) (p := P)).symm

variable {G H : Type}
  [Fintype G] [AddCommGroup G] [DecidableEq G]
  [Fintype H] [AddCommGroup H] [DecidableEq H]
  (D : XDoubleCoverData G H)

/-! ## The five per-instance inputs, as named `Prop`s -/

/-- **The base small-cycle floor** (Theorem-A shape): every nonzero base
1-cycle — logical *or* stabilizer — has weight ≥ `d`. -/
def StrongBaseFloor (d : ℕ) : Prop :=
  ∀ u : H × Fin 2 → ZMod 2,
    bbBoundary1Fn D.Ab D.Bb u = 0 → u ≠ 0 →
    d ≤ D.baseComplex.chainWeight u

/-- **The deck homotopy (R)**: the deck translation acts trivially on
`H₁(cover)`. -/
def DeckTrivialOnH1 : Prop :=
  ∀ v : G × Fin 2 → ZMod 2, v ∈ D.coverComplex.cycles →
    v + D.deckShift1 v ∈ D.coverComplex.boundaries

/-- **The dangerous floor at nonzero slice** ((M), `b ≠ 0` rungs): every
nontrivial cover cycle whose pushforward is a *nonzero* base boundary has
weight ≥ `m`. -/
def DangerousFloorNZ (m : ℕ) : Prop :=
  ∀ v : G × Fin 2 → ZMod 2,
    v ∈ D.coverComplex.cycles → v ∉ D.coverComplex.boundaries →
    D.push1 v ∈ D.baseComplex.boundaries → D.push1 v ≠ 0 →
    m ≤ D.coverComplex.chainWeight v

/-- **The safe floor**: every cover cycle whose pushforward is NOT a base
boundary has weight ≥ `m`. -/
def SafeFloor (m : ℕ) : Prop :=
  ∀ v : G × Fin 2 → ZMod 2,
    v ∈ D.coverComplex.cycles → D.push1 v ∉ D.baseComplex.boundaries →
    m ≤ D.coverComplex.chainWeight v

/-- **The Smith-coset floor** ((M-im) shape): every chain in a seam-coset
`seamC ζ + im ∂₂` (`ζ ∈ ker ∂₂`) that is not itself a base boundary has
weight ≥ `m`. -/
def SeamCosetFloor (m : ℕ) : Prop :=
  ∀ ζ : H → ZMod 2, bbBoundary2Fn D.Ab D.Bb ζ = 0 →
    ∀ f : H → ZMod 2,
      D.seamC ζ + bbBoundary2Fn D.Ab D.Bb f ∉ D.baseComplex.boundaries →
      m ≤ D.baseComplex.chainWeight
        (D.seamC ζ + bbBoundary2Fn D.Ab D.Bb f)

/-! ## The homotopy (R) from a finite matrix certificate

A chain homotopy `1 + σ = ∂₂ ∘ C + E ∘ ∂₁` certifies `DeckTrivialOnH1`.
The hypothesis `hbasis` is a finite (`native_decide`-able) statement: the
identity on the `δ`-basis of 1-chains.  The gross polynomial route
(`homotopyChain v = (1+x²)⋆B⋆v_R` with `(1+x²)·B² = 1+x⁶`) is one concrete
way to build such a homotopy; the matrix form also covers instances where
no short polynomial identity exists. -/

lemma bbBoundary1Fn_zero_chain :
    bbBoundary1Fn D.Ac D.Bc (0 : G × Fin 2 → ZMod 2) = 0 := by
  have h : D.coverComplex.boundary1 0 = 0 := map_zero _
  exact h

lemma bbBoundary2Fn_zero_chain :
    bbBoundary2Fn D.Ac D.Bc (0 : G → ZMod 2) = 0 := by
  have h : D.coverComplex.boundary2 0 = 0 := map_zero _
  exact h

lemma deckShift1_add (a b : G × Fin 2 → ZMod 2) :
    D.deckShift1 (a + b) = D.deckShift1 a + D.deckShift1 b := rfl

lemma deckShift1_zero : D.deckShift1 (0 : G × Fin 2 → ZMod 2) = 0 := rfl

/-- **The homotopy certificate lemma**: additive maps `C : C₁ → C₂` and
`E : C₀ → C₁` with `(1 + σ) = ∂₂ ∘ C + E ∘ ∂₁` on the `δ`-basis certify
that the deck acts trivially on `H₁(cover)`. -/
theorem deckTrivial_of_homotopy_certificate
    (Cmap : (G × Fin 2 → ZMod 2) → (G → ZMod 2))
    (Emap : (G → ZMod 2) → (G × Fin 2 → ZMod 2))
    (hC0 : Cmap 0 = 0)
    (hCadd : ∀ a b, Cmap (a + b) = Cmap a + Cmap b)
    (hE0 : Emap 0 = 0)
    (hEadd : ∀ a b, Emap (a + b) = Emap a + Emap b)
    (hbasis : ∀ q : G × Fin 2,
      Pi.single q 1 + D.deckShift1 (Pi.single q 1)
          + Emap (bbBoundary1Fn D.Ac D.Bc (Pi.single q 1))
        = bbBoundary2Fn D.Ac D.Bc (Cmap (Pi.single q 1))) :
    D.DeckTrivialOnH1 := by
  intro v hv
  -- lift the basis identity to all chains
  have key : ∀ w : G × Fin 2 → ZMod 2,
      w + D.deckShift1 w + Emap (bbBoundary1Fn D.Ac D.Bc w)
        = bbBoundary2Fn D.Ac D.Bc (Cmap w) := by
    intro w
    refine funLiftF2
      (fun w => w + D.deckShift1 w + Emap (bbBoundary1Fn D.Ac D.Bc w))
      (fun w => bbBoundary2Fn D.Ac D.Bc (Cmap w))
      ?_ ?_ ?_ ?_ hbasis w
    · change (0 : G × Fin 2 → ZMod 2) + D.deckShift1 0
          + Emap (bbBoundary1Fn D.Ac D.Bc 0) = 0
      rw [D.deckShift1_zero, D.bbBoundary1Fn_zero_chain, hE0, add_zero,
        add_zero]
    · change bbBoundary2Fn D.Ac D.Bc (Cmap 0) = 0
      rw [hC0, D.bbBoundary2Fn_zero_chain]
    · intro a b
      change a + b + D.deckShift1 (a + b)
          + Emap (bbBoundary1Fn D.Ac D.Bc (a + b))
        = (a + D.deckShift1 a + Emap (bbBoundary1Fn D.Ac D.Bc a))
          + (b + D.deckShift1 b + Emap (bbBoundary1Fn D.Ac D.Bc b))
      rw [D.deckShift1_add, bbBoundary1Fn_add, hEadd]
      abel
    · intro a b
      change bbBoundary2Fn D.Ac D.Bc (Cmap (a + b))
        = bbBoundary2Fn D.Ac D.Bc (Cmap a) + bbBoundary2Fn D.Ac D.Bc (Cmap b)
      rw [hCadd, bbBoundary2Fn_add]
  -- for a cycle the `E ∘ ∂₁` term vanishes
  have hv0 : bbBoundary1Fn D.Ac D.Bc v = 0 := hv
  have hkey := key v
  rw [hv0, hE0, add_zero] at hkey
  exact ⟨Cmap v, hkey.symm⟩

/-! ## The Theorem-B floor: `d(cover) ≥ d(base)`, unconditionally -/

/-- From the base floor alone: every nontrivial cover cycle has weight ≥ `d`
(the cover floor `d(cover) ≥ min{d, μ_Z} = d` of Theorem B, in the strong
small-cycle form where the base floor covers stabilizers too). -/
theorem chainWeight_ge_of_strongBaseFloor {d : ℕ}
    (hbase : D.StrongBaseFloor d) :
    ∀ v : G × Fin 2 → ZMod 2,
      v ∈ D.coverComplex.cycles → v ∉ D.coverComplex.boundaries →
      d ≤ D.coverComplex.chainWeight v := by
  intro v hv hnb
  by_cases h0 : D.push1 v = 0
  · -- diagonal: `v = τ(u)` with `u` a nonzero base cycle, `|v| = 2|u| ≥ 2d`
    obtain ⟨u, rfl⟩ := (D.push1_eq_zero_iff v).mp h0
    have hu_cyc : bbBoundary1Fn D.Ab D.Bb u = 0 := D.descend_cycle hv
    have hu_ne : u ≠ 0 := by
      rintro rfl
      exact hnb (by rw [map_zero]; exact zero_mem _)
    have hd := hbase u hu_cyc hu_ne
    rw [D.chainWeight_pull1]
    omega
  · -- projecting: `|v| ≥ |p(v)| ≥ d` since `p(v)` is a nonzero base cycle
    have hcyc : bbBoundary1Fn D.Ab D.Bb (D.push1 v) = 0 := D.push1_mem_cycles hv
    have hd := hbase (D.push1 v) hcyc h0
    exact le_trans hd (D.chainWeight_push_le v)

/-! ## The dangerous rungs -/

/-- **The `b = 0` rung**: a nontrivial cover cycle with zero pushforward is a
diagonal `τ(u)` over a nonzero base cycle, so its weight is `≥ 2d`. -/
theorem dangerous_zero_rung {d : ℕ} (hbase : D.StrongBaseFloor d)
    {v : G × Fin 2 → ZMod 2}
    (hv : v ∈ D.coverComplex.cycles) (hnb : v ∉ D.coverComplex.boundaries)
    (h0 : D.push1 v = 0) :
    2 * d ≤ D.coverComplex.chainWeight v := by
  obtain ⟨u, rfl⟩ := (D.push1_eq_zero_iff v).mp h0
  have hu_cyc : bbBoundary1Fn D.Ab D.Bb u = 0 := D.descend_cycle hv
  have hu_ne : u ≠ 0 := by
    rintro rfl
    exact hnb (by rw [map_zero]; exact zero_mem _)
  have hd := hbase u hu_cyc hu_ne
  rw [D.chainWeight_pull1]
  omega

/-- **The generic single-shape rung** (subsumes the gross hexagon rung): a
nontrivial dangerous cycle over the boundary `b = ∂₂ f₀`, where `b` has
weight `2d − 2t` (`t ≥ 1`) and the sheet-0 seam of the lifted `f₀` is
supported inside `supp b`, has weight ≥ `2d`. -/
theorem dangerous_bound_of_single_shape {d t : ℕ}
    (hbase : D.StrongBaseFloor d) (ht : 1 ≤ t)
    (f₀ : H → ZMod 2)
    (hwb : D.baseComplex.chainWeight (bbBoundary2Fn D.Ab D.Bb f₀) + 2 * t
      = 2 * d)
    (hseam : ∀ j : H × Fin 2,
      D.sheet0 (D.liftStab f₀) j ≠ 0 → bbBoundary2Fn D.Ab D.Bb f₀ j ≠ 0)
    {v : G × Fin 2 → ZMod 2}
    (hv : v ∈ D.coverComplex.cycles) (hnb : v ∉ D.coverComplex.boundaries)
    (hb : D.push1 v = bbBoundary2Fn D.Ab D.Bb f₀) :
    2 * d ≤ D.coverComplex.chainWeight v := by
  classical
  set b : H × Fin 2 → ZMod 2 := bbBoundary2Fn D.Ab D.Bb f₀ with hbdef
  have hwb' : (Finset.univ.filter fun j : H × Fin 2 => b j ≠ 0).card + 2 * t
      = 2 * d := by
    rw [hbdef]
    exact hwb
  by_cases hoff : t ≤ (Finset.univ.filter fun j =>
      D.sheet0 v j ≠ 0 ∧ D.push1 v j = 0).card
  · -- `|v| = |b| + 2·off ≥ (2d − 2t) + 2t = 2d`
    rw [D.chainWeight_sheet_eq, hb, D.baseComplex_chainWeight_eq]
    rw [hb] at hoff
    omega
  · push Not at hoff
    exfalso
    -- normalize: subtract the lifted stabilizer
    have hpush : D.push1 (v + D.liftStab f₀) = 0 := by
      rw [map_add, hb, D.push1_liftStab]
      funext j
      exact CharTwo.add_self_eq_zero _
    obtain ⟨u, hu⟩ := (D.push1_eq_zero_iff _).mp hpush
    -- `u` is a base cycle
    have hvtilde_cyc : D.pull1 u ∈ D.coverComplex.cycles := by
      rw [← hu]
      have h1 : bbBoundary1Fn D.Ac D.Bc (v + D.liftStab f₀) = 0 := by
        have hv0 : bbBoundary1Fn D.Ac D.Bc v = 0 := hv
        have hs0 : bbBoundary1Fn D.Ac D.Bc (D.liftStab f₀) = 0 :=
          bbBoundaryFn_comp D.Ac D.Bc (D.liftC2 f₀)
        rw [bbBoundary1Fn_add, hv0, hs0, add_zero]
      exact h1
    have hu_cyc : bbBoundary1Fn D.Ab D.Bb u = 0 := D.descend_cycle hvtilde_cyc
    -- `u = sheet0 v + seam part`
    have hu_eq : u = D.sheet0 v + D.sheet0 (D.liftStab f₀) := by
      have := congrArg D.sheet0 hu
      rw [D.sheet0_pull1] at this
      rw [← this]
      rfl
    -- the off-`b` support of `u` is at most `t − 1`
    have hu_off : ((Finset.univ.filter fun j => u j ≠ 0).filter
        fun j => ¬ b j ≠ 0).card ≤ t - 1 := by
      have hsub : (Finset.univ.filter fun j => u j ≠ 0).filter
          (fun j => ¬ b j ≠ 0)
          ⊆ Finset.univ.filter fun j =>
              D.sheet0 v j ≠ 0 ∧ D.push1 v j = 0 := by
        intro j hj
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
        obtain ⟨hju, hjb⟩ := hj
        push Not at hjb
        have hseamj : D.liftStab f₀ (D.sec1 j) = 0 := by
          by_contra hcon
          exact (hseam j hcon) hjb
        constructor
        · rw [hu_eq] at hju
          simpa [Pi.add_apply, hseamj] using hju
        · rw [hb]
          exact hjb
      have := Finset.card_le_card hsub
      omega
    -- the on-`b` supports of `u` and `u + b` partition `supp b`
    have hsplit_b : ((Finset.univ.filter fun j => u j ≠ 0).filter
          fun j => b j ≠ 0).card
        + ((Finset.univ.filter fun j => (u + b) j ≠ 0).filter
          fun j => b j ≠ 0).card
        = (Finset.univ.filter fun j : H × Fin 2 => b j ≠ 0).card := by
      have h1 : ((Finset.univ.filter fun j : H × Fin 2 => b j ≠ 0).filter
            fun j => u j ≠ 0).card
          + ((Finset.univ.filter fun j : H × Fin 2 => b j ≠ 0).filter
            fun j => ¬ u j ≠ 0).card
          = (Finset.univ.filter fun j : H × Fin 2 => b j ≠ 0).card := by
        rw [Finset.card_filter_add_card_filter_not]
      have e1 : (Finset.univ.filter fun j : H × Fin 2 => b j ≠ 0).filter
            (fun j => u j ≠ 0)
          = (Finset.univ.filter fun j => u j ≠ 0).filter fun j => b j ≠ 0 := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact and_comm
      have e2 : (Finset.univ.filter fun j : H × Fin 2 => b j ≠ 0).filter
            (fun j => ¬ u j ≠ 0)
          = (Finset.univ.filter fun j => (u + b) j ≠ 0).filter
            fun j => b j ≠ 0 := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Pi.add_apply]
        have key : ∀ a c : ZMod 2, ((c ≠ 0 ∧ ¬ a ≠ 0) ↔ (a + c ≠ 0 ∧ c ≠ 0)) := by
          decide
        exact key (u j) (b j)
      rw [e1, e2] at h1
      exact h1
    have hoff_ub : ((Finset.univ.filter fun j => (u + b) j ≠ 0).filter
        fun j => ¬ b j ≠ 0).card ≤ t - 1 := by
      have e3 : (Finset.univ.filter fun j => (u + b) j ≠ 0).filter
            (fun j => ¬ b j ≠ 0)
          = (Finset.univ.filter fun j => u j ≠ 0).filter
            fun j => ¬ b j ≠ 0 := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Pi.add_apply]
        have key : ∀ a c : ZMod 2, ((a + c ≠ 0 ∧ ¬ c ≠ 0) ↔ (a ≠ 0 ∧ ¬ c ≠ 0)) := by
          decide
        exact key (u j) (b j)
      rw [e3]
      exact hu_off
    -- choose the lighter of `u`, `u + b`: its weight is ≤ d − 1
    have hb_cyc : bbBoundary1Fn D.Ab D.Bb b = 0 :=
      bbBoundaryFn_comp D.Ab D.Bb f₀
    have hsmall : ∃ u'' : H × Fin 2 → ZMod 2,
        bbBoundary1Fn D.Ab D.Bb u'' = 0 ∧
        (Finset.univ.filter fun j => u'' j ≠ 0).card ≤ d - 1 ∧
        (u'' = u ∨ u'' = u + b) := by
      by_cases hcase : ((Finset.univ.filter fun j => u j ≠ 0).filter
          fun j => b j ≠ 0).card ≤ d - t
      · refine ⟨u, hu_cyc, ?_, Or.inl rfl⟩
        rw [card_filter_split u fun j => b j ≠ 0]
        omega
      · refine ⟨u + b, ?_, ?_, Or.inr rfl⟩
        · rw [bbBoundary1Fn_add, hu_cyc, hb_cyc, add_zero]
        · rw [card_filter_split (u + b) fun j => b j ≠ 0]
          omega
    obtain ⟨u'', hu''_cyc, hu''_card, hu''_form⟩ := hsmall
    -- the base floor kills it
    have hu''_zero : u'' = 0 := by
      by_contra hne
      have := hbase u'' hu''_cyc hne
      rw [D.baseComplex_chainWeight_eq] at this
      omega
    -- either way `v` is a boundary — contradiction
    have hb_bd : b ∈ D.baseComplex.boundaries := ⟨f₀, rfl⟩
    have hu_bd : u ∈ D.baseComplex.boundaries := by
      rcases hu''_form with hform | hform
      · rw [← hform, hu''_zero]
        exact zero_mem _
      · have hu_eq2 : u = u'' + b := by
          rw [hform]
          funext j
          rw [Pi.add_apply, Pi.add_apply]
          have key : ∀ a c : ZMod 2, a = a + c + c := by decide
          exact key (u j) (b j)
        rw [hu_eq2, hu''_zero, zero_add]
        exact hb_bd
    apply hnb
    have hvform : v = D.pull1 u + D.liftStab f₀ := by
      rw [← hu]
      funext p
      have key : ∀ a c : ZMod 2, a = a + c + c := by decide
      exact key (v p) (D.liftStab f₀ p)
    rw [hvform]
    exact add_mem (D.pull1_mem_boundaries hu_bd) (D.liftStab_mem_boundaries _)

/-- **The generic pair-shape rung** (subsumes the gross D-pair rung): a
nontrivial dangerous cycle over `b = b₁ + b₂` (`bᵢ = ∂₂ fᵢ`), where `b` has
weight `2d − 2t` (`t ≥ 1`), the support union `U` of `b₁, b₂` satisfies
`|U| + 2(t−1) ≤ 2d − 1`, and the sheet-0 seam of the lifted `f₁ + f₂` is
supported inside `U`, has weight ≥ `2d`. -/
theorem dangerous_bound_of_pair_shape {d t : ℕ}
    (hbase : D.StrongBaseFloor d) (ht : 1 ≤ t)
    (f₁ f₂ : H → ZMod 2)
    (hwb : D.baseComplex.chainWeight
        (bbBoundary2Fn D.Ab D.Bb f₁ + bbBoundary2Fn D.Ab D.Bb f₂) + 2 * t
      = 2 * d)
    (hU : (Finset.univ.filter fun j : H × Fin 2 =>
        bbBoundary2Fn D.Ab D.Bb f₁ j ≠ 0 ∨
        bbBoundary2Fn D.Ab D.Bb f₂ j ≠ 0).card + 2 * (t - 1) ≤ 2 * d - 1)
    (hseam : ∀ j : H × Fin 2,
      D.sheet0 (D.liftStab (f₁ + f₂)) j ≠ 0 →
      (bbBoundary2Fn D.Ab D.Bb f₁ j ≠ 0 ∨ bbBoundary2Fn D.Ab D.Bb f₂ j ≠ 0))
    {v : G × Fin 2 → ZMod 2}
    (hv : v ∈ D.coverComplex.cycles) (hnb : v ∉ D.coverComplex.boundaries)
    (hb : D.push1 v
      = bbBoundary2Fn D.Ab D.Bb f₁ + bbBoundary2Fn D.Ab D.Bb f₂) :
    2 * d ≤ D.coverComplex.chainWeight v := by
  classical
  set b₁ : H × Fin 2 → ZMod 2 := bbBoundary2Fn D.Ab D.Bb f₁ with hb₁def
  set b₂ : H × Fin 2 → ZMod 2 := bbBoundary2Fn D.Ab D.Bb f₂ with hb₂def
  have hb12 : bbBoundary2Fn D.Ab D.Bb (f₁ + f₂) = b₁ + b₂ := by
    rw [bbBoundary2Fn_add]
  by_cases hoff : t ≤ (Finset.univ.filter fun j =>
      D.sheet0 v j ≠ 0 ∧ D.push1 v j = 0).card
  · rw [D.chainWeight_sheet_eq, hb]
    have hwb' : D.baseComplex.chainWeight (b₁ + b₂) + 2 * t = 2 * d := hwb
    rw [hb] at hoff
    omega
  · push Not at hoff
    exfalso
    -- normalize
    have hpush : D.push1 (v + D.liftStab (f₁ + f₂)) = 0 := by
      rw [map_add, hb, D.push1_liftStab, hb12]
      funext j
      rw [Pi.add_apply]
      exact CharTwo.add_self_eq_zero ((b₁ + b₂) j)
    obtain ⟨u, hu⟩ := (D.push1_eq_zero_iff _).mp hpush
    have hvtilde_cyc : D.pull1 u ∈ D.coverComplex.cycles := by
      rw [← hu]
      have h1 : bbBoundary1Fn D.Ac D.Bc (v + D.liftStab (f₁ + f₂)) = 0 := by
        have hv0 : bbBoundary1Fn D.Ac D.Bc v = 0 := hv
        have hs0 : bbBoundary1Fn D.Ac D.Bc (D.liftStab (f₁ + f₂)) = 0 :=
          bbBoundaryFn_comp D.Ac D.Bc (D.liftC2 (f₁ + f₂))
        rw [bbBoundary1Fn_add, hv0, hs0, add_zero]
      exact h1
    have hu_cyc : bbBoundary1Fn D.Ab D.Bb u = 0 := D.descend_cycle hvtilde_cyc
    have hu_eq : u = D.sheet0 v + D.sheet0 (D.liftStab (f₁ + f₂)) := by
      have h2 := congrArg D.sheet0 hu
      rw [D.sheet0_pull1] at h2
      rw [← h2]
      rfl
    -- off-`U` support of `u` is confined to the off-slice cells (≤ t − 1)
    have hUoff : (Finset.univ.filter fun j =>
        u j ≠ 0 ∧ ¬ (b₁ j ≠ 0 ∨ b₂ j ≠ 0)).card ≤ t - 1 := by
      have hsub : (Finset.univ.filter fun j =>
            u j ≠ 0 ∧ ¬ (b₁ j ≠ 0 ∨ b₂ j ≠ 0))
          ⊆ Finset.univ.filter fun j =>
              D.sheet0 v j ≠ 0 ∧ D.push1 v j = 0 := by
        intro j hj
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
        obtain ⟨hju, hjU⟩ := hj
        push Not at hjU
        obtain ⟨h1, h2⟩ := hjU
        have hbj : D.push1 v j = 0 := by
          rw [hb]
          simp only [Pi.add_apply, h1, h2, add_zero]
        have hseamj : D.liftStab (f₁ + f₂) (D.sec1 j) = 0 := by
          by_contra hcon2
          rcases hseam j hcon2 with h | h
          · exact h h1
          · exact h h2
        have hsheet : D.sheet0 v j ≠ 0 := by
          rw [hu_eq] at hju
          simpa [Pi.add_apply, hseamj] using hju
        exact ⟨hsheet, hbj⟩
      have := Finset.card_le_card hsub
      omega
    -- counting over the four translates
    have hcount : (Finset.univ.filter fun j => u j ≠ 0).card
        + (Finset.univ.filter fun j => (u + b₁) j ≠ 0).card
        + (Finset.univ.filter fun j => (u + b₂) j ≠ 0).card
        + (Finset.univ.filter fun j => (u + b₁ + b₂) j ≠ 0).card
        ≤ 2 * (Finset.univ.filter fun j : H × Fin 2 =>
            b₁ j ≠ 0 ∨ b₂ j ≠ 0).card
          + 4 * (Finset.univ.filter fun j =>
            u j ≠ 0 ∧ ¬ (b₁ j ≠ 0 ∨ b₂ j ≠ 0)).card := by
      have hpt : ∀ j : H × Fin 2,
          ((if u j ≠ 0 then 1 else 0) : ℕ)
            + (if (u + b₁) j ≠ 0 then 1 else 0)
            + (if (u + b₂) j ≠ 0 then 1 else 0)
            + (if (u + b₁ + b₂) j ≠ 0 then 1 else 0)
          ≤ 2 * (if b₁ j ≠ 0 ∨ b₂ j ≠ 0 then 1 else 0)
            + 4 * (if u j ≠ 0 ∧ ¬ (b₁ j ≠ 0 ∨ b₂ j ≠ 0) then 1 else 0) := by
        intro j
        by_cases hUj : b₁ j ≠ 0 ∨ b₂ j ≠ 0
        · rw [if_pos hUj,
            if_neg (show ¬ (u j ≠ 0 ∧ ¬ (b₁ j ≠ 0 ∨ b₂ j ≠ 0)) from
              fun hcon => hcon.2 hUj)]
          simp only [Pi.add_apply]
          have key : ∀ a β₁ β₂ : ZMod 2, (β₁ ≠ 0 ∨ β₂ ≠ 0) →
              ((if a ≠ 0 then 1 else 0) : ℕ)
                + (if a + β₁ ≠ 0 then 1 else 0)
                + (if a + β₂ ≠ 0 then 1 else 0)
                + (if a + β₁ + β₂ ≠ 0 then 1 else 0) = 2 := by decide
          rw [key (u j) (b₁ j) (b₂ j) hUj]
        · rw [if_neg hUj]
          push Not at hUj
          simp only [Pi.add_apply]
          have key : ∀ a β₁ β₂ : ZMod 2, β₁ = 0 → β₂ = 0 →
              ((if a ≠ 0 then 1 else 0) : ℕ)
                + (if a + β₁ ≠ 0 then 1 else 0)
                + (if a + β₂ ≠ 0 then 1 else 0)
                + (if a + β₁ + β₂ ≠ 0 then 1 else 0)
              = 4 * (if a ≠ 0 then 1 else 0) := by decide
          rw [key (u j) (b₁ j) (b₂ j) hUj.1 hUj.2]
          by_cases hju : u j ≠ 0
          · rw [if_pos hju,
              if_pos (show u j ≠ 0 ∧ ¬ (b₁ j ≠ 0 ∨ b₂ j ≠ 0) from
                ⟨hju, fun hor => hor.elim (fun h => h hUj.1)
                  (fun h => h hUj.2)⟩)]
          · rw [if_neg hju,
              if_neg (show ¬ (u j ≠ 0 ∧ ¬ (b₁ j ≠ 0 ∨ b₂ j ≠ 0)) from
                fun hcon => hju hcon.1)]
      calc (Finset.univ.filter fun j => u j ≠ 0).card
            + (Finset.univ.filter fun j => (u + b₁) j ≠ 0).card
            + (Finset.univ.filter fun j => (u + b₂) j ≠ 0).card
            + (Finset.univ.filter fun j => (u + b₁ + b₂) j ≠ 0).card
          = ∑ j : H × Fin 2,
              (((if u j ≠ 0 then 1 else 0) : ℕ)
                + (if (u + b₁) j ≠ 0 then 1 else 0)
                + (if (u + b₂) j ≠ 0 then 1 else 0)
                + (if (u + b₁ + b₂) j ≠ 0 then 1 else 0)) := by
            simp only [Finset.sum_add_distrib, Finset.card_filter]
        _ ≤ ∑ j : H × Fin 2,
              (2 * (if b₁ j ≠ 0 ∨ b₂ j ≠ 0 then 1 else 0)
                + 4 * (if u j ≠ 0 ∧ ¬ (b₁ j ≠ 0 ∨ b₂ j ≠ 0) then 1 else 0)) :=
            Finset.sum_le_sum fun j _ => hpt j
        _ = 2 * (Finset.univ.filter fun j : H × Fin 2 =>
              b₁ j ≠ 0 ∨ b₂ j ≠ 0).card
            + 4 * (Finset.univ.filter fun j =>
              u j ≠ 0 ∧ ¬ (b₁ j ≠ 0 ∨ b₂ j ≠ 0)).card := by
            rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
              ← Finset.card_filter, ← Finset.card_filter]
    -- one of the four translates is lighter than `d`
    have hb₁_cyc : bbBoundary1Fn D.Ab D.Bb b₁ = 0 :=
      bbBoundaryFn_comp D.Ab D.Bb f₁
    have hb₂_cyc : bbBoundary1Fn D.Ab D.Bb b₂ = 0 :=
      bbBoundaryFn_comp D.Ab D.Bb f₂
    have hsmall : ∃ r : H × Fin 2 → ZMod 2,
        bbBoundary1Fn D.Ab D.Bb r = 0 ∧
        (Finset.univ.filter fun j => r j ≠ 0).card ≤ d - 1 ∧
        (u = r ∨ u = r + b₁ ∨ u = r + b₂ ∨ u = r + b₁ + b₂) := by
      have hflip : ∀ a c : ZMod 2, a = a + c + c := by decide
      by_cases h0 : (Finset.univ.filter fun j => u j ≠ 0).card ≤ d - 1
      · exact ⟨u, hu_cyc, h0, Or.inl rfl⟩
      by_cases h1 : (Finset.univ.filter fun j => (u + b₁) j ≠ 0).card ≤ d - 1
      · refine ⟨u + b₁, ?_, h1, Or.inr (Or.inl ?_)⟩
        · rw [bbBoundary1Fn_add, hu_cyc, hb₁_cyc, add_zero]
        · funext j
          exact hflip (u j) (b₁ j)
      by_cases h2 : (Finset.univ.filter fun j => (u + b₂) j ≠ 0).card ≤ d - 1
      · refine ⟨u + b₂, ?_, h2, Or.inr (Or.inr (Or.inl ?_))⟩
        · rw [bbBoundary1Fn_add, hu_cyc, hb₂_cyc, add_zero]
        · funext j
          exact hflip (u j) (b₂ j)
      · refine ⟨u + b₁ + b₂, ?_, by omega, Or.inr (Or.inr (Or.inr ?_))⟩
        · rw [bbBoundary1Fn_add, bbBoundary1Fn_add, hu_cyc, hb₁_cyc, hb₂_cyc,
            add_zero, add_zero]
        · funext j
          simp only [Pi.add_apply]
          have key5 : ∀ a c e : ZMod 2, a = a + c + e + c + e := by decide
          exact key5 (u j) (b₁ j) (b₂ j)
    obtain ⟨r, hr_cyc, hr_card, hr_form⟩ := hsmall
    have hr_zero : r = 0 := by
      by_contra hne
      have := hbase r hr_cyc hne
      rw [D.baseComplex_chainWeight_eq] at this
      omega
    -- `u` is a base boundary in every case
    have hb₁_bd : b₁ ∈ D.baseComplex.boundaries := ⟨f₁, rfl⟩
    have hb₂_bd : b₂ ∈ D.baseComplex.boundaries := ⟨f₂, rfl⟩
    have hu_bd : u ∈ D.baseComplex.boundaries := by
      rcases hr_form with rfl | rfl | rfl | rfl
      · rw [hr_zero] at *
        exact zero_mem _
      · rw [hr_zero, zero_add]
        exact hb₁_bd
      · rw [hr_zero, zero_add]
        exact hb₂_bd
      · rw [hr_zero, zero_add]
        exact add_mem hb₁_bd hb₂_bd
    apply hnb
    have hvform : v = D.pull1 u + D.liftStab (f₁ + f₂) := by
      rw [← hu]
      funext p
      have key : ∀ a c : ZMod 2, a = a + c + c := by decide
      exact key (v p) (D.liftStab (f₁ + f₂) p)
    rw [hvform]
    exact add_mem (D.pull1_mem_boundaries hu_bd)
      (D.liftStab_mem_boundaries _)

/-! ## The safe-sector reduction -/

/-- **The safe-sector reduction**: the homotopy (R) confines safe
projections to the Smith seam-cosets, so the seam-coset floor transfers to
the safe sector. -/
theorem safeFloor_of_seamCosetFloor {m : ℕ}
    (hR : D.DeckTrivialOnH1) (hMim : D.SeamCosetFloor m) :
    D.SafeFloor m := by
  intro v hv hb
  -- (R): `v + σv = ∂₂ z` for some cover 2-chain `z`
  obtain ⟨z, hz⟩ := hR v hv
  have hR' : bbBoundary2Fn D.Ac D.Bc z = v + D.deckShift1 v := hz
  -- split the homotopy 2-chain into sheets
  have hsplit : v + D.deckShift1 v
      = D.liftStab (D.sheetC2_0 z)
        + D.deckShift1 (D.liftStab (D.sheetC2_1 z)) := by
    rw [← hR']
    conv_lhs => rw [D.liftC2_decomp z]
    rw [bbBoundary2Fn_add, D.liftStab_deckShift]
    rfl
  -- read the two sheet components: both equal `w := p(v)`
  have hw0 : ∀ j, D.push1 v j
      = D.seamN (D.sheetC2_0 z) j + D.seamC (D.sheetC2_1 z) j := by
    intro j
    calc D.push1 v j
        = D.sheet0 (v + D.deckShift1 v) j := (D.sheet0_self_add_deck v j).symm
      _ = D.sheet0 (D.liftStab (D.sheetC2_0 z)
            + D.deckShift1 (D.liftStab (D.sheetC2_1 z))) j := by
          rw [hsplit]
      _ = D.seamN (D.sheetC2_0 z) j + D.seamC (D.sheetC2_1 z) j := by
          rw [D.sheet0_add, Pi.add_apply, D.sheet0_deckShift1]
          rfl
  have hw1 : ∀ j, D.push1 v j
      = D.seamC (D.sheetC2_0 z) j + D.seamN (D.sheetC2_1 z) j := by
    intro j
    calc D.push1 v j
        = D.sheet1 (v + D.deckShift1 v) j := (D.sheet1_self_add_deck v j).symm
      _ = D.sheet1 (D.liftStab (D.sheetC2_0 z)
            + D.deckShift1 (D.liftStab (D.sheetC2_1 z))) j := by
          rw [hsplit]
      _ = D.seamC (D.sheetC2_0 z) j + D.seamN (D.sheetC2_1 z) j := by
          rw [D.sheet1_add, Pi.add_apply, D.sheet1_deckShift1]
          rfl
  -- the sheet sum is a 2-cycle
  have hker : bbBoundary2Fn D.Ab D.Bb (D.sheetC2_0 z + D.sheetC2_1 z) = 0 := by
    funext j
    rw [bbBoundary2Fn_add, Pi.add_apply, Pi.zero_apply]
    have hkey : ∀ n0 c0 n1 c1 w b0 b1 : ZMod 2,
        w = n0 + c1 → w = c0 + n1 → n0 + c0 = b0 → n1 + c1 = b1 →
        b0 + b1 = 0 := by decide
    exact hkey _ _ _ _ _ _ _ (hw0 j) (hw1 j)
      (D.seamN_add_seamC (D.sheetC2_0 z) j)
      (D.seamN_add_seamC (D.sheetC2_1 z) j)
  -- the Smith-coset form of `w`
  have hwform : D.push1 v
      = D.seamC (D.sheetC2_0 z + D.sheetC2_1 z)
        + bbBoundary2Fn D.Ab D.Bb (D.sheetC2_0 z) := by
    funext j
    rw [Pi.add_apply, D.seamC_add, Pi.add_apply]
    have hkey : ∀ n0 c0 c1 w b0 : ZMod 2,
        w = n0 + c1 → n0 + c0 = b0 → w = (c0 + c1) + b0 := by decide
    exact hkey _ _ _ _ _ (hw0 j)
      (D.seamN_add_seamC (D.sheetC2_0 z) j)
  -- conclude via the seam-coset floor
  have hm : m ≤ D.baseComplex.chainWeight (D.push1 v) := by
    rw [hwform]
    refine hMim _ hker _ ?_
    rw [← hwform]
    exact hb
  exact le_trans hm (D.chainWeight_push_le v)

/-! ## The assembly: `d(cover) = 2·d(base)` -/

/-- **Sector-dichotomy assembly**: given the base floor and the two sector
floors, every nontrivial cover cycle has weight ≥ `2d`. -/
theorem chainWeight_ge_double_of_sectors {d : ℕ}
    (hbase : D.StrongBaseFloor d)
    (hM : D.DangerousFloorNZ (2 * d)) (hS : D.SafeFloor (2 * d)) :
    ∀ v : G × Fin 2 → ZMod 2,
      v ∈ D.coverComplex.cycles → v ∉ D.coverComplex.boundaries →
      2 * d ≤ D.coverComplex.chainWeight v := by
  intro v hv hnb
  by_cases hb : D.push1 v ∈ D.baseComplex.boundaries
  · by_cases h0 : D.push1 v = 0
    · exact D.dangerous_zero_rung hbase hv hnb h0
    · exact hM v hv hnb hb h0
  · exact hS v hv hb

/-- **Chain-level `d(cover) = 2·d(base)`**: the doubled weight is attained
(by the diagonal lift of the tight witness) and minimal (by the sectors). -/
theorem chain_distance_eq_double {d : ℕ}
    (hbase : D.StrongBaseFloor d)
    (hM : D.DangerousFloorNZ (2 * d)) (hS : D.SafeFloor (2 * d))
    (uStar : H × Fin 2 → ZMod 2)
    (hu_cyc : uStar ∈ D.baseComplex.cycles)
    (hu_w : D.baseComplex.chainWeight uStar = d)
    (hτnb : D.pull1 uStar ∉ D.coverComplex.boundaries) :
    IsLeast {w : ℕ | ∃ v : G × Fin 2 → ZMod 2,
      v ∈ D.coverComplex.cycles ∧ v ∉ D.coverComplex.boundaries ∧
      D.coverComplex.chainWeight v = w} (2 * d) := by
  constructor
  · refine ⟨D.pull1 uStar, D.pull1_mem_cycles hu_cyc, hτnb, ?_⟩
    rw [D.chainWeight_pull1, hu_w]
  · rintro w ⟨v, hv, hnb, rfl⟩
    exact D.chainWeight_ge_double_of_sectors hbase hM hS v hv hnb

/-! ## The dual side and the Pauli level -/

/-- Dual-side mirror of the sector bound, via the chain-level `d_X = d_Z`
duality. -/
theorem dual_chainWeight_ge_double_of_sectors {d : ℕ}
    (hbase : D.StrongBaseFloor d)
    (hM : D.DangerousFloorNZ (2 * d)) (hS : D.SafeFloor (2 * d)) :
    ∀ c ∈ D.coverComplex.dualCycles, c ∉ D.coverComplex.dualBoundaries →
      2 * d ≤ D.coverComplex.chainWeight c := by
  have hX : ∀ c ∈ (bbChainComplex D.Ac D.Bc).cycles,
      c ∉ (bbChainComplex D.Ac D.Bc).boundaries →
      2 * d ≤ (bbChainComplex D.Ac D.Bc).chainWeight c := fun c hc hnb =>
    D.chainWeight_ge_double_of_sectors hbase hM hS c hc hnb
  exact (bb_cycle_bound_iff_dual_bound D.Ac D.Bc (2 * d)).mp hX

/-- Pauli-level lower bound from the sector inputs: every nontrivial logical
operator of the cover's homological stabilizer group has weight ≥ `2d`. -/
theorem logical_weight_ge_double_of_sectors {d : ℕ}
    (hbase : D.StrongBaseFloor d)
    (hM : D.DangerousFloorNZ (2 * d)) (hS : D.SafeFloor (2 * d))
    (g : NQubitPauliGroupElement D.coverComplex.numQubits)
    (hg : Quantum.StabilizerGroup.IsNontrivialLogicalOperator g
      D.coverComplex.homologicalStabilizerGroup) :
    2 * d ≤ NQubitPauliGroupElement.weight g :=
  HomologicalCode.chainWeight_lower_bound_transfers D.coverComplex (2 * d)
    (fun c hc hnb => D.chainWeight_ge_double_of_sectors hbase hM hS c hc hnb)
    (D.dual_chainWeight_ge_double_of_sectors hbase hM hS) g hg

/-- **Pauli-level `d(cover) = 2·d(base)`**: given the base floor, the two
sector floors and the tight witness, `2d` is the least weight of a
nontrivial logical operator of the cover's homological stabilizer group. -/
theorem pauli_distance_eq_double {d : ℕ}
    (hbase : D.StrongBaseFloor d)
    (hM : D.DangerousFloorNZ (2 * d)) (hS : D.SafeFloor (2 * d))
    (uStar : H × Fin 2 → ZMod 2)
    (hu_cyc : uStar ∈ D.baseComplex.cycles)
    (hu_w : D.baseComplex.chainWeight uStar = d)
    (hτnb : D.pull1 uStar ∉ D.coverComplex.boundaries) :
    IsLeast {w : ℕ | ∃ g : NQubitPauliGroupElement D.coverComplex.numQubits,
      Quantum.StabilizerGroup.IsNontrivialLogicalOperator g
        D.coverComplex.homologicalStabilizerGroup ∧
      NQubitPauliGroupElement.weight g = w} (2 * d) := by
  constructor
  · refine ⟨D.coverComplex.chainXOperator (D.pull1 uStar), ?_, ?_⟩
    · exact (HomologicalCode.chainXOperator_isNontrivialLogical_iff
        (X := D.coverComplex) (D.pull1 uStar)).mpr
        ⟨D.pull1_mem_cycles hu_cyc, hτnb⟩
    · rw [HomologicalCode.weight_chainXOperator, D.chainWeight_pull1, hu_w]
  · rintro w ⟨g, hg, rfl⟩
    exact D.logical_weight_ge_double_of_sectors hbase hM hS g hg

end XDoubleCoverData

end BB
end Homological
end Stabilizer
end Quantum
