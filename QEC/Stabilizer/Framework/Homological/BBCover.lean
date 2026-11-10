import QEC.Stabilizer.Framework.Homological.Covering

/-!
# Free double covers of bivariate bicycle codes

A bivariate bicycle code over a finite abelian group `G`, with polynomials
`A_c`, `B_c`, is a *free double cover* of one over `H`, with polynomials `A_b`,
`B_b`, when there is a homomorphism `proj : G →+ H` such that

* the fibers of `proj` are the orbits `{g, g + s}` of a nonzero *deck
  translation* `s : G`, so that `proj` is two-to-one, and
* the polynomials descend: `proj_* A_c = A_b` and `proj_* B_c = B_b`, where
  `proj_*` is summation over the fibers.

The standard example is the reduction `ZMod (2 * ℓ) × ZMod m → ZMod ℓ × ZMod m`
of the first coordinate, with `s = (ℓ, 0)`.

`XDoubleCoverData G H` bundles `proj`, `s = deckS`, the four polynomials and a
set-theoretic section `sec` of `proj`. The image of `sec` is called *sheet 0*
and its deck translate *sheet 1*. Everything else is derived from the bundle.

## Main definitions

* `coverComplex`, `baseComplex`: the two bivariate bicycle chain complexes.
* `push0`, `push1`: the pushforward `p` (fiber summation) on chains indexed by
  `G` and on 1-chains; `pull0`, `pull1`: the pullback `τ` (composition with the
  projection).
* `deckShift0`, `deckShift1`: the action `σ` of the deck translation on chains.
* `sheet0`, `sheet1`: the restrictions of a cover 1-chain to the two sheets,
  as base 1-chains; `sheetC2_0`, `sheetC2_1`: the same for chains indexed by
  `G`.
* `liftC2 ξ`: the cover chain that equals `ξ` on sheet 0 and vanishes on
  sheet 1; `liftStab ξ = ∂₂ (liftC2 ξ)`.
* `seamN ξ`, `seamC ξ`: the sheet-0 and sheet-1 parts of `liftStab ξ`.

## Main statements

* `push_boundary1_comm`, `push_boundary2_comm`, `pull_boundary1_comm`,
  `pull_boundary2_comm`: `p` and `τ` are chain maps.
* `push1_pull1_eq_zero`, `push1_eq_zero_iff`, `pull1_push1`: `p ∘ τ = 0`,
  `ker p = im τ` and `τ ∘ p = 1 + σ` on 1-chains.
* `exists_pull_eq_add_boundary`: a cover cycle whose pushforward is a base
  boundary is, up to a cover boundary, the pullback of a base cycle.
* `chainWeight_eq_push_add_overlap`, `chainWeight_sheet_eq`,
  `chainWeight_push_le`, `chainWeight_pull1`: the weight of a cover chain in
  terms of its pushforward; `p` does not increase weight and `τ` doubles it.
* `liftC2_decomp`: a cover chain is the sum of the lifts of its two sheets.
* `seamN_add_seamC`: `seamN ξ + seamC ξ = ∂₂ ξ`.
* `seamC_mem_cycles`: if `∂₂ ζ = 0` then `seamC ζ` is a base cycle. On homology
  this is the connecting map from `ker ∂₂` to `H₁` of the base complex that the
  cover induces.
-/

namespace Quantum
namespace Stabilizer
namespace Homological
namespace BB

open scoped BigOperators

/-- A bivariate bicycle code over `G` presented as a free double cover of one
over `H`: a projection `proj : G →+ H` whose fibers are the orbits of a nonzero
deck translation `deckS`, a section `sec` of `proj`, and polynomials `Ac`, `Bc`
on `G` whose fiber sums along `proj` are `Ab`, `Bb`. -/
structure XDoubleCoverData (G H : Type)
    [Fintype G] [AddCommGroup G] [DecidableEq G]
    [Fintype H] [AddCommGroup H] [DecidableEq H] where
  /-- The covering projection. -/
  proj : G →+ H
  /-- The deck translation: the nonzero element of the kernel of `proj`. -/
  deckS : G
  /-- A set-theoretic section of `proj`. -/
  sec : H → G
  /-- The polynomial `A` of the cover code. -/
  Ac : G → ZMod 2
  /-- The polynomial `B` of the cover code. -/
  Bc : G → ZMod 2
  /-- The polynomial `A` of the base code. -/
  Ab : H → ZMod 2
  /-- The polynomial `B` of the base code. -/
  Bb : H → ZMod 2
  /-- The deck translation is nonzero, so the cover is two-to-one. -/
  deckS_ne_zero : deckS ≠ 0
  /-- The fibers of `proj` are the orbits of the deck translation. -/
  proj_fiber : ∀ g g' : G, proj g' = proj g ↔ g' = g ∨ g' = g + deckS
  /-- `sec` is a section of `proj`. -/
  proj_sec : ∀ p : H, proj (sec p) = p
  /-- The polynomial `A` descends: the fiber sums of `Ac` are `Ab`. -/
  push_A : fiberSumFn ⇑proj Ac = Ab
  /-- The polynomial `B` descends: the fiber sums of `Bc` are `Bb`. -/
  push_B : fiberSumFn ⇑proj Bc = Bb

namespace XDoubleCoverData

variable {G H : Type}
  [Fintype G] [AddCommGroup G] [DecidableEq G]
  [Fintype H] [AddCommGroup H] [DecidableEq H]
  (D : XDoubleCoverData G H)

/-! ## The deck translation -/

/-- The deck translation lies in the kernel of the projection. -/
lemma proj_deckS : D.proj D.deckS = 0 := by
  simpa using (D.proj_fiber 0 D.deckS).mpr (Or.inr (zero_add _).symm)

/-- The deck translation has order two. -/
lemma deckS_add_deckS : D.deckS + D.deckS = 0 := by
  rcases (D.proj_fiber D.deckS 0).mp (by rw [map_zero, D.proj_deckS]) with h | h
  exacts [absurd h.symm D.deckS_ne_zero, h.symm]

/-- The deck translation is its own negative. -/
lemma neg_deckS : -D.deckS = D.deckS :=
  neg_eq_of_add_eq_zero_left D.deckS_add_deckS

/-- The projection is invariant under the deck translation. -/
lemma proj_add_deckS (g : G) : D.proj (g + D.deckS) = D.proj g :=
  (D.proj_fiber g (g + D.deckS)).mpr (Or.inr rfl)

/-- The projection is surjective, having a section. -/
lemma proj_surjective : Function.Surjective ⇑D.proj := fun p =>
  ⟨D.sec p, D.proj_sec p⟩

/-- Every point of `G` is the section point of its fiber or its deck
translate: it lies on sheet 0 or on sheet 1. -/
lemma point_dichotomy (g : G) :
    g = D.sec (D.proj g) ∨ g = D.sec (D.proj g) + D.deckS :=
  (D.proj_fiber (D.sec (D.proj g)) g).mp (D.proj_sec (D.proj g)).symm

/-! ## The two chain complexes -/

/-- The chain complex of the cover code. -/
noncomputable def coverComplex : HomologicalCode := bbChainComplex D.Ac D.Bc

/-- The chain complex of the base code. -/
noncomputable def baseComplex : HomologicalCode := bbChainComplex D.Ab D.Bb

/-! ## The deck translation on qubits and chains -/

/-- The deck involution on the qubits of the cover: translate the group
coordinate by `deckS` and keep the block. -/
def deckSigma1 : G × Fin 2 → G × Fin 2 :=
  fun p => (p.1 + D.deckS, p.2)

@[simp] lemma deckSigma1_apply (p : G × Fin 2) :
    D.deckSigma1 p = (p.1 + D.deckS, p.2) := rfl

/-- The deck translation `σ` on chains indexed by `G`:
`(σ v) g = v (g + deckS)`. -/
def deckShift0 (v : G → ZMod 2) : G → ZMod 2 :=
  fun g => v (g + D.deckS)

/-- The deck translation `σ` on 1-chains: `(σ v) p = v (deckSigma1 p)`. -/
def deckShift1 (v : G × Fin 2 → ZMod 2) : G × Fin 2 → ZMod 2 :=
  fun p => v (p.1 + D.deckS, p.2)

@[simp] lemma deckShift0_apply (v : G → ZMod 2) (g : G) :
    D.deckShift0 v g = v (g + D.deckS) := rfl

@[simp] lemma deckShift1_apply (v : G × Fin 2 → ZMod 2) (p : G × Fin 2) :
    D.deckShift1 v p = v (p.1 + D.deckS, p.2) := rfl

/-- The deck involution on qubits has no fixed points. -/
lemma deckSigma1_ne (p : G × Fin 2) : D.deckSigma1 p ≠ p := fun hp =>
  D.deckS_ne_zero (add_eq_left.mp (congrArg Prod.fst hp))

/-- The fibers of `Prod.map proj id` on qubits are the orbits of
`deckSigma1`. -/
lemma proj_prodMap_fiber (q q' : G × Fin 2) :
    Prod.map ⇑D.proj id q' = Prod.map ⇑D.proj id q
      ↔ q' = q ∨ q' = D.deckSigma1 q := by
  simp only [Prod.ext_iff, Prod.map_fst, Prod.map_snd, id_eq, deckSigma1_apply,
    D.proj_fiber q.1 q'.1]
  tauto

/-- The section of `Prod.map proj id` on qubits induced by `sec`. -/
def sec1 : H × Fin 2 → G × Fin 2 := Prod.map D.sec id

/-- `sec1` is a section of `Prod.map proj id`. -/
lemma proj_prodMap_sec1 (p : H × Fin 2) :
    Prod.map ⇑D.proj id (D.sec1 p) = p :=
  Prod.ext (D.proj_sec p.1) rfl

/-! ## Pushforward and pullback -/

/-- The pushforward `p` on chains indexed by `G` (0- and 2-chains): summation
over the fibers of `proj`. -/
noncomputable def push0 :
    (G → ZMod 2) →ₗ[ZMod 2] (H → ZMod 2) :=
  fiberSum ⇑D.proj

/-- The pushforward `p` on 1-chains: summation over the fibers of
`Prod.map proj id`. -/
noncomputable def push1 :
    (G × Fin 2 → ZMod 2) →ₗ[ZMod 2] (H × Fin 2 → ZMod 2) :=
  fiberSum (Prod.map ⇑D.proj id)

/-- The pullback `τ` on chains indexed by `H` (0- and 2-chains): composition
with `proj`. -/
noncomputable def pull0 :
    (H → ZMod 2) →ₗ[ZMod 2] (G → ZMod 2) :=
  LinearMap.funLeft (ZMod 2) (ZMod 2) ⇑D.proj

/-- The pullback `τ` on 1-chains: composition with `Prod.map proj id`. -/
noncomputable def pull1 :
    (H × Fin 2 → ZMod 2) →ₗ[ZMod 2] (G × Fin 2 → ZMod 2) :=
  LinearMap.funLeft (ZMod 2) (ZMod 2) (Prod.map ⇑D.proj id)

@[simp] lemma push0_apply (v : G → ZMod 2) :
    D.push0 v = fiberSumFn ⇑D.proj v := rfl

@[simp] lemma push1_apply (v : G × Fin 2 → ZMod 2) :
    D.push1 v = fiberSumFn (Prod.map ⇑D.proj id) v := rfl

@[simp] lemma pull0_apply (u : H → ZMod 2) :
    D.pull0 u = u ∘ ⇑D.proj := rfl

@[simp] lemma pull1_apply (u : H × Fin 2 → ZMod 2) :
    D.pull1 u = u ∘ Prod.map ⇑D.proj id := rfl

/-! ## The transfer maps are chain maps -/

/-- The pushforward commutes with `∂₁`: `p (∂₁ c) = ∂₁ (p c)`. -/
theorem push_boundary1_comm (c : G × Fin 2 → ZMod 2) :
    D.push0 (D.coverComplex.boundary1 c)
      = D.baseComplex.boundary1 (D.push1 c) :=
  fiberSum_bbBoundary1Fn D.proj D.Ac D.Bc D.Ab D.Bb D.push_A D.push_B c

/-- The pushforward commutes with `∂₂`: `p (∂₂ f) = ∂₂ (p f)`. -/
theorem push_boundary2_comm (f : G → ZMod 2) :
    D.push1 (D.coverComplex.boundary2 f)
      = D.baseComplex.boundary2 (D.push0 f) :=
  fiberSum_bbBoundary2Fn D.proj D.Ac D.Bc D.Ab D.Bb D.push_A D.push_B f

/-- The pullback commutes with `∂₁`: `∂₁ (τ u) = τ (∂₁ u)`. -/
theorem pull_boundary1_comm (u : H × Fin 2 → ZMod 2) :
    D.coverComplex.boundary1 (D.pull1 u)
      = D.pull0 (D.baseComplex.boundary1 u) :=
  pullback_bbBoundary1Fn D.proj D.Ac D.Bc D.Ab D.Bb D.push_A D.push_B u

/-- The pullback commutes with `∂₂`: `∂₂ (τ f) = τ (∂₂ f)`. -/
theorem pull_boundary2_comm (f : H → ZMod 2) :
    D.coverComplex.boundary2 (D.pull0 f)
      = D.pull1 (D.baseComplex.boundary2 f) :=
  pullback_bbBoundary2Fn D.proj D.Ac D.Bc D.Ab D.Bb D.push_A D.push_B f

/-! ## Exactness of the transfer maps on 1-chains -/

/-- `p ∘ τ = 0` on 1-chains: each fiber contributes the same value twice. -/
theorem push1_pull1_eq_zero (u : H × Fin 2 → ZMod 2) :
    D.push1 (D.pull1 u) = 0 :=
  fiberSumFn_pullback D.deckSigma1_ne D.proj_prodMap_fiber u

/-- The projection on qubits is surjective. -/
lemma proj_prodMap_surjective :
    Function.Surjective (Prod.map ⇑D.proj (id : Fin 2 → Fin 2)) :=
  Function.Surjective.prodMap D.proj_surjective Function.surjective_id

/-- The pullback on 1-chains is injective. -/
lemma pull1_injective : Function.Injective ⇑D.pull1 :=
  LinearMap.funLeft_injective_of_surjective (ZMod 2) (ZMod 2) _
    D.proj_prodMap_surjective

/-- The pullback on chains indexed by `H` is injective. -/
lemma pull0_injective : Function.Injective ⇑D.pull0 :=
  LinearMap.funLeft_injective_of_surjective (ZMod 2) (ZMod 2) _
    D.proj_surjective

/-- The pushforward on 1-chains is surjective. -/
lemma push1_surjective : Function.Surjective ⇑D.push1 := fun u =>
  ⟨lift0 (Prod.map ⇑D.proj id) D.sec1 u,
    fiberSumFn_lift0 D.proj_prodMap_sec1 u⟩

/-- The pushforward on chains indexed by `G` is surjective. -/
lemma push0_surjective : Function.Surjective ⇑D.push0 := fun u =>
  ⟨lift0 ⇑D.proj D.sec u, fiberSumFn_lift0 D.proj_sec u⟩

/-- `ker p = im τ` on 1-chains. -/
theorem push1_eq_zero_iff (v : G × Fin 2 → ZMod 2) :
    D.push1 v = 0 ↔ ∃ u : H × Fin 2 → ZMod 2, v = D.pull1 u :=
  fiberSumFn_eq_zero_iff D.deckSigma1_ne D.proj_prodMap_fiber
    D.proj_prodMap_sec1 v

/-- `τ ∘ p = 1 + σ` on 1-chains: `τ (p v) = v + σ v`. -/
theorem pull1_push1 (v : G × Fin 2 → ZMod 2) :
    D.pull1 (D.push1 v) = v + D.deckShift1 v :=
  funext fun p => fiberSumFn_pair D.deckSigma1_ne D.proj_prodMap_fiber v p

/-! ## Transfer of cycles and boundaries -/

/-- Pushforwards of cycles are cycles. -/
theorem push1_mem_cycles {v : G × Fin 2 → ZMod 2}
    (hv : v ∈ D.coverComplex.cycles) :
    D.push1 v ∈ D.baseComplex.cycles := by
  have hv' : D.coverComplex.boundary1 v = 0 := hv
  change D.baseComplex.boundary1 (D.push1 v) = 0
  rw [← D.push_boundary1_comm, hv']
  exact map_zero D.push0

/-- Pullbacks of cycles are cycles. -/
theorem pull1_mem_cycles {u : H × Fin 2 → ZMod 2}
    (hu : u ∈ D.baseComplex.cycles) :
    D.pull1 u ∈ D.coverComplex.cycles := by
  have hu' : D.baseComplex.boundary1 u = 0 := hu
  change D.coverComplex.boundary1 (D.pull1 u) = 0
  rw [D.pull_boundary1_comm, hu']
  exact map_zero D.pull0

/-- Pushforwards of boundaries are boundaries. -/
theorem push1_mem_boundaries {v : G × Fin 2 → ZMod 2}
    (hv : v ∈ D.coverComplex.boundaries) :
    D.push1 v ∈ D.baseComplex.boundaries := by
  obtain ⟨f, rfl⟩ := hv
  exact ⟨D.push0 f, (D.push_boundary2_comm f).symm⟩

/-- Pullbacks of boundaries are boundaries. -/
theorem pull1_mem_boundaries {u : H × Fin 2 → ZMod 2}
    (hu : u ∈ D.baseComplex.boundaries) :
    D.pull1 u ∈ D.coverComplex.boundaries := by
  obtain ⟨f, rfl⟩ := hu
  exact ⟨D.pull0 f, D.pull_boundary2_comm f⟩

/-- A base chain whose pullback is a cover cycle is a base cycle, because the
pullback is an injective chain map. -/
lemma descend_cycle {u : H × Fin 2 → ZMod 2}
    (h : D.pull1 u ∈ D.coverComplex.cycles) :
    bbBoundary1Fn D.Ab D.Bb u = 0 := by
  have h1 : D.coverComplex.boundary1 (D.pull1 u) = 0 := h
  rw [D.pull_boundary1_comm] at h1
  exact D.pull0_injective (h1.trans (map_zero D.pull0).symm)

/-- A cover 1-cycle whose pushforward is a base boundary differs from the
pullback of a base 1-cycle by a cover boundary. If `p v = ∂₂ (p w)`, then
`p (v + ∂₂ w) = 0`, so `v + ∂₂ w = τ u`, and `u` is a cycle because `τ` is an
injective chain map. -/
theorem exists_pull_eq_add_boundary {v : G × Fin 2 → ZMod 2}
    (hv : v ∈ D.coverComplex.cycles)
    (hbd : D.push1 v ∈ D.baseComplex.boundaries) :
    ∃ u : H × Fin 2 → ZMod 2, u ∈ D.baseComplex.cycles ∧
      ∃ f : G → ZMod 2, D.pull1 u = v + bbBoundary2Fn D.Ac D.Bc f := by
  obtain ⟨w, hw⟩ := hbd
  obtain ⟨w', rfl⟩ := D.push0_surjective w
  have hzero : D.push1 (v + bbBoundary2Fn D.Ac D.Bc w') = 0 := by
    rw [map_add, show D.push1 (bbBoundary2Fn D.Ac D.Bc w') = D.push1 v from
      (D.push_boundary2_comm w').trans hw]
    exact ZModModule.add_self _
  obtain ⟨u, hu⟩ := (D.push1_eq_zero_iff _).mp hzero
  refine ⟨u, D.descend_cycle ?_, w', hu.symm⟩
  rw [← hu]
  exact add_mem hv (D.coverComplex.boundaries_le_cycles ⟨w', rfl⟩)

/-! ## Weights -/

/-- The number of qubits in the support of `v` whose deck partner is also in
the support. Each fiber contained in the support is counted twice. -/
noncomputable def overlapCount (v : G × Fin 2 → ZMod 2) : ℕ :=
  (Finset.univ.filter fun p : G × Fin 2 =>
    v p ≠ 0 ∧ v (p.1 + D.deckS, p.2) ≠ 0).card

/-- The weight of a cover 1-chain is the size of its support. -/
lemma coverComplex_chainWeight_eq (v : G × Fin 2 → ZMod 2) :
    D.coverComplex.chainWeight v
      = (Finset.univ.filter fun p : G × Fin 2 => v p ≠ 0).card := rfl

/-- The weight of a base 1-chain is the size of its support. -/
lemma baseComplex_chainWeight_eq (u : H × Fin 2 → ZMod 2) :
    D.baseComplex.chainWeight u
      = (Finset.univ.filter fun p : H × Fin 2 => u p ≠ 0).card := rfl

/-- `|v| = |p v| + overlapCount v`: the support of `v` consists of the points
whose deck partner is outside the support, which map bijectively onto the
support of `p v`, and the overlap. -/
theorem chainWeight_eq_push_add_overlap (v : G × Fin 2 → ZMod 2) :
    D.coverComplex.chainWeight v
      = D.baseComplex.chainWeight (D.push1 v) + D.overlapCount v :=
  card_support_fiberSum_add_overlap D.deckSigma1_ne D.proj_prodMap_fiber v

/-- The pushforward does not increase weight. -/
theorem chainWeight_push_le (v : G × Fin 2 → ZMod 2) :
    D.baseComplex.chainWeight (D.push1 v) ≤ D.coverComplex.chainWeight v :=
  card_support_fiberSum_le D.deckSigma1_ne D.proj_prodMap_fiber v

/-- The pullback doubles weight. -/
theorem chainWeight_pull1 (u : H × Fin 2 → ZMod 2) :
    D.coverComplex.chainWeight (D.pull1 u)
      = 2 * D.baseComplex.chainWeight u :=
  card_support_pullback D.deckSigma1_ne D.proj_prodMap_fiber
    D.proj_prodMap_sec1 u

/-! ## The two sheets of a cover 1-chain -/

/-- The restriction of a cover 1-chain to sheet 0, the image of `sec1`. -/
def sheet0 (v : G × Fin 2 → ZMod 2) : H × Fin 2 → ZMod 2 :=
  fun q => v (D.sec1 q)

/-- The restriction of a cover 1-chain to sheet 1, the deck translate of
sheet 0. -/
def sheet1 (v : G × Fin 2 → ZMod 2) : H × Fin 2 → ZMod 2 :=
  fun q => v (D.deckSigma1 (D.sec1 q))

@[simp] lemma sheet0_apply (v : G × Fin 2 → ZMod 2) (q : H × Fin 2) :
    D.sheet0 v q = v (D.sec1 q) := rfl

@[simp] lemma sheet1_apply (v : G × Fin 2 → ZMod 2) (q : H × Fin 2) :
    D.sheet1 v q = v (D.deckSigma1 (D.sec1 q)) := rfl

lemma sheet0_add (v w : G × Fin 2 → ZMod 2) :
    D.sheet0 (v + w) = D.sheet0 v + D.sheet0 w := rfl

lemma sheet1_add (v w : G × Fin 2 → ZMod 2) :
    D.sheet1 (v + w) = D.sheet1 v + D.sheet1 w := rfl

/-- The sheet-0 restriction of a pullback is the base chain. -/
lemma sheet0_pull1 (u : H × Fin 2 → ZMod 2) :
    D.sheet0 (D.pull1 u) = u :=
  funext fun q => congrArg u (D.proj_prodMap_sec1 q)

/-- The sheet-1 restriction of a pullback is the base chain. -/
lemma sheet1_pull1 (u : H × Fin 2 → ZMod 2) :
    D.sheet1 (D.pull1 u) = u :=
  funext fun q => congrArg u
    (((D.proj_prodMap_fiber _ _).mpr (Or.inr rfl)).trans (D.proj_prodMap_sec1 q))

/-- The deck translation exchanges the sheets: sheet 0 of `σ s` is sheet 1 of
`s`. -/
lemma sheet0_deckShift1 (s : G × Fin 2 → ZMod 2) :
    D.sheet0 (D.deckShift1 s) = D.sheet1 s := rfl

/-- The deck translation exchanges the sheets: sheet 1 of `σ s` is sheet 0 of
`s`. -/
lemma sheet1_deckShift1 (s : G × Fin 2 → ZMod 2) :
    D.sheet1 (D.deckShift1 s) = D.sheet0 s := by
  funext q
  change s ((D.sec1 q).1 + D.deckS + D.deckS, (D.sec1 q).2) = s (D.sec1 q)
  rw [add_assoc, D.deckS_add_deckS, add_zero]

/-- The two sheets of a chain add up to its pushforward. -/
lemma sheet0_add_sheet1 (v : G × Fin 2 → ZMod 2) :
    D.sheet0 v + D.sheet1 v = D.push1 v := by
  rw [← D.sheet0_pull1 (D.push1 v), D.pull1_push1]
  rfl

/-- The overlap of `v` is twice the number of base qubits over which both
sheets of `v` are nonzero. -/
lemma overlapCount_eq_two_mul_sheets (v : G × Fin 2 → ZMod 2) :
    D.overlapCount v
      = 2 * (Finset.univ.filter fun j =>
          D.sheet0 v j ≠ 0 ∧ D.sheet1 v j ≠ 0).card :=
  card_overlap_eq_two_mul D.deckSigma1_ne D.proj_prodMap_fiber
    D.proj_prodMap_sec1 v

/-- `|v| = |p v| + 2 * |supp (sheet0 v) \ supp (p v)|`: the weight of a cover
chain exceeds that of its pushforward by twice the number of base qubits where
sheet 0 of `v` is nonzero and the pushforward vanishes. -/
theorem chainWeight_sheet_eq (v : G × Fin 2 → ZMod 2) :
    D.coverComplex.chainWeight v
      = D.baseComplex.chainWeight (D.push1 v)
        + 2 * (Finset.univ.filter fun j =>
            D.sheet0 v j ≠ 0 ∧ D.push1 v j = 0).card := by
  have key : ∀ a b c : ZMod 2, a + b = c →
      ((a ≠ 0 ∧ b ≠ 0) ↔ (a ≠ 0 ∧ c = 0)) := by decide
  rw [D.chainWeight_eq_push_add_overlap v, D.overlapCount_eq_two_mul_sheets,
    Finset.filter_congr fun j _ => key _ _ _ (congrFun (D.sheet0_add_sheet1 v) j)]

/-! ## Lifted stabilizers -/

/-- The lift of a base chain `ξ : H → ZMod 2` to the cover: `ξ` on sheet 0 and
zero on sheet 1. -/
def liftC2 (ξ : H → ZMod 2) : G → ZMod 2 :=
  lift0 ⇑D.proj D.sec ξ

lemma liftC2_apply (ξ : H → ZMod 2) (g : G) :
    D.liftC2 ξ g = if g = D.sec (D.proj g) then ξ (D.proj g) else 0 := rfl

/-- The pushforward of the lift of `ξ` is `ξ`. -/
lemma push0_liftC2 (ξ : H → ZMod 2) :
    fiberSumFn ⇑D.proj (D.liftC2 ξ) = ξ :=
  fiberSumFn_lift0 D.proj_sec ξ

/-- `liftC2` is additive. -/
lemma liftC2_add (ξ η : H → ZMod 2) :
    D.liftC2 (ξ + η) = D.liftC2 ξ + D.liftC2 η :=
  funext fun _ => ite_add_zero

lemma liftC2_zero : D.liftC2 (0 : H → ZMod 2) = 0 :=
  funext fun _ => ite_self 0

/-- The lifted stabilizer of a base 2-chain `ξ`: the cover boundary
`∂₂ (liftC2 ξ)`. -/
def liftStab (ξ : H → ZMod 2) : G × Fin 2 → ZMod 2 :=
  bbBoundary2Fn D.Ac D.Bc (D.liftC2 ξ)

/-- The lifted stabilizer is a cover boundary. -/
lemma liftStab_mem_boundaries (ξ : H → ZMod 2) :
    D.liftStab ξ ∈ D.coverComplex.boundaries :=
  ⟨D.liftC2 ξ, rfl⟩

/-- The lifted stabilizer of `ξ` pushes forward to the base boundary `∂₂ ξ`. -/
lemma push1_liftStab (ξ : H → ZMod 2) :
    D.push1 (D.liftStab ξ) = bbBoundary2Fn D.Ab D.Bb ξ := by
  have h := D.push_boundary2_comm (D.liftC2 ξ)
  rw [push0_apply, D.push0_liftC2] at h
  exact h

/-- The lifted stabilizer of the deck translate of a lift is the deck translate
of the lifted stabilizer. -/
lemma liftStab_deckShift (ξ : H → ZMod 2) :
    bbBoundary2Fn D.Ac D.Bc (D.deckShift0 (D.liftC2 ξ))
      = D.deckShift1 (D.liftStab ξ) :=
  bbBoundary2Fn_translate D.Ac D.Bc D.deckS (D.liftC2 ξ)

/-! ## The two sheets of a cover 2-chain -/

/-- The restriction of a chain `z : G → ZMod 2` to sheet 0. -/
def sheetC2_0 (z : G → ZMod 2) : H → ZMod 2 :=
  fun j => z (D.sec j)

/-- The restriction of a chain `z : G → ZMod 2` to sheet 1. -/
def sheetC2_1 (z : G → ZMod 2) : H → ZMod 2 :=
  fun j => z (D.sec j + D.deckS)

/-- A chain on `G` is the lift of its sheet-0 restriction plus the deck
translate of the lift of its sheet-1 restriction. -/
lemma liftC2_decomp (z : G → ZMod 2) :
    z = D.liftC2 (D.sheetC2_0 z)
      + D.deckShift0 (D.liftC2 (D.sheetC2_1 z)) := by
  funext g
  simp only [Pi.add_apply, deckShift0_apply, liftC2_apply, sheetC2_0, sheetC2_1,
    D.proj_add_deckS]
  rcases D.point_dichotomy g with hg | hg
  · have hne : g + D.deckS ≠ D.sec (D.proj g) := fun h =>
      D.deckS_ne_zero (add_eq_left.mp (h.trans hg.symm))
    rw [if_pos hg, if_neg hne, add_zero, ← hg]
  · have hne : g ≠ D.sec (D.proj g) := fun h =>
      D.deckS_ne_zero (add_eq_left.mp (hg.symm.trans h))
    have hg' : g + D.deckS = D.sec (D.proj g) := by
      rw [hg, add_assoc, D.deckS_add_deckS, add_zero, D.proj_add_deckS, D.proj_sec]
    rw [if_neg hne, if_pos hg', zero_add, ← hg]

/-! ## The seam decomposition of a lifted stabilizer

The lifted stabilizer `liftStab ξ = ∂₂ (liftC2 ξ)` of a base 2-chain `ξ` is
supported on both sheets although `liftC2 ξ` lives on sheet 0. Its sheet-0 part
`seamN ξ` and its sheet-1 part `seamC ξ`, the part that crosses the seam between
the sheets, add up to the base boundary `∂₂ ξ`. -/

/-- The part of the lifted stabilizer of `ξ` on sheet 0. -/
def seamN (ξ : H → ZMod 2) : H × Fin 2 → ZMod 2 :=
  D.sheet0 (D.liftStab ξ)

/-- The part of the lifted stabilizer of `ξ` on sheet 1, the part crossing the
seam. On base 2-cycles `ζ` it is a base 1-cycle (`seamC_mem_cycles`), which
represents the image of `ζ` under the connecting map from `ker ∂₂` to `H₁`. -/
def seamC (ξ : H → ZMod 2) : H × Fin 2 → ZMod 2 :=
  D.sheet1 (D.liftStab ξ)

/-- The two seam parts add up to the base boundary: `seamN ξ + seamC ξ = ∂₂ ξ`.
-/
lemma seamN_add_seamC (ξ : H → ZMod 2) :
    D.seamN ξ + D.seamC ξ = bbBoundary2Fn D.Ab D.Bb ξ :=
  (D.sheet0_add_sheet1 (D.liftStab ξ)).trans (D.push1_liftStab ξ)

/-- `seamC` is additive. -/
lemma seamC_add (ξ η : H → ZMod 2) :
    D.seamC (ξ + η) = D.seamC ξ + D.seamC η := by
  unfold seamC liftStab
  rw [D.liftC2_add, bbBoundary2Fn_add, D.sheet1_add]

lemma seamC_zero : D.seamC (0 : H → ZMod 2) = 0 := by
  unfold seamC liftStab
  rw [D.liftC2_zero, ← bbBoundary2_apply, map_zero]
  rfl

/-- For a base 2-cycle `ζ`, the seam-crossing part `seamC ζ` is a base 1-cycle.
The lifted stabilizer of `ζ` pushes forward to `∂₂ ζ = 0`, so it is the
pullback of a base chain `u`, which is a cycle and equals both of its sheets. -/
theorem seamC_mem_cycles {ζ : H → ZMod 2}
    (hζ : bbBoundary2Fn D.Ab D.Bb ζ = 0) :
    D.seamC ζ ∈ D.baseComplex.cycles := by
  obtain ⟨u, hu⟩ := (D.push1_eq_zero_iff _).mp ((D.push1_liftStab ζ).trans hζ)
  rw [seamC, hu, D.sheet1_pull1]
  refine D.descend_cycle ?_
  rw [← hu]
  exact D.coverComplex.boundaries_le_cycles (D.liftStab_mem_boundaries ζ)

end XDoubleCoverData

end BB
end Homological
end Stabilizer
end Quantum
