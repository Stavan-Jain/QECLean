import QEC.Stabilizer.Framework.Homological.BBCover
import QEC.Stabilizer.Framework.Homological.BBDuality

/-!
# The doubling theorem for free double covers of bivariate bicycle codes

Let `D : XDoubleCoverData G H` be a free double cover of bivariate bicycle
codes, with pushforward `p = push1`, pullback `τ = pull1` and deck translation
`σ = deckShift1` on 1-chains. The pullback of a base cycle of weight `d` is a
cover cycle of weight `2 * d`, so the cover has distance at most `2 * d` as soon
as that pullback is not a cover boundary. This file proves the matching lower
bound from hypotheses on the base code, so that the distance of the cover is
exactly twice the distance of the base.

## Hypotheses

* `LogicalFloor d`: every base 1-cycle that is not a boundary has weight at
  least `d`. `StrongBaseFloor d` asks the same of every nonzero base cycle and
  implies it (`logicalFloor_of_strongBaseFloor`).
* `DeckTrivialOnH1`: `v + σ v` is a cover boundary for every cover cycle `v`,
  that is, the deck translation acts trivially on `H₁` of the cover. It follows
  from a Bézout identity `P ⋆ A + Q ⋆ B = 1 + x^s` between the cover
  polynomials, `s` being the deck translation (`deckTrivial_of_bezout`), or
  from a chain homotopy checked on the basis chains
  (`deckTrivial_of_homotopy_certificate`).
* `SeamCosetFloor m`: for every base 2-cycle `ζ` and 2-chain `f`, the chain
  `seamC ζ + ∂₂ f` has weight at least `m` unless it is a base boundary.
* `LightBoundaryAdmissible d b`: the base boundary `b`, of weight
  `2 * d - 2 * t` with `t ≥ 1`, has one of three shapes for which the cycles
  above it can be bounded.

## The argument

A cover cycle `v` that is not a boundary falls into one of three cases.

* `p v` is not a base boundary (the *safe sector*, `SafeFloor`). By
  `DeckTrivialOnH1`, `p v` has the form `seamC ζ + ∂₂ f` with `∂₂ ζ = 0`, so
  `|v| ≥ |p v| ≥ m` by `SeamCosetFloor m` (`safeFloor_of_seamCosetFloor`).
* `p v = 0`. Then `v = τ u` for a base cycle `u` that is not a boundary, and
  `|v| = 2 * |u| ≥ 2 * d` (`dangerous_zero_rung`).
* `p v = b` is a nonzero base boundary (the *dangerous sector*,
  `DangerousFloorNZ`). If `|b| ≥ 2 * d` then `|v| ≥ |b|` suffices. Otherwise
  write `b = ∂₂ f`; then `v + liftStab f = τ u` for the base cycle
  `u = sheet0 v + seamN f`, and `v` would be a boundary if `u` were. The three
  admissible shapes (`dangerous_bound_of_single_shape`,
  `dangerous_bound_of_pair_shape`, `dangerous_bound_of_window`) each force
  `|v| ≥ 2 * d` from this, and `dangerousFloorNZ_of_admissible` dispatches over
  them.

## Main statements

* `chainWeight_ge_double_of_sectors`, `chain_distance_eq_double`,
  `pauli_distance_eq_double`: from `LogicalFloor d`, `DangerousFloorNZ (2 * d)`,
  `SafeFloor (2 * d)` and a base cycle of weight `d` whose pullback is not a
  cover boundary, `2 * d` is the least weight of a cover cycle that is not a
  boundary, and of a nontrivial logical operator of the cover code. The
  Z-side bound is obtained from the X-side one through the duality of
  `BBDuality`.
* `chain_distance_eq_double_of_admissible`,
  `pauli_distance_eq_double_of_admissible`: the doubling theorem, with the two
  sector floors replaced by `DeckTrivialOnH1`, `SeamCosetFloor (2 * d)` and the
  admissibility of every nonzero base boundary of weight `< 2 * d`.
* `chainWeight_ge_of_strongBaseFloor`: from `StrongBaseFloor d` alone, every
  cover cycle that is not a boundary has weight at least `d`.
-/

namespace Quantum
namespace Stabilizer
namespace Homological
namespace BB

open scoped BigOperators

/-! ## Extending identities from the basis chains

An identity between two additive maps on `I → ZMod 2` holds everywhere once it
holds on the point masses `Pi.single i 1`, because every chain is the indicator
of its support. -/

section FunLift

variable {I : Type} [DecidableEq I]

/-- The indicator chain of a finite set. -/
def indF2 (S : Finset I) : I → ZMod 2 := fun i => if i ∈ S then 1 else 0

lemma indF2_empty : indF2 (∅ : Finset I) = 0 := by
  funext i
  simp [indF2]

/-- Adding a new point to a set adds its point mass to the indicator. -/
lemma indF2_insert {a : I} {S : Finset I} (ha : a ∉ S) :
    indF2 (insert a S) = Pi.single a 1 + indF2 S := by
  funext i
  by_cases hi : i = a
  · subst hi
    simp [indF2, ha]
  · simp [indF2, Finset.mem_insert, hi]

/-- Every `ZMod 2`-chain is the indicator of its support. -/
lemma self_eq_indF2_filter [Fintype I] (f : I → ZMod 2) :
    f = indF2 (Finset.univ.filter fun i => f i ≠ 0) := by
  funext i
  have key : ∀ a : ZMod 2, a = if a ≠ 0 then 1 else 0 := by decide
  simp only [indF2, Finset.mem_filter, Finset.mem_univ, true_and]
  exact key (f i)

/-- Two additive maps out of `I → ZMod 2` that agree on the point masses
`Pi.single i 1` agree everywhere. -/
theorem funLiftF2 [Finite I] {W : Type} [AddCommMonoid W]
    (M N : (I → ZMod 2) → W)
    (hM0 : M 0 = 0) (hN0 : N 0 = 0)
    (hMadd : ∀ a b, M (a + b) = M a + M b)
    (hNadd : ∀ a b, N (a + b) = N a + N b)
    (hbasis : ∀ i, M (Pi.single i 1) = N (Pi.single i 1))
    (f : I → ZMod 2) : M f = N f := by
  cases nonempty_fintype I
  have key : ∀ S : Finset I, M (indF2 S) = N (indF2 S) := fun S => by
    induction S using Finset.induction with
    | empty => rw [indF2_empty, hM0, hN0]
    | insert p S hp ih => rw [indF2_insert hp, hMadd, hNadd, hbasis p, ih]
  rw [self_eq_indF2_filter f]
  exact key _

end FunLift

/-! ## Two identities for chains -/

/-- The Bézout block identity in the group algebra `𝔽₂[G]`:
`(P ⋆ A + Q ⋆ B) ⋆ w + Q ⋆ (B ⋆ w + A ⋆ w') = A ⋆ (P ⋆ w + Q ⋆ w')`. The two
copies of `Q ⋆ B ⋆ w` cancel in characteristic 2. -/
lemma conv_bezout_block {G : Type} [Fintype G] [AddCommGroup G]
    (A B P Q w w' : G → ZMod 2) :
    (P ⋆ A + Q ⋆ B) ⋆ w + Q ⋆ (B ⋆ w + A ⋆ w') = A ⋆ (P ⋆ w + Q ⋆ w') := by
  rw [conv_add_left, conv_add_right, conv_add_right, conv_comm P A, conv_assoc A P w,
    conv_assoc Q B w, ← conv_assoc Q A w', conv_comm Q A, conv_assoc A Q w',
    ZModModule.add_add_add_cancel]

/-- The supports of the four translates of `u` by `0`, `b₁`, `b₂` and `b₁ + b₂`
have total size at most `2 * |U| + 4 * |supp u \ U|`, where
`U = supp b₁ ∪ supp b₂`: a point of `U` lies in exactly two of the four
supports, and a point outside `U` lies in all four or in none. -/
lemma card_support_four_translates_le {I : Type} [Fintype I] (u b₁ b₂ : I → ZMod 2) :
    (Finset.univ.filter fun j => u j ≠ 0).card
        + (Finset.univ.filter fun j => (u + b₁) j ≠ 0).card
        + (Finset.univ.filter fun j => (u + b₂) j ≠ 0).card
        + (Finset.univ.filter fun j => (u + b₁ + b₂) j ≠ 0).card
      ≤ 2 * (Finset.univ.filter fun j => b₁ j ≠ 0 ∨ b₂ j ≠ 0).card
        + 4 * (Finset.univ.filter fun j => u j ≠ 0 ∧ ¬(b₁ j ≠ 0 ∨ b₂ j ≠ 0)).card := by
  have key : ∀ a x y : ZMod 2,
      ((if a ≠ 0 then 1 else 0) + (if a + x ≠ 0 then 1 else 0)
          + (if a + y ≠ 0 then 1 else 0) + (if a + x + y ≠ 0 then 1 else 0) : ℕ)
        ≤ 2 * (if x ≠ 0 ∨ y ≠ 0 then 1 else 0)
          + 4 * (if a ≠ 0 ∧ ¬(x ≠ 0 ∨ y ≠ 0) then 1 else 0) := by
    decide
  simp only [Finset.card_filter, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun j _ => key (u j) (b₁ j) (b₂ j)

namespace XDoubleCoverData

variable {G H : Type}
  [Fintype G] [AddCommGroup G] [DecidableEq G]
  [Fintype H] [AddCommGroup H] [DecidableEq H]
  (D : XDoubleCoverData G H)

/-! ## The hypotheses of the doubling theorem -/

/-- The strong base floor: every nonzero base 1-cycle, boundary or not, has
weight at least `d`. It can only hold for `d` at most the weight of the
lightest nonzero base boundary, for instance of a single check `∂₂ δ_g`. -/
def StrongBaseFloor (d : ℕ) : Prop :=
  ∀ u : H × Fin 2 → ZMod 2,
    bbBoundary1Fn D.Ab D.Bb u = 0 → u ≠ 0 →
    d ≤ D.baseComplex.chainWeight u

/-- The logical base floor: every base 1-cycle that is not a boundary has
weight at least `d`. This says that the chain-level distance of the base code
is at least `d`. -/
def LogicalFloor (d : ℕ) : Prop :=
  ∀ u : H × Fin 2 → ZMod 2,
    bbBoundary1Fn D.Ab D.Bb u = 0 → u ∉ D.baseComplex.boundaries →
    d ≤ D.baseComplex.chainWeight u

/-- The deck translation acts trivially on `H₁` of the cover: `v + σ v` is a
cover boundary for every cover cycle `v`. -/
def DeckTrivialOnH1 : Prop :=
  ∀ v : G × Fin 2 → ZMod 2, v ∈ D.coverComplex.cycles →
    v + D.deckShift1 v ∈ D.coverComplex.boundaries

/-- The dangerous floor: every cover cycle that is not a boundary and whose
pushforward is a nonzero base boundary has weight at least `m`. -/
def DangerousFloorNZ (m : ℕ) : Prop :=
  ∀ v : G × Fin 2 → ZMod 2,
    v ∈ D.coverComplex.cycles → v ∉ D.coverComplex.boundaries →
    D.push1 v ∈ D.baseComplex.boundaries → D.push1 v ≠ 0 →
    m ≤ D.coverComplex.chainWeight v

/-- The safe floor: every cover cycle whose pushforward is not a base boundary
has weight at least `m`. -/
def SafeFloor (m : ℕ) : Prop :=
  ∀ v : G × Fin 2 → ZMod 2,
    v ∈ D.coverComplex.cycles → D.push1 v ∉ D.baseComplex.boundaries →
    m ≤ D.coverComplex.chainWeight v

/-- The seam-coset floor: for every base 2-cycle `ζ` and base 2-chain `f`, the
chain `seamC ζ + ∂₂ f` has weight at least `m` unless it is a base boundary. -/
def SeamCosetFloor (m : ℕ) : Prop :=
  ∀ ζ : H → ZMod 2, bbBoundary2Fn D.Ab D.Bb ζ = 0 →
    ∀ f : H → ZMod 2,
      D.seamC ζ + bbBoundary2Fn D.Ab D.Bb f ∉ D.baseComplex.boundaries →
      m ≤ D.baseComplex.chainWeight
        (D.seamC ζ + bbBoundary2Fn D.Ab D.Bb f)

/-- The strong floor implies the logical floor: a chain that is not a boundary
is nonzero. -/
lemma logicalFloor_of_strongBaseFloor {d : ℕ}
    (hbase : D.StrongBaseFloor d) : D.LogicalFloor d := by
  intro u hu hnb
  refine hbase u hu ?_
  rintro rfl
  exact hnb (zero_mem _)

/-! ## The deck homotopy from a chain homotopy

Maps `C : C₁ → C₂` and `E : C₀ → C₁` with `1 + σ = ∂₂ ∘ C + E ∘ ∂₁` on 1-chains
give `DeckTrivialOnH1`, since on a cycle the term `E ∘ ∂₁` vanishes. For
additive `C` and `E` it is enough to check the identity on the point masses,
which is a finite computation. -/

lemma deckShift1_add (a b : G × Fin 2 → ZMod 2) :
    D.deckShift1 (a + b) = D.deckShift1 a + D.deckShift1 b := rfl

lemma deckShift1_zero : D.deckShift1 (0 : G × Fin 2 → ZMod 2) = 0 := rfl

/-- Additive maps `C : C₁ → C₂` and `E : C₀ → C₁` that satisfy
`q + σ q + E (∂₁ q) = ∂₂ (C q)` on every point mass `q` show that the deck
translation acts trivially on `H₁` of the cover. -/
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
  have key : v + D.deckShift1 v + Emap (bbBoundary1Fn D.Ac D.Bc v)
      = bbBoundary2Fn D.Ac D.Bc (Cmap v) :=
    funLiftF2
      (fun w => w + D.deckShift1 w + Emap (bbBoundary1Fn D.Ac D.Bc w))
      (fun w => bbBoundary2Fn D.Ac D.Bc (Cmap w))
      (by simp only [deckShift1_zero, ← bbBoundary1_apply, map_zero, hE0, add_zero])
      (by simp only [hC0, ← bbBoundary2_apply, map_zero])
      (fun a b => by
        simp only [deckShift1_add, bbBoundary1Fn_add, hEadd]
        abel)
      (fun a b => by simp only [hCadd, bbBoundary2Fn_add])
      hbasis v
  rw [show bbBoundary1Fn D.Ac D.Bc v = 0 from hv, hE0, add_zero] at key
  exact ⟨Cmap v, key.symm⟩

/-! ## The deck homotopy from a Bézout identity

Write `ε = 1 + x^s` for the element `deckPoly` of `𝔽₂[G]`, where `s` is the
deck translation; convolution by `ε` is `1 + σ`. If `P ⋆ A + Q ⋆ B = ε` for the
cover polynomials `A`, `B`, then the boundary maps `∂₁'`, `∂₂'` of the bivariate
bicycle complex of `(Q, P)` form a chain homotopy
`1 + σ = ∂₂ ∘ ∂₁' + ∂₂' ∘ ∂₁`, so the deck translation acts trivially on `H₁`
of the cover. The hypothesis is one identity in `𝔽₂[G]`. -/

/-- The element `1 + x^s` of `𝔽₂[G]`, where `s` is the deck translation. -/
def deckPoly : G → ZMod 2 :=
  Pi.single (0 : G) 1 + Pi.single D.deckS 1

/-- Convolution by `deckPoly` is `1 + σ` on chains indexed by `G`. -/
lemma conv_deckPoly_eq (w : G → ZMod 2) :
    D.deckPoly ⋆ w = w + D.deckShift0 w := by
  funext g
  simp only [deckPoly, conv_add_left, Pi.add_apply,
    conv_single_left_apply, deckShift0_apply]
  rw [sub_zero, sub_eq_add_neg, D.neg_deckS]

/-- The Bézout chain homotopy: if `P ⋆ A + Q ⋆ B = 1 + x^s`, then
`v + σ v + ∂₂' (∂₁ v) = ∂₂ (∂₁' v)` for every cover 1-chain `v`, where `∂₁'`
and `∂₂'` are the boundary maps of the bivariate bicycle complex of `(Q, P)`.
-/
lemma bezout_chain_identity (P Q : G → ZMod 2)
    (hPQ : P ⋆ D.Ac + Q ⋆ D.Bc = D.deckPoly)
    (v : G × Fin 2 → ZMod 2) :
    v + D.deckShift1 v + bbBoundary2Fn Q P (bbBoundary1Fn D.Ac D.Bc v)
      = bbBoundary2Fn D.Ac D.Bc (bbBoundary1Fn Q P v) := by
  have hL := conv_bezout_block D.Ac D.Bc P Q (leftHalf v) (rightHalf v)
  have hR := conv_bezout_block D.Bc D.Ac Q P (rightHalf v) (leftHalf v)
  rw [hPQ, D.conv_deckPoly_eq] at hL
  rw [add_comm (Q ⋆ D.Bc), hPQ, D.conv_deckPoly_eq, add_comm (D.Ac ⋆ rightHalf v),
    add_comm (Q ⋆ rightHalf v)] at hR
  exact halves_ext_iff.mpr ⟨hL, hR⟩

/-- A Bézout identity `P ⋆ A + Q ⋆ B = 1 + x^s` between the cover polynomials
shows that the deck translation acts trivially on `H₁` of the cover. -/
theorem deckTrivial_of_bezout (P Q : G → ZMod 2)
    (hPQ : P ⋆ D.Ac + Q ⋆ D.Bc = D.deckPoly) :
    D.DeckTrivialOnH1 := fun v hv => by
  have h := D.bezout_chain_identity P Q hPQ v
  rw [show bbBoundary1Fn D.Ac D.Bc v = 0 from hv, ← bbBoundary2_apply, map_zero,
    add_zero] at h
  exact ⟨_, h.symm⟩

/-! ## Cycles with zero pushforward -/

/-- A cover cycle that is not a boundary and has zero pushforward is the
pullback `τ u` of a base cycle `u` that is not a boundary, so its weight
`2 * |u|` is at least `2 * d`. -/
theorem dangerous_zero_rung {d : ℕ} (hbase : D.LogicalFloor d)
    {v : G × Fin 2 → ZMod 2}
    (hv : v ∈ D.coverComplex.cycles) (hnb : v ∉ D.coverComplex.boundaries)
    (h0 : D.push1 v = 0) :
    2 * d ≤ D.coverComplex.chainWeight v := by
  obtain ⟨u, rfl⟩ := (D.push1_eq_zero_iff v).mp h0
  rw [D.chainWeight_pull1]
  exact Nat.mul_le_mul_left 2
    (hbase u (D.descend_cycle hv) fun hu => hnb (D.pull1_mem_boundaries hu))

/-- From the strong base floor alone, every cover cycle that is not a boundary
has weight at least `d`: either its pushforward is zero, or the pushforward is
a nonzero base cycle of no greater weight. -/
theorem chainWeight_ge_of_strongBaseFloor {d : ℕ}
    (hbase : D.StrongBaseFloor d) :
    ∀ v : G × Fin 2 → ZMod 2,
      v ∈ D.coverComplex.cycles → v ∉ D.coverComplex.boundaries →
      d ≤ D.coverComplex.chainWeight v := by
  intro v hv hnb
  by_cases h0 : D.push1 v = 0
  · have := D.dangerous_zero_rung (D.logicalFloor_of_strongBaseFloor hbase) hv hnb h0
    omega
  · exact (hbase _ (D.push1_mem_cycles hv) h0).trans (D.chainWeight_push_le v)

/-! ## Cycles over a nonzero base boundary

Let `v` be a cover cycle with `p v = ∂₂ f`. Then `v + liftStab f` has zero
pushforward, so it is the pullback of a base chain, namely of
`u = sheet0 v + seamN f`. This `u` is a base cycle, and `v` is a cover boundary
as soon as `u` is a base boundary. -/

/-- If `p v = ∂₂ f` then `v + liftStab f = τ (sheet0 v + seamN f)`. -/
lemma pull1_sheet0_add_seamN {v : G × Fin 2 → ZMod 2} {f : H → ZMod 2}
    (hb : D.push1 v = bbBoundary2Fn D.Ab D.Bb f) :
    D.pull1 (D.sheet0 v + D.seamN f) = v + D.liftStab f := by
  obtain ⟨u, hu⟩ := (D.push1_eq_zero_iff (v + D.liftStab f)).mp (by
    rw [map_add, hb, D.push1_liftStab]
    exact ZModModule.add_self _)
  have hu' : D.sheet0 v + D.seamN f = u := (congrArg D.sheet0 hu).trans (D.sheet0_pull1 u)
  rw [hu', hu]

/-- If `v` is a cover cycle with `p v = ∂₂ f`, then `sheet0 v + seamN f` is a
base cycle. -/
lemma sheet0_add_seamN_mem_cycles {v : G × Fin 2 → ZMod 2} {f : H → ZMod 2}
    (hv : v ∈ D.coverComplex.cycles)
    (hb : D.push1 v = bbBoundary2Fn D.Ab D.Bb f) :
    D.sheet0 v + D.seamN f ∈ D.baseComplex.cycles := by
  refine D.descend_cycle ?_
  rw [D.pull1_sheet0_add_seamN hb]
  exact add_mem hv (D.coverComplex.boundaries_le_cycles (D.liftStab_mem_boundaries f))

/-- If `p v = ∂₂ f` and `sheet0 v + seamN f` is a base boundary, then `v` is a
cover boundary. -/
lemma mem_boundaries_of_sheet0_add_seamN {v : G × Fin 2 → ZMod 2} {f : H → ZMod 2}
    (hb : D.push1 v = bbBoundary2Fn D.Ab D.Bb f)
    (hu : D.sheet0 v + D.seamN f ∈ D.baseComplex.boundaries) :
    v ∈ D.coverComplex.boundaries := by
  have e : D.pull1 (D.sheet0 v + D.seamN f) + D.liftStab f = v := by
    rw [D.pull1_sheet0_add_seamN hb, add_assoc, ZModModule.add_self, add_zero]
  rw [← e]
  exact add_mem (D.pull1_mem_boundaries hu) (D.liftStab_mem_boundaries f)

/-- The pair shape. Let `v` be a cover cycle that is not a boundary with
`p v = b₁ + b₂`, `bᵢ = ∂₂ fᵢ`. Suppose `|b₁ + b₂| = 2 * d - 2 * t` with `t ≥ 1`,
the union `U` of the supports of `b₁` and `b₂` satisfies
`|U| + 2 * (t - 1) ≤ 2 * d - 1`, and `seamN (f₁ + f₂)` is supported in `U`.
Then `|v| ≥ 2 * d`.

The base cycle `u = sheet0 v + seamN (f₁ + f₂)` and its translates by `b₁`, `b₂`
and `b₁ + b₂` are not boundaries, so each has weight at least `d`; their total
weight is at most `2 * |U| + 4 * |supp u \ U|`, and `supp u \ U` lies in the set
where `sheet0 v` is nonzero and `p v` vanishes, which contributes twice its
size to `|v| - |p v|`. -/
theorem dangerous_bound_of_pair_shape {d t : ℕ}
    (hbase : D.LogicalFloor d) (ht : 1 ≤ t)
    (f₁ f₂ : H → ZMod 2)
    (hwb : D.baseComplex.chainWeight
        (bbBoundary2Fn D.Ab D.Bb f₁ + bbBoundary2Fn D.Ab D.Bb f₂) + 2 * t
      = 2 * d)
    (hU : (Finset.univ.filter fun j : H × Fin 2 =>
        bbBoundary2Fn D.Ab D.Bb f₁ j ≠ 0 ∨
        bbBoundary2Fn D.Ab D.Bb f₂ j ≠ 0).card + 2 * (t - 1) ≤ 2 * d - 1)
    (hseam : ∀ j : H × Fin 2, D.seamN (f₁ + f₂) j ≠ 0 →
      (bbBoundary2Fn D.Ab D.Bb f₁ j ≠ 0 ∨ bbBoundary2Fn D.Ab D.Bb f₂ j ≠ 0))
    {v : G × Fin 2 → ZMod 2}
    (hv : v ∈ D.coverComplex.cycles) (hnb : v ∉ D.coverComplex.boundaries)
    (hb : D.push1 v
      = bbBoundary2Fn D.Ab D.Bb f₁ + bbBoundary2Fn D.Ab D.Bb f₂) :
    2 * d ≤ D.coverComplex.chainWeight v := by
  have hb' : D.push1 v = bbBoundary2Fn D.Ab D.Bb (f₁ + f₂) := by
    rw [hb, bbBoundary2Fn_add]
  set b₁ : H × Fin 2 → ZMod 2 := bbBoundary2Fn D.Ab D.Bb f₁
  set b₂ : H × Fin 2 → ZMod 2 := bbBoundary2Fn D.Ab D.Bb f₂
  set u : H × Fin 2 → ZMod 2 := D.sheet0 v + D.seamN (f₁ + f₂) with hu
  have hb₁ : b₁ ∈ D.baseComplex.boundaries := ⟨f₁, rfl⟩
  have hb₂ : b₂ ∈ D.baseComplex.boundaries := ⟨f₂, rfl⟩
  -- `u` and its translates by boundaries are cycles and not boundaries
  have hheavy : ∀ b : H × Fin 2 → ZMod 2, b ∈ D.baseComplex.boundaries →
      d ≤ D.baseComplex.chainWeight (u + b) := fun b hbd =>
    hbase _ (add_mem (D.sheet0_add_seamN_mem_cycles hv hb')
        (D.baseComplex.boundaries_le_cycles hbd))
      fun h => hnb (D.mem_boundaries_of_sheet0_add_seamN hb'
        ((Submodule.add_mem_iff_left _ hbd).mp h))
  have h0 := hheavy 0 (zero_mem _)
  have h1 := hheavy b₁ hb₁
  have h2 := hheavy b₂ hb₂
  have h12 := hheavy (b₁ + b₂) (add_mem hb₁ hb₂)
  rw [add_zero] at h0
  rw [← add_assoc] at h12
  -- outside `U`, the support of `u` lies where `sheet0 v ≠ 0` and `p v = 0`
  have hsub : (Finset.univ.filter fun j => u j ≠ 0 ∧ ¬(b₁ j ≠ 0 ∨ b₂ j ≠ 0))
      ⊆ Finset.univ.filter fun j => D.sheet0 v j ≠ 0 ∧ D.push1 v j = 0 := fun j hj => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    obtain ⟨hju, hjU⟩ := hj
    have hs : D.seamN (f₁ + f₂) j = 0 := by_contra fun h => hjU (hseam j h)
    rw [hu, Pi.add_apply, hs, add_zero] at hju
    push Not at hjU
    exact ⟨hju, by rw [hb, Pi.add_apply, hjU.1, hjU.2, add_zero]⟩
  have hcount := card_support_four_translates_le u b₁ b₂
  have hcard := Finset.card_le_card hsub
  rw [D.baseComplex_chainWeight_eq] at h0 h1 h2 h12
  rw [← hb] at hwb
  rw [D.chainWeight_sheet_eq]
  omega

/-- The single shape. Let `v` be a cover cycle that is not a boundary with
`p v = b = ∂₂ f₀`. Suppose `|b| = 2 * d - 2 * t` with `t ≥ 1` and `seamN f₀` is
supported in the support of `b`. Then `|v| ≥ 2 * d`. This is the pair shape
with second boundary zero. -/
theorem dangerous_bound_of_single_shape {d t : ℕ}
    (hbase : D.LogicalFloor d) (ht : 1 ≤ t)
    (f₀ : H → ZMod 2)
    (hwb : D.baseComplex.chainWeight (bbBoundary2Fn D.Ab D.Bb f₀) + 2 * t
      = 2 * d)
    (hseam : ∀ j : H × Fin 2,
      D.seamN f₀ j ≠ 0 → bbBoundary2Fn D.Ab D.Bb f₀ j ≠ 0)
    {v : G × Fin 2 → ZMod 2}
    (hv : v ∈ D.coverComplex.cycles) (hnb : v ∉ D.coverComplex.boundaries)
    (hb : D.push1 v = bbBoundary2Fn D.Ab D.Bb f₀) :
    2 * d ≤ D.coverComplex.chainWeight v := by
  have h0 : bbBoundary2Fn D.Ab D.Bb (0 : H → ZMod 2) = 0 := map_zero (bbBoundary2 D.Ab D.Bb)
  have hU : (Finset.univ.filter fun j : H × Fin 2 =>
      bbBoundary2Fn D.Ab D.Bb f₀ j ≠ 0 ∨ bbBoundary2Fn D.Ab D.Bb (0 : H → ZMod 2) j ≠ 0)
      = Finset.univ.filter fun j => bbBoundary2Fn D.Ab D.Bb f₀ j ≠ 0 :=
    Finset.filter_congr fun j _ => by rw [h0]; exact or_iff_left fun h => h rfl
  refine D.dangerous_bound_of_pair_shape hbase ht f₀ 0 ?_ ?_ ?_ hv hnb ?_
  · rwa [h0, add_zero]
  · rw [hU, ← D.baseComplex_chainWeight_eq]
    omega
  · exact fun j hj => Or.inl (hseam j (by rwa [add_zero] at hj))
  · rw [hb, h0, add_zero]

/-- The window shape. Let `v` be a cover cycle that is not a boundary with
`p v = b = ∂₂ f₀` and `|b| = 2 * d - 2`. Suppose every base cycle supported in
the window `supp b ∪ supp (seamN f₀)` is a boundary, which is a finite check.
Then `|v| ≥ 2 * d`: otherwise `sheet0 v` vanishes wherever `b` does, and
`sheet0 v + seamN f₀` is a base cycle supported in the window. -/
theorem dangerous_bound_of_window {d : ℕ}
    (f₀ : H → ZMod 2)
    (hwb : D.baseComplex.chainWeight (bbBoundary2Fn D.Ab D.Bb f₀) + 2
      = 2 * d)
    (hW : ∀ u : H × Fin 2 → ZMod 2, bbBoundary1Fn D.Ab D.Bb u = 0 →
      (∀ j : H × Fin 2, u j ≠ 0 →
        bbBoundary2Fn D.Ab D.Bb f₀ j ≠ 0 ∨ D.seamN f₀ j ≠ 0) →
      u ∈ D.baseComplex.boundaries)
    {v : G × Fin 2 → ZMod 2}
    (hv : v ∈ D.coverComplex.cycles) (hnb : v ∉ D.coverComplex.boundaries)
    (hb : D.push1 v = bbBoundary2Fn D.Ab D.Bb f₀) :
    2 * d ≤ D.coverComplex.chainWeight v := by
  rw [D.chainWeight_sheet_eq, hb]
  by_contra hlt
  have hempty : (Finset.univ.filter fun j =>
      D.sheet0 v j ≠ 0 ∧ bbBoundary2Fn D.Ab D.Bb f₀ j = 0) = ∅ :=
    Finset.card_eq_zero.mp (by omega)
  refine hnb (D.mem_boundaries_of_sheet0_add_seamN hb
    (hW _ (D.sheet0_add_seamN_mem_cycles hv hb) fun j hj => ?_))
  by_contra hcon
  push Not at hcon
  rw [Pi.add_apply, hcon.2, add_zero] at hj
  exact Finset.notMem_empty j (hempty ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj, hcon.1⟩)

/-! ## Admissible light boundaries

`LightBoundaryAdmissible d b` says that the base boundary `b` has one of the
three shapes above, with the side conditions of the corresponding theorem. Once
every nonzero base boundary of weight `< 2 * d` is admissible, the dangerous
floor `DangerousFloorNZ (2 * d)` holds. -/

/-- A base 1-chain `b` with `|b| = 2 * d - 2 * t` for some `t ≥ 1` is
*admissible* if one of the following holds.

* Single shape: `b = ∂₂ f` and `supp (seamN f) ⊆ supp b`.
* Pair shape: `b = ∂₂ f₁ + ∂₂ f₂` and, with `U = supp (∂₂ f₁) ∪ supp (∂₂ f₂)`,
  both `|U| + 2 * (t - 1) ≤ 2 * d - 1` and `supp (seamN (f₁ + f₂)) ⊆ U`.
* Window: `t = 1`, `b = ∂₂ f`, and every base 1-cycle supported in
  `supp b ∪ supp (seamN f)` is a boundary.

These are the hypotheses of `dangerous_bound_of_single_shape`,
`dangerous_bound_of_pair_shape` and `dangerous_bound_of_window`. -/
def LightBoundaryAdmissible (d : ℕ) (b : H × Fin 2 → ZMod 2) : Prop :=
  ∃ t : ℕ, 1 ≤ t ∧ D.baseComplex.chainWeight b + 2 * t = 2 * d ∧
    -- single shape
    ((∃ f : H → ZMod 2, b = bbBoundary2Fn D.Ab D.Bb f ∧
        ∀ j : H × Fin 2, D.seamN f j ≠ 0 → b j ≠ 0) ∨
    -- pair shape
     (∃ f₁ f₂ : H → ZMod 2,
        b = bbBoundary2Fn D.Ab D.Bb f₁ + bbBoundary2Fn D.Ab D.Bb f₂ ∧
        (Finset.univ.filter fun j : H × Fin 2 =>
            bbBoundary2Fn D.Ab D.Bb f₁ j ≠ 0 ∨
            bbBoundary2Fn D.Ab D.Bb f₂ j ≠ 0).card + 2 * (t - 1) ≤ 2 * d - 1 ∧
        ∀ j : H × Fin 2, D.seamN (f₁ + f₂) j ≠ 0 →
          (bbBoundary2Fn D.Ab D.Bb f₁ j ≠ 0 ∨ bbBoundary2Fn D.Ab D.Bb f₂ j ≠ 0)) ∨
    -- window
     (t = 1 ∧ ∃ f : H → ZMod 2, b = bbBoundary2Fn D.Ab D.Bb f ∧
        ∀ u : H × Fin 2 → ZMod 2, bbBoundary1Fn D.Ab D.Bb u = 0 →
          (∀ j : H × Fin 2, u j ≠ 0 → b j ≠ 0 ∨ D.seamN f j ≠ 0) →
          u ∈ D.baseComplex.boundaries))

/-- If every nonzero base boundary of weight `< 2 * d` is admissible, then the
dangerous floor `DangerousFloorNZ (2 * d)` holds. A cycle over a boundary of
weight `≥ 2 * d` is heavy because the pushforward does not increase weight; a
cycle over a lighter boundary is bounded by the theorem for its shape. -/
theorem dangerousFloorNZ_of_admissible {d : ℕ} (hbase : D.LogicalFloor d)
    (hadm : ∀ b : H × Fin 2 → ZMod 2, b ∈ D.baseComplex.boundaries → b ≠ 0 →
      D.baseComplex.chainWeight b < 2 * d → D.LightBoundaryAdmissible d b) :
    D.DangerousFloorNZ (2 * d) := by
  intro v hv hnb hbd hne
  by_cases hw : 2 * d ≤ D.baseComplex.chainWeight (D.push1 v)
  · exact le_trans hw (D.chainWeight_push_le v)
  · obtain ⟨t, ht, hwb, hcase⟩ := hadm (D.push1 v) hbd hne (by omega)
    generalize hb : D.push1 v = b at hwb hcase
    rcases hcase with ⟨f, rfl, hseam⟩ | ⟨f₁, f₂, rfl, hU, hseam⟩ |
      ⟨rfl, f, rfl, hW⟩
    · exact D.dangerous_bound_of_single_shape hbase ht f hwb hseam hv hnb hb
    · exact D.dangerous_bound_of_pair_shape hbase ht f₁ f₂ hwb hU hseam hv hnb hb
    · exact D.dangerous_bound_of_window f hwb hW hv hnb hb

/-! ## Cycles whose pushforward is not a boundary -/

/-- If the deck translation acts trivially on `H₁` of the cover, the seam-coset
floor gives the safe floor. For a cover cycle `v` write `v + σ v = ∂₂ z` and
let `z₀`, `z₁` be the two sheets of `z`. Reading off the two sheets of
`v + σ v = τ (p v)` gives `p v = seamN z₀ + seamC z₁ = seamC z₀ + seamN z₁`,
hence `∂₂ (z₀ + z₁) = 0` and `p v = seamC (z₀ + z₁) + ∂₂ z₀`. -/
theorem safeFloor_of_seamCosetFloor {m : ℕ}
    (hR : D.DeckTrivialOnH1) (hMim : D.SeamCosetFloor m) :
    D.SafeFloor m := by
  intro v hv hb
  obtain ⟨z, hz⟩ := hR v hv
  have hsplit : D.pull1 (D.push1 v)
      = D.liftStab (D.sheetC2_0 z) + D.deckShift1 (D.liftStab (D.sheetC2_1 z)) := by
    rw [D.pull1_push1, ← D.liftStab_deckShift, liftStab, ← bbBoundary2Fn_add,
      ← D.liftC2_decomp z]
    exact hz.symm
  have hw0 : D.push1 v = D.seamN (D.sheetC2_0 z) + D.seamC (D.sheetC2_1 z) := by
    rw [← D.sheet0_pull1 (D.push1 v), hsplit]
    rfl
  have hw1 : D.push1 v = D.seamC (D.sheetC2_0 z) + D.seamN (D.sheetC2_1 z) := by
    rw [← D.sheet1_pull1 (D.push1 v), hsplit, D.sheet1_add, D.sheet1_deckShift1]
    rfl
  have hker : bbBoundary2Fn D.Ab D.Bb (D.sheetC2_0 z + D.sheetC2_1 z) = 0 := by
    rw [bbBoundary2Fn_add, ← D.seamN_add_seamC (D.sheetC2_0 z),
      ← D.seamN_add_seamC (D.sheetC2_1 z), add_comm (D.seamN (D.sheetC2_1 z)),
      add_add_add_comm, ← hw0, ← hw1, ZModModule.add_self]
  have hwform : D.push1 v
      = D.seamC (D.sheetC2_0 z + D.sheetC2_1 z) + bbBoundary2Fn D.Ab D.Bb (D.sheetC2_0 z) := by
    rw [D.seamC_add, ← D.seamN_add_seamC (D.sheetC2_0 z), hw0,
      add_comm (D.seamC (D.sheetC2_0 z)) (D.seamC (D.sheetC2_1 z)),
      add_comm (D.seamN (D.sheetC2_0 z)) (D.seamC (D.sheetC2_0 z)),
      ZModModule.add_add_add_cancel, add_comm]
  refine le_trans ?_ (D.chainWeight_push_le v)
  rw [hwform]
  exact hMim _ hker _ (hwform ▸ hb)

/-! ## The distance of the cover from the sector floors -/

/-- Given the logical floor of the base and the dangerous and safe floors,
every cover cycle that is not a boundary has weight at least `2 * d`. -/
theorem chainWeight_ge_double_of_sectors {d : ℕ}
    (hbase : D.LogicalFloor d)
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

/-- Chain-level distance of the cover: given the three floors and a base cycle
`uStar` of weight `d` whose pullback is not a cover boundary, `2 * d` is the
least weight of a cover cycle that is not a boundary. It is attained by the
pullback of `uStar`. -/
theorem chain_distance_eq_double {d : ℕ}
    (hbase : D.LogicalFloor d)
    (hM : D.DangerousFloorNZ (2 * d)) (hS : D.SafeFloor (2 * d))
    (uStar : H × Fin 2 → ZMod 2)
    (hu_cyc : uStar ∈ D.baseComplex.cycles)
    (hu_w : D.baseComplex.chainWeight uStar = d)
    (hτnb : D.pull1 uStar ∉ D.coverComplex.boundaries) :
    IsLeast {w : ℕ | ∃ v : G × Fin 2 → ZMod 2,
      v ∈ D.coverComplex.cycles ∧ v ∉ D.coverComplex.boundaries ∧
      D.coverComplex.chainWeight v = w} (2 * d) := by
  refine ⟨⟨D.pull1 uStar, D.pull1_mem_cycles hu_cyc, hτnb, ?_⟩, ?_⟩
  · rw [D.chainWeight_pull1, hu_w]
  · rintro w ⟨v, hv, hnb, rfl⟩
    exact D.chainWeight_ge_double_of_sectors hbase hM hS v hv hnb

/-! ## The Z side and the Pauli level -/

/-- The bound of `chainWeight_ge_double_of_sectors` for the dual complex: every
dual cycle of the cover that is not a dual boundary has weight at least
`2 * d`. It follows from the bound on cycles because the duality map of a
bivariate bicycle complex preserves weight. -/
theorem dual_chainWeight_ge_double_of_sectors {d : ℕ}
    (hbase : D.LogicalFloor d)
    (hM : D.DangerousFloorNZ (2 * d)) (hS : D.SafeFloor (2 * d)) :
    ∀ c ∈ D.coverComplex.dualCycles, c ∉ D.coverComplex.dualBoundaries →
      2 * d ≤ D.coverComplex.chainWeight c :=
  (bb_cycle_bound_iff_dual_bound D.Ac D.Bc (2 * d)).mp
    (D.chainWeight_ge_double_of_sectors hbase hM hS)

/-- Given the three floors, every nontrivial logical operator of the stabilizer
group of the cover code has weight at least `2 * d`. -/
theorem logical_weight_ge_double_of_sectors {d : ℕ}
    (hbase : D.LogicalFloor d)
    (hM : D.DangerousFloorNZ (2 * d)) (hS : D.SafeFloor (2 * d))
    (g : NQubitPauliGroupElement D.coverComplex.numQubits)
    (hg : Quantum.StabilizerGroup.IsNontrivialLogicalOperator g
      D.coverComplex.homologicalStabilizerGroup) :
    2 * d ≤ NQubitPauliGroupElement.weight g :=
  HomologicalCode.chainWeight_lower_bound_transfers D.coverComplex (2 * d)
    (D.chainWeight_ge_double_of_sectors hbase hM hS)
    (D.dual_chainWeight_ge_double_of_sectors hbase hM hS) g hg

/-- Distance of the cover code: given the three floors and a base cycle `uStar`
of weight `d` whose pullback is not a cover boundary, `2 * d` is the least
weight of a nontrivial logical operator of the stabilizer group of the cover
code. It is attained by the X-type operator of the pullback of `uStar`. -/
theorem pauli_distance_eq_double {d : ℕ}
    (hbase : D.LogicalFloor d)
    (hM : D.DangerousFloorNZ (2 * d)) (hS : D.SafeFloor (2 * d))
    (uStar : H × Fin 2 → ZMod 2)
    (hu_cyc : uStar ∈ D.baseComplex.cycles)
    (hu_w : D.baseComplex.chainWeight uStar = d)
    (hτnb : D.pull1 uStar ∉ D.coverComplex.boundaries) :
    IsLeast {w : ℕ | ∃ g : NQubitPauliGroupElement D.coverComplex.numQubits,
      Quantum.StabilizerGroup.IsNontrivialLogicalOperator g
        D.coverComplex.homologicalStabilizerGroup ∧
      NQubitPauliGroupElement.weight g = w} (2 * d) := by
  refine ⟨⟨D.coverComplex.chainXOperator (D.pull1 uStar), ?_, ?_⟩, ?_⟩
  · exact (HomologicalCode.chainXOperator_isNontrivialLogical_iff
      (X := D.coverComplex) (D.pull1 uStar)).mpr ⟨D.pull1_mem_cycles hu_cyc, hτnb⟩
  · rw [HomologicalCode.weight_chainXOperator, D.chainWeight_pull1, hu_w]
  · rintro w ⟨g, hg, rfl⟩
    exact D.logical_weight_ge_double_of_sectors hbase hM hS g hg

/-! ## The doubling theorem

The two sector floors are replaced by the hypotheses that imply them:
`dangerousFloorNZ_of_admissible` for the dangerous sector and
`safeFloor_of_seamCosetFloor` for the safe one. The hypotheses are then

* the logical floor `LogicalFloor d` of the base,
* a base cycle `uStar` of weight `d` whose pullback is not a cover boundary,
* `DeckTrivialOnH1`,
* the seam-coset floor `SeamCosetFloor (2 * d)`, and
* the admissibility of every nonzero base boundary of weight `< 2 * d`.

No hypothesis `d ≥ 1` is needed: a chain of weight `0` is zero, and the
pullback of zero is a boundary. -/

/-- The doubling theorem at chain level: under the five hypotheses, `2 * d` is
the least weight of a cover cycle that is not a boundary. -/
theorem chain_distance_eq_double_of_admissible {d : ℕ}
    (hbase : D.LogicalFloor d)
    (uStar : H × Fin 2 → ZMod 2)
    (hu_cyc : uStar ∈ D.baseComplex.cycles)
    (hu_w : D.baseComplex.chainWeight uStar = d)
    (hτnb : D.pull1 uStar ∉ D.coverComplex.boundaries)
    (hR : D.DeckTrivialOnH1)
    (hMim : D.SeamCosetFloor (2 * d))
    (hadm : ∀ b : H × Fin 2 → ZMod 2, b ∈ D.baseComplex.boundaries → b ≠ 0 →
      D.baseComplex.chainWeight b < 2 * d → D.LightBoundaryAdmissible d b) :
    IsLeast {w : ℕ | ∃ v : G × Fin 2 → ZMod 2,
      v ∈ D.coverComplex.cycles ∧ v ∉ D.coverComplex.boundaries ∧
      D.coverComplex.chainWeight v = w} (2 * d) :=
  D.chain_distance_eq_double hbase
    (D.dangerousFloorNZ_of_admissible hbase hadm)
    (D.safeFloor_of_seamCosetFloor hR hMim) uStar hu_cyc hu_w hτnb

/-- The doubling theorem. For a free double cover `D` of bivariate bicycle
codes, assume that every base cycle that is not a boundary has weight at least
`d`; that `uStar` is a base cycle of weight `d` whose pullback is not a cover
boundary; that the deck translation acts trivially on `H₁` of the cover; that
the seam-coset floor `SeamCosetFloor (2 * d)` holds; and that every nonzero
base boundary of weight `< 2 * d` is admissible. Then `2 * d` is the least
weight of a nontrivial logical operator of the stabilizer group of the cover
code: the cover code has distance exactly `2 * d`. -/
theorem pauli_distance_eq_double_of_admissible {d : ℕ}
    (hbase : D.LogicalFloor d)
    (uStar : H × Fin 2 → ZMod 2)
    (hu_cyc : uStar ∈ D.baseComplex.cycles)
    (hu_w : D.baseComplex.chainWeight uStar = d)
    (hτnb : D.pull1 uStar ∉ D.coverComplex.boundaries)
    (hR : D.DeckTrivialOnH1)
    (hMim : D.SeamCosetFloor (2 * d))
    (hadm : ∀ b : H × Fin 2 → ZMod 2, b ∈ D.baseComplex.boundaries → b ≠ 0 →
      D.baseComplex.chainWeight b < 2 * d → D.LightBoundaryAdmissible d b) :
    IsLeast {w : ℕ | ∃ g : NQubitPauliGroupElement D.coverComplex.numQubits,
      Quantum.StabilizerGroup.IsNontrivialLogicalOperator g
        D.coverComplex.homologicalStabilizerGroup ∧
      NQubitPauliGroupElement.weight g = w} (2 * d) :=
  D.pauli_distance_eq_double hbase
    (D.dangerousFloorNZ_of_admissible hbase hadm)
    (D.safeFloor_of_seamCosetFloor hR hMim) uStar hu_cyc hu_w hτnb

end XDoubleCoverData

end BB
end Homological
end Stabilizer
end Quantum
