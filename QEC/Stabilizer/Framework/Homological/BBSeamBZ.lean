/-
# Seam-coset floors and light-boundary censuses by Brouwer–Zimmermann

For a free `ℤ₂` cover (`XDoubleCoverData`), both per-instance floors of the
doubling template can be read off one binary code on the base qubits: the
*coset code* `K = seamC (ker ∂₂) + im ∂₂`.

* `SeamCosetFloor m` says every word of `K` outside `im ∂₂` has weight `≥ m`;
* a light-boundary census lists every word of `im ∂₂ ⊆ K` of weight `< m`.

A `SeamBZCertificate` presents `K` by generators — the boundaries `∂₂ δ_g` and
the seams `seamC k` of a `ker ∂₂` basis — packed into `Nat` masks whose high
bits *tag* the seam part with the basis coordinates of `ζ`. A word of `K`
therefore records, above bit `n`, whether it is a boundary. Two
Brouwer–Zimmermann windows (`BZCertificate.lean`) then reach every coset word
of weight `< t₁ + t₂ + 2`, and the single predicate `ok` checked on the walks
yields both results:

* `SeamBZCertificate.seamCosetFloor` — if `ok` rejects every light tagged word,
  the seam-coset floor holds;
* `SeamBZCertificate.boundary_census` — if `ok` accepts a light untagged word
  only when it is in a list `L`, every light boundary is in `L`.

Nothing here depends on the instance: an instance supplies the mask encoding,
the kernel basis (`kernel_eq_sum_of_peel`), the generator and window data, and
the kernel `decide`s.
-/

import QEC.Stabilizer.Framework.Homological.BBDoubling
import QEC.Stabilizer.Framework.Homological.BZCertificate

namespace Quantum
namespace Stabilizer
namespace Homological
namespace BB

open F2Mask

open scoped BigOperators

/-! ## Sparse boundary rows -/

section Sparse

variable {H : Type} [Fintype H] [AddCommGroup H] [DecidableEq H]

/-- Convolving against the indicator of a duplicate-free list is a sum of
translates. -/
lemma conv_eq_sum_of_support {A : H → ZMod 2} {LA : List H} (hLA : LA.Nodup)
    (hA : ∀ h, A h = if h ∈ LA then 1 else 0) (f : H → ZMod 2) (p : H) :
    (A ⋆ f) p = (LA.map fun a => f (p - a)).sum := by
  rw [conv_apply]
  have hterm : ∀ h, A h * f (p - h) = if h ∈ LA.toFinset then f (p - h) else 0 := by
    intro h
    by_cases hh : h ∈ LA <;> simp [hA, hh]
  simp_rw [hterm]
  rw [Finset.sum_ite_mem, Finset.univ_inter, List.sum_toFinset _ hLA]

/-- The rows of `∂₂`: row `(p, 0)` reads the `A`-translates of `p`, row `(p, 1)`
the `B`-translates. -/
def bbRowCells (LA LB : List H) (q : H × Fin 2) : List H :=
  if q.2 = 0 then LA.map (q.1 - ·) else LB.map (q.1 - ·)

lemma bbBoundary2Fn_eq_rowSum {A B : H → ZMod 2} {LA LB : List H}
    (hLA : LA.Nodup) (hA : ∀ h, A h = if h ∈ LA then 1 else 0)
    (hLB : LB.Nodup) (hB : ∀ h, B h = if h ∈ LB then 1 else 0)
    (ζ : H → ZMod 2) (q : H × Fin 2) :
    bbBoundary2Fn A B ζ q = ((bbRowCells LA LB q).map ζ).sum := by
  obtain ⟨p, j⟩ := q
  change (if j = 0 then (A ⋆ ζ) p else (B ⋆ ζ) p) = _
  unfold bbRowCells
  split_ifs
  · rw [conv_eq_sum_of_support hLA hA, List.map_map]
    rfl
  · rw [conv_eq_sum_of_support hLB hB, List.map_map]
    rfl

end Sparse

section Tags

variable {H : Type} [AddCommGroup H]

/-! ## Free-cell tags -/

/-- The tag of a 2-chain: bit `i` records whether `ζ` is nonzero at the `i`-th
free cell. -/
def freeTag (free : List H) (ζ : H → ZMod 2) : ℕ :=
  ofBits (fun i => decide (ζ (free.getD i 0) ≠ 0)) free.length

lemma freeTag_add (free : List H) (a b : H → ZMod 2) :
    freeTag free (a + b) = freeTag free a ^^^ freeTag free b := by
  have key : ∀ x y : ZMod 2, decide (x + y ≠ 0) = (decide (x ≠ 0) ^^ decide (y ≠ 0)) := by
    decide
  refine Nat.eq_of_testBit_eq fun i => ?_
  simp only [freeTag, Nat.testBit_xor, testBit_ofBits, Pi.add_apply, key]
  cases decide (i < free.length) <;> simp

@[simp] lemma freeTag_zero (free : List H) : freeTag free 0 = 0 := by
  refine Nat.eq_of_testBit_eq fun i => ?_
  simp [freeTag, testBit_ofBits]

/-- A zero tag means `ζ` vanishes on the free cells. -/
lemma eq_zero_of_freeTag_eq_zero {free : List H} {ζ : H → ZMod 2}
    (h : freeTag free ζ = 0) : ∀ x ∈ free, ζ x = 0 := by
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  have hbit := congrArg (fun m => m.testBit i) h
  simp only [freeTag, testBit_ofBits, Nat.zero_testBit, hi, decide_true, Bool.true_and,
    decide_eq_false_iff_not, not_not] at hbit
  rwa [List.getD_eq_getElem _ _ hi] at hbit

end Tags

namespace XDoubleCoverData

variable {G H : Type}
  [Fintype G] [AddCommGroup G] [DecidableEq G]
  [Fintype H] [AddCommGroup H] [DecidableEq H]
  (D : XDoubleCoverData G H)

/-! ## Tagged coset words -/

lemma add_two_pow_mul_xor {n a b s t : ℕ} (ha : a < 2 ^ n) (hb : b < 2 ^ n) :
    (a + 2 ^ n * s) ^^^ (b + 2 ^ n * t) = (a ^^^ b) + 2 ^ n * (s ^^^ t) := by
  refine Nat.eq_of_testBit_eq fun j => ?_
  rw [Nat.testBit_xor, add_comm a, add_comm b, add_comm (a ^^^ b),
    Nat.testBit_two_pow_mul_add _ ha, Nat.testBit_two_pow_mul_add _ hb,
    Nat.testBit_two_pow_mul_add _ (Nat.xor_lt_two_pow ha hb), Nat.testBit_xor,
    Nat.testBit_xor]
  split_ifs <;> rfl

variable {n : ℕ} (e : H × Fin 2 ≃ Fin n)

/-- The tagged seam word of a 2-chain: the mask of `seamC ζ`, with `ζ`'s
free-cell tag above bit `n`. -/
def seamTagged (free : List H) (ζ : H → ZMod 2) : ℕ :=
  maskOf e (D.seamC ζ) + 2 ^ n * freeTag free ζ

/-- The tagged coset word of `seamC ζ + ∂₂ f`. -/
def cosetWord (free : List H) (ζ f : H → ZMod 2) : ℕ :=
  maskOf e (D.seamC ζ + bbBoundary2Fn D.Ab D.Bb f) + 2 ^ n * freeTag free ζ

lemma seamTagged_add (free : List H) (a b : H → ZMod 2) :
    D.seamTagged e free (a + b) = D.seamTagged e free a ^^^ D.seamTagged e free b := by
  rw [seamTagged, seamTagged, seamTagged, D.seamC_add, maskOf_add, freeTag_add,
    add_two_pow_mul_xor (maskOf_lt e _) (maskOf_lt e _)]

lemma seamTagged_zero (free : List H) : D.seamTagged e free 0 = 0 := by
  simp [seamTagged, D.seamC_zero]

lemma cosetWord_eq (free : List H) (ζ f : H → ZMod 2) :
    D.cosetWord e free ζ f
      = D.seamTagged e free ζ ^^^ maskOf e (bbBoundary2Fn D.Ab D.Bb f) := by
  rw [cosetWord, seamTagged, maskOf_add]
  have h := add_two_pow_mul_xor (s := freeTag free ζ) (t := 0) (maskOf_lt e (D.seamC ζ))
    (maskOf_lt e (bbBoundary2Fn D.Ab D.Bb f))
  rw [mul_zero, add_zero, Nat.xor_zero] at h
  exact h.symm

lemma cosetWord_mod (free : List H) (ζ f : H → ZMod 2) :
    D.cosetWord e free ζ f % 2 ^ n = maskOf e (D.seamC ζ + bbBoundary2Fn D.Ab D.Bb f) := by
  rw [cosetWord, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (maskOf_lt e _)]

lemma cosetWord_div (free : List H) (ζ f : H → ZMod 2) :
    D.cosetWord e free ζ f / 2 ^ n = freeTag free ζ := by
  rw [cosetWord, Nat.add_mul_div_left _ _ (by positivity),
    Nat.div_eq_of_lt (maskOf_lt e _), zero_add]

/-! ## The coset words lie in the generator span -/

lemma bbBoundary2Fn_base_zero : bbBoundary2Fn D.Ab D.Bb (0 : H → ZMod 2) = 0 := by
  have h : D.baseComplex.boundary2 0 = 0 := map_zero _
  exact h

/-- Every boundary's mask is in the span of the boundary generators. -/
lemma xorSpan_maskOf_boundary {gens : List ℕ}
    (hbdry : ∀ g, maskOf e (bbBoundary2Fn D.Ab D.Bb (Pi.single g 1)) ∈ gens)
    (f : H → ZMod 2) : XorSpan gens (maskOf e (bbBoundary2Fn D.Ab D.Bb f)) := by
  have key : ∀ S : Finset H, XorSpan gens (maskOf e (bbBoundary2Fn D.Ab D.Bb (indF2 S))) := by
    intro S
    induction S using Finset.induction with
    | empty =>
      rw [indF2_empty, D.bbBoundary2Fn_base_zero, maskOf_zero]
      exact .zero
    | @insert a S ha ih =>
      rw [indF2_insert ha, bbBoundary2Fn_add, maskOf_add]
      exact .step (hbdry a) ih
  rw [self_eq_indF2_filter f]
  exact key _

/-- Every combination of the kernel basis has its tagged seam word in the
span. -/
lemma xorSpan_seamTagged_sum {gens : List ℕ} (free : List H)
    (basis : List ((H → ZMod 2) × H))
    (hseam : ∀ b ∈ basis, D.seamTagged e free b.1 ∈ gens) (c : (H → ZMod 2) × H → ZMod 2) :
    XorSpan gens (D.seamTagged e free (basis.map fun b => c b • b.1).sum) := by
  have hc : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  induction basis with
  | nil => rw [List.map_nil, List.sum_nil, seamTagged_zero]; exact .zero
  | cons b rest ih =>
    rw [List.map_cons, List.sum_cons, seamTagged_add]
    refine XorSpan.xor ?_ (ih fun b' hb' => hseam b' (List.mem_cons_of_mem b hb'))
    rcases hc (c b) with h | h
    · rw [h, zero_smul, seamTagged_zero]; exact .zero
    · rw [h, one_smul]; exact .of_mem (hseam b List.mem_cons_self)

/-! ## The certificate -/

/-- A **Brouwer–Zimmermann certificate for the seam cosets** of a free `ℤ₂`
cover: a packed encoding of the base qubits, a `ker ∂₂` basis with its free
cells, a generator list containing every tagged seam word of the basis and
every boundary generator's mask, and two windows whose walks accept under `ok`.
-/
structure SeamBZCertificate where
  /-- Number of base qubits (the word length). -/
  n : ℕ
  /-- The packed encoding of base qubits. -/
  e : H × Fin 2 ≃ Fin n
  /-- A `ker ∂₂` basis, each vector paired with its free cell. -/
  basis : List ((H → ZMod 2) × H)
  span : ∀ ζ, bbBoundary2Fn D.Ab D.Bb ζ = 0 → ζ = (basis.map fun b => ζ b.2 • b.1).sum
  /-- The generator words of the tagged coset code. -/
  gens : List ℕ
  seam_mem : ∀ b ∈ basis, D.seamTagged e (basis.map Prod.snd) b.1 ∈ gens
  bdry_mem : ∀ g, maskOf e (bbBoundary2Fn D.Ab D.Bb (Pi.single g 1)) ∈ gens
  /-- The predicate checked at every word the walks visit. -/
  ok : ℕ → Bool
  ok_zero : ok 0 = true
  /-- The two windows: `(pivot bit, extended row)` pairs. -/
  w₁ : List (ℕ × ℕ)
  w₂ : List (ℕ × ℕ)
  /-- The walk depths. -/
  t₁ : ℕ
  t₂ : ℕ
  pivots_nodup : (w₁.map Prod.fst ++ w₂.map Prod.fst).Nodup
  pivots_lt : ∀ p ∈ w₁.map Prod.fst ++ w₂.map Prod.fst, p < n
  recon₁ : ∀ g ∈ gens, reconX w₁ (g % 2 ^ n) = g
  recon₂ : ∀ g ∈ gens, reconX w₂ (g % 2 ^ n) = g
  walk₁ : xorWalk ok (w₁.map Prod.snd) t₁ 0 = true
  walk₂ : xorWalk ok (w₂.map Prod.snd) t₂ 0 = true

namespace SeamBZCertificate

variable {D} (C : D.SeamBZCertificate)

/-- **The certified predicate holds on every light coset word.** -/
theorem ok_cosetWord {ζ : H → ZMod 2} (hζ : bbBoundary2Fn D.Ab D.Bb ζ = 0)
    (f : H → ZMod 2)
    (hwt : D.baseComplex.chainWeight (D.seamC ζ + bbBoundary2Fn D.Ab D.Bb f)
      < C.t₁ + C.t₂ + 2) :
    C.ok (D.cosetWord C.e (C.basis.map Prod.snd) ζ f) = true := by
  refine bz_ok_of_xorSpan C.pivots_nodup C.pivots_lt C.ok_zero C.walk₁ C.walk₂ C.recon₁
    C.recon₂ ?_ ?_
  · rw [cosetWord_eq, C.span ζ hζ]
    exact (D.xorSpan_seamTagged_sum C.e _ C.basis C.seam_mem _).xor
      (D.xorSpan_maskOf_boundary C.e C.bdry_mem f)
  · rw [← bitCount_mod, cosetWord_mod, ← card_support_eq_bitCount, ← D.baseComplex_chainWeight_eq]
    exact hwt

/-- A `ker ∂₂` element with zero tag is zero. -/
lemma eq_zero_of_tag {ζ : H → ZMod 2} (hζ : bbBoundary2Fn D.Ab D.Bb ζ = 0)
    (htag : freeTag (C.basis.map Prod.snd) ζ = 0) : ζ = 0 := by
  have hfree := eq_zero_of_freeTag_eq_zero htag
  rw [C.span ζ hζ]
  refine List.sum_eq_zero fun y hy => ?_
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hy
  rw [hfree b.2 (List.mem_map_of_mem hb), zero_smul]

/-- **The seam-coset floor.** If `ok` forces weight `≥ m` on every tagged word,
then `SeamCosetFloor m` holds, for `m ≤ t₁ + t₂ + 2`. -/
theorem seamCosetFloor {m : ℕ} (hm : m ≤ C.t₁ + C.t₂ + 2)
    (hok : ∀ X, C.ok X = true → X / 2 ^ C.n ≠ 0 → m ≤ bitCount C.n X) :
    D.SeamCosetFloor m := by
  intro ζ hζ f hnb
  by_contra hlt
  push Not at hlt
  have hX := C.ok_cosetWord hζ f (by omega)
  by_cases htag : freeTag (C.basis.map Prod.snd) ζ = 0
  · apply hnb
    rw [C.eq_zero_of_tag hζ htag, D.seamC_zero, zero_add]
    exact ⟨_, rfl⟩
  · have := hok _ hX (by rwa [cosetWord_div])
    rw [← bitCount_mod, cosetWord_mod, ← card_support_eq_bitCount,
      ← D.baseComplex_chainWeight_eq] at this
    omega

/-- **The light-boundary census.** If `ok` accepts an untagged word of weight
`< m` only when it lies in `L`, then every boundary of weight `< m` has its
mask in `L`, for `m ≤ t₁ + t₂ + 2`. -/
theorem boundary_census {m : ℕ} (hm : m ≤ C.t₁ + C.t₂ + 2) {L : List ℕ}
    (hok : ∀ X, C.ok X = true → X / 2 ^ C.n = 0 → bitCount C.n X < m → X ∈ L)
    (f : H → ZMod 2) (hwt : D.baseComplex.chainWeight (bbBoundary2Fn D.Ab D.Bb f) < m) :
    maskOf C.e (bbBoundary2Fn D.Ab D.Bb f) ∈ L := by
  have hζ : bbBoundary2Fn D.Ab D.Bb (0 : H → ZMod 2) = 0 := D.bbBoundary2Fn_base_zero
  have hw0 : D.seamC 0 + bbBoundary2Fn D.Ab D.Bb f = bbBoundary2Fn D.Ab D.Bb f := by
    rw [D.seamC_zero, zero_add]
  have hX := C.ok_cosetWord hζ f (by rw [hw0]; omega)
  have hword : D.cosetWord C.e (C.basis.map Prod.snd) 0 f
      = maskOf C.e (bbBoundary2Fn D.Ab D.Bb f) := by
    rw [cosetWord, hw0, freeTag_zero, mul_zero, add_zero]
  rw [hword] at hX
  refine hok _ hX ?_ ?_
  · rw [Nat.div_eq_of_lt (maskOf_lt C.e _)]
  · rw [← card_support_eq_bitCount, ← D.baseComplex_chainWeight_eq]
    exact hwt

end SeamBZCertificate

end XDoubleCoverData

end BB
end Homological
end Stabilizer
end Quantum
