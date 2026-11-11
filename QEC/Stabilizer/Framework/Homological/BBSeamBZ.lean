import QEC.Stabilizer.Framework.Homological.BBDoubling
import QEC.Stabilizer.Framework.Homological.BZCertificate

/-!
# Brouwer–Zimmermann certificates for seam-coset floors and light boundaries

For a free double cover `D : XDoubleCoverData G H` of bivariate bicycle codes,
two hypotheses of the doubling theorem of `BBDoubling` are statements about one
binary linear code on the base qubits, the *coset code*
`K = {seamC ζ + ∂₂ f | ∂₂ ζ = 0}`, which contains the code `im ∂₂` of base
boundaries:

* `SeamCosetFloor m` says that every word of `K` outside `im ∂₂` has weight at
  least `m`;
* the admissibility of the light base boundaries is a statement about the
  words of `im ∂₂` of weight `< m`, so it needs a list of all of them.

A `SeamBZCertificate` presents `K` by generators packed into `Nat` masks
(`F2Mask.maskOf`): the boundaries `∂₂ δ_g` and the seam chains `seamC k` of a
basis of `ker ∂₂`. Each basis vector comes with a *free cell*, at which it is
the only basis vector that does not vanish, and the bits of a mask above the
word length `n` carry the *tag* `freeTag` of `ζ`, its values at the free cells.
The tagged word `cosetWord` of `seamC ζ + ∂₂ f` therefore has tag zero only if
`ζ = 0`, in which case it is the mask of a boundary. Two Brouwer–Zimmermann
windows (`F2Mask.bz_ok_of_xorSpan`) reach every word of weight
`< t₁ + t₂ + 2`, and one predicate `ok` checked along their walks gives both
results:

* `SeamBZCertificate.seamCosetFloor`: if `ok` forces weight `≥ m` on every
  word with a nonzero tag, then `SeamCosetFloor m` holds;
* `SeamBZCertificate.boundary_census`: if `ok` accepts a word of tag zero and
  weight `< m` only when it lies in a list `L`, then the mask of every base
  boundary of weight `< m` lies in `L`.

The file also writes `∂₂` as a row-sparse map (`bbRowCells`,
`bbBoundary2Fn_eq_rowSum`), the form in which `F2Mask.kernel_eq_sum_of_peel`
certifies the basis of `ker ∂₂` required by the field `span`.
-/

namespace Quantum
namespace Stabilizer
namespace Homological
namespace BB

open F2Mask

open scoped BigOperators

/-! ## Sparse boundary rows

When `A` and `B` are the indicators of duplicate-free lists `LA`, `LB`, the
value of `∂₂ ζ` at a qubit is the sum of `ζ` over a short list of cells. -/

section Sparse

variable {H : Type} [Fintype H] [AddCommGroup H] [DecidableEq H]

/-- Convolution by the indicator of a duplicate-free list `LA` is a sum of
translates: `(A ⋆ f) p = ∑ a ∈ LA, f (p - a)`. -/
lemma conv_eq_sum_of_support {A : H → ZMod 2} {LA : List H} (hLA : LA.Nodup)
    (hA : ∀ h, A h = if h ∈ LA then 1 else 0) (f : H → ZMod 2) (p : H) :
    (A ⋆ f) p = (LA.map fun a => f (p - a)).sum := by
  rw [conv_apply]
  have hterm : ∀ h, A h * f (p - h) = if h ∈ LA.toFinset then f (p - h) else 0 := by
    intro h
    by_cases hh : h ∈ LA <;> simp [hA, hh]
  simp_rw [hterm]
  rw [Finset.sum_ite_mem, Finset.univ_inter, List.sum_toFinset _ hLA]

/-- The cells read by the row of `∂₂` at a qubit: `p - a` for `a ∈ LA` at the
qubit `(p, 0)`, and `p - b` for `b ∈ LB` at the qubit `(p, 1)`. -/
def bbRowCells (LA LB : List H) (q : H × Fin 2) : List H :=
  if q.2 = 0 then LA.map (q.1 - ·) else LB.map (q.1 - ·)

/-- `∂₂` is row-sparse: `(∂₂ ζ) q` is the sum of `ζ` over the cells
`bbRowCells LA LB q`. -/
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

/-! ## Free-cell tags -/

section Tags

variable {H : Type} [AddCommGroup H]

/-- The tag of a 2-chain `ζ` with respect to a list of free cells: bit `i`
records whether `ζ` is nonzero at the `i`-th free cell. -/
def freeTag (free : List H) (ζ : H → ZMod 2) : ℕ :=
  ofBits (fun i => decide (ζ (free.getD i 0) ≠ 0)) free.length

/-- The tag is additive: the tag of a sum is the XOR of the tags. -/
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

/-- A chain with zero tag vanishes at every free cell. -/
lemma eq_zero_of_freeTag_eq_zero {free : List H} {ζ : H → ZMod 2}
    (h : freeTag free ζ = 0) : ∀ x ∈ free, ζ x = 0 := by
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  have hbit := congrArg (fun m => m.testBit i) h
  simp only [freeTag, testBit_ofBits, Nat.zero_testBit, hi, decide_true, Bool.true_and,
    decide_eq_false_iff_not, not_not] at hbit
  rwa [List.getD_eq_getElem _ _ hi] at hbit

end Tags

/-- XOR acts separately on the low `n` bits and on the bits above them:
`(a + 2 ^ n * s) ^^^ (b + 2 ^ n * t) = (a ^^^ b) + 2 ^ n * (s ^^^ t)` for
`a, b < 2 ^ n`. -/
lemma add_two_pow_mul_xor {n a b s t : ℕ} (ha : a < 2 ^ n) (hb : b < 2 ^ n) :
    (a + 2 ^ n * s) ^^^ (b + 2 ^ n * t) = (a ^^^ b) + 2 ^ n * (s ^^^ t) := by
  refine Nat.eq_of_testBit_eq fun j => ?_
  rw [Nat.testBit_xor, add_comm a, add_comm b, add_comm (a ^^^ b),
    Nat.testBit_two_pow_mul_add _ ha, Nat.testBit_two_pow_mul_add _ hb,
    Nat.testBit_two_pow_mul_add _ (Nat.xor_lt_two_pow ha hb), Nat.testBit_xor,
    Nat.testBit_xor]
  split_ifs <;> rfl

namespace XDoubleCoverData

variable {G H : Type}
  [Fintype G] [AddCommGroup G] [DecidableEq G]
  [Fintype H] [AddCommGroup H] [DecidableEq H]
  (D : XDoubleCoverData G H)

/-! ## Tagged coset words

Base 1-chains are packed into `Nat` masks below bit `n` through a numbering
`e : H × Fin 2 ≃ Fin n` of the base qubits; the tag of `ζ` is stored above
bit `n`. -/

variable {n : ℕ} (e : H × Fin 2 ≃ Fin n)

/-- The tagged seam word of a base 2-chain `ζ`: the mask of `seamC ζ`, with
the tag of `ζ` above bit `n`. -/
def seamTagged (free : List H) (ζ : H → ZMod 2) : ℕ :=
  maskOf e (D.seamC ζ) + 2 ^ n * freeTag free ζ

/-- The tagged coset word of `seamC ζ + ∂₂ f`: its mask, with the tag of `ζ`
above bit `n`. -/
def cosetWord (free : List H) (ζ f : H → ZMod 2) : ℕ :=
  maskOf e (D.seamC ζ + bbBoundary2Fn D.Ab D.Bb f) + 2 ^ n * freeTag free ζ

/-- The tagged seam word is additive in `ζ`. -/
lemma seamTagged_add (free : List H) (a b : H → ZMod 2) :
    D.seamTagged e free (a + b) = D.seamTagged e free a ^^^ D.seamTagged e free b := by
  rw [seamTagged, seamTagged, seamTagged, D.seamC_add, maskOf_add, freeTag_add,
    add_two_pow_mul_xor (maskOf_lt e _) (maskOf_lt e _)]

lemma seamTagged_zero (free : List H) : D.seamTagged e free 0 = 0 := by
  simp [seamTagged, D.seamC_zero]

/-- The tagged coset word is the XOR of the tagged seam word of `ζ` and the
mask of `∂₂ f`. -/
lemma cosetWord_eq (free : List H) (ζ f : H → ZMod 2) :
    D.cosetWord e free ζ f
      = D.seamTagged e free ζ ^^^ maskOf e (bbBoundary2Fn D.Ab D.Bb f) := by
  rw [cosetWord, seamTagged, maskOf_add]
  have h := add_two_pow_mul_xor (s := freeTag free ζ) (t := 0) (maskOf_lt e (D.seamC ζ))
    (maskOf_lt e (bbBoundary2Fn D.Ab D.Bb f))
  rw [mul_zero, add_zero, Nat.xor_zero] at h
  exact h.symm

/-- The low `n` bits of a tagged coset word are the mask of the chain. -/
lemma cosetWord_mod (free : List H) (ζ f : H → ZMod 2) :
    D.cosetWord e free ζ f % 2 ^ n = maskOf e (D.seamC ζ + bbBoundary2Fn D.Ab D.Bb f) := by
  rw [cosetWord, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (maskOf_lt e _)]

/-- The bits of a tagged coset word above bit `n` are the tag of `ζ`. -/
lemma cosetWord_div (free : List H) (ζ f : H → ZMod 2) :
    D.cosetWord e free ζ f / 2 ^ n = freeTag free ζ := by
  rw [cosetWord, Nat.add_mul_div_left _ _ (by positivity),
    Nat.div_eq_of_lt (maskOf_lt e _), zero_add]

/-! ## The coset words lie in the span of the generators -/

/-- If the masks of the boundaries `∂₂ δ_g` of the point masses are among the
generators, the mask of every base boundary is in their span. -/
lemma xorSpan_maskOf_boundary {gens : List ℕ}
    (hbdry : ∀ g, maskOf e (bbBoundary2Fn D.Ab D.Bb (Pi.single g 1)) ∈ gens)
    (f : H → ZMod 2) : XorSpan gens (maskOf e (bbBoundary2Fn D.Ab D.Bb f)) := by
  have key : ∀ S : Finset H, XorSpan gens (maskOf e (bbBoundary2Fn D.Ab D.Bb (indF2 S))) := by
    intro S
    induction S using Finset.induction with
    | empty =>
      rw [indF2_empty, ← bbBoundary2_apply, map_zero, maskOf_zero]
      exact .zero
    | @insert a S ha ih =>
      rw [indF2_insert ha, bbBoundary2Fn_add, maskOf_add]
      exact .step (hbdry a) ih
  rw [self_eq_indF2_filter f]
  exact key _

/-- If the tagged seam words of the vectors of `basis` are among the
generators, the tagged seam word of every combination of `basis` is in their
span. -/
lemma xorSpan_seamTagged_sum {gens : List ℕ} (free : List H)
    (basis : List ((H → ZMod 2) × H))
    (hseam : ∀ b ∈ basis, D.seamTagged e free b.1 ∈ gens) (c : (H → ZMod 2) × H → ZMod 2) :
    XorSpan gens (D.seamTagged e free (basis.map fun b => c b • b.1).sum) := by
  induction basis with
  | nil =>
    rw [List.map_nil, List.sum_nil, seamTagged_zero]
    exact .zero
  | cons b rest ih =>
    rw [List.map_cons, List.sum_cons, seamTagged_add]
    refine XorSpan.xor ?_ (ih fun b' hb' => hseam b' (List.mem_cons_of_mem b hb'))
    rcases zmod2_eq_zero_or_eq_one (c b) with h | h
    · rw [h, zero_smul, seamTagged_zero]
      exact .zero
    · rw [h, one_smul]
      exact .of_mem (hseam b List.mem_cons_self)

/-! ## The certificate -/

/-- A Brouwer–Zimmermann certificate for the seam cosets of a free double
cover: a numbering of the base qubits, a basis of `ker ∂₂` with its free cells,
a list of generators containing the tagged seam word of every basis vector and
the mask of every boundary `∂₂ δ_g`, and two windows on disjoint pivot sets
whose walks satisfy the predicate `ok`. -/
structure SeamBZCertificate where
  /-- The number of base qubits (the word length). -/
  n : ℕ
  /-- The numbering of the base qubits used to pack chains into masks. -/
  e : H × Fin 2 ≃ Fin n
  /-- A basis of `ker ∂₂`, each vector paired with its free cell. -/
  basis : List ((H → ZMod 2) × H)
  /-- Every element of `ker ∂₂` is the combination of the basis whose
  coefficients are its values at the free cells. -/
  span : ∀ ζ, bbBoundary2Fn D.Ab D.Bb ζ = 0 → ζ = (basis.map fun b => ζ b.2 • b.1).sum
  /-- The generator words of the tagged coset code. -/
  gens : List ℕ
  /-- The tagged seam word of every basis vector is a generator. -/
  seam_mem : ∀ b ∈ basis, D.seamTagged e (basis.map Prod.snd) b.1 ∈ gens
  /-- The mask of the boundary of every point mass is a generator. -/
  bdry_mem : ∀ g, maskOf e (bbBoundary2Fn D.Ab D.Bb (Pi.single g 1)) ∈ gens
  /-- The predicate checked at every word the walks visit. -/
  ok : ℕ → Bool
  /-- The predicate holds at the zero word. -/
  ok_zero : ok 0 = true
  /-- The first window: a list of `(pivot bit, tagged row)` pairs. -/
  w₁ : List (ℕ × ℕ)
  /-- The second window: a list of `(pivot bit, tagged row)` pairs. -/
  w₂ : List (ℕ × ℕ)
  /-- The depth of the walk through the first window. -/
  t₁ : ℕ
  /-- The depth of the walk through the second window. -/
  t₂ : ℕ
  /-- The pivot bits of the two windows are pairwise distinct. -/
  pivots_nodup : (w₁.map Prod.fst ++ w₂.map Prod.fst).Nodup
  /-- The pivot bits lie below the word length. -/
  pivots_lt : ∀ p ∈ w₁.map Prod.fst ++ w₂.map Prod.fst, p < n
  /-- The first window reconstructs every generator from its low `n` bits. -/
  recon₁ : ∀ g ∈ gens, reconX w₁ (g % 2 ^ n) = g
  /-- The second window reconstructs every generator from its low `n` bits. -/
  recon₂ : ∀ g ∈ gens, reconX w₂ (g % 2 ^ n) = g
  /-- The walk of depth `t₁` through the rows of the first window passes. -/
  walk₁ : xorWalk ok (w₁.map Prod.snd) t₁ 0 = true
  /-- The walk of depth `t₂` through the rows of the second window passes. -/
  walk₂ : xorWalk ok (w₂.map Prod.snd) t₂ 0 = true

namespace SeamBZCertificate

variable {D} (C : D.SeamBZCertificate)

/-- The predicate `ok` holds at the tagged coset word of every chain
`seamC ζ + ∂₂ f`, `∂₂ ζ = 0`, of weight `< t₁ + t₂ + 2`. -/
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

/-- An element of `ker ∂₂` with zero tag is zero. -/
lemma eq_zero_of_tag {ζ : H → ZMod 2} (hζ : bbBoundary2Fn D.Ab D.Bb ζ = 0)
    (htag : freeTag (C.basis.map Prod.snd) ζ = 0) : ζ = 0 := by
  have hfree := eq_zero_of_freeTag_eq_zero htag
  rw [C.span ζ hζ]
  refine List.sum_eq_zero fun y hy => ?_
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hy
  rw [hfree b.2 (List.mem_map_of_mem hb), zero_smul]

/-- The seam-coset floor from a certificate: if `ok` forces weight `≥ m` on
every word with a nonzero tag, then `SeamCosetFloor m` holds, for
`m ≤ t₁ + t₂ + 2`. -/
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

/-- The list of light boundaries from a certificate: if `ok` accepts a word of
tag zero and weight `< m` only when it lies in `L`, then the mask of every base
boundary of weight `< m` lies in `L`, for `m ≤ t₁ + t₂ + 2`. -/
theorem boundary_census {m : ℕ} (hm : m ≤ C.t₁ + C.t₂ + 2) {L : List ℕ}
    (hok : ∀ X, C.ok X = true → X / 2 ^ C.n = 0 → bitCount C.n X < m → X ∈ L)
    (f : H → ZMod 2) (hwt : D.baseComplex.chainWeight (bbBoundary2Fn D.Ab D.Bb f) < m) :
    maskOf C.e (bbBoundary2Fn D.Ab D.Bb f) ∈ L := by
  have hζ : bbBoundary2Fn D.Ab D.Bb (0 : H → ZMod 2) = 0 := map_zero (bbBoundary2 D.Ab D.Bb)
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
