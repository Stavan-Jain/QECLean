/-
# The gross safe floor and light-boundary census, by Brouwer–Zimmermann

Both CRT-engine inputs of the gross `d = 12` proof come out of one certificate
for the generic `SeamBZCertificate` (`Framework/Homological/BBSeamBZ.lean`):

* `mimBound_bz : MImBound` — the seam-coset floor `SeamCosetFloor 12`. The
  certificate gives `SeamCosetFloor 11` (no tagged coset word of weight `≤ 10`),
  and the deficit wall (`seamCosetFloor_of_even_of_pred`) lifts it to `12`
  because coset words are cycles, hence of even weight.
* `lightStabilizerClassification_bz : LightStabilizerClassification` — every
  boundary of weight `≤ 11` (so `≤ 10`, by parity) is one of the 252 light
  boundaries the walks were allowed to accept, each a hexagon or a D-pair.

The certificate's ingredients are the generated data (`SeamBZData.lean`), the
two kernel walks (`SeamBZWalk.lean`), and the checks below: the `ker ∂₂` basis
by peeling, and the generator words through the sparse forms of `∂₂` and
`seamC`. All kernel `decide`, no `native_decide`.
-/

import QEC.Stabilizer.Codes.BivariateBicycle.Gross.SeamBZWalk
import QEC.Stabilizer.Codes.BivariateBicycle.Gross.SafeSector
import QEC.Stabilizer.Framework.Homological.BBSeamBZ
import QEC.Stabilizer.Framework.Homological.BBDeficitWall

namespace Quantum.Stabilizer.Homological.BB

open F2Mask

namespace GrossBZ

/-! ## The qubit encoding and the boundary rows -/

/-- Base qubits, packed as `((a, b), j) ↦ 6·a + b + 36·j`. -/
def enc : BaseGroup × Fin 2 ≃ Fin 72 :=
  (Equiv.prodComm _ _).trans
    ((Equiv.prodCongr (Equiv.refl (Fin 2)) (finProdFinEquiv : Fin 6 × Fin 6 ≃ Fin 36)).trans
      finProdFinEquiv)

/-- The support of `A = x³ + y + y²`. -/
def suppA : List BaseGroup := [(3, 0), (0, 1), (0, 2)]

/-- The support of `B = y³ + x + x²`. -/
def suppB : List BaseGroup := [(0, 3), (1, 0), (2, 0)]

/-- `∂₂` row by row: three translates per row. -/
lemma bb2_rowSum (ζ : BaseGroup → ZMod 2) (q : BaseGroup × Fin 2) :
    bbBoundary2Fn baseA baseB ζ q = ((bbRowCells suppA suppB q).map ζ).sum :=
  bbBoundary2Fn_eq_rowSum (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) ζ q

/-! ## The `ker ∂₂` basis -/

/-- The indicator of a list of cells. -/
def indicator (S : List BaseGroup) : BaseGroup → ZMod 2 := fun h => if h ∈ S then 1 else 0

/-- The `ker ∂₂` basis, each vector paired with its free cell. -/
def kbBasis : List ((BaseGroup → ZMod 2) × BaseGroup) :=
  (kbSupports.zip kbFree).map fun p => (indicator p.1, p.2)

lemma kbBasis_free : kbBasis.map Prod.snd = kbFree := by decide +kernel

/-! The checks below quantify over the raw data `kbSupports.zip kbFree`, never
over `kbBasis`: its elements `(BaseGroup → ZMod 2) × BaseGroup` form a
`Fintype`, so `decide` on `∀ b ∈ kbBasis, …` would pick
`Fintype.decidableForallFintype` and enumerate all `2³⁶ · 36` such pairs. -/

private lemma kb_rows : ∀ p ∈ kbSupports.zip kbFree,
    ∀ q, ((bbRowCells suppA suppB q).map (indicator p.1)).sum = 0 := by
  decide +kernel

private lemma kb_diag : ∀ p ∈ kbSupports.zip kbFree, indicator p.1 p.2 = 1 := by
  decide +kernel

private lemma kb_pair : (kbSupports.zip kbFree).Pairwise fun p p' =>
    indicator p.1 p'.2 = 0 ∧ indicator p'.1 p.2 = 0 := by
  decide +kernel

private lemma mem_kbBasis {b : (BaseGroup → ZMod 2) × BaseGroup} (hb : b ∈ kbBasis) :
    ∃ p ∈ kbSupports.zip kbFree, b = (indicator p.1, p.2) := by
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hb
  exact ⟨p, hp, rfl⟩

/-- Every `ker ∂₂` element is the combination of the basis read off its free
cells (Gaussian elimination as a 30-step peeling order). -/
theorem kbBasis_span (ζ : BaseGroup → ZMod 2) (hζ : bbBoundary2Fn baseA baseB ζ = 0) :
    ζ = (kbBasis.map fun b => ζ b.2 • b.1).sum := by
  refine kernel_eq_sum_of_peel (bbRowCells suppA suppB) bb2_rowSum kbBasis ?_ ?_ ?_ kbPeel
    (by rw [kbBasis_free]; decide +kernel) (by rw [kbBasis_free]; decide +kernel) ζ hζ
  · intro b hb
    obtain ⟨p, hp, rfl⟩ := mem_kbBasis hb
    exact funext fun q => by rw [bb2_rowSum]; exact kb_rows p hp q
  · intro b hb
    obtain ⟨p, hp, rfl⟩ := mem_kbBasis hb
    exact kb_diag p hp
  · exact List.pairwise_map.mpr kb_pair

/-! ## The generator words -/

/-- The packed mask of the hexagon `∂₂ δ_g`: the `g`-th generator word. -/
def hexMask (g : BaseGroup) : ℕ := gensData.getD (6 * g.1.val + g.2.val) 0

private lemma hex_rows : ∀ g : BaseGroup, hexMask g < 2 ^ 72 ∧
    ∀ q, ((bbRowCells suppA suppB q).map (Pi.single g 1)).sum = chainOfMask enc (hexMask g) q := by
  decide +kernel

private lemma hex_mem : ∀ g : BaseGroup, hexMask g ∈ gensData := by decide +kernel

lemma maskOf_hex (g : BaseGroup) :
    maskOf enc (bbBoundary2Fn baseA baseB (Pi.single g 1)) = hexMask g := by
  obtain ⟨hlt, hrow⟩ := hex_rows g
  have : bbBoundary2Fn baseA baseB (Pi.single g 1) = chainOfMask enc (hexMask g) :=
    funext fun q => by rw [bb2_rowSum]; exact hrow q
  rw [this, maskOf_chainOfMask enc hlt]

private lemma seam_gens : ∀ p ∈ kbSupports.zip kbFree, ∃ m ∈ gensData,
    (∀ q, seamCSparse (indicator p.1) q = chainOfMask enc (m % 2 ^ 72) q)
      ∧ freeTag kbFree (indicator p.1) = m / 2 ^ 72 := by
  decide +kernel

lemma bdry_mem (g : BaseGroup) :
    maskOf enc (bbBoundary2Fn grossCoverData.Ab grossCoverData.Bb (Pi.single g 1)) ∈ gensData := by
  change maskOf enc (bbBoundary2Fn baseA baseB (Pi.single g 1)) ∈ gensData
  rw [maskOf_hex]
  exact hex_mem g

lemma seam_mem (b : (BaseGroup → ZMod 2) × BaseGroup) (hb : b ∈ kbBasis) :
    grossCoverData.seamTagged enc (kbBasis.map Prod.snd) b.1 ∈ gensData := by
  obtain ⟨p, hp, rfl⟩ := mem_kbBasis hb
  obtain ⟨m, hm, hsp, htag⟩ := seam_gens p hp
  have hseam : grossCoverData.seamC (indicator p.1) = chainOfMask enc (m % 2 ^ 72) := by
    rw [grossCoverData_seamC, seamC_eq_sparse]
    exact funext hsp
  rw [XDoubleCoverData.seamTagged, hseam, maskOf_chainOfMask enc (Nat.mod_lt _ (by positivity)),
    kbBasis_free, htag, Nat.mod_add_div]
  exact hm

/-! ## The certificate -/

/-- The first window: `(pivot bit, tagged row)` pairs. -/
def window₁ : List (ℕ × ℕ) := window₁Pivots.zip window₁Rows

/-- The second window. -/
def window₂ : List (ℕ × ℕ) := window₂Pivots.zip window₂Rows

/-- **The gross seam-coset certificate.** -/
def grossSeamBZ : grossCoverData.SeamBZCertificate where
  n := 72
  e := enc
  basis := kbBasis
  span := kbBasis_span
  gens := gensData
  seam_mem := seam_mem
  bdry_mem := bdry_mem
  ok := okGross
  ok_zero := rfl
  w₁ := window₁
  w₂ := window₂
  t₁ := 5
  t₂ := 4
  pivots_nodup := by decide +kernel
  pivots_lt := by decide +kernel
  recon₁ := by decide +kernel
  recon₂ := by decide +kernel
  walk₁ := by rw [show window₁.map Prod.snd = window₁Rows by decide +kernel]; exact walk₁
  walk₂ := by rw [show window₂.map Prod.snd = window₂Rows by decide +kernel]; exact walk₂

/-! ## What `okGross` certifies -/

private lemma okGross_spec (X : ℕ) (h : okGross X = true) :
    X = 0 ∨ 11 ≤ bitCount 72 X ∨ (X / 2 ^ 72 = 0 ∧ X ∈ lightMasks) := by
  simp only [okGross, Bool.or_eq_true, Bool.and_eq_true, List.contains_iff_mem] at h
  rcases h with (h | h) | ⟨h, hmem⟩
  · exact Or.inl (Nat.eq_of_beq_eq_true h)
  · have h' := Nat.le_of_ble_eq_true h
    rw [bitCountFast_eq] at h'
    exact Or.inr (Or.inl h')
  · refine Or.inr (Or.inr ⟨?_, hmem⟩)
    rw [← Nat.shiftRight_eq_div_pow]
    exact Nat.eq_of_beq_eq_true h

lemma okGross_tagged (X : ℕ) (h : okGross X = true) (htag : X / 2 ^ 72 ≠ 0) :
    11 ≤ bitCount 72 X := by
  rcases okGross_spec X h with rfl | h | ⟨h0, _⟩
  · simp at htag
  · exact h
  · exact absurd h0 htag

lemma okGross_untagged (X : ℕ) (h : okGross X = true) (_ : X / 2 ^ 72 = 0)
    (hlt : bitCount 72 X < 11) : X ∈ 0 :: lightMasks := by
  rcases okGross_spec X h with rfl | h | ⟨_, hmem⟩
  · exact List.mem_cons_self
  · omega
  · exact List.mem_cons_of_mem _ hmem

/-! ## The two discharged inputs -/

/-- **(M-im), by Brouwer–Zimmermann**: every word of a nonzero Smith seam-coset
has weight `≥ 12`. -/
theorem mimBound_bz : MImBound :=
  grossCoverData.seamCosetFloor_of_even_of_pred baseSmallCycleData.epsA
    baseSmallCycleData.epsB (by decide)
    (grossSeamBZ.seamCosetFloor (m := 11) (by decide) okGross_tagged)

/-- The light shapes: a hexagon's or a D-pair's `2`-chain. -/
def shapeChain (g : BaseGroup) : Option BaseGroup → BaseGroup → ZMod 2
  | none => Pi.single g 1
  | some d => Pi.single g 1 + Pi.single (g + d) 1

/-- A light shape's direction is admissible (vacuous for a hexagon). -/
def dirOK : Option BaseGroup → Bool
  | none => true
  | some d => decide (d ∈ pairDirections)

/-- The mask a light-shape record must carry: one hexagon, or the XOR of two. -/
def shapeMask (g : BaseGroup) : Option BaseGroup → ℕ
  | none => hexMask g
  | some d => Nat.xor (hexMask g) (hexMask (g + d))

private lemma light_shapes : ∀ x ∈ lightData, dirOK x.2.2 = true ∧ x.1 = shapeMask x.2.1 x.2.2 := by
  decide +kernel

lemma maskOf_shape (g : BaseGroup) (d : Option BaseGroup) :
    maskOf enc (bbBoundary2Fn baseA baseB (shapeChain g d)) = shapeMask g d := by
  cases d with
  | none => exact maskOf_hex g
  | some d =>
    change maskOf enc (bbBoundary2Fn baseA baseB (Pi.single g 1 + Pi.single (g + d) 1)) = _
    rw [bbBoundary2Fn_add, maskOf_add, maskOf_hex, maskOf_hex]
    rfl

private lemma lightMasks_eq : lightMasks = lightData.map Prod.fst := by decide +kernel

/-- **The light-stabilizer classification, by Brouwer–Zimmermann**: every
nonzero base boundary of weight `≤ 11` is a hexagon or a D-pair. -/
theorem lightStabilizerClassification_bz : LightStabilizerClassification := by
  intro f hne hwt
  have heven : (Finset.univ.filter fun j => bbBoundary2Fn baseA baseB f j ≠ 0).card % 2 = 0 :=
    cycle_weight_even _ (bb72Complex.boundaries_le_cycles ⟨f, rfl⟩)
  have hmem := grossSeamBZ.boundary_census (m := 11) (by decide)
    (L := 0 :: lightMasks) okGross_untagged f
    (by change bb72Complex.chainWeight (bbBoundary2Fn baseA baseB f) < 11
        rw [bb72Complex_chainWeight_eq]; omega)
  rcases List.mem_cons.mp hmem with h0 | hL
  · exact absurd (maskOf_injective enc (h0.trans (maskOf_zero enc).symm)) hne
  · rw [lightMasks_eq] at hL
    obtain ⟨⟨m, g, d⟩, hx, hm⟩ := List.mem_map.mp hL
    obtain ⟨hdir, hmask⟩ := light_shapes (m, g, d) hx
    have hshape : bbBoundary2Fn baseA baseB f = bbBoundary2Fn baseA baseB (shapeChain g d) := by
      refine maskOf_injective enc ?_
      rw [maskOf_shape]
      exact hm.symm.trans hmask
    cases d with
    | none => exact Or.inl ⟨g, hshape⟩
    | some d => exact Or.inr ⟨g, d, of_decide_eq_true hdir, hshape⟩

/-- **The dangerous sector** (`DangerousFloorNZ 12`), from the light census. -/
theorem dangerousSector_bz : DangerousSectorGe12 :=
  dangerous_sector_of_classification lightStabilizerClassification_bz

end GrossBZ

end Quantum.Stabilizer.Homological.BB
