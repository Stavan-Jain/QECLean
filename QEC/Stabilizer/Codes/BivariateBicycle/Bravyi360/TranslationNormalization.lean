import QEC.Stabilizer.Framework.Homological.Certificate.MaskFiber
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.Defs

noncomputable section

namespace Quantum.Stabilizer.Homological.BB

variable {G H : Type} [Fintype G] [AddCommGroup G] [DecidableEq G]
  [Fintype H] [AddCommGroup H] [DecidableEq H]

/-- Translation moves a point mass by the opposite group displacement. -/
theorem translate1_single (g : G) (q : G × Fin 2) :
    translate1 g (Pi.single q 1) = Pi.single (q.1-g,q.2) 1 := by
  ext p
  simp only [translate1, Pi.single_apply]
  have he : (p.1+g,p.2) = q ↔ p = (q.1-g,q.2) := by
    simp only [Prod.ext_iff, eq_sub_iff_add_eq]
  simp only [he]

/--
Projection of a translated chain is the translation of its projected chain.
-/
theorem XDoubleCoverData.push1_translate1 (D : XDoubleCoverData G H) (g : G)
    (v : G × Fin 2 → ZMod 2) :
    D.push1 (translate1 g v) = translate1 (D.proj g) (D.push1 v) := by
  let S : (G × Fin 2 → ZMod 2) →ₗ[ZMod 2] (G × Fin 2 → ZMod 2) :=
    LinearMap.funLeft (ZMod 2) (ZMod 2) (fun q => (q.1+g,q.2))
  let T : (H × Fin 2 → ZMod 2) →ₗ[ZMod 2] (H × Fin 2 → ZMod 2) :=
    LinearMap.funLeft (ZMod 2) (ZMod 2) (fun q => (q.1+D.proj g,q.2))
  have he : D.push1.comp S = T.comp D.push1 := by
    apply linearMap_eq_of_single
    intro q
    change D.push1 (translate1 g (Pi.single q 1)) =
      translate1 (D.proj g) (D.push1 (Pi.single q 1))
    rw [translate1_single, D.push1_single, D.push1_single, translate1_single]
    simp only [map_sub]
  exact LinearMap.congr_fun he v

/-- Pullback intertwines translations through the covering projection. -/
theorem XDoubleCoverData.pull1_translate1 (D : XDoubleCoverData G H) (g : G)
    (u : H × Fin 2 → ZMod 2) :
    translate1 g (D.pull1 u) = D.pull1 (translate1 (D.proj g) u) := by
  ext q
  simp [translate1, D.pull1_apply, map_add]

/-- Translation preserves primal cycles in every BB code. -/
theorem translate1_mem_cycles {A B : G → ZMod 2} (g : G) {v : G × Fin 2 → ZMod 2}
    (hv : v ∈ (bbChainComplex A B).cycles) :
    translate1 g v ∈ (bbChainComplex A B).cycles := by
  change bbBoundary1Fn A B v = 0 at hv
  change bbBoundary1Fn A B (translate1 g v) = 0
  rw [bbBoundary1Fn_translate1, hv]
  rfl

/-- Translation preserves primal boundaries in every BB code. -/
theorem translate1_mem_boundaries {A B : G → ZMod 2} (g : G) {v : G × Fin 2 → ZMod 2}
    (hv : v ∈ (bbChainComplex A B).boundaries) :
    translate1 g v ∈ (bbChainComplex A B).boundaries := by
  obtain ⟨f, rfl⟩ := (show ∃ f : G → ZMod 2, bbBoundary2Fn A B f = v from hv)
  let f' : G → ZMod 2 := translate g f
  refine ⟨f', ?_⟩
  exact bbBoundary2Fn_translate A B g f

/-- Applying opposite translations returns the original chain. -/
theorem translate1_neg_cancel (g : G) (v : G × Fin 2 → ZMod 2) :
    translate1 (-g) (translate1 g v) = v := by
  ext p
  simp [translate1, add_assoc]

/-- Translation preserves the property of being a non-boundary. -/
theorem translate1_not_boundary {A B : G → ZMod 2} (g : G) {v : G × Fin 2 → ZMod 2}
    (hv : v ∉ (bbChainComplex A B).boundaries) :
    translate1 g v ∉ (bbChainComplex A B).boundaries := by
  intro h
  have h' := translate1_mem_boundaries (-g) h
  rw [translate1_neg_cancel] at h'
  exact hv h'

/-- Translation preserves Hamming weight in every BB complex. -/
theorem chainWeight_translate1 (A B : G → ZMod 2) (g : G) (v : G × Fin 2 → ZMod 2) :
    (bbChainComplex A B).chainWeight (translate1 g v) =
      (bbChainComplex A B).chainWeight v := SmallCycle.card_support_translate1 g v

namespace Bravyi360

/-- Lift a bottom translation through the two chosen sections. -/
noncomputable def liftTranslation (h : BaseGroup) : Group := topSection (baseSection h)

/-- The lifted translation projects to the desired bottom displacement. -/
theorem liftTranslation_projects (h : BaseGroup) :
    baseProjection (topProjection (liftTranslation h)) = h := by
  rw [liftTranslation, topProjection_section, baseProjection_section]

/--
The two-level pushforward intertwines a physical and its bottom translation.
-/
theorem push_push_translate1 (h : BaseGroup) (v : Group × Fin 2 → ZMod 2) :
    baseCover.push1 (topCover.push1 (translate1 (liftTranslation h) v)) =
      translate1 h (baseCover.push1 (topCover.push1 v)) := by
  rw [topCover.push1_translate1, baseCover.push1_translate1]
  change translate1 (baseProjection (topProjection (liftTranslation h))) _ = _
  rw [liftTranslation_projects]

/--
A physical translation realizes the chosen bottom translation of a diagonal
middle chain.
-/
theorem top_push_diagonal_translate (h : BaseGroup)
    (v : Group × Fin 2 → ZMod 2) (gamma : BaseGroup × Fin 2 → ZMod 2)
    (hv : topCover.push1 v = baseCover.pull1 gamma) :
    topCover.push1 (translate1 (liftTranslation h) v) =
      baseCover.pull1 (translate1 h gamma) := by
  rw [topCover.push1_translate1, hv, baseCover.pull1_translate1]
  change baseCover.pull1 (translate1 (baseProjection (topProjection (liftTranslation h))) gamma) = _
  rw [liftTranslation_projects]

/--
A horizontal half-period on physical qubits projects to the middle deck shift.
-/
theorem top_push_horizontal_translation (v : Group × Fin 2 → ZMod 2) :
    topCover.push1 (translate1 (15,0) v) =
      baseCover.deckShift1 (topCover.push1 v) := by
  rw [topCover.push1_translate1]
  rfl

/--
The same horizontal half-period exchanges either middle deck partner back.
-/
theorem top_push_horizontal_translation_deck (v : Group × Fin 2 → ZMod 2)
    (b : MiddleGroup × Fin 2 → ZMod 2)
    (h : topCover.push1 v = baseCover.deckShift1 b) :
    topCover.push1 (translate1 (15,0) v) = b := by
  rw [top_push_horizontal_translation, h]
  ext q
  simp only [XDoubleCoverData.deckShift1_apply, add_assoc,
    baseCover.deckS_add_deckS, add_zero]

/--
Any bottom translation of a physical cycle is realized with the same weight
and homology status.
-/
theorem translated_cycle_normalization (h : BaseGroup) (v : Group × Fin 2 → ZMod 2)
    (hc : v ∈ complex.cycles) (hn : v ∉ complex.boundaries) :
    ∃ w, w ∈ complex.cycles ∧ w ∉ complex.boundaries ∧
      complex.chainWeight w = complex.chainWeight v ∧
      baseCover.push1 (topCover.push1 w) =
        translate1 h (baseCover.push1 (topCover.push1 v)) := by
  refine ⟨translate1 (liftTranslation h) v,
    translate1_mem_cycles _ hc, translate1_not_boundary _ hn,
    chainWeight_translate1 A B _ _, push_push_translate1 h v⟩

end Bravyi360
end Quantum.Stabilizer.Homological.BB

#print axioms Quantum.Stabilizer.Homological.BB.Bravyi360.translated_cycle_normalization
#print axioms Quantum.Stabilizer.Homological.BB.Bravyi360.top_push_horizontal_translation_deck
