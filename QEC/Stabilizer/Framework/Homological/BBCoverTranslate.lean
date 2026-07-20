/-
# Translation transport for the free-ℤ₂ cover bundle

Every clause of the doubling dispatch with a *fixed pushforward value* —

  `∀ v, v ∈ cycles → v ∉ boundaries → push1 v = b → m ≤ chainWeight v`

— transports along the full base translation group: for any base
translation `c : H` and any lift `c' : G` with `proj c' = c`, the clause
for `b` yields the clause for `translate1 c b`.  Only the projection is
involved — never the section — so unlike the rung *hypotheses* (whose
seam data wraps under doubled-axis translations), the transported
*conclusion* is available at every translate.  This is what collapses a
per-(class × translate) dangerous-sector dispatch to one rung application
per translation class (A15, `Z5Z15F2A6`).

Contents: `translate1` composition/zero lemmas (generic), the four
transport lemmas (`push1_translate1`, cycle/boundary membership,
`chainWeight_translate1`), and the reduction wrapper
`weight_floor_translate1_reduce`.
-/

import QEC.Stabilizer.Framework.Homological.BBCover

namespace Quantum
namespace Stabilizer
namespace Homological
namespace BB

open scoped BigOperators

-- Defeq checks through `D.coverComplex`'s structure projections unfold deep
-- `Prod`/`ZMod` instance chains, exactly as in `BBCover.lean` (the
-- `set_option` there is file-scoped and does not export).
set_option maxRecDepth 4096

/-! ## Generic `translate1` algebra -/

section Translate1Algebra

variable {G : Type} [AddCommGroup G]

lemma translate1_translate1 (a b : G) (v : G × Fin 2 → ZMod 2) :
    translate1 a (translate1 b v) = translate1 (a + b) v := by
  funext p
  change v (p.1 + a + b, p.2) = v (p.1 + (a + b), p.2)
  rw [add_assoc]

lemma translate1_zero (v : G × Fin 2 → ZMod 2) :
    translate1 (0 : G) v = v := by
  funext p
  change v (p.1 + 0, p.2) = v p
  rw [add_zero]

end Translate1Algebra

namespace XDoubleCoverData

variable {G H : Type}
  [Fintype G] [AddCommGroup G] [DecidableEq G]
  [Fintype H] [AddCommGroup H] [DecidableEq H]
  (D : XDoubleCoverData G H)

/-! ## The four transports -/

/-- The pushforward intertwines proj-compatible translations. -/
lemma push1_translate1 {c' : G} {c : H} (hproj : D.proj c' = c)
    (v : G × Fin 2 → ZMod 2) :
    D.push1 (translate1 c' v) = translate1 c (D.push1 v) := by
  funext p
  obtain ⟨h, j⟩ := p
  change fiberSumFn (Prod.map ⇑D.proj id) (translate1 c' v) (h, j)
    = fiberSumFn (Prod.map ⇑D.proj id) v (h + c, j)
  simp only [fiberSumFn_apply]
  refine Fintype.sum_equiv
    ((Equiv.addRight c').prodCongr (Equiv.refl (Fin 2))) _ _ ?_
  intro q
  obtain ⟨g, i⟩ := q
  simp only [Equiv.prodCongr_apply, Equiv.coe_addRight, Equiv.refl_apply,
    Prod.map_apply, id_eq, translate1_apply]
  have hcond : (D.proj g, i) = (h, j) ↔ (D.proj (g + c'), i) = (h + c, j) := by
    rw [map_add, hproj, Prod.mk.injEq, Prod.mk.injEq, add_left_inj]
  rw [if_congr hcond rfl rfl]

/-- Translates of cycles are cycles. -/
lemma translate1_mem_cycles (c' : G) {v : G × Fin 2 → ZMod 2}
    (hv : v ∈ D.coverComplex.cycles) :
    translate1 c' v ∈ D.coverComplex.cycles := by
  have hv' : bbBoundary1Fn D.Ac D.Bc v = 0 := hv
  have hgoal : bbBoundary1Fn D.Ac D.Bc (translate1 c' v) = 0 := by
    rw [bbBoundary1Fn_translate1, hv']
    funext g
    change (0 : G → ZMod 2) (g + c') = 0
    rfl
  exact hgoal

/-- Translates of boundaries are boundaries. -/
lemma translate1_mem_boundaries (c' : G) {v : G × Fin 2 → ZMod 2}
    (hv : v ∈ D.coverComplex.boundaries) :
    translate1 c' v ∈ D.coverComplex.boundaries := by
  -- destructure with the witness born over the concrete group type (the
  -- submodule's own carrier is only defeq to it; cf. `Z3Z6/Dangerous.lean`)
  obtain ⟨f, hf⟩ : ∃ f : G → ZMod 2, bbBoundary2Fn D.Ac D.Bc f = v := by
    obtain ⟨fraw, hfraw⟩ := hv
    exact ⟨fraw, hfraw⟩
  -- pin the witness type: without the `show`, `translate`'s implicit group
  -- is inferred syntactically from the submodule carrier `C2` and instance
  -- synthesis fails before the defeq unfolding is attempted
  refine ⟨show G → ZMod 2 from translate c' f, ?_⟩
  change bbBoundary2Fn D.Ac D.Bc (translate c' f) = translate1 c' v
  rw [bbBoundary2Fn_translate, hf]

/-- Translation preserves chain weight. -/
lemma chainWeight_translate1 (c' : G) (v : G × Fin 2 → ZMod 2) :
    D.coverComplex.chainWeight (translate1 c' v)
      = D.coverComplex.chainWeight v := by
  rw [D.coverComplex_chainWeight_eq, D.coverComplex_chainWeight_eq]
  refine Finset.card_bij' (fun p _ => (p.1 + c', p.2))
    (fun q _ => (q.1 - c', q.2)) ?_ ?_ ?_ ?_
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      translate1_apply] at hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hp
  · intro q hq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      translate1_apply, sub_add_cancel]
    exact hq
  · intro p _
    exact Prod.ext (add_sub_cancel_right p.1 c') rfl
  · intro q _
    exact Prod.ext (sub_add_cancel q.1 c') rfl

/-! ## The reduction wrapper -/

/-- **Translate-reduce for weight floors over a fixed pushforward**: the
dangerous-floor clause proved at one representative `b` holds at every
base translate of `b`.  `c'` is any lift of the base translation `c`
through the covering projection; for a concrete bundle such a lift exists
for every `c` (pick any section value), so this applies to the whole
translation orbit. -/
theorem weight_floor_translate1_reduce {m : ℕ} {c' : G} {c : H}
    (hproj : D.proj c' = c) {b : H × Fin 2 → ZMod 2}
    (hfloor : ∀ v : G × Fin 2 → ZMod 2,
      v ∈ D.coverComplex.cycles → v ∉ D.coverComplex.boundaries →
      D.push1 v = b → m ≤ D.coverComplex.chainWeight v) :
    ∀ v : G × Fin 2 → ZMod 2,
      v ∈ D.coverComplex.cycles → v ∉ D.coverComplex.boundaries →
      D.push1 v = translate1 c b → m ≤ D.coverComplex.chainWeight v := by
  intro v hv hnb hpush
  have hproj_neg : D.proj (-c') = -c := by
    rw [map_neg, hproj]
  have hpush' : D.push1 (translate1 (-c') v) = b := by
    rw [D.push1_translate1 hproj_neg, hpush, translate1_translate1,
      neg_add_cancel, translate1_zero]
  have hcyc' : translate1 (-c') v ∈ D.coverComplex.cycles :=
    D.translate1_mem_cycles (-c') hv
  have hnb' : translate1 (-c') v ∉ D.coverComplex.boundaries := by
    intro hbd
    apply hnb
    have hback : translate1 c' (translate1 (-c') v) = v := by
      rw [translate1_translate1, add_neg_cancel, translate1_zero]
    rw [← hback]
    exact D.translate1_mem_boundaries c' hbd
  have hfl := hfloor (translate1 (-c') v) hcyc' hnb' hpush'
  rwa [D.chainWeight_translate1] at hfl

end XDoubleCoverData

end BB
end Homological
end Stabilizer
end Quantum
