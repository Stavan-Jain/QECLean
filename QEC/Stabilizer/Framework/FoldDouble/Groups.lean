import QEC.Stabilizer.Framework.FoldDouble.OperatorImage

/-!
# The four groups of a paired stabilizer code

Fix a stabilizer group `S` on `n` qubits and a pairing
`e : Fin n ≃ Fin m × Fin 2` of its qubits. Writing `G` for the phase-free image
of `S` and `C(G)` for that of its centralizer, the fold and the double cut out
four subgroups of the phase-free Pauli group on the `m` pairs:

* `foldImage e S` — `J := fold G`, the **stabilizer folds**;
* `logicalFoldImage e S` — `P := fold C(G)`, the **logical folds**;
* `seamGroup e S` — `T := double⁻¹ G`, the **seam operators**;
* `doublingGroup e S` — `K := double⁻¹ C(G)`, the operators whose double is a
  logical operator.

A **doubling logical** (`IsDoublingLogical`) is an element of `K ∖ T`, a
**seam logical** (`IsSeamLogical`) an element of `T ∖ J`, and a **logical
fold** (`IsLogicalFold`) an element of `P ∖ J`. The double of a doubling
logical is a nontrivial logical operator of `S` of twice the weight
(`isNontrivialLogicalOperator_ofOperator_double`, `weight_ofOperator_double`),
and `K` is always the symplectic centralizer of `J`
(`mem_doublingGroup_iff_forall_foldImage`).

When the pairing is **symmetric** for `S` (`IsSymmetric`) — the sheet swap
preserves the phase-free image of `S` — `J` is isotropic
(`symplecticInner_eq_zero_of_mem_foldImage`), `J ≤ T`
(`foldImage_le_seamGroup`) and `P ≤ K` (`logicalFoldImage_le_doublingGroup`),
so by `exists_stabilizerGroup_operatorImage_eq` there is a stabilizer group
`F : StabilizerGroup m` whose operator image is `J`: the **folded code**
(`foldedStabilizerGroup`). Its centralizer is read off `K`, and its nontrivial
logical operators are the elements of `K ∖ J`
(`isNontrivialLogicalOperator_iff_of_operatorImage_eq`), so the distance of the
folded code is the least weight on `K ∖ J`. Condition (R), `g * g^σ ∈ G` for
every logical `g`, is equivalent to `P ≤ T`
(`logicalFoldImage_le_seamGroup_iff`).

The floors `d_K` (`doublingFloor`, the least weight of a doubling logical) and
`d_P` (`logicalFoldFloor`, the least weight of a logical fold) are defined in
`ℕ∞`, so that they are `⊤` exactly when the corresponding set is empty.
-/

namespace Quantum
namespace Stabilizer
namespace FoldDouble

open NQubitPauliOperator NQubitPauliGroupElement StabilizerGroup

variable {n m : ℕ} (e : Fin n ≃ Fin m × Fin 2) (S : StabilizerGroup n)

/-! ## The four groups -/

/-- `J`: the stabilizer folds, the fold of the phase-free image of `S`. -/
noncomputable def foldImage : Subgroup (NQubitPauliOperator m) :=
  (operatorImage S.toSubgroup).map (foldHom e)

/-- `P`: the logical folds, the fold of the phase-free image of the centralizer
of `S`. -/
noncomputable def logicalFoldImage : Subgroup (NQubitPauliOperator m) :=
  (operatorImage (centralizer S)).map (foldHom e)

/-- `T`: the seam operators, those `u` whose double is (the operator part of) a
stabilizer. -/
noncomputable def seamGroup : Subgroup (NQubitPauliOperator m) :=
  (operatorImage S.toSubgroup).comap (doubleHom e)

/-- `K`: those `u` whose double is (the operator part of) a logical operator.
-/
noncomputable def doublingGroup : Subgroup (NQubitPauliOperator m) :=
  (operatorImage (centralizer S)).comap (doubleHom e)

lemma mem_foldImage {b : NQubitPauliOperator m} :
    b ∈ foldImage e S ↔ ∃ s ∈ S.toSubgroup, fold e s.operators = b := by
  simp only [foldImage, Subgroup.mem_map, mem_operatorImage, exists_exists_and_eq_and,
    foldHom_apply]

lemma mem_logicalFoldImage {b : NQubitPauliOperator m} :
    b ∈ logicalFoldImage e S ↔ ∃ g ∈ centralizer S, fold e g.operators = b := by
  simp only [logicalFoldImage, Subgroup.mem_map, mem_operatorImage, exists_exists_and_eq_and,
    foldHom_apply]

lemma mem_seamGroup {u : NQubitPauliOperator m} :
    u ∈ seamGroup e S ↔ double e u ∈ operatorImage S.toSubgroup :=
  Iff.rfl

lemma mem_doublingGroup {u : NQubitPauliOperator m} :
    u ∈ doublingGroup e S ↔ double e u ∈ operatorImage (centralizer S) :=
  Iff.rfl

lemma fold_operators_mem_foldImage {s : NQubitPauliGroupElement n} (hs : s ∈ S.toSubgroup) :
    fold e s.operators ∈ foldImage e S :=
  (mem_foldImage e S).mpr ⟨s, hs, rfl⟩

/-- The fold of a logical operator is a logical fold. -/
lemma fold_operators_mem_logicalFoldImage {g : NQubitPauliGroupElement n}
    (hg : g ∈ centralizer S) : fold e g.operators ∈ logicalFoldImage e S :=
  (mem_logicalFoldImage e S).mpr ⟨g, hg, rfl⟩

/-- `K` consists of the operators orthogonal to the fold of every stabilizer,
by the first commutation rule. No symmetry is needed. -/
theorem mem_doublingGroup_iff_forall (u : NQubitPauliOperator m) :
    u ∈ doublingGroup e S ↔ ∀ s ∈ S.toSubgroup, symplecticInner (fold e s.operators) u = 0 := by
  rw [mem_doublingGroup, mem_operatorImage_centralizer_iff]
  exact forall₂_congr fun s _ => by rw [symplecticInner_double_right]

/-- `K` is the symplectic centralizer of `J`. -/
theorem mem_doublingGroup_iff_forall_foldImage (u : NQubitPauliOperator m) :
    u ∈ doublingGroup e S ↔ ∀ b ∈ foldImage e S, symplecticInner b u = 0 := by
  simp only [mem_doublingGroup_iff_forall, mem_foldImage, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂]

/-! ## The inclusions, and doubling logicals -/

/-- `J ≤ P`. -/
lemma foldImage_le_logicalFoldImage : foldImage e S ≤ logicalFoldImage e S :=
  Subgroup.map_mono (operatorImage_le_operatorImage_centralizer S)

/-- `T ≤ K`. -/
lemma seamGroup_le_doublingGroup : seamGroup e S ≤ doublingGroup e S :=
  Subgroup.comap_mono (operatorImage_le_operatorImage_centralizer S)

/-- A **doubling logical**: an element of `K ∖ T`. -/
def IsDoublingLogical (u : NQubitPauliOperator m) : Prop :=
  u ∈ doublingGroup e S ∧ u ∉ seamGroup e S

/-- A **seam logical**: an element of `T ∖ J`. -/
def IsSeamLogical (b : NQubitPauliOperator m) : Prop :=
  b ∈ seamGroup e S ∧ b ∉ foldImage e S

/-- A **logical fold**: an element of `P ∖ J`. -/
def IsLogicalFold (b : NQubitPauliOperator m) : Prop :=
  b ∈ logicalFoldImage e S ∧ b ∉ foldImage e S

/-- The double of a doubling logical is a nontrivial logical operator of `S`.
-/
theorem isNontrivialLogicalOperator_ofOperator_double {u : NQubitPauliOperator m}
    (hu : IsDoublingLogical e S u) :
    IsNontrivialLogicalOperator (ofOperator (double e u)) S :=
  (isNontrivialLogicalOperator_ofOperator_iff S _).mpr hu

/-- The double of `u` has twice the weight of `u`. -/
theorem weight_ofOperator_double (u : NQubitPauliOperator m) :
    NQubitPauliGroupElement.weight (ofOperator (double e u)) = 2 * weight u := by
  rw [weight_ofOperator, weight_double]

/-- Every doubling logical `u` yields a nontrivial logical operator of `S` of
weight `2 wt u`: the distance of `S` is at most `2 d_K`. -/
theorem exists_isNontrivialLogicalOperator_weight_eq_two_mul {u : NQubitPauliOperator m}
    (hu : IsDoublingLogical e S u) :
    ∃ g, IsNontrivialLogicalOperator g S ∧ NQubitPauliGroupElement.weight g = 2 * weight u :=
  ⟨ofOperator (double e u), isNontrivialLogicalOperator_ofOperator_double e S hu,
    weight_ofOperator_double e u⟩

/-- A nontrivial logical operator that folds to the identity is the double of
its sheet-`0` part, which is a doubling logical. -/
theorem isDoublingLogical_sheet_of_fold_eq_one {v : NQubitPauliGroupElement n}
    (hv : IsNontrivialLogicalOperator v S) (h : fold e v.operators = 1) :
    IsDoublingLogical e S (sheet e 0 v.operators) := by
  rw [isNontrivialLogicalOperator_iff_operators, mem_centralizer_iff_operators_mem,
    (fold_eq_one_iff e _).mp h] at hv
  exact hv

/-- Products of a doubling logical with a seam operator are doubling logicals:
`K ∖ T` is a union of cosets of `T`. -/
theorem IsDoublingLogical.mul_seam {u t : NQubitPauliOperator m}
    (hu : IsDoublingLogical e S u) (ht : t ∈ seamGroup e S) :
    IsDoublingLogical e S (u * t) :=
  ⟨(doublingGroup e S).mul_mem hu.1 (seamGroup_le_doublingGroup e S ht),
    fun h => hu.2 ((Subgroup.mul_mem_cancel_right _ ht).mp h)⟩

/-! ## Symmetric pairings -/

/-- The pairing is **symmetric** for `S` if the sheet swap preserves the
phase-free image of `S`: `s^σ ∈ G` for every stabilizer `s`. -/
def IsSymmetric : Prop :=
  ∀ s ∈ S.toSubgroup, sheetSwap e s.operators ∈ operatorImage S.toSubgroup

lemma IsSymmetric.sheetSwap_mem (h : IsSymmetric e S) {u : NQubitPauliOperator n}
    (hu : u ∈ operatorImage S.toSubgroup) : sheetSwap e u ∈ operatorImage S.toSubgroup := by
  obtain ⟨s, hs, rfl⟩ := hu
  exact h s hs

/-- For a symmetric pairing, `J` is isotropic (its elements pairwise commute),
by the second commutation rule. -/
theorem symplecticInner_eq_zero_of_mem_foldImage (h : IsSymmetric e S)
    {b b' : NQubitPauliOperator m} (hb : b ∈ foldImage e S) (hb' : b' ∈ foldImage e S) :
    symplecticInner b b' = 0 := by
  obtain ⟨s, hs, rfl⟩ := (mem_foldImage e S).mp hb
  obtain ⟨t, ht, rfl⟩ := (mem_foldImage e S).mp hb'
  have hs' := operators_mem_operatorImage hs
  rw [symplecticInner_fold_fold,
    symplecticInner_eq_zero_of_mem_operatorImage S hs' (operators_mem_operatorImage ht),
    symplecticInner_eq_zero_of_mem_operatorImage S hs' (h t ht), add_zero]

/-- For a symmetric pairing, `J ≤ T`: the double of a stabilizer fold `fold s`
is `s * s^σ`, a stabilizer. -/
theorem foldImage_le_seamGroup (h : IsSymmetric e S) : foldImage e S ≤ seamGroup e S := by
  intro b hb
  obtain ⟨s, hs, rfl⟩ := (mem_foldImage e S).mp hb
  rw [mem_seamGroup, double_fold]
  exact (operatorImage S.toSubgroup).mul_mem (operators_mem_operatorImage hs) (h s hs)

/-- For a symmetric pairing, `P ≤ K`: the fold of a logical operator commutes
with every stabilizer fold. -/
theorem logicalFoldImage_le_doublingGroup (h : IsSymmetric e S) :
    logicalFoldImage e S ≤ doublingGroup e S := by
  intro b hb
  obtain ⟨g, hg, rfl⟩ := (mem_logicalFoldImage e S).mp hb
  rw [mem_doublingGroup_iff_forall]
  intro s hs
  rw [mem_centralizer_iff_symplecticInner] at hg
  obtain ⟨t, ht, hts⟩ := mem_operatorImage.mp (h s hs)
  rw [symplecticInner_fold_fold, hg s hs, ← symplecticInner_sheetSwap_left, ← hts, hg t ht,
    add_zero]

/-- Condition (R), `g * g^σ ∈ G` for every logical operator `g`, is equivalent
to `P ≤ T`. -/
theorem logicalFoldImage_le_seamGroup_iff :
    (∀ g ∈ centralizer S, g.operators * sheetSwap e g.operators ∈ operatorImage S.toSubgroup) ↔
      logicalFoldImage e S ≤ seamGroup e S := by
  refine ⟨fun hR b hb => ?_, fun hPT g hg => ?_⟩
  · obtain ⟨g, hg, rfl⟩ := (mem_logicalFoldImage e S).mp hb
    rw [mem_seamGroup, double_fold]
    exact hR g hg
  · rw [← double_fold]
    exact hPT (fold_operators_mem_logicalFoldImage e S hg)

/-- For a symmetric pairing, every doubling logical is a nontrivial logical of
the folded code: it lies in `K ∖ J`. -/
theorem IsDoublingLogical.not_mem_foldImage (h : IsSymmetric e S) {u : NQubitPauliOperator m}
    (hu : IsDoublingLogical e S u) : u ∉ foldImage e S :=
  fun hb => hu.2 (foldImage_le_seamGroup e S h hb)

/-- For a symmetric pairing, `d_K = d₀` as soon as some doubling logical has
weight `d₀`, the least weight on `K ∖ J`. -/
theorem isLeast_doubling_of_witness (h : IsSymmetric e S) {d₀ : ℕ}
    (hd₀ : IsLeast {w | ∃ u, u ∈ doublingGroup e S ∧ u ∉ foldImage e S ∧ weight u = w} d₀)
    (hW : ∃ u, IsDoublingLogical e S u ∧ weight u = d₀) :
    IsLeast {w | ∃ u, IsDoublingLogical e S u ∧ weight u = w} d₀ := by
  refine ⟨hW, ?_⟩
  rintro w ⟨u, hu, rfl⟩
  exact hd₀.2 ⟨u, hu.1, hu.not_mem_foldImage e S h, rfl⟩

/-- For a symmetric pairing, every doubling logical has weight at least any
lower bound `d₀` on the weights on `K ∖ J`: `d₀ ≤ d_K`. -/
theorem le_weight_of_isDoublingLogical (h : IsSymmetric e S) {d₀ : ℕ}
    (hd₀ : ∀ u, u ∈ doublingGroup e S → u ∉ foldImage e S → d₀ ≤ weight u)
    {u : NQubitPauliOperator m} (hu : IsDoublingLogical e S u) : d₀ ≤ weight u :=
  hd₀ u hu.1 (hu.not_mem_foldImage e S h)

/-! ## The folded code -/

/-- For a symmetric pairing, the stabilizer folds are the operator image of a
stabilizer group on the `m` pairs. -/
theorem exists_foldedStabilizerGroup (h : IsSymmetric e S) :
    ∃ F : StabilizerGroup m, operatorImage F.toSubgroup = foldImage e S :=
  exists_stabilizerGroup_operatorImage_eq _
    fun _ hb _ hb' => symplecticInner_eq_zero_of_mem_foldImage e S h hb hb'

/-- **The folded code**: a stabilizer group on the `m` pairs whose operator
image is `J`, with signs chosen by `exists_stabilizerGroup_operatorImage_eq`.
Any two choices have the same operator image, hence the same logical operators
and the same distance. -/
noncomputable def foldedStabilizerGroup (h : IsSymmetric e S) : StabilizerGroup m :=
  Classical.choose (exists_foldedStabilizerGroup e S h)

theorem operatorImage_foldedStabilizerGroup (h : IsSymmetric e S) :
    operatorImage (foldedStabilizerGroup e S h).toSubgroup = foldImage e S :=
  Classical.choose_spec (exists_foldedStabilizerGroup e S h)

section Folded

variable {F : StabilizerGroup m}

/-- The centralizer of a folded code is `K`, read on operator parts. -/
theorem mem_centralizer_iff_of_operatorImage_eq
    (hF : operatorImage F.toSubgroup = foldImage e S) (g : NQubitPauliGroupElement m) :
    g ∈ centralizer F ↔ g.operators ∈ doublingGroup e S := by
  simp only [mem_centralizer_iff_symplecticInner, mem_doublingGroup_iff_forall_foldImage, ← hF,
    mem_operatorImage, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]

/-- The nontrivial logical operators of a folded code are the elements of
`K ∖ J`, read on operator parts. -/
theorem isNontrivialLogicalOperator_iff_of_operatorImage_eq
    (hF : operatorImage F.toSubgroup = foldImage e S) (g : NQubitPauliGroupElement m) :
    IsNontrivialLogicalOperator g F ↔
      g.operators ∈ doublingGroup e S ∧ g.operators ∉ foldImage e S := by
  rw [isNontrivialLogicalOperator_iff_operators, mem_centralizer_iff_of_operatorImage_eq e S hF,
    hF]

/-- The weights of the nontrivial logical operators of a folded code are the
weights of the elements of `K ∖ J`. -/
theorem logicalWeights_eq_of_operatorImage_eq
    (hF : operatorImage F.toSubgroup = foldImage e S) :
    {w | ∃ g, IsNontrivialLogicalOperator g F ∧ NQubitPauliGroupElement.weight g = w} =
      {w | ∃ u, u ∈ doublingGroup e S ∧ u ∉ foldImage e S ∧ weight u = w} := by
  ext w
  constructor
  · rintro ⟨g, hg, rfl⟩
    rw [isNontrivialLogicalOperator_iff_of_operatorImage_eq e S hF] at hg
    exact ⟨g.operators, hg.1, hg.2, rfl⟩
  · rintro ⟨u, hK, hJ, rfl⟩
    exact ⟨ofOperator u,
      (isNontrivialLogicalOperator_iff_of_operatorImage_eq e S hF _).mpr ⟨hK, hJ⟩, rfl⟩

/-- The distance of a folded code is the least weight of an element of
`K ∖ J`. -/
theorem isLeast_logicalWeight_iff_of_operatorImage_eq
    (hF : operatorImage F.toSubgroup = foldImage e S) (d : ℕ) :
    IsLeast {w | ∃ g, IsNontrivialLogicalOperator g F ∧ NQubitPauliGroupElement.weight g = w} d ↔
      IsLeast {w | ∃ u, u ∈ doublingGroup e S ∧ u ∉ foldImage e S ∧ weight u = w} d := by
  rw [logicalWeights_eq_of_operatorImage_eq e S hF]

end Folded

/-! ## The floors `d_K` and `d_P` -/

/-- The **doubling floor** `d_K`: the least weight of a doubling logical, `⊤`
if there is none (`K = T`). -/
noncomputable def doublingFloor : ℕ∞ :=
  sInf ((fun u => (NQubitPauliOperator.weight u : ℕ∞)) '' {u | IsDoublingLogical e S u})

/-- The **logical-fold floor** `d_P`: the least weight of a logical fold, `⊤`
if there is none (`P = J`). -/
noncomputable def logicalFoldFloor : ℕ∞ :=
  sInf ((fun b => (NQubitPauliOperator.weight b : ℕ∞)) '' {b | IsLogicalFold e S b})

lemma doublingFloor_le {u : NQubitPauliOperator m} (hu : IsDoublingLogical e S u) :
    doublingFloor e S ≤ weight u :=
  sInf_le ⟨u, hu, rfl⟩

lemma le_doublingFloor_iff {k : ℕ∞} :
    k ≤ doublingFloor e S ↔ ∀ u, IsDoublingLogical e S u → k ≤ weight u := by
  rw [doublingFloor, le_sInf_iff, Set.forall_mem_image]
  exact Iff.rfl

lemma logicalFoldFloor_le {b : NQubitPauliOperator m} (hb : IsLogicalFold e S b) :
    logicalFoldFloor e S ≤ weight b :=
  sInf_le ⟨b, hb, rfl⟩

lemma le_logicalFoldFloor_iff {k : ℕ∞} :
    k ≤ logicalFoldFloor e S ↔ ∀ b, IsLogicalFold e S b → k ≤ weight b := by
  rw [logicalFoldFloor, le_sInf_iff, Set.forall_mem_image]
  exact Iff.rfl

/-- `d_P = ⊤` exactly when there is no logical fold (`P = J`). -/
lemma logicalFoldFloor_eq_top_iff : logicalFoldFloor e S = ⊤ ↔ ∀ b, ¬ IsLogicalFold e S b := by
  rw [logicalFoldFloor, sInf_eq_top]
  refine ⟨fun h b hb => ENat.coe_ne_top _ (h _ ⟨b, hb, rfl⟩), ?_⟩
  rintro h _ ⟨b, hb, rfl⟩
  exact absurd hb (h b)

/-- The doubling floor is a natural number `d_K` iff `d_K` is the least weight
of a doubling logical. -/
theorem doublingFloor_eq_coe_iff (dK : ℕ) :
    doublingFloor e S = dK ↔ IsLeast {w | ∃ u, IsDoublingLogical e S u ∧ weight u = w} dK := by
  refine ⟨fun h => ?_, fun h => le_antisymm ?_ ?_⟩
  · have hne : ((fun u => (NQubitPauliOperator.weight u : ℕ∞)) ''
        {u | IsDoublingLogical e S u}).Nonempty := by
      by_contra hemp
      rw [Set.not_nonempty_iff_eq_empty] at hemp
      rw [doublingFloor, hemp, sInf_empty] at h
      exact ENat.top_ne_coe dK h
    obtain ⟨u, hu, hw⟩ := csInf_mem hne
    refine ⟨⟨u, hu, Nat.cast_injective (hw.trans h)⟩, ?_⟩
    rintro w ⟨v, hv, rfl⟩
    exact ENat.coe_le_coe.mp (h ▸ doublingFloor_le e S hv)
  · obtain ⟨u, hu, rfl⟩ := h.1
    exact doublingFloor_le e S hu
  · exact (le_doublingFloor_iff e S).mpr fun u hu => ENat.coe_le_coe.mpr (h.2 ⟨u, hu, rfl⟩)

end FoldDouble
end Stabilizer
end Quantum
