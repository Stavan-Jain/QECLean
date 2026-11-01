import QEC.Stabilizer.Framework.FoldDouble.OperatorImage

/-!
# The four groups of a paired stabilizer code

Fix a stabilizer group `S` on `n` qubits and a pairing
`e : Fin n ≃ Fin m × Fin 2` of its qubits. Writing `G` for the phase-free image
of `S` and `C(G)` for that
of its centralizer, the fold and the double cut out four subgroups of the
phase-free Pauli group on the `m` pairs:

* `foldImage e S` — `J := fold G`, the **stabilizer folds**;
* `logicalFoldImage e S` — `P := fold C(G)`, the **logical folds**;
* `seamGroup e S` — `T := double⁻¹ G`, the **seam operators**;
* `doublingGroup e S` — `K := double⁻¹ C(G)`, the operators whose double is a
  logical operator.

A **doubling logical** is an element of `K ∖ T`, a **seam logical** an element
of `T ∖ J`, and a **logical fold** an element of `P ∖ J`. The double of a
doubling logical is a nontrivial logical operator of `S` of twice the weight
(Lemma 3.2), and `K` is always the symplectic centralizer of `J`
(Proposition 3.4 (1)).

When the pairing is **symmetric** for `S` — the sheet swap preserves the
phase-free image of `S` — `J` is isotropic, `J ≤ T` and `P ≤ K`
(Proposition 3.4), so by Lemma 1.8 there is a genuine stabilizer group
`F : StabilizerGroup m` whose operator image is `J`: the **folded code**. Its
centralizer is read off `K`, and its nontrivial logical operators are the
elements of `K ∖ J` (Definition 3.5), so the distance of the folded code is the
least weight on `K ∖ J`. Condition (R), `g * g^σ ∈ G` for every logical `g`, is
equivalent to `P ≤ T` (Proposition 3.4 (4)).

The floors `d_K` (`doublingFloor`) and `d_P` (`logicalFoldFloor`) are defined
in `ℕ∞`, so that they are `⊤` exactly when the corresponding set is empty.
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
  simp only [foldImage, Subgroup.mem_map, foldHom_apply, mem_operatorImage]
  constructor
  · rintro ⟨_, ⟨s, hs, rfl⟩, rfl⟩
    exact ⟨s, hs, rfl⟩
  · rintro ⟨s, hs, rfl⟩
    exact ⟨s.operators, ⟨s, hs, rfl⟩, rfl⟩

lemma mem_logicalFoldImage {b : NQubitPauliOperator m} :
    b ∈ logicalFoldImage e S ↔ ∃ g ∈ centralizer S, fold e g.operators = b := by
  simp only [logicalFoldImage, Subgroup.mem_map, foldHom_apply, mem_operatorImage]
  constructor
  · rintro ⟨_, ⟨g, hg, rfl⟩, rfl⟩
    exact ⟨g, hg, rfl⟩
  · rintro ⟨g, hg, rfl⟩
    exact ⟨g.operators, ⟨g, hg, rfl⟩, rfl⟩

lemma mem_seamGroup {u : NQubitPauliOperator m} :
    u ∈ seamGroup e S ↔ double e u ∈ operatorImage S.toSubgroup :=
  Iff.rfl

lemma mem_doublingGroup {u : NQubitPauliOperator m} :
    u ∈ doublingGroup e S ↔ double e u ∈ operatorImage (centralizer S) :=
  Iff.rfl

lemma fold_operators_mem_foldImage {s : NQubitPauliGroupElement n} (hs : s ∈ S.toSubgroup) :
    fold e s.operators ∈ foldImage e S :=
  (mem_foldImage e S).mpr ⟨s, hs, rfl⟩

/-- Lemma 4.1: the fold of a logical operator is a logical fold. -/
lemma fold_operators_mem_logicalFoldImage {g : NQubitPauliGroupElement n}
    (hg : g ∈ centralizer S) : fold e g.operators ∈ logicalFoldImage e S :=
  (mem_logicalFoldImage e S).mpr ⟨g, hg, rfl⟩

/-- Proposition 3.4 (1), which needs no symmetry: `K` is the symplectic
centralizer of `J`, by the first commutation rule. -/
theorem mem_doublingGroup_iff_forall (u : NQubitPauliOperator m) :
    u ∈ doublingGroup e S ↔ ∀ s ∈ S.toSubgroup, symplecticInner (fold e s.operators) u = 0 := by
  rw [mem_doublingGroup, mem_operatorImage_centralizer_iff]
  exact forall₂_congr fun s _ => by rw [symplecticInner_double_right]

/-- `K` is the symplectic centralizer of `J`. -/
theorem mem_doublingGroup_iff_forall_foldImage (u : NQubitPauliOperator m) :
    u ∈ doublingGroup e S ↔ ∀ b ∈ foldImage e S, symplecticInner b u = 0 := by
  rw [mem_doublingGroup_iff_forall]
  constructor
  · intro h b hb
    obtain ⟨s, hs, rfl⟩ := (mem_foldImage e S).mp hb
    exact h s hs
  · intro h s hs
    exact h _ (fold_operators_mem_foldImage e S hs)

/-! ## Lemma 3.2: the inclusions, and doubling logicals -/

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

/-- Lemma 3.2: the double of a doubling logical is a nontrivial logical
operator of `S`. -/
theorem isNontrivialLogicalOperator_ofOperator_double {u : NQubitPauliOperator m}
    (hu : IsDoublingLogical e S u) :
    IsNontrivialLogicalOperator (ofOperator (double e u)) S := by
  rw [isNontrivialLogicalOperator_ofOperator_iff]
  exact ⟨(mem_doublingGroup e S).mp hu.1, fun h => hu.2 ((mem_seamGroup e S).mpr h)⟩

/-- Lemma 3.2: the double of `u` has twice the weight of `u`. -/
theorem weight_ofOperator_double (u : NQubitPauliOperator m) :
    NQubitPauliGroupElement.weight (ofOperator (double e u)) = 2 * weight u := by
  rw [weight_ofOperator, weight_double]

/-- Lemma 3.2: the distance of `S` is at most `2 d_K` — every doubling logical
`u` yields a nontrivial logical operator of weight `2 wt u`. -/
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
  have hv' := (fold_eq_one_iff e _).mp h
  rw [isNontrivialLogicalOperator_iff_operators, mem_centralizer_iff_operators_mem] at hv
  refine ⟨(mem_doublingGroup e S).mpr ?_, fun ht => hv.2 ?_⟩
  · rw [← hv']
    exact hv.1
  · rw [hv']
    exact (mem_seamGroup e S).mp ht

/-- Products of a doubling logical with a seam operator are doubling logicals:
`K ∖ T` is a union of cosets of `T`. -/
theorem IsDoublingLogical.mul_seam {u t : NQubitPauliOperator m}
    (hu : IsDoublingLogical e S u) (ht : t ∈ seamGroup e S) :
    IsDoublingLogical e S (u * t) := by
  refine ⟨(doublingGroup e S).mul_mem hu.1 (seamGroup_le_doublingGroup e S ht), fun h => hu.2 ?_⟩
  have := (seamGroup e S).mul_mem h ht
  rwa [_root_.mul_assoc, mul_self_eq_one, _root_.mul_one] at this

/-! ## Symmetric pairings and Proposition 3.4 -/

/-- The pairing is **symmetric** for `S` if the sheet swap preserves the
phase-free image of `S`: `s^σ ∈ G` for every stabilizer `s`. -/
def IsSymmetric : Prop :=
  ∀ s ∈ S.toSubgroup, sheetSwap e s.operators ∈ operatorImage S.toSubgroup

lemma IsSymmetric.sheetSwap_mem (h : IsSymmetric e S) {u : NQubitPauliOperator n}
    (hu : u ∈ operatorImage S.toSubgroup) : sheetSwap e u ∈ operatorImage S.toSubgroup := by
  obtain ⟨s, hs, rfl⟩ := mem_operatorImage.mp hu
  exact h s hs

/-- Proposition 3.4 (1): for a symmetric pairing, `J` is isotropic (its
elements pairwise commute), by the second commutation rule. -/
theorem symplecticInner_eq_zero_of_mem_foldImage (h : IsSymmetric e S)
    {b b' : NQubitPauliOperator m} (hb : b ∈ foldImage e S) (hb' : b' ∈ foldImage e S) :
    symplecticInner b b' = 0 := by
  obtain ⟨s, hs, rfl⟩ := (mem_foldImage e S).mp hb
  obtain ⟨t, ht, rfl⟩ := (mem_foldImage e S).mp hb'
  rw [symplecticInner_fold_fold,
    symplecticInner_eq_zero_of_mem_operatorImage S (operators_mem_operatorImage hs)
      (operators_mem_operatorImage ht),
    symplecticInner_eq_zero_of_mem_operatorImage S (operators_mem_operatorImage hs) (h t ht),
    add_zero]

/-- Proposition 3.4 (2): for a symmetric pairing, `J ≤ T`: the double of a
stabilizer fold `fold s` is `s * s^σ`, a stabilizer. -/
theorem foldImage_le_seamGroup (h : IsSymmetric e S) : foldImage e S ≤ seamGroup e S := by
  intro b hb
  obtain ⟨s, hs, rfl⟩ := (mem_foldImage e S).mp hb
  rw [mem_seamGroup, double_fold]
  exact (operatorImage S.toSubgroup).mul_mem (operators_mem_operatorImage hs) (h s hs)

/-- Proposition 3.4 (2): for a symmetric pairing, `P ≤ K`: the fold of a logical
operator commutes with every stabilizer fold. -/
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

/-- Proposition 3.4 (4): condition (R), `g * g^σ ∈ G` for every logical
operator `g`, is equivalent to `P ≤ T`. -/
theorem logicalFoldImage_le_seamGroup_iff :
    (∀ g ∈ centralizer S, g.operators * sheetSwap e g.operators ∈ operatorImage S.toSubgroup) ↔
      logicalFoldImage e S ≤ seamGroup e S := by
  constructor
  · intro hR b hb
    obtain ⟨g, hg, rfl⟩ := (mem_logicalFoldImage e S).mp hb
    rw [mem_seamGroup, double_fold]
    exact hR g hg
  · intro hPT g hg
    have := hPT (fold_operators_mem_logicalFoldImage e S hg)
    rwa [mem_seamGroup, double_fold] at this

/-- For a symmetric pairing, every doubling logical is a nontrivial logical of
the folded code: it lies in `K ∖ J`. -/
theorem IsDoublingLogical.not_mem_foldImage (h : IsSymmetric e S) {u : NQubitPauliOperator m}
    (hu : IsDoublingLogical e S u) : u ∉ foldImage e S :=
  fun hb => hu.2 (foldImage_le_seamGroup e S h hb)

/-- Proposition 3.4 (3): for a symmetric pairing, `d_K = d_0` as soon as some
doubling logical has weight `d_0`. -/
theorem isLeast_doubling_of_witness (h : IsSymmetric e S) {d₀ : ℕ}
    (hd₀ : IsLeast {w | ∃ u, u ∈ doublingGroup e S ∧ u ∉ foldImage e S ∧ weight u = w} d₀)
    (hW : ∃ u, IsDoublingLogical e S u ∧ weight u = d₀) :
    IsLeast {w | ∃ u, IsDoublingLogical e S u ∧ weight u = w} d₀ := by
  refine ⟨hW, ?_⟩
  rintro w ⟨u, hu, rfl⟩
  exact hd₀.2 ⟨u, hu.1, hu.not_mem_foldImage e S h, rfl⟩

/-- Proposition 3.4 (3), the inequality `d_0 ≤ d_K`: every doubling logical has
weight at least the distance of the folded code. -/
theorem le_weight_of_isDoublingLogical (h : IsSymmetric e S) {d₀ : ℕ}
    (hd₀ : ∀ u, u ∈ doublingGroup e S → u ∉ foldImage e S → d₀ ≤ weight u)
    {u : NQubitPauliOperator m} (hu : IsDoublingLogical e S u) : d₀ ≤ weight u :=
  hd₀ u hu.1 (hu.not_mem_foldImage e S h)

/-! ## The folded code -/

/-- Lemma 1.8 applied to `J`: for a symmetric pairing, the stabilizer folds are
the operator image of a stabilizer group on the `m` pairs. -/
theorem exists_foldedStabilizerGroup (h : IsSymmetric e S) :
    ∃ F : StabilizerGroup m, operatorImage F.toSubgroup = foldImage e S :=
  exists_stabilizerGroup_operatorImage_eq _
    fun _ hb _ hb' => symplecticInner_eq_zero_of_mem_foldImage e S h hb hb'

/-- **The folded code** (Definition 3.5): a stabilizer group on the `m` pairs
whose operator image is `J`, with the signs chosen by Lemma 1.8. Any two
choices have the same operator image, hence the same logical operators and the
same distance. -/
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
  rw [mem_centralizer_iff_symplecticInner, mem_doublingGroup_iff_forall_foldImage, ← hF]
  constructor
  · intro h b hb
    obtain ⟨f, hf, rfl⟩ := mem_operatorImage.mp hb
    exact h f hf
  · intro h f hf
    exact h _ (operators_mem_operatorImage hf)

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

/-- The distance of a folded code, in the library's sense, is the least weight
of an element of `K ∖ J`. -/
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
  constructor
  · intro h b hb
    exact ENat.coe_ne_top _ (h _ ⟨b, hb, rfl⟩)
  · rintro h _ ⟨b, hb, rfl⟩
    exact absurd hb (h b)

/-- The doubling floor is a natural number `d_K` iff `d_K` is the least weight
of a doubling logical. -/
theorem doublingFloor_eq_coe_iff (dK : ℕ) :
    doublingFloor e S = dK ↔ IsLeast {w | ∃ u, IsDoublingLogical e S u ∧ weight u = w} dK := by
  constructor
  · intro h
    have hne : ((fun u => (NQubitPauliOperator.weight u : ℕ∞)) ''
        {u | IsDoublingLogical e S u}).Nonempty := by
      by_contra hemp
      rw [Set.not_nonempty_iff_eq_empty] at hemp
      rw [doublingFloor, hemp, sInf_empty] at h
      exact ENat.top_ne_coe dK h
    have hmem : doublingFloor e S ∈ (fun u => (NQubitPauliOperator.weight u : ℕ∞)) ''
        {u | IsDoublingLogical e S u} := csInf_mem hne
    obtain ⟨u, hu, hw⟩ := hmem
    rw [h] at hw
    refine ⟨⟨u, hu, Nat.cast_injective hw⟩, ?_⟩
    rintro w ⟨v, hv, rfl⟩
    exact ENat.coe_le_coe.mp (h ▸ doublingFloor_le e S hv)
  · intro h
    apply le_antisymm
    · obtain ⟨u, hu, rfl⟩ := h.1
      exact doublingFloor_le e S hu
    · rw [le_doublingFloor_iff]
      intro u hu
      exact ENat.coe_le_coe.mpr (h.2 ⟨u, hu, rfl⟩)

end FoldDouble
end Stabilizer
end Quantum
