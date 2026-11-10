import QEC.Stabilizer.Framework.FoldDouble.Distance

/-!
# The fold trichotomy bound, and doubling in weight form

Fix a stabilizer group `S` on `n` qubits with a symmetric pairing
`e : Fin n ≃ Fin m × Fin 2`, and a folded code `F` (a stabilizer group on the
pairs whose operator image is the stabilizer folds `J`). The fold `b = fold v`
of a nontrivial logical operator `v` of `S` is a logical operator of `F`, so it
is exactly one of

* the identity: then `v` is the double of a nontrivial logical operator of
  `F`, and `wt v ≥ 2 d` for any lower bound `d` on those;
* a nontrivial logical operator of `F` (a *logical fold*): then
  `wt v ≥ wt b`;
* a stabilizer of `F` other than the identity: no general bound beyond
  `wt v ≥ wt b`.

`min_le_logicalWeight_of_symmetric_trichotomy` turns the three cases into the
lower bound `wt v ≥ min φ (min (2 d) ρ)`, where `φ` bounds the logical folds and
`ρ` bounds the nontrivial logical operators of `S` that fold to a non-identity
stabilizer. `min_floors_le_logicalWeight` is the same statement with `φ` and
`ρ` the floors `logicalFoldFloor` and `stabilizerFoldFloor` in `ℕ∞`.

`exists_logicalWeight_two_mul_of_not_isSeamLogical` is the matching upper
bound: a nontrivial logical operator of `F` that is not a seam logical doubles
to a nontrivial logical operator of `S` of twice its weight.

`isLeast_logicalWeight_two_mul_of_symmetric_weight` and
`hasCodeDistance_two_mul_of_symmetric_weight` are the doubling theorem with its
last hypothesis in *weight form*: for every stabilizer fold `b ≠ 1` of weight
`< 2 d₀`, every nontrivial logical operator of `S` folding to `b` has weight
`≥ 2 d₀`. This hypothesis is implied by the slice form
`wt b + 2 · residualWeight v ≥ 2 d₀` of
`isLeast_logicalWeight_two_mul_of_symmetric` (by the slice inequality), and is
necessary for the conclusion. The witness hypothesis (W) of that theorem is not
needed either: a minimum-weight nontrivial logical operator of `F` cannot be a
seam logical once every seam logical has weight `≥ 2 d₀`.
-/

namespace Quantum
namespace Stabilizer
namespace FoldDouble

open NQubitPauliOperator NQubitPauliGroupElement StabilizerGroup

variable {n m : ℕ} (e : Fin n ≃ Fin m × Fin 2) (S : StabilizerGroup n)

/-! ## Doubling logicals and the folded code -/

/-- For a symmetric pairing, every doubling logical has weight at least any
lower bound on the nontrivial logical operators of a folded code. -/
theorem le_weight_of_isDoublingLogical_of_folded (hsym : IsSymmetric e S)
    {F : StabilizerGroup m} (hF : operatorImage F.toSubgroup = foldImage e S) {d : ℕ}
    (hd : ∀ g, IsNontrivialLogicalOperator g F → d ≤ NQubitPauliGroupElement.weight g)
    {u : NQubitPauliOperator m} (hu : IsDoublingLogical e S u) : d ≤ weight u :=
  hd (ofOperator u) ((isNontrivialLogicalOperator_iff_of_operatorImage_eq e S hF _).mpr
    ⟨hu.1, hu.not_mem_foldImage e S hsym⟩)

/-- A nontrivial logical operator of a folded code that is not a seam logical
is a doubling logical, read on operator parts. -/
theorem isDoublingLogical_of_not_isSeamLogical
    {F : StabilizerGroup m} (hF : operatorImage F.toSubgroup = foldImage e S)
    {g : NQubitPauliGroupElement m} (hg : IsNontrivialLogicalOperator g F)
    (hns : ¬ IsSeamLogical e S g.operators) : IsDoublingLogical e S g.operators := by
  rw [isNontrivialLogicalOperator_iff_of_operatorImage_eq e S hF] at hg
  exact ⟨hg.1, fun hT => hns ⟨hT, hg.2⟩⟩

/-- **Upper bound.** A nontrivial logical operator `g` of a folded code that is
not a seam logical doubles to a nontrivial logical operator of `S` of weight
`2 · wt g`. -/
theorem exists_logicalWeight_two_mul_of_not_isSeamLogical
    {F : StabilizerGroup m} (hF : operatorImage F.toSubgroup = foldImage e S)
    {g : NQubitPauliGroupElement m} (hg : IsNontrivialLogicalOperator g F)
    (hns : ¬ IsSeamLogical e S g.operators) :
    ∃ v, IsNontrivialLogicalOperator v S ∧
      NQubitPauliGroupElement.weight v = 2 * NQubitPauliGroupElement.weight g :=
  exists_isNontrivialLogicalOperator_weight_eq_two_mul e S
    (isDoublingLogical_of_not_isSeamLogical e S hF hg hns)

/-! ## The lower bound -/

/-- **The fold trichotomy lower bound** (symmetric pairing). Let `F` be a folded
code whose nontrivial logical operators all have weight `≥ d`. If every logical
fold has weight `≥ φ`, and every nontrivial logical operator of `S` that folds
to a stabilizer fold other than the identity has weight `≥ ρ`, then every
nontrivial logical operator of `S` has weight `≥ min φ (min (2 d) ρ)`. -/
theorem min_le_logicalWeight_of_symmetric_trichotomy (hsym : IsSymmetric e S)
    {F : StabilizerGroup m} (hF : operatorImage F.toSubgroup = foldImage e S) {d φ ρ : ℕ}
    (hd : ∀ g, IsNontrivialLogicalOperator g F → d ≤ NQubitPauliGroupElement.weight g)
    (hφ : ∀ b, IsLogicalFold e S b → φ ≤ weight b)
    (hρ : ∀ v, IsNontrivialLogicalOperator v S → fold e v.operators ∈ foldImage e S →
      fold e v.operators ≠ 1 → ρ ≤ NQubitPauliGroupElement.weight v)
    {v : NQubitPauliGroupElement n} (hv : IsNontrivialLogicalOperator v S) :
    min φ (min (2 * d) ρ) ≤ NQubitPauliGroupElement.weight v := by
  have hvc : v ∈ centralizer S := ((isNontrivialLogicalOperator_iff_operators S v).mp hv).1
  by_cases hbJ : fold e v.operators ∈ foldImage e S
  · by_cases hb1 : fold e v.operators = 1
    · exact (min_le_right _ _).trans ((min_le_left _ _).trans
        (two_mul_le_weight_of_fold_eq_one e S hv hb1
          fun u hu => le_weight_of_isDoublingLogical_of_folded e S hsym hF hd hu))
    · exact (min_le_right _ _).trans ((min_le_right _ _).trans (hρ v hv hbJ hb1))
  · exact (min_le_left _ _).trans (le_weight_of_fold_not_mem_foldImage e S hvc hbJ hφ)

/-- The **stabilizer-fold floor**: the least weight of a nontrivial logical
operator of `S` whose fold is a stabilizer fold other than the identity; `⊤` if
there is none. -/
noncomputable def stabilizerFoldFloor : ℕ∞ :=
  sInf ((fun v : NQubitPauliGroupElement n => (NQubitPauliGroupElement.weight v : ℕ∞)) ''
    {v | IsNontrivialLogicalOperator v S ∧ fold e v.operators ∈ foldImage e S ∧
      fold e v.operators ≠ 1})

lemma stabilizerFoldFloor_le {v : NQubitPauliGroupElement n}
    (hv : IsNontrivialLogicalOperator v S) (hbJ : fold e v.operators ∈ foldImage e S)
    (hb1 : fold e v.operators ≠ 1) :
    stabilizerFoldFloor e S ≤ NQubitPauliGroupElement.weight v :=
  sInf_le ⟨v, ⟨hv, hbJ, hb1⟩, rfl⟩

lemma le_stabilizerFoldFloor_iff {k : ℕ∞} :
    k ≤ stabilizerFoldFloor e S ↔
      ∀ v, IsNontrivialLogicalOperator v S → fold e v.operators ∈ foldImage e S →
        fold e v.operators ≠ 1 → k ≤ NQubitPauliGroupElement.weight v := by
  rw [stabilizerFoldFloor, le_sInf_iff, Set.forall_mem_image]
  exact ⟨fun h v hv hbJ hb1 => h ⟨hv, hbJ, hb1⟩, fun h v hv => h v hv.1 hv.2.1 hv.2.2⟩

/-- **The fold trichotomy lower bound**, floor form: for a symmetric pairing
and a folded code whose nontrivial logical operators all have weight `≥ d`,
every nontrivial logical operator of `S` has weight at least
`min (logicalFoldFloor) (min (2 d) (stabilizerFoldFloor))`. -/
theorem min_floors_le_logicalWeight (hsym : IsSymmetric e S)
    {F : StabilizerGroup m} (hF : operatorImage F.toSubgroup = foldImage e S) {d : ℕ}
    (hd : ∀ g, IsNontrivialLogicalOperator g F → d ≤ NQubitPauliGroupElement.weight g)
    {v : NQubitPauliGroupElement n} (hv : IsNontrivialLogicalOperator v S) :
    min (logicalFoldFloor e S) (min (2 * (d : ℕ∞)) (stabilizerFoldFloor e S)) ≤
      (NQubitPauliGroupElement.weight v : ℕ∞) := by
  have hvc : v ∈ centralizer S := ((isNontrivialLogicalOperator_iff_operators S v).mp hv).1
  by_cases hbJ : fold e v.operators ∈ foldImage e S
  · by_cases hb1 : fold e v.operators = 1
    · refine (min_le_right _ _).trans ((min_le_left _ _).trans ?_)
      exact_mod_cast two_mul_le_weight_of_fold_eq_one e S hv hb1
        fun u hu => le_weight_of_isDoublingLogical_of_folded e S hsym hF hd hu
    · exact (min_le_right _ _).trans ((min_le_right _ _).trans
        (stabilizerFoldFloor_le e S hv hbJ hb1))
  · refine (min_le_left _ _).trans
      ((logicalFoldFloor_le e S ⟨fold_operators_mem_logicalFoldImage e S hvc, hbJ⟩).trans ?_)
    exact_mod_cast weight_fold_le e v.operators

/-! ## Doubling, weight form -/

/-- **Doubling, weight form** (symmetric pairing). Let `F` be a folded code of
distance `d₀`. Suppose
(R) `g * g^σ` is a stabilizer for every logical operator `g` of `S`;
(F) every seam logical has weight `≥ 2 d₀`;
(S) for every stabilizer fold `b ≠ 1` of weight `< 2 d₀`, every nontrivial
logical operator of `S` folding to `b` has weight `≥ 2 d₀`.
Then `2 d₀` is the least weight of a nontrivial logical operator of `S`. -/
theorem isLeast_logicalWeight_two_mul_of_symmetric_weight (hsym : IsSymmetric e S)
    {F : StabilizerGroup m} (hF : operatorImage F.toSubgroup = foldImage e S) {d₀ : ℕ}
    (hd₀ : IsLeast {w | ∃ g, IsNontrivialLogicalOperator g F ∧
      NQubitPauliGroupElement.weight g = w} d₀)
    (hR : ∀ g ∈ centralizer S, g.operators * sheetSwap e g.operators ∈ operatorImage S.toSubgroup)
    (hFl : ∀ b, IsSeamLogical e S b → 2 * d₀ ≤ weight b)
    (hS : ∀ b ∈ foldImage e S, b ≠ 1 → weight b < 2 * d₀ →
      ∀ v, IsNontrivialLogicalOperator v S → fold e v.operators = b →
        2 * d₀ ≤ NQubitPauliGroupElement.weight v) :
    IsLeast {w | ∃ g, IsNontrivialLogicalOperator g S ∧ NQubitPauliGroupElement.weight g = w}
      (2 * d₀) := by
  have hPT := (logicalFoldImage_le_seamGroup_iff e S).mp hR
  constructor
  · -- a minimum-weight logical of `F` is not a seam logical; its double is a witness
    obtain ⟨g, hg, hw⟩ := hd₀.1
    have h1 : 1 ≤ NQubitPauliGroupElement.weight g :=
      one_le_weight_of_isNontrivialLogicalOperator hg
    have hns : ¬ IsSeamLogical e S g.operators := fun hseam => by
      have := hFl _ hseam
      rw [← weight_eq_weight_operators, hw] at this
      omega
    obtain ⟨v, hv, hvw⟩ := exists_logicalWeight_two_mul_of_not_isSeamLogical e S hF hg hns
    exact ⟨v, hv, by rw [hvw, hw]⟩
  · rintro w ⟨v, hv, rfl⟩
    have h := min_le_logicalWeight_of_symmetric_trichotomy e S hsym hF (d := d₀)
      (φ := 2 * d₀) (ρ := 2 * d₀)
      (fun g hg => hd₀.2 ⟨g, hg, rfl⟩)
      (fun b hb => hFl b ⟨hPT hb.1, hb.2⟩)
      (fun v' hv' hbJ hb1 => by
        by_cases hlt : weight (fold e v'.operators) < 2 * d₀
        · exact hS _ hbJ hb1 hlt v' hv' rfl
        · push Not at hlt
          exact hlt.trans (weight_fold_le e _))
      hv
    simpa using h

/-- Doubling in weight form for a packaged `[[n, k]]` code: under the
hypotheses of `isLeast_logicalWeight_two_mul_of_symmetric_weight`, a stabilizer
code with stabilizer group `S` has distance `2 d₀`. -/
theorem hasCodeDistance_two_mul_of_symmetric_weight {k : ℕ} (C : StabilizerCode n k)
    (hC : C.toStabilizerGroup.toSubgroup = S.toSubgroup) (hsym : IsSymmetric e S)
    {F : StabilizerGroup m} (hF : operatorImage F.toSubgroup = foldImage e S) {d₀ : ℕ}
    (hd₀ : IsLeast {w | ∃ g, IsNontrivialLogicalOperator g F ∧
      NQubitPauliGroupElement.weight g = w} d₀)
    (hR : ∀ g ∈ centralizer S, g.operators * sheetSwap e g.operators ∈ operatorImage S.toSubgroup)
    (hFl : ∀ b, IsSeamLogical e S b → 2 * d₀ ≤ weight b)
    (hS : ∀ b ∈ foldImage e S, b ≠ 1 → weight b < 2 * d₀ →
      ∀ v, IsNontrivialLogicalOperator v S → fold e v.operators = b →
        2 * d₀ ≤ NQubitPauliGroupElement.weight v) :
    HasCodeDistance C (2 * d₀) := by
  have h1 : 1 ≤ d₀ := by
    obtain ⟨g, hg, hw⟩ := hd₀.1
    exact hw ▸ one_le_weight_of_isNontrivialLogicalOperator hg
  exact has_code_distance_of_isLeast C hC (by omega)
    (isLeast_logicalWeight_two_mul_of_symmetric_weight e S hsym hF hd₀ hR hFl hS)

end FoldDouble
end Stabilizer
end Quantum
