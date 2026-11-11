import Mathlib.Tactic
import Mathlib.Data.Nat.Bitwise
import QEC.Stabilizer.Foundations.BinarySymplectic.CheckMatrixDecidable
import QEC.Stabilizer.Foundations.PauliGroup.Commutation
import QEC.Stabilizer.Foundations.PauliGroup.Notation
import QEC.Stabilizer.Framework.Core.CodeNotation
import QEC.Stabilizer.Framework.Core.CSS.CSSCommutationLemmas
import QEC.Stabilizer.Framework.Core.CSS.CSSDistance
import QEC.Stabilizer.Framework.Core.Logical.CodeDistance
import QEC.Stabilizer.Framework.Core.Logical.LogicalOperators
import QEC.Stabilizer.Framework.Core.Stabilizer.StabilizerCode
import QEC.Stabilizer.Framework.Symplectic.Presentation
import QEC.Stabilizer.Framework.Symplectic.SymplecticSpan

/-!
# Quantum Hamming codes `[[2^r − 1, 2^r − 1 − 2r, 3]]`

The CSS codes of the classical `[2^r − 1, 2^r − 1 − r, 3]` Hamming codes, for
`r ≥ 3`: self-dual CSS stabilizer codes on `n = 2^r − 1` qubits encoding
`2^r − 1 − 2r` logical qubits, with code distance 3. The Hamming parity-check
matrix has `r` rows, and its column at qubit `k` is the binary expansion of
`k + 1`, so the columns are the nonzero vectors of `𝔽₂ʳ`. The `2r` generators
are `Z` and `X` on each row. The Steane code `[[7, 1, 3]]` is the case `r = 3`.

Being parametric, the family takes the **CSS route** rather than the decide
route: the generator list is built with `List.ofFn`, which `decide` cannot
evaluate. Any two rows meet in an even number of qubits (`2^(r−2)` for distinct
rows and `2^(r−1)` for a row with itself, both even when `r ≥ 3`), which gives
the commutation of Z-checks with X-checks; `−I ∉ closure` follows by
`CSS.negIdentity_not_mem_closure_union`, and independence from one pivot column
per row.

Distance 3 is `hasCodeDistance_three_of_columns`, as for the Steane code: the
columns of the check matrix are nonzero and pairwise distinct, which rules out
nontrivial logicals of weight 1 and 2; `X` on qubits `{0, 1, 2}` (the columns
`1`, `2`, `3`, with `1 ⊕ 2 = 3`) is a nontrivial logical of weight 3.

The transversal logical pair `X̄ = X⊗ⁿ`, `Z̄ = Z⊗ⁿ` is in
`QuantumHammingLogicals.lean`.

## Outline

- The Hamming parity-check matrix by rows, `row`: `even_card_row_inter_row`,
  `row_cover`, `row_separate`, and the pivot qubits `pivot`
- Generators `ZStab`, `XStab`, the list `generatorsList`, the sets
  `ZGenerators`, `XGenerators`, `generators` and the subgroup `subgroup`
- Hypotheses on the generators: `ZGenerators_isZType`, `XGenerators_isXType`,
  `ZGenerators_commute_XGenerators`, `generators_commute`,
  `AllPhaseZero_generatorsList`, `rowsLinearIndependent_generatorsList`
- `negIdentity_not_mem`, the bundled `stabilizerGroup`
- `presentation`, `stabilizerCode : Code[[2^r − 1, 2^r − 1 − 2r]]`
- Centralizer criteria `xOn_mem_centralizer`, `zOn_mem_centralizer`: `X` or `Z`
  on a support meeting every row evenly commutes with the stabilizer
- Distance 3 (column condition on the Hamming rows `row`, weight-3 logical):
  `code_has_distance_three`,
  `stabilizerCodeWithDistance : Code[[2^r − 1, 2^r − 1 − 2r, 3]]`
-/

namespace Quantum
namespace StabilizerGroup
namespace QuantumHamming

open NQubitPauliGroupElement
open scoped Pauli

variable (r : ℕ)

/-! ## The Hamming parity-check matrix

The `r × (2^r − 1)` Hamming parity-check matrix is given by its rows, as sets
of qubits: row `a` holds the qubits `k` for which bit `a` of `k + 1` is set.
Column `k` is then the binary expansion of `k + 1`, a nonzero number below
`2^r`. -/

/-- Row `a` of the Hamming check matrix as a support: the qubits `k` with bit
`a` of `k + 1` set. -/
def row (a : Fin r) : Finset (Fin (2 ^ r - 1)) :=
  Finset.univ.filter fun k => (k.val + 1).testBit a.val

lemma mem_row {a : Fin r} {k : Fin (2 ^ r - 1)} :
    k ∈ row r a ↔ (k.val + 1).testBit a.val = true := by
  simp [row]

/-- The numbers below `2 ^ r` with bits `a` and `b` set are even in number as
soon as there is a third bit `c < r`: flipping bit `c` pairs them up. -/
private lemma even_card_filter_testBit {r a b c : ℕ} (hc : c < r) (hca : c ≠ a) (hcb : c ≠ b) :
    Even ((Finset.range (2 ^ r)).filter fun m => m.testBit a = true ∧ m.testBit b = true).card := by
  rw [← ZMod.natCast_eq_zero_iff_even, Finset.card_eq_sum_ones, Nat.cast_sum]
  refine Finset.sum_involution (fun m _ => m ^^^ 2 ^ c) (fun _ _ => by decide) (fun m _ _ h => ?_)
    (fun m hm => ?_) (fun m _ => Nat.xor_xor_cancel_right ..)
  · simpa using congrArg (·.testBit c) h
  · rw [Finset.mem_filter, Finset.mem_range] at hm ⊢
    exact ⟨Nat.xor_lt_two_pow hm.1 (Nat.pow_lt_pow_right one_lt_two hc),
      by simp [hca, hm.2.1], by simp [hcb, hm.2.2]⟩

/-- Any two rows of the Hamming check matrix, distinct or not, meet in an even
number of qubits when `r ≥ 3`: flipping a third bit of the column pairs up the
common qubits. -/
theorem even_card_row_inter_row (hr : 3 ≤ r) (a b : Fin r) : Even (row r a ∩ row r b).card := by
  obtain ⟨c, hc, hca, hcb⟩ : ∃ c, c < r ∧ c ≠ a.val ∧ c ≠ b.val := by
    by_contra h
    push Not at h
    have h0 := h 0 (by omega)
    have h1 := h 1 (by omega)
    have h2 := h 2 (by omega)
    omega
  have h : (row r a ∩ row r b).card = ((Finset.range (2 ^ r)).filter fun m =>
      m.testBit a.val = true ∧ m.testBit b.val = true).card := by
    refine Finset.card_bij (fun k _ => k.val + 1) (fun k hk => ?_)
      (fun k _ l _ h => Fin.ext (Nat.succ_injective h)) (fun m hm => ?_)
    · rw [Finset.mem_inter, mem_row, mem_row] at hk
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr (show k.val + 1 < 2 ^ r by have := k.isLt; omega), hk⟩
    · rw [Finset.mem_filter, Finset.mem_range] at hm
      have hm0 : m ≠ 0 := by
        rintro rfl
        simp at hm
      have hm1 : m - 1 + 1 = m := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hm0)
      refine ⟨⟨m - 1, by omega⟩, ?_, hm1⟩
      rw [Finset.mem_inter, mem_row, mem_row, hm1]
      exact hm.2
  rw [h]
  exact even_card_filter_testBit hc hca hcb

/-- Each row of the Hamming check matrix has an even number of qubits when
`r ≥ 3`. -/
lemma even_card_row (hr : 3 ≤ r) (a : Fin r) : Even (row r a).card :=
  Finset.inter_self (row r a) ▸ even_card_row_inter_row r hr a a

/-- A bit set in a column `k + 1 < 2^r` lies below `r`. -/
private lemma lt_of_testBit {k : Fin (2 ^ r - 1)} {b : ℕ}
    (hb : (k.val + 1).testBit b = true) : b < r := by
  by_contra h
  have hk : k.val + 1 < 2 ^ b :=
    calc k.val + 1 < 2 ^ r := by have := k.isLt; omega
      _ ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) (not_lt.mp h)
  rw [Nat.testBit_lt_two_pow hk] at hb
  exact Bool.false_ne_true hb

/-- Every qubit lies on some Hamming row: no column is zero, since `k + 1 ≠ 0`
has a set bit. -/
lemma row_cover : ∀ k : Fin (2 ^ r - 1), ∃ a, k ∈ row r a := by
  intro k
  obtain ⟨b, hb⟩ := Nat.exists_testBit_of_ne_zero (Nat.succ_ne_zero k.val)
  exact ⟨⟨b, lt_of_testBit r hb⟩, (mem_row r).mpr hb⟩

/-- Any two distinct qubits are separated by some Hamming row: no two columns
coincide, since `k + 1` and `j + 1` differ in some bit. -/
lemma row_separate :
    ∀ k j : Fin (2 ^ r - 1), k ≠ j → ∃ a, (k ∈ row r a ↔ j ∉ row r a) := by
  intro k j hkj
  obtain ⟨b, hb⟩ := Nat.exists_testBit_ne_of_ne
    (fun h : k.val + 1 = j.val + 1 => hkj (Fin.ext (by omega)))
  have key : ∀ x y : Bool, x ≠ y → (x = true ↔ ¬y = true) := by decide
  refine ⟨⟨b, ?_⟩, by simpa only [mem_row] using key _ _ hb⟩
  cases hk : (k.val + 1).testBit b
  · exact lt_of_testBit r (k := j) (by simpa [hk] using hb.symm)
  · exact lt_of_testBit r hk

/-- The pivot qubit of row `a`: the qubit `2^a − 1`, whose column `2^a` has bit
`a` set and no other. -/
def pivot (a : Fin r) : Fin (2 ^ r - 1) :=
  ⟨2 ^ a.val - 1, Nat.sub_lt_sub_right Nat.one_le_two_pow (Nat.pow_lt_pow_right one_lt_two a.isLt)⟩

/-- Row `a` contains the pivot qubit of row `b` only for `a = b`. -/
lemma pivot_mem_row {a b : Fin r} : pivot r b ∈ row r a ↔ a = b := by
  rw [mem_row]
  change (2 ^ b.val - 1 + 1).testBit a.val = true ↔ _
  rw [Nat.sub_add_cancel Nat.one_le_two_pow, Nat.testBit_two_pow, decide_eq_true_eq, Fin.ext_iff,
    eq_comm]

/-! ## Generators -/

/-- The Z-check stabilizer of row `a`: `Z` on the qubits of the row. -/
def ZStab (a : Fin r) : NQubitPauliGroupElement (2 ^ r - 1) :=
  zOn (row r a)

/-- The X-check stabilizer of row `a`: `X` on the qubits of the row. -/
def XStab (a : Fin r) : NQubitPauliGroupElement (2 ^ r - 1) :=
  xOn (row r a)

/-- The `2r` generators as a list (Z-checks first, then X-checks). -/
def generatorsList : List (NQubitPauliGroupElement (2 ^ r - 1)) :=
  List.ofFn (ZStab r) ++ List.ofFn (XStab r)

/-- The Z-generators: one Z-check per row. -/
def ZGenerators : Set (NQubitPauliGroupElement (2 ^ r - 1)) :=
  Set.range (ZStab r)

/-- The X-generators: one X-check per row. -/
def XGenerators : Set (NQubitPauliGroupElement (2 ^ r - 1)) :=
  Set.range (XStab r)

/-- The `2r` generators as a set. -/
def generators : Set (NQubitPauliGroupElement (2 ^ r - 1)) :=
  ZGenerators r ∪ XGenerators r

/-- The subgroup generated by the Hamming checks. -/
noncomputable def subgroup : Subgroup (NQubitPauliGroupElement (2 ^ r - 1)) :=
  Subgroup.closure (generators r)

/-- The generator list has the elements of the generator set. -/
lemma listToSet_generatorsList : listToSet (generatorsList r) = generators r := by
  rw [generators, ZGenerators, XGenerators, ← listToSet_ofFn, ← listToSet_ofFn]
  exact Set.ext fun _ => List.mem_append

/-! ## Hypotheses on the generators

A Z-check and an X-check meet on the common qubits of two rows, an even number,
so they commute. For independence, the pivot of the Z-check of row `a` is the
`Z`-column of the qubit `pivot r a`, and that of its X-check the `X`-column of
the same qubit: no other check has a `1` there. -/

/-- Every Z-generator is Z-type. -/
lemma ZGenerators_isZType : ∀ g ∈ ZGenerators r, IsZTypeElement g := by
  rintro _ ⟨a, rfl⟩
  exact IsZTypeElement_zOn _

/-- Every X-generator is X-type. -/
lemma XGenerators_isXType : ∀ g ∈ XGenerators r, IsXTypeElement g := by
  rintro _ ⟨a, rfl⟩
  exact IsXTypeElement_xOn _

/-- Every Z-generator commutes with every X-generator: two rows meet in an
even number of qubits. -/
lemma ZGenerators_commute_XGenerators (hr : 3 ≤ r) :
    ∀ z ∈ ZGenerators r, ∀ x ∈ XGenerators r, z * x = x * z := by
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
  exact ((commutes_xOn_zOn_iff _ _).mpr (even_card_row_inter_row r hr b a)).symm

/-- All `2r` generators pairwise commute. -/
lemma generators_commute (hr : 3 ≤ r) :
    ∀ g ∈ generators r, ∀ h ∈ generators r, g * h = h * g := by
  rintro g (hgZ | hgX) h (hhZ | hhX)
  · exact (ZGenerators_isZType r g hgZ).commute (ZGenerators_isZType r h hhZ)
  · exact ZGenerators_commute_XGenerators r hr g hgZ h hhX
  · exact (ZGenerators_commute_XGenerators r hr h hhZ g hgX).symm
  · exact (XGenerators_isXType r g hgX).commute (XGenerators_isXType r h hhX)

/-- Every generator has phase power 0. -/
lemma AllPhaseZero_generatorsList : AllPhaseZero (generatorsList r) := fun g hg =>
  (List.mem_append.mp hg).elim (AllPhaseZero_ofFn _ (fun _ => rfl) g)
    (AllPhaseZero_ofFn _ (fun _ => rfl) g)

/-- The check-matrix rows of the `2r` generators are linearly independent. -/
lemma rowsLinearIndependent_generatorsList : rowsLinearIndependent (generatorsList r) := by
  rw [generatorsList, ← List.ofFn_fin_append]
  refine rowsLinearIndependent_ofFn_of_pivots _
    (Fin.append (fun a => Fin.natAdd _ (pivot r a)) fun a => Fin.castAdd _ (pivot r a))
    (fun i => ?_) (fun i j hij => ?_)
  · induction i using Fin.addCases with
    | left a =>
      rw [Fin.append_left, Fin.append_left, ZStab, toSymplectic_zOn_natAdd,
        if_pos ((pivot_mem_row r).mpr rfl)]
    | right a =>
      rw [Fin.append_right, Fin.append_right, XStab, toSymplectic_xOn_castAdd,
        if_pos ((pivot_mem_row r).mpr rfl)]
  · induction i using Fin.addCases with
    | left a =>
      induction j using Fin.addCases with
      | left b =>
        rw [Fin.append_left, Fin.append_left, ZStab, toSymplectic_zOn_natAdd, if_neg]
        rw [pivot_mem_row]
        rintro rfl
        exact lt_irrefl _ hij
      | right b => rw [Fin.append_left, Fin.append_right, ZStab, toSymplectic_zOn_castAdd]
    | right a =>
      induction j using Fin.addCases with
      | left b => rw [Fin.append_right, Fin.append_left, XStab, toSymplectic_xOn_natAdd]
      | right b =>
        rw [Fin.append_right, Fin.append_right, XStab, toSymplectic_xOn_castAdd, if_neg]
        rw [pivot_mem_row]
        rintro rfl
        exact lt_irrefl _ hij

/-! ## No `−I` in the stabilizer subgroup -/

/-- The closure of the `2r` generators does not contain `−I`. -/
lemma negIdentity_not_mem (hr : 3 ≤ r) : negIdentity (2 ^ r - 1) ∉ subgroup r :=
  CSS.negIdentity_not_mem_closure_union (ZGenerators r) (XGenerators r)
    (ZGenerators_isZType r) (XGenerators_isXType r) (ZGenerators_commute_XGenerators r hr)

/-! ## Bundled `StabilizerGroup (2^r − 1)` -/

/-- The stabilizer group of the quantum Hamming code, generated by
`generatorsList r`. -/
noncomputable def stabilizerGroup (hr : 3 ≤ r) : StabilizerGroup (2 ^ r - 1) :=
  mkStabilizerFromGenerators (2 ^ r - 1) (generatorsList r)
    (by rw [listToSet_generatorsList]; exact generators_commute r hr)
    (by rw [listToSet_generatorsList]; exact negIdentity_not_mem r hr)

/-- The stabilizer subgroup is the closure of the generator set. -/
lemma stabilizerGroup_toSubgroup_eq (hr : 3 ≤ r) :
    (stabilizerGroup r hr).toSubgroup = subgroup r :=
  congrArg Subgroup.closure (listToSet_generatorsList r)

/-! ## The bare code `Code[[2^r − 1, 2^r − 1 − 2r]]`

`2r` independent, pairwise commuting generators on `2^r − 1` qubits:
`2^r − 1 − 2r` logical qubits, at least one since `2r + 1 ≤ 2^r` for `r ≥ 3`. -/

/-- `2r + 1 ≤ 2^r` for `r ≥ 3`, so the `2r` generators fit on `2^r − 1`
qubits. -/
lemma two_mul_add_one_le_two_pow (hr : 3 ≤ r) : 2 * r + 1 ≤ 2 ^ r := by
  induction r, hr using Nat.le_induction with
  | base => decide
  | succ m _ ih => rw [pow_succ]; omega

/-- The generator list as a presentation of a `[[2^r − 1, 2^r − 1 − 2r]]` code:
its `2r` check-matrix rows are linearly independent. -/
def presentation (hr : 3 ≤ r) :
    StabilizerCode.Presentation (2 ^ r - 1) (2 ^ r - 1 - 2 * r) where
  hk := Nat.sub_le _ _
  generatorsList := generatorsList r
  generators_length := by
    have := two_mul_add_one_le_two_pow r hr
    rw [generatorsList, List.length_append, List.length_ofFn, List.length_ofFn]
    omega
  generators_phaseZero := AllPhaseZero_generatorsList r
  generators_independent := rowsLinearIndependent_generatorsList r
  generators_commute := by
    have h := generators_commute r hr
    rw [← listToSet_generatorsList] at h
    exact h
  closure_no_neg_identity := by rw [listToSet_generatorsList]; exact negIdentity_not_mem r hr

/-- The quantum Hamming code as a stabilizer code
`[[2^r − 1, 2^r − 1 − 2r]]`. -/
noncomputable def stabilizerCode (hr : 3 ≤ r) : Code[[2 ^ r - 1, 2 ^ r - 1 - 2 * r]] :=
  (presentation r hr).toCode

/-- The stabilizer code's subgroup is the closure of the generator set. -/
lemma stabilizerCode_toSubgroup_eq (hr : 3 ≤ r) :
    (stabilizerCode r hr).toStabilizerGroup.toSubgroup = subgroup r :=
  stabilizerGroup_toSubgroup_eq r hr

/-! ## Centralizer criteria

`X` on a support `S` meets the Z-check of row `a` on `S ∩ row r a` and is
X-type like the X-checks, so it commutes with the stabilizer as soon as `S`
meets every row in an even number of qubits, that is, as soon as `S` is a
codeword of the classical Hamming code; dually for `Z` on `S`. The distance
witness below and the logical pair in `QuantumHammingLogicals.lean` are of this
form. -/

/-- `X` on a support meeting every Hamming row in an even number of qubits
commutes with every element of the stabilizer. -/
lemma xOn_mem_centralizer (hr : 3 ≤ r) {S : Finset (Fin (2 ^ r - 1))}
    (hS : ∀ a, Even (S ∩ row r a).card) : xOn S ∈ centralizer (stabilizerGroup r hr) := by
  rw [mem_centralizer_iff_closure _ _ (generators r) (stabilizerGroup_toSubgroup_eq r hr)]
  rintro _ (⟨a, rfl⟩ | ⟨a, rfl⟩)
  · exact ((commutes_xOn_zOn_iff _ _).mpr (hS a)).symm
  · exact (IsXTypeElement_xOn _).commute (IsXTypeElement_xOn S)

/-- `Z` on a support meeting every Hamming row in an even number of qubits
commutes with every element of the stabilizer. -/
lemma zOn_mem_centralizer (hr : 3 ≤ r) {S : Finset (Fin (2 ^ r - 1))}
    (hS : ∀ a, Even (S ∩ row r a).card) : zOn S ∈ centralizer (stabilizerGroup r hr) := by
  rw [mem_centralizer_iff_closure _ _ (generators r) (stabilizerGroup_toSubgroup_eq r hr)]
  rintro _ (⟨a, rfl⟩ | ⟨a, rfl⟩)
  · exact (IsZTypeElement_zOn _).commute (IsZTypeElement_zOn S)
  · exact (commutes_xOn_zOn_iff _ _).mpr (Finset.inter_comm S _ ▸ hS a)

/-! ## Distance 3

### No nontrivial logical of weight 1 or 2

The rows of the Hamming check matrix are the supports of both the Z-checks and
the X-checks. Its columns are nonzero (`row_cover`) and pairwise distinct
(`row_separate`). -/

/-- `Z` on each Hamming row is a generator. -/
lemma zOn_row_mem (a : Fin r) : zOn (row r a) ∈ generators r :=
  .inl ⟨a, rfl⟩

/-- `X` on each Hamming row is a generator. -/
lemma xOn_row_mem (a : Fin r) : xOn (row r a) ∈ generators r :=
  .inr ⟨a, rfl⟩

/-! ### A nontrivial logical of weight 3

Qubits `0, 1, 2` are the columns `1, 2, 3`, and `1 ⊕ 2 = 3`: a weight-3
codeword of the classical Hamming code. So `X` on `{0, 1, 2}` meets every row
in an even number of qubits (row 0 in `{0, 2}`, row 1 in `{1, 2}`, the others
not at all) and commutes with every check. So does `Z` on `{0, 1, 2}`, and the
two meet on three qubits, so they anticommute. -/

/-- The qubits `{0, 1, 2}`. -/
def minWeightSupport : Finset (Fin (2 ^ r - 1)) :=
  Finset.univ.filter fun k => k.val < 3

/-- `X` on qubits `{0, 1, 2}`: a nontrivial logical of weight 3. -/
def minWeightLogical : NQubitPauliGroupElement (2 ^ r - 1) :=
  xOn (minWeightSupport r)

/-- `Z` on qubits `{0, 1, 2}`: a centralizer element anticommuting with
`minWeightLogical`. -/
def minWeightPartner : NQubitPauliGroupElement (2 ^ r - 1) :=
  zOn (minWeightSupport r)

/-- `{0, 1, 2}` has three qubits. -/
lemma card_minWeightSupport (hr : 3 ≤ r) : (minWeightSupport r).card = 3 := by
  have h3 : 3 < 2 ^ r - 1 := by have := two_mul_add_one_le_two_pow r hr; omega
  have h : minWeightSupport r = Finset.Iio ⟨3, h3⟩ := by
    ext k
    simp [minWeightSupport, Fin.lt_def]
  rw [h, Fin.card_Iio]

/-- `{0, 1, 2}` meets every Hamming row in an even number of qubits. Read off
in `ℕ`, the meet is `{m < 3 | bit a of m + 1}`: `{0, 2}` for `a = 0`, `{1, 2}`
for `a = 1`, and empty for `a ≥ 2`, since `m + 1 < 4`. -/
lemma even_card_minWeightSupport_inter_row (hr : 3 ≤ r) (a : Fin r) :
    Even (minWeightSupport r ∩ row r a).card := by
  have h3 : 3 < 2 ^ r - 1 := by have := two_mul_add_one_le_two_pow r hr; omega
  have hmap : (minWeightSupport r ∩ row r a).map Fin.valEmbedding =
      (Finset.range 3).filter fun m => (m + 1).testBit a.val = true := by
    ext m
    simp only [Finset.mem_map, Finset.mem_inter, minWeightSupport, row, Finset.mem_filter,
      Finset.mem_univ, true_and, Fin.valEmbedding_apply, Finset.mem_range]
    exact ⟨by rintro ⟨k, h, rfl⟩; exact h, fun h => ⟨⟨m, by omega⟩, h, rfl⟩⟩
  rw [← Finset.card_map Fin.valEmbedding, hmap]
  obtain h | h | h : a.val = 0 ∨ a.val = 1 ∨ 2 ≤ a.val := by omega
  · rw [h]; decide
  · rw [h]; decide
  · rw [Finset.filter_false_of_mem fun m hm => ?_]
    · simp
    · have hm4 : m + 1 < 2 ^ a.val :=
        calc m + 1 < 2 ^ 2 := by rw [Finset.mem_range] at hm; omega
          _ ≤ 2 ^ a.val := Nat.pow_le_pow_right (by norm_num) h
      simp [Nat.testBit_lt_two_pow hm4]

/-- `X` on `{0, 1, 2}` has weight 3. -/
lemma minWeightLogical_weight (hr : 3 ≤ r) : weight (minWeightLogical r) = 3 := by
  rw [minWeightLogical, weight_xOn, card_minWeightSupport r hr]

/-- `X` on `{0, 1, 2}` commutes with every element of the stabilizer. -/
lemma minWeightLogical_mem_centralizer (hr : 3 ≤ r) :
    minWeightLogical r ∈ centralizer (stabilizerGroup r hr) :=
  xOn_mem_centralizer r hr (even_card_minWeightSupport_inter_row r hr)

/-- `Z` on `{0, 1, 2}` commutes with every element of the stabilizer. -/
lemma minWeightPartner_mem_centralizer (hr : 3 ≤ r) :
    minWeightPartner r ∈ centralizer (stabilizerGroup r hr) :=
  zOn_mem_centralizer r hr (even_card_minWeightSupport_inter_row r hr)

/-- `X` and `Z` on `{0, 1, 2}` meet on three qubits, an odd number. -/
lemma minWeightLogical_anticommutes_minWeightPartner (hr : 3 ≤ r) :
    Anticommute (minWeightLogical r) (minWeightPartner r) := by
  rw [minWeightLogical, minWeightPartner, anticommute_xOn_zOn_iff, Finset.inter_self,
    card_minWeightSupport r hr]
  decide

/-- `X` on `{0, 1, 2}` is a nontrivial logical operator: it lies in the
centralizer and anticommutes with the centralizer element `minWeightPartner`. -/
lemma minWeightLogical_isNontrivial (hr : 3 ≤ r) :
    IsNontrivialLogicalOperator (minWeightLogical r) (stabilizerCode r hr).toStabilizerGroup :=
  isNontrivialLogicalOperator_of_anticommute_centralizer _ (minWeightLogical_mem_centralizer r hr)
    (minWeightPartner_mem_centralizer r hr) (minWeightLogical_anticommutes_minWeightPartner r hr)

/-! ### The code with its distance `Code[[2^r − 1, 2^r − 1 − 2r, 3]]` -/

/-- **Every quantum Hamming code has distance 3.** Both check matrices are the
Hamming matrix, whose columns are nonzero and pairwise distinct, so no Pauli of
weight 1 or 2 is a nontrivial logical; `X` on `{0, 1, 2}` is one of weight 3. -/
theorem code_has_distance_three (hr : 3 ≤ r) : HasCodeDistance (stabilizerCode r hr) 3 :=
  hasCodeDistance_three_of_columns (row r) (row r) (generators r) (stabilizerCode r hr)
    (stabilizerCode_toSubgroup_eq r hr) (zOn_row_mem r) (xOn_row_mem r) (row_cover r)
    (row_cover r) (row_separate r) (row_separate r)
    ⟨minWeightLogical r, minWeightLogical_isNontrivial r hr, minWeightLogical_weight r hr⟩

/-- The quantum Hamming code packaged with its distance. -/
noncomputable def stabilizerCodeWithDistance (hr : 3 ≤ r) :
    Code[[2 ^ r - 1, 2 ^ r - 1 - 2 * r, 3]] where
  toStabilizerCode := stabilizerCode r hr
  hasDistance := code_has_distance_three r hr

end QuantumHamming
end StabilizerGroup
end Quantum
