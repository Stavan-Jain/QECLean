import Mathlib.Tactic
import Mathlib.Data.List.OfFn
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Bitwise
import QEC.Stabilizer.Framework.Core.Stabilizer.StabilizerGroup
import QEC.Stabilizer.Framework.Core.Stabilizer.StabilizerCode
import QEC.Stabilizer.Framework.Core.CodeNotation
import QEC.Stabilizer.Framework.Core.Stabilizer.SubgroupLemmas
import QEC.Stabilizer.Framework.Core.CSS.CSSNoNegI
import QEC.Stabilizer.Framework.Core.Stabilizer.Centralizer
import QEC.Stabilizer.Framework.Core.CSS.CSSCommutationLemmas
import QEC.Stabilizer.Framework.Core.CSS.CSSDistance
import QEC.Stabilizer.Framework.Core.Logical.CodeDistance
import QEC.Stabilizer.Framework.Core.Logical.LogicalOperators
import QEC.Stabilizer.Foundations.PauliGroup.Commutation
import QEC.Stabilizer.Foundations.PauliGroup.CommutationTactics
import QEC.Stabilizer.Foundations.BinarySymplectic.SymplecticInner
import QEC.Stabilizer.Foundations.BinarySymplectic.CheckMatrix
import QEC.Stabilizer.Foundations.BinarySymplectic.CheckMatrixDecidable
import QEC.Stabilizer.Foundations.BinarySymplectic.Core
import QEC.Stabilizer.Framework.Symplectic.IndependentEquiv
import QEC.Stabilizer.Framework.Symplectic.Presentation
import QEC.Stabilizer.Foundations.PauliGroup.NQubitOperator

namespace Quantum
open scoped BigOperators

namespace StabilizerGroup
namespace QuantumHamming

/-!
# Quantum Hamming codes `[[2^r − 1, 2^r − 1 − 2r, 3]]`

The quantum Hamming code family is a CSS construction based on the classical
`[2^r − 1, 2^r − 1 − r, 3]` Hamming code [Steane 1996,
`arxiv:quant-ph/9601029`]. For a parameter `r ≥ 3`:
- Physical qubits: `n = 2^r − 1`
- Z-generators: for each row `a : Fin r` of the Hamming parity-check matrix,
  apply Z to qubits in the support of that row (r generators)
- X-generators: same supports, but apply X instead (r generators)
- Total generators: 2r, encoding `2^r − 1 − 2r` logical qubits

The Hamming parity-check matrix has columns indexed by `Fin (2^r − 1)`, where
column `k` represents the binary expansion of `k + 1` (all nonzero r-bit
vectors).

Cross-commutation holds because any two rows of the Hamming parity-check matrix
overlap in an even number of positions: specifically `2^(r−2)` for distinct rows
and `2^(r−1)` for equal rows, both even when `r ≥ 3`.

The Steane `[[7, 1, 3]]` code is the special case `r = 3`.

Being parametric, the family takes the **CSS route** rather than the decide
route: the generator list is a `List.ofFn` that `decide` cannot evaluate, so
commutation comes from the Z/X typing and the even row overlaps, `−I ∉ closure`
from `CSS.negIdentity_not_mem_closure_union`, and independence from a pivot
column per row.

The distance argument is the Steane one, for every `r`: the columns of the
Hamming check matrix are the nonzero vectors of `𝔽₂ʳ`, so no column is zero and
no two coincide, and `hasCodeDistance_three_of_columns` rules out nontrivial
logicals of weight `1` and `2`. `X` on qubits `{0, 1, 2}` (columns `1, 2, 3`,
with `1 ⊕ 2 = 3`) is a nontrivial logical of weight `3`.

The transversal logical pair `X̄ = X⊗ⁿ`, `Z̄ = Z⊗ⁿ` is in
`QuantumHammingLogicals.lean`.

## Outline

- The Hamming parity-check matrix and `hammingRowDot_eq_zero`
- Generators `ZGen`, `XGen` and the list `generatorsList`
- Z/X typing, cross-commutation, `generators_commute`
- Check-matrix independence `rowsLinearIndependent_generatorsList`
- `negIdentity_not_mem`, the bundled `stabilizerGroup`
- `stabilizerCode : Code[[2^r − 1, 2^r − 1 − 2r]]`
- Distance 3 (Hamming column condition, weight-3 witness):
  `code_has_distance_three`,
  `stabilizerCodeWithDistance : Code[[2^r − 1, 2^r − 1 − 2r, 3]]`
-/

open NQubitPauliGroupElement

variable (r : ℕ)

/-!
## Hamming parity-check matrix

The `r × (2^r − 1)` Hamming parity-check matrix has columns that enumerate all
nonzero binary vectors of length `r`. Column `k` (0-indexed) is the binary
expansion of `k + 1`.
-/

/-- Entry `(a, k)` of the Hamming parity-check matrix: bit `a` of `k + 1`.
    Row `a` has a 1 at column `k` iff the `(k+1)`-th nonzero vector has its `a`-th bit set.
-/
def hammingEntry (a : Fin r) (k : Fin (2 ^ r - 1)) : ZMod 2 :=
  if (k.val + 1).testBit a.val then 1 else 0

/-- The number of columns where rows `a` and `b` both have a 1. Over ZMod 2,
this is the
    dot product of rows `a` and `b` of the parity-check matrix. -/
def hammingRowDot (a b : Fin r) : ZMod 2 :=
  ∑ k : Fin (2 ^ r - 1), hammingEntry r a k * hammingEntry r b k

/-- Even cardinality from a fixed-point-free involution on a Finset. -/
private lemma even_card_of_fpf_involution {α : Type*}
    (S : Finset α) (f : α → α) (hf_mem : ∀ x ∈ S, f x ∈ S)
    (hf_inv : ∀ x ∈ S, f (f x) = x) (hf_ne : ∀ x ∈ S, f x ≠ x) :
    Even S.card := by
  classical
  induction S using Finset.strongInduction with
  | H S ih =>
    by_cases hS : S = ∅
    · simp [hS]
    · obtain ⟨x, hx⟩ := Finset.nonempty_of_ne_empty hS
      have hfx := hf_mem x hx
      have hne : f x ≠ x := hf_ne x hx
      let S' := (S.erase (f x)).erase x
      have hS_eq : S.card = S'.card + 2 := by
        have h1 : (S.erase (f x)).card = S.card - 1 :=
          Finset.card_erase_of_mem hfx
        have h2 : x ∈ S.erase (f x) := Finset.mem_erase.mpr ⟨hne.symm, hx⟩
        have h3 : S'.card = (S.erase (f x)).card - 1 :=
          Finset.card_erase_of_mem h2
        have h5 : 1 < S.card := by
          rw [Finset.one_lt_card]
          exact ⟨x, hx, f x, hfx, hne.symm⟩
        omega
      have hS'_sub : S' ⊂ S :=
        Finset.ssubset_of_subset_of_ssubset
          (Finset.erase_subset _ _) (Finset.erase_ssubset hfx)
      rw [hS_eq]
      have hS'_even := ih S' hS'_sub (fun y hy => by
          simp only [S', Finset.mem_erase] at hy ⊢
          refine ⟨fun h => ?_, fun h => ?_, hf_mem y hy.2.2⟩
          · have hinv := hf_inv y hy.2.2
            rw [h] at hinv
            exact hy.2.1 hinv.symm
          · have : f (f y) = f (f x) := by rw [h]
            rw [hf_inv y hy.2.2, hf_inv x hx] at this
            exact hy.1 this)
        (fun y hy => by simp only [S', Finset.mem_erase] at hy; exact hf_inv y hy.2.2)
        (fun y hy => by simp only [S', Finset.mem_erase] at hy; exact hf_ne y hy.2.2)
      obtain ⟨k, hk⟩ := hS'_even
      exact ⟨k + 1, by omega⟩

/-- XOR with `2^c` preserves `testBit` at positions other than `c`. -/
private lemma testBit_xor_two_pow (m c i : ℕ) (hic : i ≠ c) :
    (m ^^^ 2 ^ c).testBit i = m.testBit i := by
  rw [Nat.testBit_xor, Nat.testBit_two_pow]
  simp [Ne.symm hic]

/-- If `m < 2^r` and `c < r`, then `m ^^^ 2^c < 2^r`. -/
private lemma xor_pow_lt_pow {m c r : ℕ} (hm : m < 2 ^ r) (hc : c < r) :
    m ^^^ 2 ^ c < 2 ^ r := by
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  rw [Nat.testBit_xor, Nat.testBit_two_pow]
  have hmi : m.testBit i = false := Nat.testBit_lt_two_pow (by
    calc m < 2 ^ r := hm
    _ ≤ 2 ^ i := Nat.pow_le_pow_right (by omega) hi)
  simp [show ¬ (c = i) from by omega, hmi]

/-- For `k : Fin (2^r - 1)` with bit `a` set (where `a ≠ c`), `(k+1) ⊕ 2^c - 1`
is
    a valid element of `Fin (2^r - 1)`. -/
private lemma xor_flip_val_lt {r c : ℕ} (hc : c < r) {k : Fin (2 ^ r - 1)}
    {a : ℕ} (hac : a ≠ c) (ha : (k.val + 1).testBit a = true) :
    (k.val + 1 ^^^ 2 ^ c) - 1 < 2 ^ r - 1 := by
  have hk_lt : k.val + 1 < 2 ^ r := by omega
  have hxor_lt : k.val + 1 ^^^ 2 ^ c < 2 ^ r := xor_pow_lt_pow hk_lt hc
  have hxor_pos : 0 < k.val + 1 ^^^ 2 ^ c := by
    rw [Nat.pos_iff_ne_zero]
    intro h
    have hbad : (k.val + 1 ^^^ 2 ^ c).testBit a = (k.val + 1).testBit a :=
      testBit_xor_two_pow _ _ _ hac
    rw [h] at hbad
    simp only [Nat.zero_testBit] at hbad
    rw [ha] at hbad
    exact absurd hbad (by simp)
  omega

/-- The XOR-flip function on `Fin (2^r - 1)`, defined for elements where bit `a`
is set. -/
private def xorFlip (r c : ℕ) (hc : c < r) (a : ℕ) (hac : a ≠ c)
    (k : Fin (2 ^ r - 1)) (ha : (k.val + 1).testBit a = true) : Fin (2 ^ r - 1) :=
  ⟨(k.val + 1 ^^^ 2 ^ c) - 1, xor_flip_val_lt hc hac ha⟩

/-- The XOR result is positive when bit `a ≠ c` is set. -/
private lemma xor_pos_of_testBit {m c a : ℕ} (hac : a ≠ c)
    (ha : m.testBit a = true) : 0 < m ^^^ 2 ^ c := by
  rw [Nat.pos_iff_ne_zero]
  intro h
  have := testBit_xor_two_pow m c a hac
  rw [h] at this
  simp only [Nat.zero_testBit] at this
  rw [ha] at this
  exact Bool.false_ne_true this

/-- The dot product of any two rows of the Hamming parity-check matrix is 0 (mod
2)
    for `r ≥ 3`.

    **Proof sketch:** We find a bit position `c` distinct from `a` and `b` (possible
    since `r ≥ 3`), then define an involution on the overlap set by XORing with `2^c`.
    This involution is fixed-point-free, so the overlap set has even cardinality.
-/
theorem hammingRowDot_eq_zero (hr : 3 ≤ r) (a b : Fin r) :
    hammingRowDot r a b = 0 := by
  -- Step 1: Rewrite as card of a filter set
  simp only [hammingRowDot, hammingEntry]
  conv_lhs =>
    arg 2; ext k
    rw [show (if (k.val + 1).testBit a.val then (1 : ZMod 2) else 0) *
        (if (k.val + 1).testBit b.val then (1 : ZMod 2) else 0) =
        if ((k.val + 1).testBit a.val = true ∧ (k.val + 1).testBit b.val = true) then 1 else 0
      by split_ifs <;> simp_all]
  rw [Finset.sum_boole]
  rw [ZMod.natCast_eq_zero_iff_even]
  -- Step 2: Find bit c < r with c ≠ a and c ≠ b (possible since r ≥ 3)
  have hc_exists : ∃ c : ℕ, c < r ∧ c ≠ a.val ∧ c ≠ b.val := by
    by_contra hall; push Not at hall
    have h0 := hall 0 (by omega); have h1 := hall 1 (by omega); have h2 := hall 2 (by omega)
    omega
  obtain ⟨c, hc_lt, hca, hcb⟩ := hc_exists
  -- Step 3: Define the XOR involution and show even cardinality
  let S := Finset.univ.filter (fun k : Fin (2 ^ r - 1) =>
    (k.val + 1).testBit a.val = true ∧ (k.val + 1).testBit b.val = true)
  -- Define f on all of Fin (2^r - 1); on S it will be the XOR map
  let f : Fin (2 ^ r - 1) → Fin (2 ^ r - 1) := fun k =>
    if ha : (k.val + 1).testBit a.val = true then
      xorFlip r c hc_lt a.val hca.symm k ha
    else k
  apply even_card_of_fpf_involution S f
  -- f maps S to S: XOR with 2^c preserves bits a and b (since c ≠ a, c ≠ b)
  · intro k hk
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
    have hka := hk.1; have hkb := hk.2
    simp only [f, dif_pos hka, xorFlip]
    have hxor_pos := xor_pos_of_testBit hca.symm hka
    constructor
    · show ((k.val + 1 ^^^ 2 ^ c) - 1 + 1).testBit a.val = true
      rw [Nat.sub_one_add_one_eq_of_pos hxor_pos]
      rwa [testBit_xor_two_pow _ _ _ hca.symm]
    · show ((k.val + 1 ^^^ 2 ^ c) - 1 + 1).testBit b.val = true
      rw [Nat.sub_one_add_one_eq_of_pos hxor_pos]
      rwa [testBit_xor_two_pow _ _ _ hcb.symm]
  -- f is an involution on S
  · intro k hk
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hk
    have hka := hk.1
    simp only [f]
    rw [dif_pos hka]
    simp only [xorFlip]
    have hxor_pos := xor_pos_of_testBit hca.symm hka
    have hbit_a : ((k.val + 1 ^^^ 2 ^ c) - 1 + 1).testBit a.val = true := by
      rw [Nat.sub_one_add_one_eq_of_pos hxor_pos]
      rwa [testBit_xor_two_pow _ _ _ hca.symm]
    rw [dif_pos hbit_a]
    ext
    change ((k.val + 1 ^^^ 2 ^ c) - 1 + 1 ^^^ 2 ^ c) - 1 = k.val
    rw [Nat.sub_one_add_one_eq_of_pos hxor_pos, Nat.xor_xor_cancel_right]; omega
  -- f has no fixed points on S
  · intro k hk
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hk
    have hka := hk.1
    simp only [f]
    rw [dif_pos hka]
    intro h
    have heq := congr_arg Fin.val h
    simp only [xorFlip] at heq
    have hxor_pos := xor_pos_of_testBit hca.symm hka
    have h1 : k.val + 1 ^^^ 2 ^ c = k.val + 1 := by omega
    have h2 := Nat.xor_xor_cancel_left (k.val + 1) (2 ^ c)
    rw [h1, Nat.xor_self] at h2
    exact absurd h2.symm (by positivity)

/-!
## Generators

For each row `a : Fin r`, we have a Z-generator and an X-generator. The support
of generator `a` is the set of qubits `k` where row `a` has a 1.
-/

/-- Z-generator for row `a`: Z on qubits where bit `a` of `(k+1)` is set. -/
def ZGen (a : Fin r) : NQubitPauliGroupElement (2 ^ r - 1) :=
  ⟨0, fun k => if (k.val + 1).testBit a.val then PauliOperator.Z else PauliOperator.I⟩

/-- X-generator for row `a`: X on qubits where bit `a` of `(k+1)` is set. -/
def XGen (a : Fin r) : NQubitPauliGroupElement (2 ^ r - 1) :=
  ⟨0, fun k => if (k.val + 1).testBit a.val then PauliOperator.X else PauliOperator.I⟩

/-- The set of Z-generators (one per parity-check row). -/
def ZGenerators : Set (NQubitPauliGroupElement (2 ^ r - 1)) :=
  Set.range (ZGen r)

/-- The set of X-generators (one per parity-check row). -/
def XGenerators : Set (NQubitPauliGroupElement (2 ^ r - 1)) :=
  Set.range (XGen r)

/-- The full generator set: Z-generators ∪ X-generators. -/
def generators : Set (NQubitPauliGroupElement (2 ^ r - 1)) :=
  ZGenerators r ∪ XGenerators r

/-- The quantum Hamming stabilizer subgroup: closure of the 2r generators. -/
noncomputable def subgroup : Subgroup (NQubitPauliGroupElement (2 ^ r - 1)) :=
  Subgroup.closure (generators r)

/-!
## Generator list

We combine the Z-generators and X-generators into a single function on
`Fin (2 * r)`, mapping the first `r` indices to Z-generators and the last `r` to
X-generators.
-/

/-- Combined generator function: indices `[0, r)` map to Z-generators,
    indices `[r, 2r)` map to X-generators. -/
def allGen (i : Fin (2 * r)) : NQubitPauliGroupElement (2 ^ r - 1) :=
  if h : i.val < r then ZGen r ⟨i.val, h⟩ else XGen r ⟨i.val - r, by omega⟩

/-- Generators as a list (for check-matrix and independence arguments). -/
def generatorsList : List (NQubitPauliGroupElement (2 ^ r - 1)) :=
  List.ofFn (allGen r)

lemma generatorsList_length : (generatorsList r).length = 2 * r := by
  simp [generatorsList, List.length_ofFn]

/-- Every element of the generators list has phase power 0. -/
lemma AllPhaseZero_generatorsList :
    NQubitPauliGroupElement.AllPhaseZero (generatorsList r) := by
  rw [generatorsList]
  apply NQubitPauliGroupElement.AllPhaseZero_ofFn
  intro i
  simp only [allGen]
  split_ifs <;> rfl

/-- The list of generators has the same elements as the generator set. -/
lemma listToSet_generatorsList :
    NQubitPauliGroupElement.listToSet (generatorsList r) = generators r := by
  rw [generatorsList, NQubitPauliGroupElement.listToSet_ofFn]
  ext g
  simp only [Set.mem_range, generators, ZGenerators, XGenerators, Set.mem_union]
  constructor
  · rintro ⟨i, rfl⟩
    simp only [allGen]
    split_ifs with h
    · exact Or.inl ⟨⟨i.val, h⟩, rfl⟩
    · exact Or.inr ⟨⟨i.val - r, by omega⟩, rfl⟩
  · rintro (⟨a, rfl⟩ | ⟨a, rfl⟩)
    · exact ⟨⟨a.val, by omega⟩, by simp [allGen, a.isLt]⟩
    · exact ⟨⟨r + a.val, by omega⟩, by simp [allGen, show ¬(r + a.val < r) from by omega]⟩

/-!
## Typing: Z-type / X-type generators
-/

/-- Each Z-generator is Z-type (phase 0, each qubit is I or Z). -/
lemma ZGenerators_are_ZType :
    ∀ g, g ∈ ZGenerators r → NQubitPauliGroupElement.IsZTypeElement g := by
  intro g hg
  obtain ⟨a, rfl⟩ := hg
  refine ⟨rfl, fun k => ?_⟩
  simp only [ZGen]
  split_ifs
  · exact Or.inr rfl
  · exact Or.inl rfl

/-- Each X-generator is X-type (phase 0, each qubit is I or X). -/
lemma XGenerators_are_XType :
    ∀ g, g ∈ XGenerators r → NQubitPauliGroupElement.IsXTypeElement g := by
  intro g hg
  obtain ⟨a, rfl⟩ := hg
  refine ⟨rfl, fun k => ?_⟩
  simp only [XGen]
  split_ifs
  · exact Or.inr rfl
  · exact Or.inl rfl

/-!
## Cross-commutation: Z-generators commute with X-generators

The symplectic inner product between `ZGen a` and `XGen b` reduces to the dot
product of rows `a` and `b` of the Hamming parity-check matrix (over ZMod 2),
which is 0.
-/

/-- The symplectic inner product of `ZGen a` and `XGen b` equals the Hamming row
dot
    product of rows `a` and `b`. -/
lemma ZGen_XGen_symplectic_eq_hammingRowDot (a b : Fin r) :
    NQubitPauliOperator.symplecticInner (ZGen r a).operators (XGen r b).operators =
      hammingRowDot r a b := by
  simp only [NQubitPauliOperator.symplecticInner, hammingRowDot, hammingEntry, ZGen, XGen]
  congr 1
  ext k
  simp only [PauliOperator.symplecticProductSingle]
  split_ifs with ha hb hb
  · simp [PauliOperator.toSymplecticSingle]
  · simp [PauliOperator.toSymplecticSingle]
  · simp [PauliOperator.toSymplecticSingle]
  · simp [PauliOperator.toSymplecticSingle]

/-- Every Z-generator commutes with every X-generator. -/
theorem ZGenerators_commute_XGenerators (hr : 3 ≤ r) :
    ∀ z ∈ ZGenerators r, ∀ x ∈ XGenerators r, z * x = x * z := by
  intro z hz x hx
  obtain ⟨a, rfl⟩ := hz
  obtain ⟨b, rfl⟩ := hx
  rw [NQubitPauliOperator.commutes_iff_symplectic_inner_zero]
  rw [ZGen_XGen_symplectic_eq_hammingRowDot]
  exact hammingRowDot_eq_zero r hr a b

/-!
## Pairwise commutation of all generators
-/

private lemma ZType_commutes {m : ℕ} {g h : NQubitPauliGroupElement m}
    (hg : NQubitPauliGroupElement.IsZTypeElement g)
    (hh : NQubitPauliGroupElement.IsZTypeElement h) :
    g * h = h * g := by
  exact CSSCommutationLemmas.ZType_commutes hg hh

private lemma XType_commutes {m : ℕ} {g h : NQubitPauliGroupElement m}
    (hg : NQubitPauliGroupElement.IsXTypeElement g)
    (hh : NQubitPauliGroupElement.IsXTypeElement h) :
    g * h = h * g := by
  exact CSSCommutationLemmas.XType_commutes hg hh

/-- All generators pairwise commute. -/
theorem generators_commute (hr : 3 ≤ r) :
    ∀ g ∈ generators r, ∀ h ∈ generators r, g * h = h * g := by
  intro g hg h hh
  have hg' : g ∈ ZGenerators r ∨ g ∈ XGenerators r := by simpa [generators] using hg
  have hh' : h ∈ ZGenerators r ∨ h ∈ XGenerators r := by simpa [generators] using hh
  rcases hg' with hgZ | hgX <;> rcases hh' with hhZ | hhX
  · exact ZType_commutes (ZGenerators_are_ZType r g hgZ) (ZGenerators_are_ZType r h hhZ)
  · exact ZGenerators_commute_XGenerators r hr g hgZ h hhX
  · simpa using (ZGenerators_commute_XGenerators r hr h hhZ g hgX).symm
  · exact XType_commutes (XGenerators_are_XType r g hgX) (XGenerators_are_XType r h hhX)

/-!
## Linear independence of generators

The check-matrix rows of the 2r generators are linearly independent over ZMod 2.
This ensures the stabilizer has exactly 2r independent generators, giving a code
encoding `2^r − 1 − 2r` logical qubits.
-/

/-- `testBit (2^a) a = true` -/
private lemma testBit_two_pow_self (a : ℕ) : (2 ^ a).testBit a = true := by
  rw [Nat.testBit_two_pow]; simp

/-- `testBit (2^a) b = false` when `b ≠ a` -/
private lemma testBit_two_pow_ne {a b : ℕ} (h : b ≠ a) : (2 ^ a).testBit b = false := by
  rw [Nat.testBit_two_pow]; simp [Ne.symm h]

/-- `2^a - 1 < 2^r - 1` when `a < r` (so `2^a - 1` is a valid column index). -/
private lemma two_pow_sub_one_lt_two_pow_sub_one {a r : ℕ} (h : a < r) :
    2 ^ a - 1 < 2 ^ r - 1 := by
  exact Nat.sub_lt_sub_right Nat.one_le_two_pow (Nat.pow_lt_pow_right (by omega) h)

/-- The pivot entry: `hammingEntry r a (2^a - 1) = 1`. -/
private lemma hammingEntry_pivot (a : Fin r) :
    hammingEntry r a ⟨2 ^ a.val - 1, two_pow_sub_one_lt_two_pow_sub_one a.isLt⟩ = 1 := by
  simp only [hammingEntry]
  rw [Nat.sub_one_add_one_eq_of_pos (by positivity), testBit_two_pow_self]; rfl

/-- Off-pivot entries: `hammingEntry r b (2^a - 1) = 0` when `b ≠ a`. -/
private lemma hammingEntry_off_pivot {a b : Fin r} (hab : b ≠ a) :
    hammingEntry r b ⟨2 ^ a.val - 1, two_pow_sub_one_lt_two_pow_sub_one a.isLt⟩ = 0 := by
  simp only [hammingEntry]
  rw [Nat.sub_one_add_one_eq_of_pos (by positivity), testBit_two_pow_ne (Fin.val_ne_of_ne hab)]
  simp

/-- The rows of the Hamming parity-check matrix are linearly independent.
    Proved by showing that column `2^a - 1` serves as a pivot for row `a`. -/
private lemma hammingRows_linearIndependent :
    ∀ f : Fin r → ZMod 2,
      (∀ k : Fin (2 ^ r - 1), ∑ a : Fin r, f a * hammingEntry r a k = 0) →
      f = 0 := by
  intro f hf
  funext a
  simp only [Pi.zero_apply]
  -- Evaluate at the pivot column k = 2^a - 1
  have hbound := two_pow_sub_one_lt_two_pow_sub_one a.isLt
  have hpivot := hf ⟨2 ^ a.val - 1, hbound⟩
  -- In this sum, all terms with b ≠ a vanish (off-pivot = 0), leaving f(a) * 1 = 0
  have hsplit : ∑ b : Fin r, f b * hammingEntry r b ⟨2 ^ a.val - 1, hbound⟩ =
      f a * 1 + ∑ b ∈ Finset.univ.erase a, f b * hammingEntry r b ⟨2 ^ a.val - 1, hbound⟩ := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a)]
    congr 1
    rw [hammingEntry_pivot]
  rw [hsplit] at hpivot
  have hrest : ∑ b ∈ Finset.univ.erase a, f b * hammingEntry r b ⟨2 ^ a.val - 1, hbound⟩ = 0 := by
    apply Finset.sum_eq_zero
    intro b hb
    rw [Finset.mem_erase] at hb
    rw [hammingEntry_off_pivot (hab := hb.1), mul_zero]
  rw [hrest, add_zero, _root_.mul_one] at hpivot
  exact hpivot

/-- The check matrix entry for a ZGen generator at a Z-component column equals
hammingEntry.
    For ZGen a, the Z-component (column n + k) is hammingEntry r a k. -/
private lemma checkMatrix_ZGen_Z_part (a : Fin r) (k : Fin (2 ^ r - 1)) :
    NQubitPauliOperator.toSymplectic (ZGen r a).operators (Fin.natAdd (2 ^ r - 1) k) =
      hammingEntry r a k := by
  rw [NQubitPauliOperator.toSymplectic_Z_part]
  simp only [ZGen, hammingEntry]
  split_ifs with h
  · simp [PauliOperator.toSymplecticSingle]
  · simp [PauliOperator.toSymplecticSingle]

/-- The check matrix entry for a ZGen generator at an X-component column is 0.
-/
private lemma checkMatrix_ZGen_X_part (a : Fin r) (k : Fin (2 ^ r - 1)) :
    NQubitPauliOperator.toSymplectic (ZGen r a).operators (Fin.castAdd (2 ^ r - 1) k) = 0 := by
  rw [NQubitPauliOperator.toSymplectic_X_part]
  simp only [ZGen]
  split_ifs with h
  · simp [PauliOperator.toSymplecticSingle]
  · simp [PauliOperator.toSymplecticSingle]

/-- The check matrix entry for an XGen generator at an X-component column equals
hammingEntry. -/
private lemma checkMatrix_XGen_X_part (a : Fin r) (k : Fin (2 ^ r - 1)) :
    NQubitPauliOperator.toSymplectic (XGen r a).operators (Fin.castAdd (2 ^ r - 1) k) =
      hammingEntry r a k := by
  rw [NQubitPauliOperator.toSymplectic_X_part]
  simp only [XGen, hammingEntry]
  split_ifs with h
  · simp [PauliOperator.toSymplecticSingle]
  · simp [PauliOperator.toSymplecticSingle]

/-- The check matrix entry for an XGen generator at a Z-component column is 0.
-/
private lemma checkMatrix_XGen_Z_part (a : Fin r) (k : Fin (2 ^ r - 1)) :
    NQubitPauliOperator.toSymplectic (XGen r a).operators (Fin.natAdd (2 ^ r - 1) k) = 0 := by
  rw [NQubitPauliOperator.toSymplectic_Z_part]
  simp only [XGen]
  split_ifs with h
  · simp [PauliOperator.toSymplecticSingle]
  · simp [PauliOperator.toSymplecticSingle]

/-- The check matrix entry for the Z-component column of a generatorsList entry.
-/
private lemma checkMatrix_generatorsList_Z
    (idx : Fin (generatorsList r).length) (k : Fin (2 ^ r - 1)) :
    NQubitPauliGroupElement.checkMatrix (generatorsList r) idx
      (Fin.natAdd (2 ^ r - 1) k) =
      if hlt : idx.val < r then hammingEntry r ⟨idx.val, hlt⟩ k else 0 := by
  have hlen := generatorsList_length r
  simp only [NQubitPauliGroupElement.checkMatrix]
  by_cases hlt : idx.val < r
  · have : (generatorsList r).get idx = ZGen r ⟨idx.val, hlt⟩ := by
      simp only [generatorsList, List.get_ofFn, allGen]; simp [hlt]
    rw [this, dif_pos hlt, checkMatrix_ZGen_Z_part]
  · have h_idx : idx.val - r < r := by omega
    have : (generatorsList r).get idx = XGen r ⟨idx.val - r, h_idx⟩ := by
      simp only [generatorsList, List.get_ofFn, allGen]
      simp [show ¬(idx.val < r) from hlt]
    rw [this, dif_neg hlt, checkMatrix_XGen_Z_part]

/-- The check matrix entry for the X-component column of a generatorsList entry.
-/
private lemma checkMatrix_generatorsList_X
    (idx : Fin (generatorsList r).length) (k : Fin (2 ^ r - 1)) :
    NQubitPauliGroupElement.checkMatrix (generatorsList r) idx
      (Fin.castAdd (2 ^ r - 1) k) =
      if hlt : idx.val < r then 0
      else hammingEntry r ⟨idx.val - r,
        by have := generatorsList_length r; omega⟩ k := by
  have hlen := generatorsList_length r
  simp only [NQubitPauliGroupElement.checkMatrix]
  by_cases hlt : idx.val < r
  · have : (generatorsList r).get idx = ZGen r ⟨idx.val, hlt⟩ := by
      simp only [generatorsList, List.get_ofFn, allGen]; simp [hlt]
    rw [this, dif_pos hlt, checkMatrix_ZGen_X_part]
  · have h_idx : idx.val - r < r := by omega
    have : (generatorsList r).get idx = XGen r ⟨idx.val - r, h_idx⟩ := by
      simp only [generatorsList, List.get_ofFn, allGen]
      simp [show ¬(idx.val < r) from hlt]
    rw [this, dif_neg hlt, checkMatrix_XGen_X_part]

/-- The sum ∑_{idx} f(idx) * checkMatrix(idx, Z-col k) = ∑_{a:Fin r} f(a) *
hammingEntry(a,k). -/
private lemma sum_checkMatrix_Z_eq
    (f : Fin (generatorsList r).length → ZMod 2)
    (k : Fin (2 ^ r - 1)) :
    ∑ idx, f idx * NQubitPauliGroupElement.checkMatrix
      (generatorsList r) idx (Fin.natAdd (2 ^ r - 1) k) =
    ∑ a : Fin r, f ⟨a.val,
      by rw [generatorsList_length]; omega⟩ * hammingEntry r a k := by
  have hrewrite :
      (∑ idx, f idx * NQubitPauliGroupElement.checkMatrix
        (generatorsList r) idx (Fin.natAdd (2 ^ r - 1) k)) =
      ∑ idx, if hlt : idx.val < r
        then f idx * hammingEntry r ⟨idx.val, hlt⟩ k
        else 0 := by
    apply Finset.sum_congr rfl
    intro idx _
    rw [checkMatrix_generatorsList_Z]
    split_ifs <;> simp
  rw [hrewrite, Finset.sum_dite]
  simp only [Finset.sum_const_zero]
  let p : Fin (generatorsList r).length → Prop := fun i => i.val < r
  let s : Finset (Fin (generatorsList r).length) :=
    Finset.filter p Finset.univ
  have hs : ∀ x : Fin (generatorsList r).length, x ∈ s ↔ p x := by
    intro x; simp [s, p, Finset.mem_filter]
  simp +zetaDelta only [Finset.univ_eq_attach, add_zero] at *
  refine Finset.sum_bij (fun x _ => ⟨x.val, by grind +qlia⟩) ?_ ?_ ?_ ?_ <;>
    simp_all +decide only [Fin.natAdd_eq_addNat, Finset.mem_attach, Finset.mem_univ,
      Fin.mk.injEq, forall_const, Subtype.forall, Subtype.mk.injEq, exists_const,
      Subtype.exists, Fin.eta, implies_true]
  · exact fun a ha b hb hab => Fin.ext hab
  · exact fun b => ⟨⟨b, by rw [generatorsList_length]; linarith [Fin.is_lt b]⟩,
      by simp +decide⟩

/-- The sum ∑_{idx} f(idx) * checkMatrix(idx, X-col k) = ∑_{a:Fin r} f(r+a) *
hammingEntry(a,k). -/
private lemma sum_checkMatrix_X_eq
    (f : Fin (generatorsList r).length → ZMod 2)
    (k : Fin (2 ^ r - 1)) :
    ∑ idx, f idx * NQubitPauliGroupElement.checkMatrix
      (generatorsList r) idx (Fin.castAdd (2 ^ r - 1) k) =
    ∑ a : Fin r, f ⟨r + a.val,
      by rw [generatorsList_length]; omega⟩ * hammingEntry r a k := by
  have hrewrite :
      (∑ idx, f idx * NQubitPauliGroupElement.checkMatrix
        (generatorsList r) idx (Fin.castAdd (2 ^ r - 1) k)) =
      ∑ idx, if hlt : idx.val < r
        then 0
        else f idx * hammingEntry r
          ⟨idx.val - r, by have := generatorsList_length r; omega⟩ k := by
    apply Finset.sum_congr rfl
    intro idx _
    rw [checkMatrix_generatorsList_X]
    split_ifs <;> simp
  rw [hrewrite, Finset.sum_dite]
  simp only [Finset.sum_const_zero]
  let p : Fin (generatorsList r).length → Prop := fun i => r ≤ i.val
  let s : Finset (Fin (generatorsList r).length) :=
    Finset.filter p Finset.univ
  have hs : ∀ x : Fin (generatorsList r).length, x ∈ s ↔ p x := by
    intro x; simp [s, p, Finset.mem_filter]
  simp only [Finset.univ_eq_attach, zero_add]
  refine Finset.sum_bij (fun x _ => ⟨x.val - r, by
    have hxge : r ≤ x.val := by
      exact le_of_not_gt (by simpa [p] using x.property)
    have hxlt : x.val < (generatorsList r).length := x.1.isLt
    have hlen : (generatorsList r).length = 2 * r := generatorsList_length r
    have hxlt' : x.val < 2 * r := by simpa [hlen] using hxlt
    omega⟩) ?_ ?_ ?_ ?_ <;>
    simp +decide only [Finset.mem_attach, Finset.mem_univ, implies_true, Fin.mk.injEq,
      forall_const, Subtype.forall, not_lt, Finset.mem_filter, true_and, Subtype.mk.injEq,
      exists_const, Subtype.exists, mul_eq_mul_right_iff]
  · exact fun a ha b hb hab =>
      Fin.ext <| by linarith [Nat.sub_add_cancel ha, Nat.sub_add_cancel hb]
  · intro b; use ⟨r + b, by rw [generatorsList_length]; linarith [Fin.is_lt b]⟩; aesop
  · exact fun a ha =>
      Or.inl <| congr_arg f <| Fin.ext <| by simp +decide [Nat.add_sub_of_le ha]

/-- The check-matrix rows of the quantum Hamming generators are linearly
independent. -/
theorem rowsLinearIndependent_generatorsList :
    NQubitPauliGroupElement.rowsLinearIndependent (generatorsList r) := by
  rw [NQubitPauliGroupElement.rowsLinearIndependent_iff_forall]
  intro f hf
  have hlen : (generatorsList r).length = 2 * r := generatorsList_length r
  -- Extract pointwise zero condition
  have hzero : ∀ j, ∑ idx, f idx *
      NQubitPauliGroupElement.checkMatrix (generatorsList r) idx j = 0 := by
    intro j; have := congr_fun hf j
    simp only [Pi.zero_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this; exact this
  -- Step 1: f(a) = 0 for a < r (ZGen coefficients)
  have hfZ : ∀ a : Fin r, f ⟨a.val, by rw [hlen]; omega⟩ = 0 := by
    have key : ∀ k : Fin (2 ^ r - 1),
        ∑ a : Fin r, f ⟨a.val, by rw [hlen]; omega⟩ * hammingEntry r a k = 0 := by
      intro k; rw [← sum_checkMatrix_Z_eq]; exact hzero _
    exact congr_fun (hammingRows_linearIndependent r _ key)
  -- Step 2: f(r + a) = 0 for a < r (XGen coefficients)
  have hfX : ∀ a : Fin r, f ⟨r + a.val, by rw [hlen]; omega⟩ = 0 := by
    have key : ∀ k : Fin (2 ^ r - 1),
        ∑ a : Fin r, f ⟨r + a.val, by rw [hlen]; omega⟩ * hammingEntry r a k = 0 := by
      intro k; rw [← sum_checkMatrix_X_eq]; exact hzero _
    exact congr_fun (hammingRows_linearIndependent r _ key)
  -- Combine: every coefficient is zero
  funext idx
  simp only [Pi.zero_apply]
  by_cases hlt : idx.val < r
  · exact hfZ ⟨idx.val, hlt⟩
  · have h_idx : idx.val - r < r := by omega
    have := hfX ⟨idx.val - r, h_idx⟩
    convert this using 2
    simp [Fin.ext_iff]; omega

/-- The quantum Hamming generator list is an independent generating set. -/
theorem GeneratorsIndependent_generatorsList :
    GeneratorsIndependent (2 ^ r - 1) (generatorsList r) :=
  GeneratorsIndependent_of_rowsLinearIndependent (rowsLinearIndependent_generatorsList r)

/-!
## No `−I` in the stabilizer subgroup

`CSS.negIdentity_not_mem_closure_union` needs only the Z/X split, the typing
lemmas and the cross-commutation.
-/

/-- The quantum Hamming stabilizer does not contain −I. -/
theorem negIdentity_not_mem (hr : 3 ≤ r) :
    negIdentity (2 ^ r - 1) ∉ subgroup r := by
  simpa [subgroup, generators] using
    CSS.negIdentity_not_mem_closure_union (ZGenerators r) (XGenerators r)
      (ZGenerators_are_ZType r) (XGenerators_are_XType r) (ZGenerators_commute_XGenerators r hr)

/-!
## Bundled `StabilizerGroup (2^r − 1)`
-/

/-- The quantum Hamming code as a `StabilizerGroup (2^r − 1)`. -/
noncomputable def stabilizerGroup (hr : 3 ≤ r) : StabilizerGroup (2 ^ r - 1) :=
  mkStabilizerFromGenerators (2 ^ r - 1) (generatorsList r)
    (by rw [listToSet_generatorsList]; exact generators_commute r hr)
    (by rw [listToSet_generatorsList]; exact negIdentity_not_mem r hr)

/-- The stabilizer subgroup is the closure of the generator set. -/
lemma stabilizerGroup_toSubgroup_eq (hr : 3 ≤ r) :
    (stabilizerGroup r hr).toSubgroup = subgroup r := by
  simp only [stabilizerGroup, mkStabilizerFromGenerators, subgroup]
  rw [listToSet_generatorsList]

/-!
## The bare code `Code[[2^r − 1, 2^r − 1 − 2r]]`

`2r` independent, pairwise commuting generators on `2^r − 1` qubits:
`2^r − 1 − 2r` logical qubits, at least one since `2r + 1 ≤ 2^r` for `r ≥ 3`.
-/

/-- `2r + 1 ≤ 2^r` for `r ≥ 3`, so the `2r` generators fit on `2^r − 1`
qubits. -/
lemma two_mul_add_one_le_two_pow (hr : 3 ≤ r) : 2 * r + 1 ≤ 2 ^ r := by
  induction r, hr using Nat.le_induction with
  | base => decide
  | succ m _ ih => rw [pow_succ]; omega

/-- The `2r` Hamming checks as a presentation of a
`[[2^r − 1, 2^r − 1 − 2r]]` code. -/
def presentation (hr : 3 ≤ r) :
    StabilizerCode.Presentation (2 ^ r - 1) (2 ^ r - 1 - 2 * r) where
  hk := Nat.sub_le _ _
  generatorsList := generatorsList r
  generators_length := by
    have := two_mul_add_one_le_two_pow r hr
    rw [generatorsList_length]; omega
  generators_phaseZero := AllPhaseZero_generatorsList r
  generators_independent := rowsLinearIndependent_generatorsList r
  generators_commute := by rw [listToSet_generatorsList]; exact generators_commute r hr
  closure_no_neg_identity := by rw [listToSet_generatorsList]; exact negIdentity_not_mem r hr

/-- The quantum Hamming code as a stabilizer code
`[[2^r − 1, 2^r − 1 − 2r]]`. -/
noncomputable def stabilizerCode (hr : 3 ≤ r) : Code[[2 ^ r - 1, 2 ^ r - 1 - 2 * r]] :=
  (presentation r hr).toCode

/-- The stabilizer code's subgroup is the closure of the generator set. -/
lemma stabilizerCode_toSubgroup_eq (hr : 3 ≤ r) :
    (stabilizerCode r hr).toStabilizerGroup.toSubgroup = subgroup r :=
  stabilizerGroup_toSubgroup_eq r hr

/-! ## Distance 3

### No nontrivial logical of weight 1 or 2

Row `a` of the Hamming check matrix, read as a set of qubits, is the support of
both the `Z`-check `ZGen a` and the `X`-check `XGen a` (the code is self-dual
CSS). Column `k` of the check matrix is the binary expansion of `k + 1`, a
nonzero number below `2^r`. So no column is zero, and two distinct columns
differ in some bit, which lies below `r`. -/

/-- Row `a` of the Hamming check matrix as a support: the qubits `k` with bit
`a` of `k + 1` set. -/
def row (a : Fin r) : Finset (Fin (2 ^ r - 1)) :=
  Finset.univ.filter fun k => (k.val + 1).testBit a.val

lemma mem_row {a : Fin r} {k : Fin (2 ^ r - 1)} :
    k ∈ row r a ↔ (k.val + 1).testBit a.val = true := by
  simp [row]

/-- The `Z`-checks are `Z` along the Hamming rows. -/
lemma ZGen_eq_zOn (a : Fin r) : ZGen r a = zOn (row r a) := by
  simp [ZGen, zOn, ofOperator, row]

/-- The `X`-checks are `X` along the same rows. -/
lemma XGen_eq_xOn (a : Fin r) : XGen r a = xOn (row r a) := by
  simp [XGen, xOn, ofOperator, row]

/-- Each `Z`-check along a Hamming row is a generator. -/
lemma zOn_row_mem (a : Fin r) : zOn (row r a) ∈ generators r :=
  Set.mem_union_left _ ⟨a, ZGen_eq_zOn r a⟩

/-- Each `X`-check along a Hamming row is a generator. -/
lemma xOn_row_mem (a : Fin r) : xOn (row r a) ∈ generators r :=
  Set.mem_union_right _ ⟨a, XGen_eq_xOn r a⟩

/-- A bit set in a column `k + 1 < 2^r` lies below `r`. -/
private lemma lt_of_testBit {k : Fin (2 ^ r - 1)} {b : ℕ}
    (hb : (k.val + 1).testBit b = true) : b < r := by
  by_contra h
  have hk : k.val + 1 < 2 ^ b :=
    calc k.val + 1 < 2 ^ r := by have := k.isLt; omega
      _ ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) (not_lt.mp h)
  rw [Nat.testBit_lt_two_pow hk] at hb
  exact Bool.false_ne_true hb

/-- Every qubit lies on some Hamming row (no zero column): `k + 1 ≠ 0` has a
set bit. -/
lemma row_cover : ∀ k : Fin (2 ^ r - 1), ∃ a, k ∈ row r a := by
  intro k
  obtain ⟨b, hb⟩ := Nat.exists_testBit_of_ne_zero (Nat.succ_ne_zero k.val)
  exact ⟨⟨b, lt_of_testBit r hb⟩, (mem_row r).mpr hb⟩

/-- Any two distinct qubits are separated by some Hamming row (distinct
columns): `k + 1` and `j + 1` differ in some bit. -/
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

/-- `X` on `S` and `Z` on `T` meet on `S ∩ T`, which decides commutation. -/
private lemma symplecticInner_xOn_zOn {m : ℕ} (S T : Finset (Fin m)) :
    NQubitPauliOperator.symplecticInner (xOn S).operators (zOn T).operators =
      ((S ∩ T).card : ZMod 2) := by
  have h : ∀ k, PauliOperator.symplecticProductSingle ((xOn S).operators k)
      ((zOn T).operators k) = if k ∈ S ∩ T then 1 else 0 := by
    intro k
    by_cases hS : k ∈ S <;> by_cases hT : k ∈ T <;>
      simp [hS, hT, PauliOperator.symplecticProductSingle, PauliOperator.toSymplecticSingle]
  rw [NQubitPauliOperator.symplecticInner, Finset.sum_congr rfl fun k _ => h k,
    Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.univ_inter]

/-- `X` on `S` has weight `|S|`. -/
private lemma weight_xOn {m : ℕ} (S : Finset (Fin m)) : weight (xOn S) = S.card := by
  simp [xOn, NQubitPauliOperator.weight, NQubitPauliOperator.support]

/-- `X` on a support is X-type. -/
private lemma xOn_isXType {m : ℕ} (S : Finset (Fin m)) : IsXTypeElement (xOn S) := by
  refine ⟨rfl, fun k => ?_⟩
  by_cases hk : k ∈ S <;> simp [hk, PauliOperator.IsXType]

/-- `Z` on a support is Z-type. -/
private lemma zOn_isZType {m : ℕ} (S : Finset (Fin m)) : IsZTypeElement (zOn S) := by
  refine ⟨rfl, fun k => ?_⟩
  by_cases hk : k ∈ S <;> simp [hk, PauliOperator.IsZType]

/-- There are more than three qubits (`2^r − 1 ≥ 7`). -/
private lemma three_lt (hr : 3 ≤ r) : 3 < 2 ^ r - 1 := by
  have := two_mul_add_one_le_two_pow r hr
  omega

/-- `{0, 1, 2}` has three qubits. -/
lemma card_minWeightSupport (hr : 3 ≤ r) : (minWeightSupport r).card = 3 := by
  have h : minWeightSupport r = Finset.Iio ⟨3, three_lt r hr⟩ := by
    ext k
    simp [minWeightSupport, Fin.lt_def]
  rw [h, Fin.card_Iio]

/-- `{0, 1, 2}` meets every Hamming row in an even number of qubits. Read off
in `ℕ`, the meet is `{m < 3 | bit a of m + 1}`: `{0, 2}` for `a = 0`, `{1, 2}`
for `a = 1`, and empty for `a ≥ 2`, since `m + 1 < 4`. -/
lemma even_card_minWeightSupport_inter_row (hr : 3 ≤ r) (a : Fin r) :
    Even (minWeightSupport r ∩ row r a).card := by
  have h3 := three_lt r hr
  have hmap : (minWeightSupport r ∩ row r a).map Fin.valEmbedding =
      (Finset.range 3).filter fun m => (m + 1).testBit a.val = true := by
    ext m
    simp only [Finset.mem_map, Finset.mem_inter, minWeightSupport, row, Finset.mem_filter,
      Finset.mem_univ, true_and, Fin.valEmbedding_apply, Finset.mem_range]
    constructor
    · rintro ⟨k, ⟨hk3, hka⟩, rfl⟩
      exact ⟨hk3, hka⟩
    · rintro ⟨hm3, hma⟩
      exact ⟨⟨m, by omega⟩, ⟨hm3, hma⟩, rfl⟩
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

lemma minWeightLogical_weight (hr : 3 ≤ r) : weight (minWeightLogical r) = 3 := by
  rw [minWeightLogical, weight_xOn, card_minWeightSupport r hr]

lemma minWeightLogical_mem_centralizer (hr : 3 ≤ r) :
    minWeightLogical r ∈ centralizer (stabilizerGroup r hr) := by
  rw [StabilizerGroup.mem_centralizer_iff_closure _ _ (generators r)
    (stabilizerGroup_toSubgroup_eq r hr)]
  intro s hs
  simp only [generators, ZGenerators, XGenerators, Set.mem_union, Set.mem_range] at hs
  rcases hs with ⟨a, rfl⟩ | ⟨a, rfl⟩
  · refine ((NQubitPauliOperator.commutes_iff_symplectic_inner_zero _ _).mpr ?_).symm
    rw [ZGen_eq_zOn, minWeightLogical, symplecticInner_xOn_zOn,
      ZMod.natCast_eq_zero_iff_even]
    exact even_card_minWeightSupport_inter_row r hr a
  · exact XType_commutes (XGenerators_are_XType r _ ⟨a, rfl⟩) (xOn_isXType _)

lemma minWeightPartner_mem_centralizer (hr : 3 ≤ r) :
    minWeightPartner r ∈ centralizer (stabilizerGroup r hr) := by
  rw [StabilizerGroup.mem_centralizer_iff_closure _ _ (generators r)
    (stabilizerGroup_toSubgroup_eq r hr)]
  intro s hs
  simp only [generators, ZGenerators, XGenerators, Set.mem_union, Set.mem_range] at hs
  rcases hs with ⟨a, rfl⟩ | ⟨a, rfl⟩
  · exact ZType_commutes (ZGenerators_are_ZType r _ ⟨a, rfl⟩) (zOn_isZType _)
  · refine (NQubitPauliOperator.commutes_iff_symplectic_inner_zero _ _).mpr ?_
    rw [XGen_eq_xOn, minWeightPartner, symplecticInner_xOn_zOn, Finset.inter_comm,
      ZMod.natCast_eq_zero_iff_even]
    exact even_card_minWeightSupport_inter_row r hr a

/-- `X` and `Z` on `{0, 1, 2}` meet on three qubits, an odd number. -/
lemma minWeightLogical_anticommutes_minWeightPartner (hr : 3 ≤ r) :
    Anticommute (minWeightLogical r) (minWeightPartner r) := by
  rw [NQubitPauliOperator.anticommutes_iff_symplectic_inner_one, minWeightLogical,
    minWeightPartner, symplecticInner_xOn_zOn, Finset.inter_self, card_minWeightSupport r hr]
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
weight `1` or `2` is a nontrivial logical; `X` on `{0, 1, 2}` is one of weight
`3`. -/
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
