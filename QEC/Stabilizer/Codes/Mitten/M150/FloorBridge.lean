/-
# M4 chain↔mask bridge — generic layer

Connects `ZMod 2` chains on the mitten qubit cells to the packed 30-bit
masks the M4 sweep layer (`FloorCore`/`FloorData`/`FloorSweep*`)
operates on.  Provides:

* `maskOf` — the canonical (GAP-ordered, little-endian) mask of a
  `M150G → ZMod 2` block chain, with its `testBit` anatomy, bounds,
  additivity, inverse `comask`, and injectivity;
* `maskOf_op` — the transfer principle: an additive chain operator whose
  basis images match a packed column table acts as `xorFold tbl` on
  masks (via `linear_ext`);
* `entrySum`/`blockMapped` — the sparse-entry form of the two check maps
  (`d2term` for `H_X`, `cmTerm` for `H_Z`) restricted to qubit blocks,
  and the 5-block XOR split of a check-row mask;
* the weight bridges: `popCntGo 30 (maskOf f) = suppCard f` and the
  block split of `chainWeight`.

The per-instance basis-image certificates live in `FloorChecksX.lean` and
`FloorChecksZ.lean`; derived forms and classification consumption live in
`FloorZSide.lean` and `FloorXSide.lean`. Design and offline validation:
`qec-lab:pipeline/attempts/mitten_150_30_10/m4_findings.md` and
`scripts/a32_m4_bridge_check.py`.
-/

import QEC.Stabilizer.Codes.Mitten.M150.Sparse
import QEC.Stabilizer.Codes.Mitten.M150.FloorData

namespace Quantum
namespace Stabilizer
namespace Homological
namespace LP
namespace M150

open scoped BigOperators

/-! ## Canonical group coordinates and the shared mask API -/

/-- A binary field element is nonzero exactly when it equals one. -/
private lemma zmod2_ne_zero : ∀ a : ZMod 2, a ≠ 0 ↔ a = 1 := by decide

/-- Index of a carrier element in the GAP order. -/
def idxOfG (g : M150G) : Nat := gapElems.idxOf g

/-- Looking up a group element by its canonical index recovers the element. -/
lemma elemOf_idxOfG : ∀ g : M150G, elemOf (idxOfG g) = g := by decide

/-- Every canonical group index is less than thirty. -/
lemma idxOfG_lt : ∀ g : M150G, idxOfG g < 30 := by decide

/-- The index of a canonical group entry is its original index. -/
lemma idxOfG_elemOf : ∀ i < 30, idxOfG (elemOf i) = i := by decide

/-- The canonical GAP ordering identifies the carrier with thirty indices. -/
def groupEnum : M150G ≃ Fin 30 where
  toFun g := ⟨idxOfG g, idxOfG_lt g⟩
  invFun i := elemOf i
  left_inv := elemOf_idxOfG
  right_inv i := Fin.ext (idxOfG_elemOf i i.isLt)

/-- The shared binary-chain encoding in the canonical GAP element order. -/
def maskOf (f : M150G → ZMod 2) : Nat := F2Mask.maskOf groupEnum f

/-- A block mask fits into thirty bits. -/
lemma maskOf_lt (f : M150G → ZMod 2) : maskOf f < 2 ^ 30 :=
  F2Mask.maskOf_lt groupEnum f

/-- A bit of the block mask reads its canonical chain coefficient. -/
lemma maskOf_testBit (f : M150G → ZMod 2) (i : Nat) :
    (maskOf f).testBit i = (decide (i < 30) && decide (f (elemOf i) = 1)) := by
  rw [maskOf, F2Mask.testBit_maskOf]
  by_cases hi : i < 30
  · simp only [hi, dif_pos, decide_true, Bool.true_and]
    change decide (f (elemOf i) ≠ 0) = decide (f (elemOf i) = 1)
    rw [decide_eq_decide]
    exact zmod2_ne_zero _
  · rw [dif_neg hi]
    simp only [hi, decide_false, Bool.false_and]

/-- The zero chain has mask zero. -/
lemma maskOf_zero : maskOf (0 : M150G → ZMod 2) = 0 :=
  F2Mask.maskOf_zero groupEnum

/-- Encoding addition of chains gives XOR of their masks. -/
lemma maskOf_add (f g : M150G → ZMod 2) :
    maskOf (f + g) = maskOf f ^^^ maskOf g := F2Mask.maskOf_add groupEnum f g

/-- Decode a mask using the same canonical GAP group coordinates. -/
def comask (m : Nat) : M150G → ZMod 2 := F2Mask.chainOfMask groupEnum m

/-- The delta chain at canonical index `i`. -/
def deltaFn (i : Nat) : M150G → ZMod 2 :=
  fun g => if g = elemOf i then 1 else 0

/-- Decoding the mask of a block chain recovers the chain. -/
lemma comask_maskOf (f : M150G → ZMod 2) : comask (maskOf f) = f :=
  F2Mask.chainOfMask_maskOf groupEnum f

/-- Encoding a bounded mask after decoding recovers the mask. -/
lemma maskOf_comask {m : Nat} (hm : m < 2 ^ 30) : maskOf (comask m) = m :=
  F2Mask.maskOf_chainOfMask groupEnum hm

/-- The zero mask decodes to the zero chain. -/
lemma comask_zero : comask 0 = (0 : M150G → ZMod 2) := by
  funext g
  simp only [comask, F2Mask.chainOfMask, Nat.zero_testBit, Bool.false_eq_true,
    ite_false, Pi.zero_apply]

/-- Decoding XOR is pointwise addition of binary chains. -/
lemma comask_xor (m₁ m₂ : Nat) :
    comask (m₁ ^^^ m₂) = comask m₁ + comask m₂ := by
  funext g
  simp only [comask, F2Mask.chainOfMask, Nat.testBit_xor, Pi.add_apply]
  cases h1 : m₁.testBit (groupEnum g) <;> cases h2 : m₂.testBit (groupEnum g) <;>
    decide

/-- A single-bit mask decodes to its canonical point mass. -/
lemma comask_bit {i : Nat} (hi : i < 30) : comask (1 <<< i) = deltaFn i := by
  funext g
  have hbit : (1 <<< i).testBit (idxOfG g) = decide (idxOfG g = i) := by
    rw [Nat.testBit_shiftLeft, testBit_one']
    rcases Nat.lt_or_ge (idxOfG g) i with h | h
    · have h1 : decide (idxOfG g ≥ i) = false := by
        rw [decide_eq_false_iff_not]
        omega
      have h2 : decide (idxOfG g = i) = false := by
        rw [decide_eq_false_iff_not]
        omega
      rw [h1, h2, Bool.false_and]
    · have h1 : decide (idxOfG g ≥ i) = true := by simpa using h
      rw [h1, Bool.true_and, decide_eq_decide]
      omega
  change (if (1 <<< i).testBit (idxOfG g) then (1 : ZMod 2) else 0) =
    if g = elemOf i then 1 else 0
  rw [hbit]
  by_cases hg : g = elemOf i
  · subst hg
    rw [idxOfG_elemOf i hi]
    simp
  · have hidx : idxOfG g ≠ i := by
      intro h
      exact hg (by rw [← h, elemOf_idxOfG g])
    simp [hg, hidx]

/-- `maskOf` is injective. -/
lemma maskOf_inj {f g : M150G → ZMod 2} (h : maskOf f = maskOf g) : f = g := by
  rw [← comask_maskOf f, h, comask_maskOf g]

/-- A zero mask means the zero chain. -/
lemma eq_zero_of_maskOf_eq_zero {f : M150G → ZMod 2} (h : maskOf f = 0) :
    f = 0 := by
  rw [← comask_maskOf f, h, comask_zero]

/-! ## §4  The operator-transfer principle -/

/-- An additive chain operator whose basis images match a packed table
acts as `xorFold tbl` on masks. -/
lemma maskOf_op {op : (M150G → ZMod 2) → (M150G → ZMod 2)}
    (hadd : ∀ f g, op (f + g) = op f + op g)
    {tbl : List Nat}
    (hbasis : ∀ i < 30, maskOf (op (deltaFn i)) = tbl.getD i 0)
    (f : M150G → ZMod 2) :
    maskOf (op f) = xorFold tbl (maskOf f) := by
  have hop0 : op 0 = 0 := by
    have h := hadd 0 0
    rw [add_zero] at h
    have h' : op 0 + 0 = op 0 + op 0 := by
      rw [add_zero]
      exact h
    exact (add_left_cancel h').symm
  have hF0 : maskOf (op (comask 0)) = 0 := by
    rw [comask_zero, hop0, maskOf_zero]
  have hFx : ∀ m₁ m₂ : Nat, maskOf (op (comask (m₁ ^^^ m₂)))
      = maskOf (op (comask m₁)) ^^^ maskOf (op (comask m₂)) := by
    intro m₁ m₂
    rw [comask_xor, hadd, maskOf_add]
  have hbit : ∀ i < 30, maskOf (op (comask (1 <<< i)))
      = xorFold tbl (1 <<< i) := by
    intro i hi
    rw [comask_bit hi, xorFold_bit]
    exact hbasis i hi
  have key : ∀ m < 2 ^ 30, maskOf (op (comask m)) = xorFold tbl m :=
    linear_ext 30 hF0 (by simp) hFx (xorFold_xor tbl) hbit
  calc maskOf (op f) = maskOf (op (comask (maskOf f))) := by
        rw [comask_maskOf]
    _ = xorFold tbl (maskOf f) := key _ (maskOf_lt f)

/-! ## §5  Blocks, embeddings, and the sparse-entry check maps -/

/-- Block `m` of a qubit chain. -/
def blockOf (c : Fin 5 × M150G → ZMod 2) (m : Fin 5) : M150G → ZMod 2 :=
  fun g => c (m, g)

/-- Embed a block chain at block `m` (zero elsewhere). -/
def embed (m : Fin 5) (f : M150G → ZMod 2) : Fin 5 × M150G → ZMod 2 :=
  fun q => if q.1 = m then f q.2 else 0

/-- Embedding a block preserves addition. -/
lemma embed_add (m : Fin 5) (f g : M150G → ZMod 2) :
    embed m (f + g) = embed m f + embed m g := by
  funext q
  simp only [embed, Pi.add_apply]
  split
  · rfl
  · rw [add_zero]

/-- Sparse-entry application of a check matrix (`E = d2term` gives the
`H_X` action `dualBfn`, `E = cmTerm` the `H_Z` action `∂₁`). -/
def entrySum (E : Fin 2 × M150G → Fin 5 × M150G → ZMod 2)
    (c : Fin 5 × M150G → ZMod 2) (p : Fin 2 × M150G) : ZMod 2 :=
  ∑ q : Fin 5 × M150G, c q * E p q

/-- Applying a check matrix preserves addition of chains. -/
lemma entrySum_add (E) (c c' : Fin 5 × M150G → ZMod 2) (p : Fin 2 × M150G) :
    entrySum E (c + c') p = entrySum E c p + entrySum E c' p := by
  simp only [entrySum, Pi.add_apply, add_mul]
  exact Finset.sum_add_distrib

/-- `dualBfn` is the `d2term` entry sum. -/
lemma dualBfn_eq_entrySum (c : Fin 5 × M150G → ZMod 2) (p : Fin 2 × M150G) :
    dualBfn c p = entrySum d2term c p := rfl

/-- `∂₁` is the `cmTerm` entry sum. -/
lemma boundary1_eq_entrySum (c : Fin 5 × M150G → ZMod 2) (p : Fin 2 × M150G) :
    m150Complex.boundary1 c p = entrySum cmTerm c p := by
  rw [HomologicalCode.boundary1_apply_eq_sum]
  exact Finset.sum_congr rfl fun q _ => by rw [boundary1_single_apply]

/-- The block decomposition of a qubit chain, pointwise. -/
lemma sum_embed_blockOf (c : Fin 5 × M150G → ZMod 2) (q : Fin 5 × M150G) :
    c q = ∑ m : Fin 5, embed m (blockOf c m) q := by
  obtain ⟨mq, g⟩ := q
  simp only [embed, blockOf]
  rw [Finset.sum_ite_eq]
  simp

/-- Entry sums split over the five blocks. -/
lemma entrySum_sum_blocks (E) (c : Fin 5 × M150G → ZMod 2)
    (p : Fin 2 × M150G) :
    entrySum E c p = ∑ m : Fin 5, entrySum E (embed m (blockOf c m)) p := by
  have h1 : entrySum E c p
      = ∑ q : Fin 5 × M150G, (∑ m : Fin 5, embed m (blockOf c m) q) * E p q := by
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [← sum_embed_blockOf]
  rw [h1]
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  rfl

/-- Check-row map of one block through the entry function. -/
def blockMapped (E : Fin 2 × M150G → Fin 5 × M150G → ZMod 2) (idx : Fin 2)
    (m : Fin 5) (f : M150G → ZMod 2) : M150G → ZMod 2 :=
  fun y => entrySum E (embed m f) (idx, y)

/-- Every block of a check map preserves addition. -/
lemma blockMapped_add (E) (idx : Fin 2) (m : Fin 5)
    (f g : M150G → ZMod 2) :
    blockMapped E idx m (f + g) = blockMapped E idx m f + blockMapped E idx m g := by
  funext y
  simp only [blockMapped, Pi.add_apply]
  rw [embed_add, entrySum_add]

/-- A block map on a point mass is the corresponding check entry. -/
lemma blockMapped_delta (E : Fin 2 × M150G → Fin 5 × M150G → ZMod 2)
    (idx : Fin 2) (m : Fin 5) (i : Nat) :
    blockMapped E idx m (deltaFn i) = fun y => E (idx, y) (m, elemOf i) := by
  funext y
  unfold blockMapped entrySum embed deltaFn
  rw [Finset.sum_eq_single (m, elemOf i)]
  · simp
  · rintro ⟨n, g⟩ _ hne
    by_cases hn : n = m
    · subst n
      have hg : g ≠ elemOf i := by
        intro h
        exact hne (Prod.ext rfl h)
      simp only [ite_true, hg, ite_false, zero_mul]
    · simp only [hn, ite_false, zero_mul]
  · simp

/-- `maskOf`-level 5-block split of a check row. -/
lemma maskOf_entrySum_blocks (E) (idx : Fin 2) (c : Fin 5 × M150G → ZMod 2) :
    maskOf (fun y => entrySum E c (idx, y))
      = maskOf (blockMapped E idx 0 (blockOf c 0))
        ^^^ (maskOf (blockMapped E idx 1 (blockOf c 1))
        ^^^ (maskOf (blockMapped E idx 2 (blockOf c 2))
        ^^^ (maskOf (blockMapped E idx 3 (blockOf c 3))
        ^^^ maskOf (blockMapped E idx 4 (blockOf c 4))))) := by
  have h1 : (fun y => entrySum E c (idx, y))
      = blockMapped E idx 0 (blockOf c 0)
        + (blockMapped E idx 1 (blockOf c 1)
        + (blockMapped E idx 2 (blockOf c 2)
        + (blockMapped E idx 3 (blockOf c 3)
        + blockMapped E idx 4 (blockOf c 4)))) := by
    funext y
    rw [entrySum_sum_blocks]
    simp only [Pi.add_apply, blockMapped]
    rw [Fin.sum_univ_five]
    ring
  rw [h1, maskOf_add, maskOf_add, maskOf_add, maskOf_add]

/-! ## §6  Weight bridges -/

/-- Support size of a block chain. -/
def suppCard (f : M150G → ZMod 2) : ℕ :=
  (Finset.univ.filter fun g => f g ≠ 0).card

/-- The fueled popcount of a block mask is the block's support size. -/
lemma popCntGo_maskOf (f : M150G → ZMod 2) :
    popCntGo 30 (maskOf f) = suppCard f := by
  rw [popCntGo_eq_bitCount]
  exact (F2Mask.card_support_eq_bitCount groupEnum f).symm

/-- The chain weight splits over the five blocks. -/
lemma chainWeight_eq_sum_suppCard (c : Fin 5 × M150G → ZMod 2) :
    m150Complex.chainWeight c = ∑ m : Fin 5, suppCard (blockOf c m) := by
  have h0 : m150Complex.chainWeight c
      = (Finset.univ.filter fun q : Fin 5 × M150G => c q ≠ 0).card := rfl
  rw [h0, Finset.card_filter]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [suppCard, Finset.card_filter]
  rfl

end M150
end LP
end Homological
end Stabilizer
end Quantum
