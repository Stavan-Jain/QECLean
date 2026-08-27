/-
# A22: linearity and packed-mask bridges for the light classification

The 𝔽₂-linear layer between the semantic (ε, δ)-extraction of
`LightSite.lean` and the packed certificate data of `LightCertData.lean`:

* `maskFun*` unpackers with XOR/zero laws, and the `packChain` /
  `maskFun150` round trip;
* additivity of the (ε, δ)-data in the chain and of `f ↦ deltaData (∂₂ f)`;
* the generic selector-XOR fold `xorSelTab` and its `testBit`-as-sum
  lemma — the transposed-syndrome engine behind both the pivot
  orthogonality checks (`COLPACK` columns) and the generator-preimage
  identities (`DGEN` rows);
* the two semantic `native_decide` bridges tying `COLPACK`/`DGEN` to
  `deltaData ∘ ∂₂` on the 75-point basis, and their `funLiftF2` lifts:
  every pivot functional with vanishing column fold annihilates every
  boundary's δ-data (`pairW_boundary`), boundary δ-data is the `DGEN`
  row fold of the 2-chain mask (`deltaData_boundary_mask`), and paired
  fibers of a boundary share ε-coordinates (`hV_boundary_eq_hU`).
-/

import QEC.Stabilizer.Codes.BivariateBicycle.Z5Z15F2A6.ClassData
import QEC.Stabilizer.Codes.BivariateBicycle.Z5Z15F2A6.LightSite
import QEC.Stabilizer.Codes.BivariateBicycle.Z5Z15F2A6.LightCertData

namespace Quantum
namespace Stabilizer
namespace Homological
namespace BB
namespace Z5Z15F2A6

open scoped BigOperators

set_option maxRecDepth 4096

/-! ## Mask unpackers -/

/-- Unpack a `Nat` as αβ-data (120 bits). -/
def maskFun120 (m : ℕ) : Fin 120 → ZMod 2 := fun p =>
  if m.testBit p.val then 1 else 0

/-- Unpack a `Nat` as a 2-chain (75 bits, `cell2Idx` order). -/
def maskFun75 (m : ℕ) : G150 → ZMod 2 := fun g =>
  if m.testBit (cell2Idx g) then 1 else 0

/-- Unpack a `Nat` as an h-vector (15 bits). -/
def maskFun15 (m : ℕ) : Fin 15 → ZMod 2 := fun s =>
  if m.testBit s.val then 1 else 0

/-- Unpack a `Nat` as a 1-chain pair (150 bits, `cellIdx` order). -/
def maskFun150 (m : ℕ) : G150 × Fin 2 → ZMod 2 := fun p =>
  if m.testBit (cellIdx p) then 1 else 0

lemma ite_xor_split (x y : Bool) :
    (if (x ^^ y) then (1 : ZMod 2) else 0)
      = (if x then (1 : ZMod 2) else 0) + (if y then 1 else 0) := by
  cases x <;> cases y <;> decide

lemma maskFun120_xor (a b : ℕ) :
    maskFun120 (a ^^^ b) = maskFun120 a + maskFun120 b := by
  funext p
  simp only [maskFun120, Nat.testBit_xor, Pi.add_apply]
  exact ite_xor_split _ _

lemma maskFun120_zero : maskFun120 0 = 0 := by
  funext p
  simp [maskFun120]

/-! ## Additivity of the (ε, δ)-extraction -/

lemma hU_add (b₁ b₂ : G150 × Fin 2 → ZMod 2) (s : Fin 15) :
    hU (b₁ + b₂) s = hU b₁ s + hU b₂ s := by
  simp only [hU, Pi.add_apply]
  exact Finset.sum_add_distrib

lemma hV_add (b₁ b₂ : G150 × Fin 2 → ZMod 2) (s : Fin 15) :
    hV (b₁ + b₂) s = hV b₁ s + hV b₂ s := by
  simp only [hV, Pi.add_apply]
  exact Finset.sum_add_distrib

lemma deltaData_add (b₁ b₂ : G150 × Fin 2 → ZMod 2) :
    deltaData (b₁ + b₂) = deltaData b₁ + deltaData b₂ := by
  funext p
  simp only [deltaData, dU, dV, Pi.add_apply]
  split <;> ring

lemma deltaData_zero : deltaData (0 : G150 × Fin 2 → ZMod 2) = 0 := by
  funext p
  simp only [deltaData, dU, dV, Pi.zero_apply]
  split <;> simp

/-- `∂₂` of the zero chain (computable form). -/
lemma bbBoundary2Fn_zero :
    bbBoundary2Fn a150 b150 (0 : G150 → ZMod 2) = 0 := by
  have h : (bbChainComplex a150 b150).boundary2 0 = 0 := map_zero _
  exact h

/-! ## The pairing -/

/-- Pairing of a packed functional against αβ-data. -/
def pairW (W : ℕ) (y : Fin 120 → ZMod 2) : ZMod 2 :=
  ∑ p : Fin 120, if W.testBit p.val then y p else 0

lemma pairW_add (W : ℕ) (y₁ y₂ : Fin 120 → ZMod 2) :
    pairW W (y₁ + y₂) = pairW W y₁ + pairW W y₂ := by
  simp only [pairW, Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  split <;> simp

lemma pairW_zero (W : ℕ) : pairW W (0 : Fin 120 → ZMod 2) = 0 := by
  simp only [pairW, Pi.zero_apply]
  refine Finset.sum_eq_zero fun p _ => ?_
  split <;> rfl

/-! ## The selector-XOR fold -/

/-- XOR of `tab p` over selected `p < k`. -/
def xorSelTab (sel : ℕ → Bool) (tab : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => (if sel k then tab k else 0) ^^^ xorSelTab sel tab k

/-- Bits of the fold are the mod-2 sums of the selected tables' bits. -/
lemma xorSelTab_testBit (sel : ℕ → Bool) (tab : ℕ → ℕ) (i : ℕ) :
    ∀ k : ℕ, (if (xorSelTab sel tab k).testBit i then (1 : ZMod 2) else 0)
      = ∑ p ∈ Finset.range k,
          (if sel p then (if (tab p).testBit i then (1 : ZMod 2) else 0)
           else 0) := by
  intro k
  induction k with
  | zero => simp [xorSelTab]
  | succ k ih =>
    rw [Finset.sum_range_succ, ← ih]
    show (if ((if sel k then tab k else 0) ^^^ xorSelTab sel tab k).testBit i
        then (1 : ZMod 2) else 0) = _
    rw [Nat.testBit_xor, ite_xor_split]
    rcases hsel : sel k with _ | _
    · simp [Nat.zero_testBit]
    · rw [if_pos rfl, if_pos rfl]
      exact add_comm _ _

/-- The pivot-functional column fold: XOR of `COLPACK` at the set bits. -/
def xorFoldCols (W : ℕ) : ℕ :=
  xorSelTab W.testBit (fun p => COLPACK.getD p 0) 120

/-- The row fold of a 2-chain mask: XOR of `DGEN` at the set cells. -/
def rowFold (m : ℕ) : ℕ :=
  xorSelTab m.testBit (fun k => DGEN.getD k 0) 75

/-! ## Semantic bridges (native, on the 75-point basis) -/

/-- `COLPACK` bridge: bit `cell2Idx g` of column `p` is position `p` of
the δ-data of `∂₂ (Pi.single g 1)`. -/
lemma colpack_bridge : ∀ g : G150, ∀ p : Fin 120,
    deltaData (bbBoundary2Fn a150 b150 (Pi.single g 1)) p
      = if (COLPACK.getD p.val 0).testBit (cell2Idx g) then 1 else 0 := by
  native_decide

/-- `DGEN` bridge: the δ-data of `∂₂ (Pi.single g 1)` is the unpacked
`DGEN` row of `g`. -/
lemma dgen_bridge : ∀ g : G150, ∀ p : Fin 120,
    deltaData (bbBoundary2Fn a150 b150 (Pi.single g 1)) p
      = maskFun120 (DGEN.getD (cell2Idx g) 0) p := by
  native_decide

/-- ε-relation on the basis: paired fibers of a generator boundary share
ε-coordinates. -/
lemma eps_basis : ∀ g : G150, ∀ s : Fin 15,
    hV (bbBoundary2Fn a150 b150 (Pi.single g 1)) s
      = hU (bbBoundary2Fn a150 b150 (Pi.single g 1)) s := by
  native_decide

/-! ## `funLiftF2` lifts -/

/-- **The ε-relation**: every boundary's paired fibers share
ε-coordinates. -/
theorem hV_boundary_eq_hU (f : G150 → ZMod 2) (s : Fin 15) :
    hV (bbBoundary2Fn a150 b150 f) s = hU (bbBoundary2Fn a150 b150 f) s := by
  have h := funLiftF2
    (fun f => fun s : Fin 15 => hV (bbBoundary2Fn a150 b150 f) s)
    (fun f => fun s : Fin 15 => hU (bbBoundary2Fn a150 b150 f) s)
    ?_ ?_ ?_ ?_ ?_ f
  · exact congrFun h s
  · funext s
    show hV (bbBoundary2Fn a150 b150 0) s = 0
    rw [bbBoundary2Fn_zero]
    simp [hV]
  · funext s
    show hU (bbBoundary2Fn a150 b150 0) s = 0
    rw [bbBoundary2Fn_zero]
    simp [hU]
  · intro a b
    funext s
    show hV (bbBoundary2Fn a150 b150 (a + b)) s
      = hV (bbBoundary2Fn a150 b150 a) s + hV (bbBoundary2Fn a150 b150 b) s
    rw [bbBoundary2Fn_add]
    exact hV_add _ _ s
  · intro a b
    funext s
    show hU (bbBoundary2Fn a150 b150 (a + b)) s
      = hU (bbBoundary2Fn a150 b150 a) s + hU (bbBoundary2Fn a150 b150 b) s
    rw [bbBoundary2Fn_add]
    exact hU_add _ _ s
  · intro g
    funext s
    exact eps_basis g s

/-- **Orthogonality transfer**: a functional whose column fold vanishes
annihilates every boundary's δ-data. -/
theorem pairW_boundary (W : ℕ) (hW : xorFoldCols W = 0)
    (f : G150 → ZMod 2) :
    pairW W (deltaData (bbBoundary2Fn a150 b150 f)) = 0 := by
  refine funLiftF2
    (fun f => pairW W (deltaData (bbBoundary2Fn a150 b150 f)))
    (fun _ => (0 : ZMod 2)) ?_ rfl ?_ ?_ ?_ f
  · show pairW W (deltaData (bbBoundary2Fn a150 b150 0)) = 0
    rw [bbBoundary2Fn_zero, deltaData_zero]
    exact pairW_zero W
  · intro a b
    show pairW W (deltaData (bbBoundary2Fn a150 b150 (a + b)))
      = pairW W (deltaData (bbBoundary2Fn a150 b150 a))
        + pairW W (deltaData (bbBoundary2Fn a150 b150 b))
    rw [bbBoundary2Fn_add, deltaData_add]
    exact pairW_add _ _ _
  · intro a b
    show (0 : ZMod 2) = 0 + 0
    rw [add_zero]
  · intro g
    show pairW W (deltaData (bbBoundary2Fn a150 b150 (Pi.single g 1))) = 0
    have hsum : pairW W (deltaData (bbBoundary2Fn a150 b150 (Pi.single g 1)))
        = ∑ p ∈ Finset.range 120,
            (if W.testBit p
             then (if (COLPACK.getD p 0).testBit (cell2Idx g)
                   then (1 : ZMod 2) else 0)
             else 0) := by
      rw [pairW, ← Fin.sum_univ_eq_sum_range]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [colpack_bridge g p]
    rw [hsum, ← xorSelTab_testBit W.testBit (fun p => COLPACK.getD p 0)
      (cell2Idx g) 120]
    show (if (xorFoldCols W).testBit (cell2Idx g) then (1 : ZMod 2) else 0) = 0
    rw [hW]
    simp

/-! ## Boundary δ-data of a packed 2-chain -/

/-- Additive maps pass through `Finset` sums. -/
lemma addMap_sum {α : Type} {W : Type} [AddCommMonoid W]
    (M : (α → ZMod 2) → W) (h0 : M 0 = 0)
    (hadd : ∀ a b, M (a + b) = M a + M b)
    {ι : Type} (t : Finset ι) (F : ι → (α → ZMod 2)) :
    M (∑ i ∈ t, F i) = ∑ i ∈ t, M (F i) := by
  induction t using Finset.cons_induction with
  | empty => simpa using h0
  | cons i t hi ih => rw [Finset.sum_cons, Finset.sum_cons, hadd, ih]

/-- Decode a 2-chain cell index. -/
def g2cell (k : ℕ) : G150 := ((k / 15 : ℕ), (k % 15 : ℕ))

lemma cell2Idx_g2cell : ∀ k : Fin 75, cell2Idx (g2cell k.val) = k.val := by
  decide

lemma g2cell_cell2Idx : ∀ g : G150, g2cell (cell2Idx g) = g := by
  decide

lemma cell2Idx_lt : ∀ g : G150, cell2Idx g < 75 := by
  decide

/-- A packed 2-chain is the sum of point masses at its set bits. -/
lemma maskFun75_eq_sum (m : ℕ) :
    maskFun75 m = ∑ k ∈ Finset.range 75,
      (if m.testBit k then Pi.single (g2cell k) (1 : ZMod 2) else 0) := by
  funext g
  rw [Finset.sum_apply]
  have hg : cell2Idx g ∈ Finset.range 75 :=
    Finset.mem_range.mpr (cell2Idx_lt g)
  have hside : ∀ k ∈ Finset.range 75, k ≠ cell2Idx g →
      (if m.testBit k then Pi.single (g2cell k) (1 : ZMod 2)
       else (0 : G150 → ZMod 2)) g = 0 := by
    intro k hk hne
    have hklt : k < 75 := Finset.mem_range.mp hk
    have hgk : g2cell k ≠ g := by
      intro he
      apply hne
      have := cell2Idx_g2cell ⟨k, hklt⟩
      rw [he] at this
      exact this.symm
    rcases hb : m.testBit k with _ | _
    · rw [if_neg (by simp)]
      rfl
    · rw [if_pos rfl]
      exact Pi.single_eq_of_ne (M := fun _ : G150 => ZMod 2)
        (Ne.symm hgk) 1
  rw [Finset.sum_eq_single_of_mem (cell2Idx g) hg hside]
  show (if m.testBit (cell2Idx g) then (1 : ZMod 2) else 0)
    = (if m.testBit (cell2Idx g)
       then Pi.single (g2cell (cell2Idx g)) (1 : ZMod 2)
       else (0 : G150 → ZMod 2)) g
  rcases hb : m.testBit (cell2Idx g) with _ | _
  · rw [if_neg (by simp), if_neg (by simp)]
    rfl
  · rw [if_pos rfl, if_pos rfl, g2cell_cell2Idx g, Pi.single_eq_same]

/-- **The row-fold identity**: the δ-data of the boundary of a packed
2-chain is the unpacked `DGEN` row fold. -/
theorem deltaData_boundary_mask (m : ℕ) :
    deltaData (bbBoundary2Fn a150 b150 (maskFun75 m))
      = maskFun120 (rowFold m) := by
  funext p
  have hM0 : deltaData (bbBoundary2Fn a150 b150 (0 : G150 → ZMod 2)) = 0 := by
    rw [bbBoundary2Fn_zero, deltaData_zero]
  have hMadd : ∀ x y : G150 → ZMod 2,
      deltaData (bbBoundary2Fn a150 b150 (x + y))
        = deltaData (bbBoundary2Fn a150 b150 x)
          + deltaData (bbBoundary2Fn a150 b150 y) := by
    intro x y
    rw [bbBoundary2Fn_add, deltaData_add]
  rw [maskFun75_eq_sum,
    addMap_sum (fun x => deltaData (bbBoundary2Fn a150 b150 x)) hM0 hMadd,
    Finset.sum_apply]
  have hterm : ∀ k ∈ Finset.range 75,
      deltaData (bbBoundary2Fn a150 b150
        (if m.testBit k then Pi.single (g2cell k) (1 : ZMod 2) else 0)) p
      = (if m.testBit k
         then (if (DGEN.getD k 0).testBit p.val then (1 : ZMod 2) else 0)
         else 0) := by
    intro k hk
    have hklt : k < 75 := Finset.mem_range.mp hk
    rcases hbit : m.testBit k with _ | _
    · rw [if_neg (by simp), if_neg (by simp), hM0]
      rfl
    · rw [if_pos rfl, if_pos rfl]
      have hbr := dgen_bridge (g2cell k) p
      rw [hbr]
      have hidx : cell2Idx (g2cell k) = k := cell2Idx_g2cell ⟨k, hklt⟩
      rw [hidx]
      rfl
  rw [Finset.sum_congr rfl hterm,
    ← xorSelTab_testBit m.testBit (fun k => DGEN.getD k 0) p.val 75]
  rfl

/-! ## Chain packing and the round trip -/

/-- Decode a 1-chain cell index (total; inverse of `cellIdx` below 150). -/
def lightCoord (q : ℕ) : G150 × Fin 2 :=
  ((((q % 75) / 15 : ℕ), ((q % 75) % 15 : ℕ)),
    ⟨(q / 75) % 2, Nat.mod_lt _ (by norm_num)⟩)

lemma lightCoord_cellIdx : ∀ p : G150 × Fin 2, lightCoord (cellIdx p) = p := by
  decide

lemma cellIdx_lt_150 : ∀ p : G150 × Fin 2, cellIdx p < 150 := by
  decide

/-- Pack the first `k` cells of a 1-chain pair. -/
def packChainUpTo (b : G150 × Fin 2 → ZMod 2) : ℕ → ℕ
  | 0 => 0
  | k + 1 => (if b (lightCoord k) ≠ 0 then 1 <<< k else 0) ^^^ packChainUpTo b k

/-- The packed mask of a 1-chain pair. -/
def packChain (b : G150 × Fin 2 → ZMod 2) : ℕ := packChainUpTo b 150

lemma packChainUpTo_testBit (b : G150 × Fin 2 → ZMod 2) :
    ∀ k i : ℕ, (packChainUpTo b k).testBit i
      = (decide (i < k) && decide (b (lightCoord i) ≠ 0)) := by
  intro k
  induction k with
  | zero =>
    intro i
    simp [packChainUpTo]
  | succ k ih =>
    intro i
    show ((if b (lightCoord k) ≠ 0 then 1 <<< k else 0)
        ^^^ packChainUpTo b k).testBit i = _
    rw [Nat.testBit_xor, ih i]
    by_cases hik : i = k
    · subst hik
      have h2 : ¬ i < i := by omega
      have h3 : i < i + 1 := by omega
      simp only [h2, decide_false, Bool.false_and, Bool.xor_false, h3,
        decide_true, Bool.true_and]
      split
      · next hb =>
        simp [Nat.one_shiftLeft, Nat.testBit_two_pow, hb]
      · next hb =>
        simp [Nat.zero_testBit, hb]
    · have hbit0 : (if b (lightCoord k) ≠ 0 then 1 <<< k else 0).testBit i
          = false := by
        split
        · simp [Nat.one_shiftLeft, Nat.testBit_two_pow, Ne.symm hik]
        · simp [Nat.zero_testBit]
      rw [hbit0, Bool.false_xor]
      congr 1
      simp only [decide_eq_decide]
      omega

/-- **Round trip**: unpacking the packed mask restores the chain. -/
theorem maskFun150_packChain (b : G150 × Fin 2 → ZMod 2) :
    maskFun150 (packChain b) = b := by
  funext p
  show (if (packChainUpTo b 150).testBit (cellIdx p) then (1 : ZMod 2) else 0)
    = b p
  rw [packChainUpTo_testBit b 150 (cellIdx p)]
  have hlt : cellIdx p < 150 := cellIdx_lt_150 p
  have hco : lightCoord (cellIdx p) = p := lightCoord_cellIdx p
  simp only [hlt, decide_true, Bool.true_and, hco]
  have hval : ∀ a : ZMod 2, (if decide (a ≠ 0) = true then (1 : ZMod 2) else 0) = a := by
    decide
  exact hval (b p)

end Z5Z15F2A6
end BB
end Homological
end Stabilizer
end Quantum
