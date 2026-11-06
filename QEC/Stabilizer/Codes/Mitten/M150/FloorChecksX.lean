import QEC.Stabilizer.Codes.Mitten.M150.FloorBridge

/-!
# Finite certificates for the X-check floor

The basis-image certificates use sparse point-mass formulas. The census
certificates check nonzero shared blocks and identify the join rows with
all sixty physical checks. The remaining thirty-column identities certify
inverse maps, annihilator corrections, parity constraints, and split coverage.
-/

namespace Quantum
namespace Stabilizer
namespace Homological
namespace LP
namespace M150

open scoped BigOperators

/-! ## §1  Row chains and the packed 150-bit layout -/

/-- Row `k` of `H_Z` as a 1-chain (`k < 60`, canonical check order). -/
def rowChainX (k : Nat) : Fin 5 × M150G → ZMod 2 :=
  fun q => cmTerm (checkOf k) q

/-- The X-side join packing of a 1-chain: blocks `(0,2,4 | 1,3,4)`. -/
def packX (c : Fin 5 × M150G → ZMod 2) : Nat :=
  pack5
    (packTriple (maskOf (blockOf c 0)) (maskOf (blockOf c 2))
      (maskOf (blockOf c 4)))
    (packTriple (maskOf (blockOf c 1)) (maskOf (blockOf c 3))
      (maskOf (blockOf c 4)))

namespace FloorChecksX

/-! ## §2  Kernel-checked bridge and census certificates -/

set_option maxRecDepth 65536 in
/-- Basis images of the five block maps of both X-check rows match the
generated tables (`0` = the empty-table blocks). -/
lemma bridgeX : ∀ i < 30,
    maskOf (blockMapped d2term 0 0 (deltaFn i)) = tRawAX.getD i 0
    ∧ maskOf (blockMapped d2term 0 1 (deltaFn i)) = 0
    ∧ maskOf (blockMapped d2term 0 2 (deltaFn i)) = tWCX0.getD i 0
    ∧ maskOf (blockMapped d2term 0 3 (deltaFn i)) = 0
    ∧ maskOf (blockMapped d2term 0 4 (deltaFn i)) = tTCX0.getD i 0
    ∧ maskOf (blockMapped d2term 1 0 (deltaFn i)) = 0
    ∧ maskOf (blockMapped d2term 1 1 (deltaFn i)) = tRawAX.getD i 0
    ∧ maskOf (blockMapped d2term 1 2 (deltaFn i)) = 0
    ∧ maskOf (blockMapped d2term 1 3 (deltaFn i)) = tWCX1.getD i 0
    ∧ maskOf (blockMapped d2term 1 4 (deltaFn i)) = tTCX1.getD i 0 := by
  simp_rw [blockMapped_delta]
  decide +kernel

set_option maxRecDepth 65536 in
/-- The first nonzero triple census has a nonzero shared block. -/
lemma clsX0_shared_nonzero : ∀ pk ∈ clsX0, pk >>> 60 ≠ 0 := by
  decide +kernel

set_option maxRecDepth 65536 in
/-- The second nonzero triple census has a nonzero shared block. -/
lemma clsX1_shared_nonzero : ∀ pk ∈ clsX1, pk >>> 60 ≠ 0 := by
  decide +kernel

set_option maxRecDepth 65536 in
/-- The join row table is the sorted list of all sixty physical check rows. -/
lemma rowsXpk_eq : rowsXpk =
    ((List.range 60).map fun k => packX (rowChainX k)).insertionSort (· ≤ ·) := by
  decide +kernel

/-- Every join-table entry is a physical check row. -/
lemma rowsXpk_realized : ∀ pk ∈ rowsXpk,
    ∃ k, k < 60 ∧ packX (rowChainX k) = pk := by
  intro pk hp
  rw [rowsXpk_eq] at hp
  have hm : pk ∈ (List.range 60).map (fun k => packX (rowChainX k)) :=
    (List.perm_insertionSort _ _).mem_iff.mp hp
  obtain ⟨k, hk, he⟩ := List.mem_map.mp hm
  exact ⟨k, List.mem_range.mp hk, he⟩

/-- Census entries have nonzero shared blocks and all join rows are physical. -/
lemma clsX_facts :
    (∀ pk ∈ clsX0, pk >>> 60 ≠ 0) ∧ (∀ pk ∈ clsX1, pk >>> 60 ≠ 0)
    ∧ (∀ pk ∈ rowsXpk, ∃ k, k < 60 ∧ packX (rowChainX k) = pk) :=
  ⟨clsX0_shared_nonzero, clsX1_shared_nonzero, rowsXpk_realized⟩

/-! ## §3  Kernel decides against the generated tables -/

/-- Reading the empty column table returns zero. -/
lemma getD_nil (i : Nat) : ([] : List Nat).getD i 0 = 0 := by
  simp

/-- The inverse shared-block table cancels its forward map on basis masks. -/
lemma dCinvC_X0 : ∀ i < 30,
    xorFold tCinvX0 (tTCX0.getD i 0) = 1 <<< i := by decide
/-- The inverse shared-block table gives the first derivation map. -/
lemma dCinvA_X0 : ∀ i < 30,
    xorFold tCinvX0 (tRawAX.getD i 0) = tUTX0.getD i 0 := by decide
/-- The inverse shared-block table gives the second derivation map. -/
lemma dCinvB_X0 : ∀ i < 30,
    xorFold tCinvX0 (tWCX0.getD i 0) = tWTX0.getD i 0 := by decide
/-- The two opposite derivation maps compose to the identity on basis masks. -/
lemma dTWWT_X0 : ∀ i < 30,
    xorFold tTWX0 (tWTX0.getD i 0) = 1 <<< i := by decide
/-- The mixed derivation maps agree on all basis masks. -/
lemma dTWUT_X0 : ∀ i < 30,
    xorFold tTWX0 (tUTX0.getD i 0) = tUWX0.getD i 0 := by decide
/-- Every decoder correction belongs to the annihilator census. -/
lemma dCorr_X0 : ∀ i < 30,
    (1 <<< i ^^^ xorFold tPX0 (tRawAX.getD i 0)) ∈ annX0 := by decide
/-- The annihilator census contains zero and is closed under XOR. -/
lemma dAnn_X0 : (0 : Nat) ∈ annX0
    ∧ ∀ a ∈ annX0, ∀ b ∈ annX0, a ^^^ b ∈ annX0 := by decide
/-- The left-null parity functional vanishes on each map column. -/
lemma dLn0_X0 : ∀ i < 30,
    popCntGo 30 (m4TX0.ln0 &&& tRawAX.getD i 0) % 2 = 0 := by decide
/-- The left-null parity functional vanishes on each map column. -/
lemma dLn1_X0 : ∀ i < 30,
    popCntGo 30 (m4TX0.ln1 &&& tRawAX.getD i 0) % 2 = 0 := by decide
/-- Every listed map column fits into thirty bits. -/
lemma dBndB_X0 : ∀ x ∈ tWCX0, x < 2 ^ 30 := by decide
/-- Every listed map column fits into thirty bits. -/
lemma dBndC_X0 : ∀ x ∈ tTCX0, x < 2 ^ 30 := by decide

/-- The inverse shared-block table cancels its forward map on basis masks. -/
lemma dCinvC_X1 : ∀ i < 30,
    xorFold tCinvX1 (tTCX1.getD i 0) = 1 <<< i := by decide
/-- The inverse shared-block table gives the first derivation map. -/
lemma dCinvA_X1 : ∀ i < 30,
    xorFold tCinvX1 (tRawAX.getD i 0) = tUTX1.getD i 0 := by decide
/-- The inverse shared-block table gives the second derivation map. -/
lemma dCinvB_X1 : ∀ i < 30,
    xorFold tCinvX1 (tWCX1.getD i 0) = tWTX1.getD i 0 := by decide
/-- The two opposite derivation maps compose to the identity on basis masks. -/
lemma dTWWT_X1 : ∀ i < 30,
    xorFold tTWX1 (tWTX1.getD i 0) = 1 <<< i := by decide
/-- The mixed derivation maps agree on all basis masks. -/
lemma dTWUT_X1 : ∀ i < 30,
    xorFold tTWX1 (tUTX1.getD i 0) = tUWX1.getD i 0 := by decide
/-- Every decoder correction belongs to the annihilator census. -/
lemma dCorr_X1 : ∀ i < 30,
    (1 <<< i ^^^ xorFold tPX1 (tRawAX.getD i 0)) ∈ annX1 := by decide
/-- The annihilator census contains zero and is closed under XOR. -/
lemma dAnn_X1 : (0 : Nat) ∈ annX1
    ∧ ∀ a ∈ annX1, ∀ b ∈ annX1, a ^^^ b ∈ annX1 := by decide
/-- The left-null parity functional vanishes on each map column. -/
lemma dLn0_X1 : ∀ i < 30,
    popCntGo 30 (m4TX1.ln0 &&& tRawAX.getD i 0) % 2 = 0 := by decide
/-- The left-null parity functional vanishes on each map column. -/
lemma dLn1_X1 : ∀ i < 30,
    popCntGo 30 (m4TX1.ln1 &&& tRawAX.getD i 0) % 2 = 0 := by decide
/-- Every listed map column fits into thirty bits. -/
lemma dBndB_X1 : ∀ x ∈ tWCX1, x < 2 ^ 30 := by decide
/-- Every listed map column fits into thirty bits. -/
lemma dBndC_X1 : ∀ x ∈ tTCX1, x < 2 ^ 30 := by decide

/-- Every listed map column has odd parity. -/
lemma dOddA_X : ∀ i < 30,
    popCntGo 30 (tRawAX.getD i 0) % 2 = 1 := by decide
/-- Every listed map column has odd parity. -/
lemma dOddB_X0 : ∀ i < 30,
    popCntGo 30 (tWCX0.getD i 0) % 2 = 1 := by decide
/-- Every listed map column has odd parity. -/
lemma dOddC_X0 : ∀ i < 30,
    popCntGo 30 (tTCX0.getD i 0) % 2 = 1 := by decide
/-- Every listed map column has odd parity. -/
lemma dOddB_X1 : ∀ i < 30,
    popCntGo 30 (tWCX1.getD i 0) % 2 = 1 := by decide
/-- Every listed map column has odd parity. -/
lemma dOddC_X1 : ∀ i < 30,
    popCntGo 30 (tTCX1.getD i 0) % 2 = 1 := by decide

/-- The generated split table covers every allowed even weight split. -/
lemma covX0 : ∀ p < 9, ∀ q < 9, ∀ r < 9,
    p + q + r ≤ 8 → (p + q + r) % 2 = 0 →
    (splitsX0.contains (p, q, r, 0) || splitsX0.contains (p, q, r, 1)
      || splitsX0.contains (p, q, r, 2)) = true := by decide
/-- The generated split table covers every allowed even weight split. -/
lemma covX1 : ∀ p < 9, ∀ q < 9, ∀ r < 9,
    p + q + r ≤ 8 → (p + q + r) % 2 = 0 →
    (splitsX1.contains (p, q, r, 0) || splitsX1.contains (p, q, r, 1)
      || splitsX1.contains (p, q, r, 2)) = true := by decide

end FloorChecksX

end M150
end LP
end Homological
end Stabilizer
end Quantum
