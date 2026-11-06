import QEC.Stabilizer.Codes.Mitten.M150.FloorBridge

/-!
# Finite certificates for the Z-check floor

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

/-- Row `k` of `H_X` as a 1-chain (`k < 60`, canonical check order). -/
def rowChainZ (k : Nat) : Fin 5 × M150G → ZMod 2 :=
  fun q => d2term (checkOf k) q

/-- The Z-side join packing of a 1-chain: blocks `(0,1,4 | 2,3,4)`. -/
def packZ (c : Fin 5 × M150G → ZMod 2) : Nat :=
  pack5
    (packTriple (maskOf (blockOf c 0)) (maskOf (blockOf c 1))
      (maskOf (blockOf c 4)))
    (packTriple (maskOf (blockOf c 2)) (maskOf (blockOf c 3))
      (maskOf (blockOf c 4)))

namespace FloorChecksZ

/-! ## §2  Kernel-checked bridge and census certificates -/

set_option maxRecDepth 65536 in
/-- Basis images of the five block maps of both Z-check rows match the
generated tables (`0` = the empty-table blocks). -/
lemma bridgeZ : ∀ i < 30,
    maskOf (blockMapped cmTerm 0 0 (deltaFn i)) = tUCZ0.getD i 0
    ∧ maskOf (blockMapped cmTerm 0 1 (deltaFn i)) = tWC2Z0.getD i 0
    ∧ maskOf (blockMapped cmTerm 0 2 (deltaFn i)) = 0
    ∧ maskOf (blockMapped cmTerm 0 3 (deltaFn i)) = 0
    ∧ maskOf (blockMapped cmTerm 0 4 (deltaFn i)) = tRawCZ0.getD i 0
    ∧ maskOf (blockMapped cmTerm 1 0 (deltaFn i)) = 0
    ∧ maskOf (blockMapped cmTerm 1 1 (deltaFn i)) = 0
    ∧ maskOf (blockMapped cmTerm 1 2 (deltaFn i)) = tUCZ1.getD i 0
    ∧ maskOf (blockMapped cmTerm 1 3 (deltaFn i)) = tWC2Z1.getD i 0
    ∧ maskOf (blockMapped cmTerm 1 4 (deltaFn i)) = tRawCZ1.getD i 0 := by
  simp_rw [blockMapped_delta]
  decide +kernel

set_option maxRecDepth 65536 in
/-- The first nonzero triple census has a nonzero shared block. -/
lemma clsZ0_shared_nonzero : ∀ pk ∈ clsZ0, pk >>> 60 ≠ 0 := by
  decide +kernel

set_option maxRecDepth 65536 in
/-- The second nonzero triple census has a nonzero shared block. -/
lemma clsZ1_shared_nonzero : ∀ pk ∈ clsZ1, pk >>> 60 ≠ 0 := by
  decide +kernel

set_option maxRecDepth 65536 in
/-- The join row table is the sorted list of all sixty physical check rows. -/
lemma rowsZpk_eq : rowsZpk =
    ((List.range 60).map fun k => packZ (rowChainZ k)).insertionSort (· ≤ ·) := by
  decide +kernel

/-- Every join-table entry is a physical check row. -/
lemma rowsZpk_realized : ∀ pk ∈ rowsZpk,
    ∃ k, k < 60 ∧ packZ (rowChainZ k) = pk := by
  intro pk hp
  rw [rowsZpk_eq] at hp
  have hm : pk ∈ (List.range 60).map (fun k => packZ (rowChainZ k)) :=
    (List.perm_insertionSort _ _).mem_iff.mp hp
  obtain ⟨k, hk, he⟩ := List.mem_map.mp hm
  exact ⟨k, List.mem_range.mp hk, he⟩

/-- Census entries have nonzero shared blocks and all join rows are physical. -/
lemma clsZ_facts :
    (∀ pk ∈ clsZ0, pk >>> 60 ≠ 0) ∧ (∀ pk ∈ clsZ1, pk >>> 60 ≠ 0)
    ∧ (∀ pk ∈ rowsZpk, ∃ k, k < 60 ∧ packZ (rowChainZ k) = pk) :=
  ⟨clsZ0_shared_nonzero, clsZ1_shared_nonzero, rowsZpk_realized⟩

/-! ## §3  Kernel decides against the generated tables -/

/-- Reading the empty column table returns zero. -/
lemma getD_nil (i : Nat) : ([] : List Nat).getD i 0 = 0 := by
  simp

/-- The inverse first-block table cancels its forward map on basis masks. -/
lemma dAinvA_Z0 : ∀ i < 30,
    xorFold tAinvZ (tUCZ0.getD i 0) = 1 <<< i := by decide
/-- The inverse first-block table gives the second-block derivation map. -/
lemma dAinvB_Z0 : ∀ i < 30,
    xorFold tAinvZ (tWC2Z0.getD i 0) = tWCZ0.getD i 0 := by decide
/-- The inverse first-block table gives the shared-block derivation map. -/
lemma dAinvC_Z0 : ∀ i < 30,
    xorFold tAinvZ (tRawCZ0.getD i 0) = tTCZ0.getD i 0 := by decide
/-- The inverse second-block derivation cancels its forward map. -/
lemma dUWWC_Z0 : ∀ i < 30,
    xorFold tUWZ0 (tWCZ0.getD i 0) = 1 <<< i := by decide
/-- The second-block and shared-block derivation maps compose correctly. -/
lemma dUWTC_Z0 : ∀ i < 30,
    xorFold tUWZ0 (tTCZ0.getD i 0) = tTWZ0.getD i 0 := by decide
/-- The pseudoinverse table is the identity on basis masks. -/
lemma dPid_Z0 : ∀ i < 30, tPZ0.getD i 0 = 1 <<< i := by decide
/-- Every shared-block decoder correction lies in its annihilator census. -/
lemma dCorrT_Z0 : ∀ i < 30,
    (1 <<< i ^^^ xorFold tPTZ0 (tRawCZ0.getD i 0)) ∈ annTZ0 := by decide
/-- The shared-block annihilator census contains zero and is XOR closed. -/
lemma dAnnT_Z0 : (0 : Nat) ∈ annTZ0
    ∧ ∀ a ∈ annTZ0, ∀ b ∈ annTZ0, a ^^^ b ∈ annTZ0 := by decide
/-- The annihilator census contains zero. -/
lemma dAnn0_Z0 : (0 : Nat) ∈ annZ0 := by decide
/-- The left-null parity functional vanishes on each map column. -/
lemma dLnT0_Z0 : ∀ i < 30,
    popCntGo 30 (m4TZ0.lnT0 &&& tRawCZ0.getD i 0) % 2 = 0 := by decide
/-- The left-null parity functional vanishes on each map column. -/
lemma dLnT1_Z0 : ∀ i < 30,
    popCntGo 30 (m4TZ0.lnT1 &&& tRawCZ0.getD i 0) % 2 = 0 := by decide
/-- Every listed map column fits into thirty bits. -/
lemma dBndA_Z0 : ∀ x ∈ tUCZ0, x < 2 ^ 30 := by decide
/-- Every listed map column fits into thirty bits. -/
lemma dBndB_Z0 : ∀ x ∈ tWC2Z0, x < 2 ^ 30 := by decide
/-- Every listed map column fits into thirty bits. -/
lemma dBndWC_Z0 : ∀ x ∈ tWCZ0, x < 2 ^ 30 := by decide
/-- Every listed map column fits into thirty bits. -/
lemma dBndTC_Z0 : ∀ x ∈ tTCZ0, x < 2 ^ 30 := by decide

/-- The inverse first-block table cancels its forward map on basis masks. -/
lemma dAinvA_Z1 : ∀ i < 30,
    xorFold tAinvZ (tUCZ1.getD i 0) = 1 <<< i := by decide
/-- The inverse first-block table gives the second-block derivation map. -/
lemma dAinvB_Z1 : ∀ i < 30,
    xorFold tAinvZ (tWC2Z1.getD i 0) = tWCZ1.getD i 0 := by decide
/-- The inverse first-block table gives the shared-block derivation map. -/
lemma dAinvC_Z1 : ∀ i < 30,
    xorFold tAinvZ (tRawCZ1.getD i 0) = tTCZ1.getD i 0 := by decide
/-- The inverse second-block derivation cancels its forward map. -/
lemma dUWWC_Z1 : ∀ i < 30,
    xorFold tUWZ1 (tWCZ1.getD i 0) = 1 <<< i := by decide
/-- The second-block and shared-block derivation maps compose correctly. -/
lemma dUWTC_Z1 : ∀ i < 30,
    xorFold tUWZ1 (tTCZ1.getD i 0) = tTWZ1.getD i 0 := by decide
/-- The pseudoinverse table is the identity on basis masks. -/
lemma dPid_Z1 : ∀ i < 30, tPZ1.getD i 0 = 1 <<< i := by decide
/-- Every shared-block decoder correction lies in its annihilator census. -/
lemma dCorrT_Z1 : ∀ i < 30,
    (1 <<< i ^^^ xorFold tPTZ1 (tRawCZ1.getD i 0)) ∈ annTZ1 := by decide
/-- The shared-block annihilator census contains zero and is XOR closed. -/
lemma dAnnT_Z1 : (0 : Nat) ∈ annTZ1
    ∧ ∀ a ∈ annTZ1, ∀ b ∈ annTZ1, a ^^^ b ∈ annTZ1 := by decide
/-- The annihilator census contains zero. -/
lemma dAnn0_Z1 : (0 : Nat) ∈ annZ1 := by decide
/-- The left-null parity functional vanishes on each map column. -/
lemma dLnT0_Z1 : ∀ i < 30,
    popCntGo 30 (m4TZ1.lnT0 &&& tRawCZ1.getD i 0) % 2 = 0 := by decide
/-- The left-null parity functional vanishes on each map column. -/
lemma dLnT1_Z1 : ∀ i < 30,
    popCntGo 30 (m4TZ1.lnT1 &&& tRawCZ1.getD i 0) % 2 = 0 := by decide
/-- Every listed map column fits into thirty bits. -/
lemma dBndA_Z1 : ∀ x ∈ tUCZ1, x < 2 ^ 30 := by decide
/-- Every listed map column fits into thirty bits. -/
lemma dBndB_Z1 : ∀ x ∈ tWC2Z1, x < 2 ^ 30 := by decide
/-- Every listed map column fits into thirty bits. -/
lemma dBndWC_Z1 : ∀ x ∈ tWCZ1, x < 2 ^ 30 := by decide
/-- Every listed map column fits into thirty bits. -/
lemma dBndTC_Z1 : ∀ x ∈ tTCZ1, x < 2 ^ 30 := by decide

/-- Every listed map column has odd parity. -/
lemma dOddA_Z0 : ∀ i < 30,
    popCntGo 30 (tUCZ0.getD i 0) % 2 = 1 := by decide
/-- Every listed map column has odd parity. -/
lemma dOddB_Z0 : ∀ i < 30,
    popCntGo 30 (tWC2Z0.getD i 0) % 2 = 1 := by decide
/-- Every listed map column has odd parity. -/
lemma dOddC_Z0 : ∀ i < 30,
    popCntGo 30 (tRawCZ0.getD i 0) % 2 = 1 := by decide
/-- Every listed map column has odd parity. -/
lemma dOddA_Z1 : ∀ i < 30,
    popCntGo 30 (tUCZ1.getD i 0) % 2 = 1 := by decide
/-- Every listed map column has odd parity. -/
lemma dOddB_Z1 : ∀ i < 30,
    popCntGo 30 (tWC2Z1.getD i 0) % 2 = 1 := by decide
/-- Every listed map column has odd parity. -/
lemma dOddC_Z1 : ∀ i < 30,
    popCntGo 30 (tRawCZ1.getD i 0) % 2 = 1 := by decide

/-- The generated split table covers every allowed even weight split. -/
lemma covZ0 : ∀ p < 9, ∀ q < 9, ∀ r < 9,
    p + q + r ≤ 8 → (p + q + r) % 2 = 0 →
    (splitsZ0.contains (p, q, r, 0) || splitsZ0.contains (p, q, r, 2)
      || splitsZ0.contains (p, q, r, 3)) = true := by decide
/-- The generated split table covers every allowed even weight split. -/
lemma covZ1 : ∀ p < 9, ∀ q < 9, ∀ r < 9,
    p + q + r ≤ 8 → (p + q + r) % 2 = 0 →
    (splitsZ1.contains (p, q, r, 0) || splitsZ1.contains (p, q, r, 2)
      || splitsZ1.contains (p, q, r, 3)) = true := by decide

end FloorChecksZ

end M150
end LP
end Homological
end Stabilizer
end Quantum
