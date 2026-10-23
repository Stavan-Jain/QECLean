import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import QEC.Stabilizer.Foundations.BinarySymplectic.CheckMatrix

/-!
# Right-inverse certificates for `rowsLinearIndependent`

The `Decidable (rowsLinearIndependent L)` instance enumerates all `2 ^ m`
coefficient vectors, where `m = L.length`. This module replaces that search by
a certificate checked in polynomial time: a right inverse of the check matrix.

* **Soundness** (`linearIndependent_rows_of_mul_eq_one`,
  `rowsLinearIndependent_of_mul_eq_one`). If `checkMatrix L * B = 1` then the
  rows are independent: from `v ᵥ* M = 0` we get
  `v = v ᵥ* (M * B) = (v ᵥ* M) ᵥ* B = 0`.
* **The check** (`RankCertificate.check`). Rows and certificate columns are
  packed into `2n`-bit `Nat` masks, and `M * B = 1` becomes `m²` parities of
  bitwise ANDs (`RankCertificate.mul_certMatrix_eq_one`). Each parity is an
  XOR-fold of `O(log n)` GMP operations on `2n`-bit numbers
  (`RankCertificate.parityLow`), so the kernel does `O(m² · n)` bit work, with
  no `Finset` sums and no `ZMod` arithmetic.
* **The Pauli instance** (`rowsLinearIndependent_of_rankCertCheck`).
  `rankCertCheck L bs` packs each generator's symplectic row
  (`RankCertificate.rowMask`) and runs the check, so a concrete code closes
  independence with
  `rowsLinearIndependent_of_rankCertCheck L bs (by decide +kernel)`.

The certificate `bs` (column `j` of `B` as a bitmask over the `n + n`
symplectic columns) is untrusted data: `scripts/RankCertificateGen.lean`
computes it by Gaussian elimination over `𝔽₂` and prints it as Lean source.
-/

namespace Quantum

open Matrix

/-! ## Right inverses certify independent rows -/

/-- A matrix with a right inverse has linearly independent rows. -/
theorem linearIndependent_rows_of_mul_eq_one {R : Type*} [CommRing R]
    {m k : Type*} [Finite m] [DecidableEq m] [Fintype k]
    (M : Matrix m k R) (B : Matrix k m R) (h : M * B = 1) :
    LinearIndependent R (fun i => M i) := by
  have := Fintype.ofFinite m
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have h0 : g ᵥ* M = 0 := by
    rw [← hg]
    ext c
    simp [vecMul, dotProduct, Finset.sum_apply]
  have h1 := congrArg (· ᵥ* B) h0
  simp only [vecMul_vecMul, h, vecMul_one, zero_vecMul] at h1
  exact congrFun h1 i

namespace NQubitPauliGroupElement

variable {n : ℕ}

/-- A right inverse of the check matrix certifies independent rows. -/
theorem rowsLinearIndependent_of_mul_eq_one (L : List (NQubitPauliGroupElement n))
    (B : Matrix (Fin (n + n)) (Fin L.length) (ZMod 2)) (h : checkMatrix L * B = 1) :
    rowsLinearIndependent L :=
  linearIndependent_rows_of_mul_eq_one _ B h

end NQubitPauliGroupElement

namespace RankCertificate

/-! ## Packed bit vectors

Everything that runs inside `decide +kernel` is written with the raw `Nat.*`
functions rather than `%`, `/`, `&&&`: the kernel evaluates both with GMP, but
the notation goes through typeclass instances that it re-unfolds at each
call. -/

private lemma beq_eq_decide (i j : ℕ) : Nat.beq i j = decide (i = j) := by
  rw [Bool.eq_iff_iff, Nat.beq_eq, decide_eq_true_eq]

private lemma ite_xor (a b : Bool) :
    (if xor a b then (1 : ZMod 2) else 0) =
      (if a then 1 else 0) + (if b then 1 else 0) := by
  cases a <;> cases b <;> decide

/-- XOR-folding: `foldXor j x` halves the window `j` times, so that its bit `0`
is the parity of the low `2 ^ j` bits of `x` (`ite_foldXor`). -/
def foldXor : ℕ → ℕ → ℕ
  | 0, x => x
  | j + 1, x => foldXor j (Nat.xor x (Nat.shiftRight x (Nat.pow 2 j)))

lemma ite_foldXor (j x : ℕ) :
    (if (foldXor j x).testBit 0 then (1 : ZMod 2) else 0) =
      ∑ i ∈ Finset.range (2 ^ j), if x.testBit i then (1 : ZMod 2) else 0 := by
  induction j generalizing x with
  | zero => rw [pow_zero, Finset.sum_range_one]; rfl
  | succ j ih =>
    rw [foldXor, ih, pow_succ, mul_two, Finset.sum_range_add, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    change (if (x ^^^ x >>> 2 ^ j).testBit i then _ else _) = _
    rw [Nat.testBit_xor, Nat.testBit_shiftRight, ite_xor]

/-- The parity of the set bits of `x` among positions `0, …, k − 1`: mask to
`k` bits, then XOR-fold a window of `2 ^ (log₂ k + 1) > k` bits. The kernel
cost is `O(log k)` big-number operations. -/
def parityLow (k x : ℕ) : Bool :=
  Nat.beq (Nat.land (foldXor (Nat.succ (Nat.log2 k))
    (Nat.land x (Nat.sub (Nat.pow 2 k) 1))) 1) 1

/-- `parityLow k x` is the `𝔽₂`-sum of the low `k` bits of `x`. -/
lemma ite_parityLow (k x : ℕ) :
    (if parityLow k x then (1 : ZMod 2) else 0) =
      ∑ i ∈ Finset.range k, if x.testBit i then (1 : ZMod 2) else 0 := by
  have hk : k < 2 ^ (k.log2 + 1) := Nat.lt_log2_self
  have hpar : parityLow k x =
      (foldXor (k.log2 + 1) (x &&& (2 ^ k - 1))).testBit 0 := by
    rw [parityLow, beq_eq_decide, Nat.testBit_zero]
    change decide ((_ &&& 1) = 1) = _
    rw [Nat.and_one_is_mod]
    rfl
  rw [hpar, ite_foldXor, ← Nat.add_sub_cancel' hk.le, Finset.sum_range_add]
  have htail : ∑ i ∈ Finset.range (2 ^ (k.log2 + 1) - k),
      (if (x &&& (2 ^ k - 1)).testBit (k + i) then (1 : ZMod 2) else 0) = 0 :=
    Finset.sum_eq_zero fun i _ => by simp
  rw [htail, add_zero]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Nat.testBit_land, Nat.testBit_two_pow_sub_one, decide_eq_true (Finset.mem_range.mp hi),
    Bool.and_true]

/-- The number with bits `b s, b (s + 1), …, b (s + len − 1)`, low bit first. -/
def ofBitsFrom (b : ℕ → Bool) : ℕ → ℕ → ℕ
  | _, 0 => 0
  | s, len + 1 => Nat.add (Nat.mul 2 (ofBitsFrom b (s + 1) len)) (b s).toNat

lemma testBit_ofBitsFrom (b : ℕ → Bool) (s len i : ℕ) :
    (ofBitsFrom b s len).testBit i = (decide (i < len) && b (s + i)) := by
  induction len generalizing s i with
  | zero => simp [ofBitsFrom]
  | succ len ih =>
    have hbit : ofBitsFrom b s (len + 1) = Nat.bit (b s) (ofBitsFrom b (s + 1) len) := by
      rw [Nat.bit_val]
      rfl
    rw [hbit]
    cases i with
    | zero => simp
    | succ i =>
      rw [Nat.testBit_bit_succ, ih]
      simp [Nat.add_assoc, Nat.add_comm 1 i]

/-! ## The check -/

/-- `rowCheck k r i bs j` checks, for the certificate columns `bs` numbered
from `j`, that `r` has inner product `1` with column `i` and `0` with every
other column. -/
def rowCheck (k r i : ℕ) : List ℕ → ℕ → Bool
  | [], _ => true
  | b :: bs, j => (parityLow k (Nat.land r b) == Nat.beq i j) && rowCheck k r i bs (j + 1)

/-- `rowsCheck k bs rows i` runs `rowCheck` on every row, numbered from `i`. -/
def rowsCheck (k : ℕ) (bs : List ℕ) : List ℕ → ℕ → Bool
  | [], _ => true
  | r :: rs, i => rowCheck k r i bs 0 && rowsCheck k bs rs (i + 1)

/-- The certificate check on `k`-bit rows: as many columns as rows, and the
row-by-column inner products form the identity matrix. -/
def check (k : ℕ) (rows bs : List ℕ) : Bool :=
  Nat.beq rows.length bs.length && rowsCheck k bs rows 0

lemma rowCheck_sound {k r i : ℕ} :
    ∀ {bs : List ℕ} {j : ℕ}, rowCheck k r i bs j = true →
      ∀ t (ht : t < bs.length), parityLow k (Nat.land r bs[t]) = decide (i = j + t) := by
  intro bs
  induction bs with
  | nil => intro _ _ t ht; exact absurd ht (Nat.not_lt_zero _)
  | cons b bs ih =>
    intro j h t ht
    simp only [rowCheck, Bool.and_eq_true, beq_iff_eq] at h
    cases t with
    | zero => simpa [beq_eq_decide] using h.1
    | succ t =>
      rw [List.getElem_cons_succ, ih h.2 t (by simpa using ht)]
      simp [Nat.add_assoc, Nat.add_comm 1 t]

lemma rowsCheck_sound {k : ℕ} {bs : List ℕ} :
    ∀ {rows : List ℕ} {i : ℕ}, rowsCheck k bs rows i = true →
      ∀ s (hs : s < rows.length) t (ht : t < bs.length),
        parityLow k (Nat.land rows[s] bs[t]) = decide (i + s = t) := by
  intro rows
  induction rows with
  | nil => intro _ _ s hs; exact absurd hs (Nat.not_lt_zero _)
  | cons r rs ih =>
    intro i h s hs t ht
    simp only [rowsCheck, Bool.and_eq_true] at h
    cases s with
    | zero => simpa using rowCheck_sound h.1 t ht
    | succ s =>
      rw [List.getElem_cons_succ, ih h.2 s (by simpa using hs) t ht]
      simp [Nat.add_assoc, Nat.add_comm 1 s]

/-- The matrix whose column `j` is the bitmask `bs[j]`. -/
def certMatrix (k m : ℕ) (bs : List ℕ) : Matrix (Fin k) (Fin m) (ZMod 2) :=
  fun c j => if (bs.getD j 0).testBit c then 1 else 0

/-- **Soundness of the check.** If the rows of `M` are the bitmasks `rows`
and `check k rows bs` passes, then `certMatrix k m bs` is a right inverse of
`M`. -/
theorem mul_certMatrix_eq_one {m k : ℕ} (M : Matrix (Fin m) (Fin k) (ZMod 2))
    (rows bs : List ℕ) (hlen : rows.length = m)
    (hrow : ∀ i c, M i c = if (rows.getD i 0).testBit c then 1 else 0)
    (h : check k rows bs = true) : M * certMatrix k m bs = 1 := by
  simp only [check, Bool.and_eq_true, beq_eq_decide, decide_eq_true_eq] at h
  obtain ⟨hbs, h⟩ := h
  ext i j
  have hi : i.val < rows.length := hlen ▸ i.isLt
  have hj : j.val < bs.length := hbs ▸ hlen ▸ j.isLt
  have hsum : (M * certMatrix k m bs) i j =
      ∑ c ∈ Finset.range k,
        if (Nat.land rows[i.val] bs[j.val]).testBit c then (1 : ZMod 2) else 0 := by
    rw [mul_apply, ← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [hrow, certMatrix, List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hj]
    change _ = if (rows[i.val] &&& bs[j.val]).testBit c then _ else _
    rw [Nat.testBit_land]
    cases rows[i.val].testBit c <;> cases bs[j.val].testBit c <;> simp
  rw [hsum, ← ite_parityLow, rowsCheck_sound h i hi j hj, one_apply, zero_add]
  simp [Fin.ext_iff]

/-! ## Symplectic rows as bitmasks -/

/-- The X bit of a single-qubit Pauli (`X^x Z^z`). -/
def xBit : PauliOperator → Bool
  | .I => false
  | .X => true
  | .Y => true
  | .Z => false

/-- The Z bit of a single-qubit Pauli (`X^x Z^z`). -/
def zBit : PauliOperator → Bool
  | .I => false
  | .X => false
  | .Y => true
  | .Z => true

variable {n : ℕ}

/-- Bit `c` of the symplectic row of `op`: X bits in positions `0, …, n − 1`,
Z bits in positions `n, …, 2n − 1`. -/
def symplecticBit (op : NQubitPauliOperator n) (c : ℕ) : Bool :=
  if h : c < n then xBit (op ⟨c, h⟩)
  else if h' : c - n < n then zBit (op ⟨c - n, h'⟩) else false

/-- The symplectic row of `op` packed into a `2n`-bit mask. -/
def rowMask (op : NQubitPauliOperator n) : ℕ :=
  ofBitsFrom (symplecticBit op) 0 (n + n)

lemma toSymplectic_eq_ite (op : NQubitPauliOperator n) (c : Fin (n + n)) :
    NQubitPauliOperator.toSymplectic op c =
      if (rowMask op).testBit c then 1 else 0 := by
  have hc := c.isLt
  rw [rowMask, testBit_ofBitsFrom, decide_eq_true hc, Bool.true_and, zero_add,
    NQubitPauliOperator.toSymplectic, symplecticBit]
  by_cases h : c.val < n
  · rw [dif_pos h, dif_pos h]
    cases op ⟨c.val, h⟩ <;> rfl
  · have h' : c.val - n < n := by omega
    rw [dif_neg h, dif_neg h, dif_pos h']
    cases op ⟨c.val - n, h'⟩ <;> rfl

end RankCertificate

namespace NQubitPauliGroupElement

open RankCertificate

variable {n : ℕ}

/-- The rank-certificate check for a generator list: pack each symplectic row
and verify that the bitmasks `bs` are the columns of a right inverse. -/
def rankCertCheck (L : List (NQubitPauliGroupElement n)) (bs : List ℕ) : Bool :=
  check (n + n) (L.map fun g => rowMask g.operators) bs

/-- **Independence from a rank certificate.** A passing `rankCertCheck`
gives `rowsLinearIndependent`, with `certMatrix` as the right inverse of the
check matrix. The check is polynomial in `L.length` and `n`, against `2 ^ m`
coefficient vectors for the exhaustive `Decidable` instance. -/
theorem rowsLinearIndependent_of_rankCertCheck (L : List (NQubitPauliGroupElement n))
    (bs : List ℕ) (h : rankCertCheck L bs = true) : rowsLinearIndependent L := by
  refine rowsLinearIndependent_of_mul_eq_one L (certMatrix (n + n) L.length bs) ?_
  refine mul_certMatrix_eq_one _ _ bs (List.length_map _) (fun i c => ?_) h
  rw [List.getD_eq_getElem _ _ (by simp), List.getElem_map, checkMatrix,
    toSymplectic_eq_ite]
  rfl

end NQubitPauliGroupElement

end Quantum
