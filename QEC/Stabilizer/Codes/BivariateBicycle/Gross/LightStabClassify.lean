/-
# Discharging `LightStabilizerClassification` (the `hC` hypothesis)

This module proves `lightStabilizerClassification_holds : LightStabilizerClassification`
(`DangerousSector.lean`), the last analytic input that made the dangerous sector of
the gross `[[144,12,12]]` BB code conditional.  With it, the dangerous-sector bound
`DangerousSectorGe12` becomes unconditional (the only remaining assumed input for
`d = 12` is `MImBound`).

## Strategy (A4 §6.3, the CRT-engine classification, made effective)

The classification — *every nonzero base boundary `∂₂f` of weight ≤ 11 is a hexagon
or a D-pair* — is reduced to a finite `native_decide` over the two lighter A-block
shapes, bridged back to the function level:

* **Bitmask scan** (`classifyCore`, `classifyCoreEven`): every *gated* weight-≤5
  origin-containing A-block mask is a hexagon/D-pair A-block, or has no `|b|≤10`
  completion (its minimal B-block coset weight is too large).  The odd scan
  `supMask [0,q₁,q₂,q₃,q₄]` covers weights 3, 5 (hexagons); the even scan
  `supMask [0,q₁,q₂,q₃]` covers weight 4 (D-pairs).
* **Soundness bridge** (`bitmaskOf_add`, `wtM_eq_bwt`, `gateM_conv_baseA`,
  `coset_mem`, `minBcoset_le_bwt`): a keystone `Nat`-XOR additivity for `bitmaskOf`
  lifts the bitmask facts to the actual `conv baseA`/`conv baseB`.  In particular
  `minBcoset` is a genuine lower bound for the real B-block completion weight.
* **Witness extraction** (`isHexDpairA_witness`, `exists_supMask5/4`): the recognised
  A-block is translated into a `conv baseA` equality with a hexagon/D-pair witness,
  and the L4c endgame transfers (`transfer_hexagon`/`transfer_dpair`, in `LightStab`)
  promote it to a full boundary equality.
* **Normalization + symmetry** (`classify_Alighter`, `classify_Blighter`): a
  translation moves a support cell of the lighter block to the origin, and the
  `x ↔ y` swap (`swapFn`, exchanging `baseA ↔ baseB`) transports the A-side argument
  to the B-lighter case.

Everything is axiom-clean: the standard three (`propext`, `Classical.choice`,
`Quot.sound`) plus sanctioned `native_decide`.  No `sorry`, no custom axioms.
-/
import QEC.Stabilizer.Codes.BivariateBicycle.Gross.LightStab

open Quantum.Stabilizer.Homological.BB
open Quantum.Stabilizer.Homological.BB.CRTFrame
open Quantum.Stabilizer.Homological.BB.LightStab

namespace Quantum.Stabilizer.Homological.BB.LightStab

/-! ## Bitmask layer (data + defs) -/

def HA_rows : List (List Nat) :=
  [[0,1,4,5,18,20],[0,1,2,5,19,21],[2,3,4,5,18,22],[0,3,4,5,19,23],
   [6,7,10,11,24,26],[6,7,8,11,25,27],[8,9,10,11,24,28],[6,9,10,11,25,29],
   [12,13,16,17,30,32],[12,13,14,17,31,33],[14,15,16,17,30,34],[12,15,16,17,31,35]]
def hexB : Array Nat := #[
  4168, 8336, 16672, 33281, 66562, 133124, 266752, 533504, 1067008, 2129984, 4259968, 8519936,
  17072128, 34144256, 68288512, 136318976, 272637952, 545275904, 1092616192, 2185232384,
  4370464768, 8724414464, 17448828928, 34897657856, 1207959553, 2415919106, 4831838212,
  8606711816, 17213423632, 34426847264, 8589934657, 17179869314, 34359738628, 1073742344,
  2147484688, 4294969376]
def hexA : Array Nat := #[
  262150, 524300, 1048600, 2097200, 4194337, 8388611, 16777600, 33555200, 67110400, 134220800,
  268437568, 536871104, 1073766400, 2147532800, 4295065600, 8590131200, 17180004352, 34359750656,
  1572865, 3145730, 6291460, 12582920, 8650768, 786464, 100663360, 201326720, 402653440,
  805306880, 553649152, 50333696, 6442455040, 12884910080, 25769820160, 51539640320, 35433545728,
  3221356544]
def MBAcols : Array Nat := #[
  2185365508, 2185232384, 1092741043, 2185482023, 2185465351, 2185432070, 2424439042, 2415919106,
  1215950017, 2431896002, 2430828994, 2428699010, 17725145218, 17179869314, 9101324353,
  18202390658, 18134102146, 17997783170, 3277977595, 3277981700, 0, 0, 0, 0, 3632135875,
  3632398595, 0, 0, 0, 0, 26298265795, 26315079875, 0, 0, 0, 0]
def Bbasis : Array Nat := #[
  37082952697, 18541607420, 10909896487, 5463205811, 769133430, 464783085]
def gdMaps : Array (Array Nat) := #[
  #[1,2,3,4,5,0,7,8,9,10,11,6,13,14,15,16,17,12,19,20,21,22,23,18,25,26,27,28,29,24,31,32,33,34,
    35,30],
  #[5,0,1,2,3,4,11,6,7,8,9,10,17,12,13,14,15,16,23,18,19,20,21,22,29,24,25,26,27,28,35,30,31,32,
    33,34],
  #[19,20,21,22,23,18,25,26,27,28,29,24,31,32,33,34,35,30,1,2,3,4,5,0,7,8,9,10,11,6,13,14,15,16,
    17,12],
  #[20,21,22,23,18,19,26,27,28,29,24,25,32,33,34,35,30,31,2,3,4,5,0,1,8,9,10,11,6,7,14,15,16,17,
    12,13],
  #[22,23,18,19,20,21,28,29,24,25,26,27,34,35,30,31,32,33,4,5,0,1,2,3,10,11,6,7,8,9,16,17,12,13,
    14,15],
  #[23,18,19,20,21,22,29,24,25,26,27,28,35,30,31,32,33,34,5,0,1,2,3,4,11,6,7,8,9,10,17,12,13,14,
    15,16],
  #[6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,0,1,2,
    3,4,5],
  #[9,10,11,6,7,8,15,16,17,12,13,14,21,22,23,18,19,20,27,28,29,24,25,26,33,34,35,30,31,32,3,4,5,
    0,1,2],
  #[15,16,17,12,13,14,21,22,23,18,19,20,27,28,29,24,25,26,33,34,35,30,31,32,3,4,5,0,1,2,9,10,11,
    6,7,8],
  #[27,28,29,24,25,26,33,34,35,30,31,32,3,4,5,0,1,2,9,10,11,6,7,8,15,16,17,12,13,14,21,22,23,18,
    19,20],
  #[30,31,32,33,34,35,0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,
    28,29],
  #[33,34,35,30,31,32,3,4,5,0,1,2,9,10,11,6,7,8,15,16,17,12,13,14,21,22,23,18,19,20,27,28,29,24,
    25,26]]

def cellOf (i : Nat) : BaseGroup := ((i / 6 : ℕ), (i % 6 : ℕ))
def idxOf (g : BaseGroup) : Nat := g.1.val * 6 + g.2.val
def bitmaskOf (b : BaseGroup → ZMod 2) : Nat :=
  (List.range 36).foldl (fun acc i => if b (cellOf i) = 1 then acc ^^^ (1 <<< i) else acc) 0
def supMask (sup : List (Fin 36)) : Nat := sup.foldl (fun acc i => acc ^^^ (1 <<< i.val)) 0
def gateM (m : Nat) : Bool :=
  HA_rows.all (fun row => (row.foldl (fun acc i => acc ^^^ ((m >>> i) &&& 1)) 0) == 0)
def wtM (m : Nat) : Nat := (List.range 36).foldl (fun acc i => acc + ((m >>> i) &&& 1)) 0
/-- Generic "select-and-XOR": XOR of `cols i` over the set bits `i < n` of `m`. -/
def selXor (cols : Nat → Nat) (n : Nat) (m : Nat) : Nat :=
  (List.range n).foldl (fun acc i => if m.testBit i then acc ^^^ cols i else acc) 0
def applyCols (cols : Array Nat) (m : Nat) : Nat :=
  (List.range 36).foldl (fun acc i => if (m >>> i) &&& 1 == 1 then acc ^^^ cols.getD i 0 else acc) 0
/-- The `c`-th offset in the 6-dimensional B-block coset span. -/
def bOffset (c : Nat) : Nat := selXor (fun i => Bbasis.getD i 0) 6 c
def minBcoset (m : Nat) : Nat :=
  (List.range 64).foldl (fun acc c => min acc (wtM (applyCols MBAcols m ^^^ bOffset c))) 99
def isHexA (m : Nat) : Bool := (List.range 36).any (fun g => m == hexA.getD g 0)
def isDpairA (m : Nat) : Bool :=
  (List.range 36).any (fun g => (List.range 12).any (fun k =>
    m == (hexA.getD g 0 ^^^ hexA.getD ((gdMaps.getD k #[]).getD g 0) 0)))
def isHexDpairA (m : Nat) : Bool := isHexA m || isDpairA m

/-! ## Keystone: bitmaskOf additivity over XOR -/

theorem foldl_testBit (P : Nat → Prop) [DecidablePred P] (i : Nat) :
    ∀ (L : List Nat), L.Nodup → ∀ (a0 : Nat),
    (L.foldl (fun acc j => if P j then acc ^^^ (1 <<< j) else acc) a0).testBit i
      = (a0.testBit i ^^ (decide (i ∈ L) && decide (P i))) := by
  intro L
  induction L with
  | nil => intro _ a0; simp
  | cons j t ih =>
    intro hnd a0
    rw [List.foldl_cons]
    have hjt : j ∉ t := (List.nodup_cons.mp hnd).1
    have hndt : t.Nodup := (List.nodup_cons.mp hnd).2
    rw [ih hndt]
    have hstep : ((if P j then a0 ^^^ (1 <<< j) else a0).testBit i)
        = (a0.testBit i ^^ (decide (P j) && decide (j = i))) := by
      by_cases hpj : P j
      · rw [if_pos hpj, Nat.testBit_xor, Nat.shiftLeft_eq, one_mul, Nat.testBit_two_pow]; simp [hpj]
      · rw [if_neg hpj]; simp [hpj]
    rw [hstep]
    by_cases hij : i = j
    · subst hij
      have h1 : decide (i ∈ t) = false := by simp [hjt]
      have h2 : decide (i = i) = true := by simp
      rw [h1, h2]; simp [Bool.and_comm]
    · have h3 : decide (j = i) = false := by simp [Ne.symm hij]
      rw [h3]; simp only [List.mem_cons, hij, false_or, Bool.and_false, Bool.xor_false]

theorem testBit_bitmaskOf (b : BaseGroup → ZMod 2) (i : Nat) :
    (bitmaskOf b).testBit i = (decide (i ∈ List.range 36) && decide (b (cellOf i) = 1)) := by
  unfold bitmaskOf
  rw [foldl_testBit (fun i => b (cellOf i) = 1) i (List.range 36) List.nodup_range 0]
  simp

theorem bitmaskOf_add (x y : BaseGroup → ZMod 2) :
    bitmaskOf (x + y) = bitmaskOf x ^^^ bitmaskOf y := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_xor, testBit_bitmaskOf, testBit_bitmaskOf, testBit_bitmaskOf]
  by_cases hi : i ∈ List.range 36
  · simp only [hi, decide_true, Bool.true_and]
    have hpt : (x + y) (cellOf i) = x (cellOf i) + y (cellOf i) := rfl
    rw [hpt]
    have key : ∀ u v : ZMod 2, decide (u + v = 1) = (decide (u = 1) ^^ decide (v = 1)) := by decide
    rw [key]
  · simp [hi]

theorem bitmaskOf_zero : bitmaskOf 0 = 0 := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [testBit_bitmaskOf]; simp

/-! ## Nat-bit helper -/

theorem bit_and_one (m i : Nat) : (m >>> i) &&& 1 = if m.testBit i then 1 else 0 := by
  have hdef : m.testBit i = (1 &&& (m >>> i) != 0) := rfl
  rw [hdef, Nat.and_comm 1 (m >>> i), Nat.and_one_is_mod]
  rcases Nat.mod_two_eq_zero_or_one (m >>> i) with h | h <;> rw [h] <;> rfl

/-! ## idxOf round trips -/

theorem cellOf_idxOf (g : BaseGroup) : cellOf (idxOf g) = g := by
  obtain ⟨a, b⟩ := g
  fin_cases a <;> fin_cases b <;> rfl

theorem idxOf_lt (g : BaseGroup) : idxOf g < 36 := by
  obtain ⟨a, b⟩ := g
  fin_cases a <;> fin_cases b <;> decide

theorem cellOf_surj (g : BaseGroup) : ∃ i, i < 36 ∧ cellOf i = g :=
  ⟨idxOf g, idxOf_lt g, cellOf_idxOf g⟩

/-! ## §B weight bridge + injectivity -/

theorem bitmaskOf_injective {a b : BaseGroup → ZMod 2} (h : bitmaskOf a = bitmaskOf b) : a = b := by
  funext g
  obtain ⟨i, hi, hcell⟩ := cellOf_surj g
  have := congrArg (fun m => Nat.testBit m i) h
  simp only [testBit_bitmaskOf] at this
  have hir : i ∈ List.range 36 := List.mem_range.mpr hi
  simp only [hir, decide_true, Bool.true_and] at this
  rw [hcell] at this
  -- this : decide (a g = 1) = decide (b g = 1)
  revert this
  generalize a g = u; generalize b g = v
  revert u v; decide


/-! ## §B weight bridge -/

theorem foldl_count_eq_sum (f : Nat → Nat) (n : Nat) :
    (List.range n).foldl (fun acc i => acc + f i) 0 = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ k ih => rw [Finset.sum_range_succ, List.range_succ, List.foldl_append, ← ih]; simp

theorem idxOf_cellOf {i : Nat} (hi : i < 36) : idxOf (cellOf i) = i := by
  interval_cases i <;> rfl

theorem wtM_eq_bwt (b : BaseGroup → ZMod 2) : wtM (bitmaskOf b) = bwt b := by
  unfold wtM
  rw [show (fun acc i => acc + ((bitmaskOf b >>> i) &&& 1))
        = (fun acc i => acc + (if (bitmaskOf b).testBit i then 1 else 0)) from by
      funext acc i; rw [bit_and_one]]
  rw [foldl_count_eq_sum]
  have hsum : ∑ i ∈ Finset.range 36, (if (bitmaskOf b).testBit i then 1 else 0)
      = ∑ i ∈ Finset.range 36, (if b (cellOf i) = 1 then 1 else 0) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [testBit_bitmaskOf]
    have : i ∈ List.range 36 := List.mem_range.mpr (Finset.mem_range.mp hi)
    simp only [this, decide_true, Bool.true_and, decide_eq_true_eq]
  rw [hsum, Finset.sum_boole]
  unfold bwt
  apply Finset.card_bij' (fun i _ => cellOf i) (fun g _ => idxOf g)
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_range] at hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hi.2
  · intro g hg
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨idxOf_lt g, by rw [cellOf_idxOf]; exact hg⟩
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_range] at hi
    exact idxOf_cellOf hi.1
  · intro g _; exact cellOf_idxOf g

/-! ## §C gate annihilates the image -/

theorem foldl_xor_split (g h : Nat → Nat) :
    ∀ (row : List Nat) (a b : Nat),
      row.foldl (fun acc i => acc ^^^ (g i ^^^ h i)) (a ^^^ b)
      = (row.foldl (fun acc i => acc ^^^ g i) a) ^^^ (row.foldl (fun acc i => acc ^^^ h i) b) := by
  intro row
  induction row with
  | nil => intro a b; rfl
  | cons i t ih =>
    intro a b
    simp only [List.foldl_cons]
    rw [show (a ^^^ b) ^^^ (g i ^^^ h i) = (a ^^^ g i) ^^^ (b ^^^ h i) from by
      simp only [Nat.xor_assoc]
      congr 1
      rw [← Nat.xor_assoc, Nat.xor_comm b (g i), Nat.xor_assoc]]
    exact ih _ _

theorem gateM_xor {m n : Nat} (hm : gateM m = true) (hn : gateM n = true) :
    gateM (m ^^^ n) = true := by
  unfold gateM at *
  rw [List.all_eq_true] at hm hn ⊢
  intro row hrow
  have hmr := hm row hrow
  have hnr := hn row hrow
  rw [beq_iff_eq] at hmr hnr ⊢
  have hterm : ∀ i, ((m ^^^ n) >>> i) &&& 1 = ((m >>> i) &&& 1) ^^^ ((n >>> i) &&& 1) := by
    intro i; rw [Nat.shiftRight_xor_distrib, Nat.and_xor_distrib_right]
  rw [show (fun acc i => acc ^^^ (((m ^^^ n) >>> i) &&& 1))
        = (fun acc i => acc ^^^ (((m >>> i) &&& 1) ^^^ ((n >>> i) &&& 1))) from by
      funext acc i; rw [hterm]]
  have hsplit := foldl_xor_split (fun i => (m >>> i) &&& 1) (fun i => (n >>> i) &&& 1) row 0 0
  simp only [Nat.xor_zero] at hsplit
  rw [hsplit, hmr, hnr]
  rfl

theorem gateM_zero : gateM 0 = true := by native_decide



/-! ## Native-decide cores (the combinatorial heart) -/

theorem hexA_correct : ∀ g : Fin 36,
    hexA.getD g.val 0 = bitmaskOf (conv baseA (Pi.single (cellOf g.val) 1)) := by native_decide
theorem gate_hexA : ∀ g : Fin 36, gateM (hexA.getD g.val 0) = true := by native_decide
theorem hexB_correct : ∀ g : Fin 36,
    hexB.getD g.val 0 = bitmaskOf (conv baseB (Pi.single (cellOf g.val) 1)) := by native_decide

theorem classifyCore : ∀ q₁ q₂ q₃ q₄ : Fin 36,
    gateM (supMask [0, q₁, q₂, q₃, q₄]) = true →
    isHexDpairA (supMask [0, q₁, q₂, q₃, q₄]) = true
      ∨ 10 < wtM (supMask [0, q₁, q₂, q₃, q₄]) + minBcoset (supMask [0, q₁, q₂, q₃, q₄]) := by
  native_decide

theorem classifyCoreEven : ∀ q₁ q₂ q₃ : Fin 36,
    gateM (supMask [0, q₁, q₂, q₃]) = true →
    3 ≤ wtM (supMask [0, q₁, q₂, q₃]) →
    isHexDpairA (supMask [0, q₁, q₂, q₃]) = true
      ∨ 10 < wtM (supMask [0, q₁, q₂, q₃]) + minBcoset (supMask [0, q₁, q₂, q₃]) := by
  native_decide

/-! ## Generic XOR-lift (additive map into an XOR-closed predicate, basis ⟹ all) -/

theorem xorLift (M : (BaseGroup → ZMod 2) → Nat) (P : Nat → Prop)
    (hM0 : M 0 = 0)
    (hadd : ∀ a b, M (a + b) = M a ^^^ M b)
    (hP0 : P 0)
    (hPxor : ∀ m n, P m → P n → P (m ^^^ n))
    (hbasis : ∀ g, P (M (Pi.single g 1)))
    (b : BaseGroup → ZMod 2) : P (M b) := by
  have key : ∀ S : Finset BaseGroup, P (M (ind S)) := by
    intro S
    induction S using Finset.induction with
    | empty => rw [ind_empty, hM0]; exact hP0
    | @insert p S hp ih => rw [ind_insert hp, hadd]; exact hPxor _ _ (hbasis p) ih
  rw [self_eq_ind_filter b]; exact key _

theorem gateM_conv_baseA (z : BaseGroup → ZMod 2) :
    gateM (bitmaskOf (conv baseA z)) = true := by
  apply xorLift (fun w => bitmaskOf (conv baseA w)) (fun m => gateM m = true)
  · show bitmaskOf (conv baseA 0) = 0
    rw [show conv baseA (0 : BaseGroup → ZMod 2) = 0 from by funext g; simp [conv_apply],
      bitmaskOf_zero]
  · intro a b; show bitmaskOf (conv baseA (a + b)) = _
    rw [conv_add_right, bitmaskOf_add]
  · exact gateM_zero
  · intro m n hm hn; exact gateM_xor hm hn
  · intro g
    show gateM (bitmaskOf (conv baseA (Pi.single g 1))) = true
    have hk : cellOf (idxOf g) = g := cellOf_idxOf g
    have hc := hexA_correct ⟨idxOf g, idxOf_lt g⟩
    rw [hk] at hc
    rw [← hc]
    exact gate_hexA ⟨idxOf g, idxOf_lt g⟩



/-! ## §D the B-block coset membership -/

theorem xorLeftComm (a b c : Nat) : a ^^^ (b ^^^ c) = b ^^^ (a ^^^ c) := by
  rw [← Nat.xor_assoc, Nat.xor_comm a b, Nat.xor_assoc]

theorem xor4comm (p q r s : Nat) : (p ^^^ q) ^^^ (r ^^^ s) = (p ^^^ r) ^^^ (q ^^^ s) := by
  rw [Nat.xor_assoc, Nat.xor_assoc, xorLeftComm q r s]

theorem bit_cond (m i : Nat) : ((m >>> i) &&& 1 == 1) = m.testBit i := by
  rw [bit_and_one]; cases m.testBit i <;> simp

theorem selXor_zero (cols : Nat → Nat) (n : Nat) : selXor cols n 0 = 0 := by
  unfold selXor
  have : (fun (acc : Nat) (i : Nat) => if (0 : Nat).testBit i then acc ^^^ cols i else acc)
      = (fun acc _ => acc) := by funext acc i; rw [Nat.zero_testBit]; rfl
  rw [this]
  clear this
  induction (List.range n) with
  | nil => rfl
  | cons a t ih => rw [List.foldl_cons]; exact ih

theorem selXor_xor (cols : Nat → Nat) (n m m' : Nat) :
    selXor cols n (m ^^^ m') = selXor cols n m ^^^ selXor cols n m' := by
  unfold selXor
  rw [show (fun acc i => if (m ^^^ m').testBit i then acc ^^^ cols i else acc)
        = (fun acc i => acc ^^^ ((if m.testBit i then cols i else 0)
            ^^^ (if m'.testBit i then cols i else 0))) from by
      funext acc i; rw [Nat.testBit_xor]; cases m.testBit i <;> cases m'.testBit i <;> simp]
  rw [show (fun acc i => if m.testBit i then acc ^^^ cols i else acc)
        = (fun acc i => acc ^^^ (if m.testBit i then cols i else 0)) from by
      funext acc i; cases m.testBit i <;> simp]
  rw [show (fun acc i => if m'.testBit i then acc ^^^ cols i else acc)
        = (fun acc i => acc ^^^ (if m'.testBit i then cols i else 0)) from by
      funext acc i; cases m'.testBit i <;> simp]
  have h := foldl_xor_split (fun i => if m.testBit i then cols i else 0)
    (fun i => if m'.testBit i then cols i else 0) (List.range n) 0 0
  simpa using h

theorem applyCols_eq (cols : Array Nat) (m : Nat) :
    applyCols cols m = selXor (fun i => cols.getD i 0) 36 m := by
  unfold applyCols selXor
  congr 1; funext acc i; rw [bit_cond]

theorem applyCols_xor (cols : Array Nat) (m n : Nat) :
    applyCols cols (m ^^^ n) = applyCols cols m ^^^ applyCols cols n := by
  rw [applyCols_eq, applyCols_eq, applyCols_eq, selXor_xor]

theorem applyCols_zero (cols : Array Nat) : applyCols cols 0 = 0 := by
  rw [applyCols_eq, selXor_zero]

theorem bOffset_xor (a b : Nat) : bOffset (a ^^^ b) = bOffset a ^^^ bOffset b := by
  unfold bOffset; exact selXor_xor _ _ _ _

/-- Membership in the 6-dimensional B-coset span (decidable: bounded `∃`). -/
def inBspan (x : Nat) : Prop := ∃ c : Fin 64, bOffset c.val = x

local instance : DecidablePred inBspan := fun x =>
  inferInstanceAs (Decidable (∃ c : Fin 64, bOffset c.val = x))

theorem inBspan_zero : inBspan 0 := ⟨⟨0, by norm_num⟩, by unfold bOffset; exact selXor_zero _ _⟩

theorem inBspan_xor {x y : Nat} (hx : inBspan x) (hy : inBspan y) : inBspan (x ^^^ y) := by
  obtain ⟨c, hc⟩ := hx
  obtain ⟨c', hc'⟩ := hy
  have e : (2 : Nat) ^ 6 = 64 := by norm_num
  have hc6 : c.val < 2 ^ 6 := by rw [e]; exact c.isLt
  have hc'6 : c'.val < 2 ^ 6 := by rw [e]; exact c'.isLt
  have hlt : c.val ^^^ c'.val < 64 := by
    have h := Nat.xor_lt_two_pow hc6 hc'6; rwa [e] at h
  exact ⟨⟨c.val ^^^ c'.val, hlt⟩, by rw [bOffset_xor, hc, hc']⟩

/-- The coset-defect map: `Φ f = MBA·(Â-block) ⊕ (B̂-block)`, lands in `Bspan`. -/
def Phi (f : BaseGroup → ZMod 2) : Nat :=
  applyCols MBAcols (bitmaskOf (conv baseA f)) ^^^ bitmaskOf (conv baseB f)

theorem Phi_zero : Phi 0 = 0 := by
  unfold Phi
  rw [show conv baseA (0 : BaseGroup → ZMod 2) = 0 from by funext g; simp [conv_apply],
      show conv baseB (0 : BaseGroup → ZMod 2) = 0 from by funext g; simp [conv_apply],
      bitmaskOf_zero, applyCols_zero, Nat.xor_zero]

theorem Phi_add (a b : BaseGroup → ZMod 2) : Phi (a + b) = Phi a ^^^ Phi b := by
  unfold Phi
  rw [conv_add_right, conv_add_right, bitmaskOf_add, bitmaskOf_add, applyCols_xor]
  exact xor4comm _ _ _ _

theorem coset_basis : ∀ g : Fin 36,
    inBspan (applyCols MBAcols (hexA.getD g.val 0) ^^^ hexB.getD g.val 0) := by
  native_decide

theorem coset_mem (f : BaseGroup → ZMod 2) : inBspan (Phi f) := by
  apply xorLift Phi inBspan Phi_zero Phi_add inBspan_zero (fun _ _ => inBspan_xor)
  intro g
  have hk := cellOf_idxOf g
  have hA := hexA_correct ⟨idxOf g, idxOf_lt g⟩
  have hB := hexB_correct ⟨idxOf g, idxOf_lt g⟩
  rw [hk] at hA hB
  change inBspan (Phi (Pi.single g 1))
  unfold Phi
  rw [← hA, ← hB]
  exact coset_basis ⟨idxOf g, idxOf_lt g⟩

/-! ## §E the minBcoset lower bound -/

theorem foldl_min_le_init (f : Nat → Nat) :
    ∀ (L : List Nat) (init : Nat), L.foldl (fun acc x => min acc (f x)) init ≤ init := by
  intro L
  induction L with
  | nil => intro init; exact le_refl _
  | cons a t ih => intro init; rw [List.foldl_cons]; exact le_trans (ih _) (min_le_left _ _)

theorem foldl_min_le (f : Nat → Nat) :
    ∀ (L : List Nat) (init c : Nat), c ∈ L →
      L.foldl (fun acc x => min acc (f x)) init ≤ f c := by
  intro L
  induction L with
  | nil => intro init c hc; exact absurd hc (List.not_mem_nil)
  | cons a t ih =>
    intro init c hc
    rw [List.foldl_cons]
    rcases List.mem_cons.mp hc with rfl | hct
    · exact le_trans (foldl_min_le_init f t (min init (f c))) (min_le_right _ _)
    · exact ih _ c hct

theorem minBcoset_le_bwt (f : BaseGroup → ZMod 2) :
    minBcoset (bitmaskOf (conv baseA f)) ≤ bwt (conv baseB f) := by
  obtain ⟨c, hc⟩ := coset_mem f
  simp only [Phi] at hc
  have hrw : bitmaskOf (conv baseB f)
      = applyCols MBAcols (bitmaskOf (conv baseA f)) ^^^ bOffset c.val := by
    rw [hc, ← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]
  calc minBcoset (bitmaskOf (conv baseA f))
      ≤ wtM (applyCols MBAcols (bitmaskOf (conv baseA f)) ^^^ bOffset c.val) := by
        unfold minBcoset
        exact foldl_min_le _ (List.range 64) 99 c.val (List.mem_range.mpr c.isLt)
    _ = wtM (bitmaskOf (conv baseB f)) := by rw [← hrw]
    _ = bwt (conv baseB f) := wtM_eq_bwt _



/-! ## §F isHexDpairA → function-level hexagon / D-pair witness -/

/-- The 12 D-pair directions, in the order matching `gdMaps`
(identical to `pairDirections`). -/
def dpairDirList : List BaseGroup :=
  [(0, 1), (0, 5), (3, 1), (3, 2), (3, 4), (3, 5),
   (1, 0), (1, 3), (2, 3), (4, 3), (5, 0), (5, 3)]

theorem gdMaps_lt : ∀ k : Fin 12, ∀ g : Fin 36,
    (gdMaps.getD k.val #[]).getD g.val 0 < 36 := by native_decide

theorem gdMaps_dir : ∀ k : Fin 12, ∀ g : Fin 36,
    cellOf ((gdMaps.getD k.val #[]).getD g.val 0)
      = cellOf g.val + dpairDirList.getD k.val 0 := by native_decide

theorem dpairDirList_mem : ∀ k : Fin 12, dpairDirList.getD k.val 0 ∈ pairDirections := by decide

/-- A gated A-block recognised as hexagon/D-pair lifts to a function-level witness:
its `conv baseA` equals that of a single hexagon, or of a D-pair `δ_g + δ_{g+d}`. -/
theorem isHexDpairA_witness (f : BaseGroup → ZMod 2)
    (h : isHexDpairA (bitmaskOf (conv baseA f)) = true) :
    (∃ g : BaseGroup, conv baseA f = conv baseA (Pi.single g 1)) ∨
    (∃ g : BaseGroup, ∃ d ∈ pairDirections,
        conv baseA f = conv baseA (Pi.single g 1 + Pi.single (g + d) 1)) := by
  unfold isHexDpairA at h
  rw [Bool.or_eq_true] at h
  rcases h with hHex | hDp
  · left
    unfold isHexA at hHex
    rw [List.any_eq_true] at hHex
    obtain ⟨g, hg_mem, hg_eq⟩ := hHex
    rw [List.mem_range] at hg_mem
    rw [beq_iff_eq] at hg_eq
    refine ⟨cellOf g, ?_⟩
    apply bitmaskOf_injective
    rw [hg_eq]
    exact hexA_correct ⟨g, hg_mem⟩
  · right
    unfold isDpairA at hDp
    rw [List.any_eq_true] at hDp
    obtain ⟨g, hg_mem, hk⟩ := hDp
    rw [List.mem_range] at hg_mem
    rw [List.any_eq_true] at hk
    obtain ⟨k, hk_mem, hk_eq⟩ := hk
    rw [List.mem_range] at hk_mem
    rw [beq_iff_eq] at hk_eq
    refine ⟨cellOf g, dpairDirList.getD k 0, dpairDirList_mem ⟨k, hk_mem⟩, ?_⟩
    apply bitmaskOf_injective
    have hd : cellOf g + dpairDirList.getD k 0 = cellOf ((gdMaps.getD k #[]).getD g 0) :=
      (gdMaps_dir ⟨k, hk_mem⟩ ⟨g, hg_mem⟩).symm
    rw [conv_add_right, bitmaskOf_add, hk_eq, hd,
        ← hexA_correct ⟨g, hg_mem⟩,
        ← hexA_correct ⟨(gdMaps.getD k #[]).getD g 0, gdMaps_lt ⟨k, hk_mem⟩ ⟨g, hg_mem⟩⟩]



/-! ## §G support extraction: `bitmaskOf a` as a `supMask` of explicit indices -/

theorem foldl_xor_init (g : Fin 36 → Nat) :
    ∀ (L : List (Fin 36)) (s : Nat),
      L.foldl (fun acc i => acc ^^^ g i) s = s ^^^ L.foldl (fun acc i => acc ^^^ g i) 0 := by
  intro L
  induction L with
  | nil => intro s; simp
  | cons a t ih =>
    intro s
    rw [List.foldl_cons, List.foldl_cons, ih (s ^^^ g a), ih (0 ^^^ g a),
      Nat.zero_xor, Nat.xor_assoc]

theorem supMask_append (L M : List (Fin 36)) :
    supMask (L ++ M) = supMask L ^^^ supMask M := by
  unfold supMask; rw [List.foldl_append, foldl_xor_init]

theorem supMask_singleton (x : Fin 36) : supMask [x] = 1 <<< x.val := by
  unfold supMask; simp

theorem supMask_cons (a : Fin 36) (t : List (Fin 36)) :
    supMask (a :: t) = 1 <<< a.val ^^^ supMask t := by
  rw [show (a :: t) = [a] ++ t from rfl, supMask_append, supMask_singleton]

theorem supMask_replicate_even (x : Fin 36) :
    ∀ k, supMask (List.replicate (2 * k) x) = 0 := by
  intro k
  induction k with
  | zero => rfl
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 from by ring, List.replicate_succ, List.replicate_succ,
      show (x :: x :: List.replicate (2 * n) x) = ([x] ++ [x]) ++ List.replicate (2 * n) x from rfl,
      supMask_append, supMask_append, ih, supMask_singleton, Nat.xor_self]
    simp

theorem testBit_supMask (L : List (Fin 36)) (j : Nat) :
    (supMask L).testBit j = decide (Odd ((L.countP (fun i => i.val == j)))) := by
  induction L with
  | nil => simp [supMask]
  | cons a t ih =>
    rw [supMask_cons, Nat.testBit_xor, ih, Nat.shiftLeft_eq, one_mul, Nat.testBit_two_pow,
      List.countP_cons]
    by_cases h : a.val = j
    · simp only [h, decide_true, beq_self_eq_true, if_true, Bool.true_xor,
        Nat.odd_add_one, decide_not]
    · have hb : (a.val == j) = false := by simp [h]
      simp only [h, decide_false, Bool.false_xor]
      rw [hb]; simp

theorem supMask_perm {L L' : List (Fin 36)} (h : L.Perm L') : supMask L = supMask L' := by
  apply Nat.eq_of_testBit_eq; intro j
  rw [testBit_supMask, testBit_supMask, h.countP_eq]

/-- The set-bit indices of the chain `a` (as `Fin 36` cell indices), in ascending order. -/
def setBits (a : BaseGroup → ZMod 2) : List (Fin 36) :=
  (List.finRange 36).filter (fun i => decide (a (cellOf i.val) = 1))

theorem supMask_setBits (a : BaseGroup → ZMod 2) : supMask (setBits a) = bitmaskOf a := by
  unfold supMask setBits bitmaskOf
  rw [List.foldl_filter, ← List.map_coe_finRange_eq_range, List.foldl_map]
  congr 1
  funext acc i
  simp only [decide_eq_true_eq]

theorem setBits_length (a : BaseGroup → ZMod 2) : (setBits a).length = bwt a := by
  have hnd : (setBits a).Nodup := (List.nodup_finRange 36).filter _
  rw [← List.toFinset_card_of_nodup hnd]
  unfold bwt
  apply Finset.card_bij' (fun i _ => cellOf i.val) (fun g _ => (⟨idxOf g, idxOf_lt g⟩ : Fin 36))
  · intro i hi
    simp only [List.mem_toFinset, setBits, List.mem_filter, List.mem_finRange, true_and,
      decide_eq_true_eq] at hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hi
  · intro g hg
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg
    simp only [List.mem_toFinset, setBits, List.mem_filter, List.mem_finRange, true_and,
      decide_eq_true_eq]
    rw [cellOf_idxOf]; exact hg
  · intro i hi
    simp only [List.mem_toFinset, setBits, List.mem_filter, List.mem_finRange, true_and,
      decide_eq_true_eq] at hi
    apply Fin.ext
    exact idxOf_cellOf i.isLt
  · intro g _; exact cellOf_idxOf g



/-! ### Reshaping the support list into the `supMask [0, …]` scan form. -/

theorem origin_mem_setBits {a : BaseGroup → ZMod 2} (horig : a (0, 0) = 1) :
    (0 : Fin 36) ∈ setBits a := by
  unfold setBits
  rw [List.mem_filter]
  exact ⟨List.mem_finRange _, by simp only [decide_eq_true_eq]; exact horig⟩

/-- Padding the (origin-erased) support with an even number of origin indices and
prepending the origin recovers `bitmaskOf a` — the key reshape identity. -/
theorem supMask_pad_eq (a : BaseGroup → ZMod 2) (horig : a (0, 0) = 1)
    (pad : Nat) (hpad : Even pad) :
    supMask ((0 : Fin 36) :: ((setBits a).erase 0 ++ List.replicate pad 0)) = bitmaskOf a := by
  have hperm : (setBits a).Perm ((0 : Fin 36) :: (setBits a).erase 0) :=
    List.perm_cons_erase (origin_mem_setBits horig)
  obtain ⟨t, ht⟩ := hpad
  have hpad0 : supMask (List.replicate pad (0 : Fin 36)) = 0 := by
    rw [ht, ← two_mul]; exact supMask_replicate_even 0 t
  rw [supMask_cons, supMask_append, hpad0, Nat.xor_zero, ← supMask_cons,
    ← supMask_perm hperm, supMask_setBits]

/-- Odd-weight (≤5) origin-containing A-blocks are `supMask [0,q₁,q₂,q₃,q₄]`. -/
theorem exists_supMask5 (a : BaseGroup → ZMod 2) (horig : a (0, 0) = 1)
    (hwt : bwt a ≤ 5) (hodd : Odd (bwt a)) :
    ∃ q1 q2 q3 q4 : Fin 36, supMask [0, q1, q2, q3, q4] = bitmaskOf a := by
  have herase_len : ((setBits a).erase 0).length = bwt a - 1 := by
    rw [List.length_erase_of_mem (origin_mem_setBits horig), setBits_length]
  obtain ⟨m, hm⟩ := hodd
  have hpad_even : Even (5 - bwt a) := ⟨2 - m, by omega⟩
  have hqs_len : ((setBits a).erase 0 ++ List.replicate (5 - bwt a) (0 : Fin 36)).length = 4 := by
    rw [List.length_append, List.length_replicate, herase_len]; omega
  obtain ⟨q1, q2, q3, q4, hq⟩ := List.length_eq_four.mp hqs_len
  refine ⟨q1, q2, q3, q4, ?_⟩
  rw [show ([0, q1, q2, q3, q4] : List (Fin 36))
      = (0 : Fin 36) :: ((setBits a).erase 0 ++ List.replicate (5 - bwt a) (0 : Fin 36)) from by
    rw [hq]]
  exact supMask_pad_eq a horig (5 - bwt a) hpad_even

/-- Even-weight (≤5, ≥1) origin-containing A-blocks are `supMask [0,q₁,q₂,q₃]`. -/
theorem exists_supMask4 (a : BaseGroup → ZMod 2) (horig : a (0, 0) = 1)
    (hwt : bwt a ≤ 5) (hge : 1 ≤ bwt a) (heven : Even (bwt a)) :
    ∃ q1 q2 q3 : Fin 36, supMask [0, q1, q2, q3] = bitmaskOf a := by
  have herase_len : ((setBits a).erase 0).length = bwt a - 1 := by
    rw [List.length_erase_of_mem (origin_mem_setBits horig), setBits_length]
  obtain ⟨m, hm⟩ := heven
  have hpad_even : Even (4 - bwt a) := ⟨2 - m, by omega⟩
  have hqs_len : ((setBits a).erase 0 ++ List.replicate (4 - bwt a) (0 : Fin 36)).length = 3 := by
    rw [List.length_append, List.length_replicate, herase_len]; omega
  obtain ⟨q1, q2, q3, hq⟩ := List.length_eq_three.mp hqs_len
  refine ⟨q1, q2, q3, ?_⟩
  rw [show ([0, q1, q2, q3] : List (Fin 36))
      = (0 : Fin 36) :: ((setBits a).erase 0 ++ List.replicate (4 - bwt a) (0 : Fin 36)) from by
    rw [hq]]
  exact supMask_pad_eq a horig (4 - bwt a) hpad_even



/-! ## §G′ minimum distance: a gated nonzero A-block has weight ≥ 3 -/

theorem no_gated_weight1 : ∀ i : Fin 36, gateM (1 <<< i.val) = false := by native_decide
theorem no_gated_weight2 : ∀ i j : Fin 36, i ≠ j →
    gateM (1 <<< i.val ^^^ 1 <<< j.val) = false := by native_decide

theorem gated_bwt_ge3 (b : BaseGroup → ZMod 2) (hgate : gateM (bitmaskOf b) = true)
    (hge1 : 1 ≤ bwt b) : 3 ≤ bwt b := by
  by_contra hlt
  have hcases : bwt b = 1 ∨ bwt b = 2 := by omega
  have hlen := setBits_length b
  rcases hcases with h1 | h2
  · rw [h1] at hlen
    obtain ⟨x, hx⟩ := List.length_eq_one_iff.mp hlen
    have hbm : bitmaskOf b = 1 <<< x.val := by rw [← supMask_setBits, hx, supMask_singleton]
    rw [hbm, no_gated_weight1] at hgate
    exact absurd hgate (by simp)
  · rw [h2] at hlen
    obtain ⟨x, y, hxy⟩ := List.length_eq_two.mp hlen
    have hne : x ≠ y := by
      have hnd : (setBits b).Nodup := (List.nodup_finRange 36).filter _
      rw [hxy] at hnd; simp only [List.nodup_cons, List.mem_singleton, List.nodup_nil,
        and_true] at hnd; exact hnd.1
    have hbm : bitmaskOf b = 1 <<< x.val ^^^ 1 <<< y.val := by
      rw [← supMask_setBits, hxy, supMask_cons, supMask_singleton]
    rw [hbm, no_gated_weight2 x y hne] at hgate
    exact absurd hgate (by simp)



/-! ## §H master classification of a light A-block (origin-normalized) -/

/-- The heart of the classification: an origin-normalized A-block `conv baseA f` of
weight ≤ 5 whose boundary is light (`bwt A + bwt B ≤ 10`) is a hexagon or D-pair
A-block. -/
theorem classify_master (f : BaseGroup → ZMod 2)
    (horig : conv baseA f (0, 0) = 1)
    (hwt5 : bwt (conv baseA f) ≤ 5)
    (hbnd : bwt (conv baseA f) + bwt (conv baseB f) ≤ 10) :
    (∃ g : BaseGroup, conv baseA f = conv baseA (Pi.single g 1)) ∨
    (∃ g : BaseGroup, ∃ d ∈ pairDirections,
        conv baseA f = conv baseA (Pi.single g 1 + Pi.single (g + d) 1)) := by
  have hgate : gateM (bitmaskOf (conv baseA f)) = true := gateM_conv_baseA f
  have hge1 : 1 ≤ bwt (conv baseA f) := by
    unfold bwt
    exact Finset.card_pos.mpr ⟨(0, 0), Finset.mem_filter.mpr ⟨Finset.mem_univ _, horig⟩⟩
  have hge3 : 3 ≤ bwt (conv baseA f) := gated_bwt_ge3 (conv baseA f) hgate hge1
  have hmb : minBcoset (bitmaskOf (conv baseA f)) ≤ bwt (conv baseB f) := minBcoset_le_bwt f
  have hclass : isHexDpairA (bitmaskOf (conv baseA f)) = true := by
    rcases Nat.even_or_odd (bwt (conv baseA f)) with heven | hodd
    · obtain ⟨q1, q2, q3, hq⟩ := exists_supMask4 (conv baseA f) horig hwt5 (by omega) heven
      have hgate' : gateM (supMask [0, q1, q2, q3]) = true := by rw [hq]; exact hgate
      have h3 : 3 ≤ wtM (supMask [0, q1, q2, q3]) := by rw [hq, wtM_eq_bwt]; exact hge3
      rcases classifyCoreEven q1 q2 q3 hgate' h3 with hhd | hbig
      · rw [hq] at hhd; exact hhd
      · exfalso; rw [hq, wtM_eq_bwt] at hbig; omega
    · obtain ⟨q1, q2, q3, q4, hq⟩ := exists_supMask5 (conv baseA f) horig hwt5 hodd
      have hgate' : gateM (supMask [0, q1, q2, q3, q4]) = true := by rw [hq]; exact hgate
      rcases classifyCore q1 q2 q3 q4 hgate' with hhd | hbig
      · rw [hq] at hhd; exact hhd
      · exfalso; rw [hq, wtM_eq_bwt] at hbig; omega
  exact isHexDpairA_witness f hclass



/-! ## §H translation normalization and the A-lighter classification -/

/-- A boundary of weight ≤ 11 has weight ≤ 10 (it is a cycle, hence even weight). -/
theorem boundary_weight_le_ten (f : BaseGroup → ZMod 2)
    (h11 : (Finset.univ.filter fun j : BaseGroup × Fin 2 =>
      bbBoundary2Fn baseA baseB f j ≠ 0).card ≤ 11) :
    (Finset.univ.filter fun j : BaseGroup × Fin 2 =>
      bbBoundary2Fn baseA baseB f j ≠ 0).card ≤ 10 := by
  have he : (Finset.univ.filter fun j : BaseGroup × Fin 2 =>
      bbBoundary2Fn baseA baseB f j ≠ 0).card % 2 = 0 :=
    cycle_weight_even (bbBoundary2Fn baseA baseB f) (bbBoundaryFn_comp baseA baseB f)
  omega

theorem translate_neg_translate (c : BaseGroup) (v : BaseGroup → ZMod 2) :
    translate (-c) (translate c v) = v := by
  funext g; change v (g + -c + c) = v g; congr 1; abel

theorem translate_add (c : BaseGroup) (u v : BaseGroup → ZMod 2) :
    translate c (u + v) = translate c u + translate c v := by funext g; rfl

theorem translate_single (c g : BaseGroup) :
    translate (-c) (Pi.single g 1) = Pi.single (g + c) 1 := by
  funext x
  change (Pi.single g 1 : BaseGroup → ZMod 2) (x + -c)
    = (Pi.single (g + c) 1 : BaseGroup → ZMod 2) x
  rw [Pi.single_apply, Pi.single_apply]
  congr 1
  apply propext
  constructor
  · intro h; rw [← h]; abel
  · intro h; rw [h]; abel

theorem bwt_translate (c : BaseGroup) (v : BaseGroup → ZMod 2) :
    bwt (translate c v) = bwt v := by
  unfold bwt
  apply Finset.card_bij' (fun g _ => g + c) (fun g _ => g - c)
  · intro g hg
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg ⊢
    rw [show (g + c) = g + c from rfl]; exact hg
  · intro g hg
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg ⊢
    show translate c v (g - c) = 1
    rw [show translate c v (g - c) = v ((g - c) + c) from rfl, sub_add_cancel]; exact hg
  · intro g _; show g + c - c = g; abel
  · intro g _; show g - c + c = g; abel

/-- The A-lighter classification: if the (necessarily nonzero) A-block of a light
boundary has weight ≤ 5, the boundary is a hexagon or D-pair. -/
theorem classify_Alighter (f : BaseGroup → ZMod 2)
    (hAne : conv baseA f ≠ 0)
    (hle10 : (Finset.univ.filter fun j : BaseGroup × Fin 2 =>
      bbBoundary2Fn baseA baseB f j ≠ 0).card ≤ 10)
    (hAlight : bwt (conv baseA f) ≤ 5) :
    (∃ g : BaseGroup, bbBoundary2Fn baseA baseB f
        = bbBoundary2Fn baseA baseB (Pi.single g 1)) ∨
    (∃ g : BaseGroup, ∃ d ∈ pairDirections, bbBoundary2Fn baseA baseB f
        = bbBoundary2Fn baseA baseB (Pi.single g 1 + Pi.single (g + d) 1)) := by
  obtain ⟨c, hc⟩ : ∃ c, conv baseA f c = 1 := by
    by_contra hcon
    push Not at hcon
    apply hAne
    funext x
    have h := hcon x
    change conv baseA f x = (0 : ZMod 2)
    revert h; generalize conv baseA f x = u; revert u; decide
  have hAf' : conv baseA (translate c f) = translate c (conv baseA f) := conv_translate baseA f c
  have hBf' : conv baseB (translate c f) = translate c (conv baseB f) := conv_translate baseB f c
  have horig : conv baseA (translate c f) (0, 0) = 1 := by
    rw [hAf']
    change conv baseA f ((0 : BaseGroup) + c) = 1
    rw [zero_add]
    exact hc
  have hAwt' : bwt (conv baseA (translate c f)) ≤ 5 := by rw [hAf', bwt_translate]; exact hAlight
  have hbnd : bwt (conv baseA (translate c f)) + bwt (conv baseB (translate c f)) ≤ 10 := by
    rw [hAf', hBf', bwt_translate, bwt_translate]
    exact le_trans (bwt_blocks_le_boundary f) hle10
  rcases classify_master (translate c f) horig hAwt' hbnd with ⟨g', hg'⟩ | ⟨g', d, hd, hg'⟩
  · left
    refine ⟨g' + c, ?_⟩
    apply transfer_hexagon f (g' + c) ?_ hle10
    have hh : translate c (conv baseA f) = conv baseA (Pi.single g' 1) := by rw [← hAf']; exact hg'
    have h2 : conv baseA f = translate (-c) (conv baseA (Pi.single g' 1)) := by
      rw [← hh, translate_neg_translate]
    rw [h2, ← conv_translate, translate_single]
  · right
    refine ⟨g' + c, d, hd, ?_⟩
    apply transfer_dpair f (g' + c) d hd ?_ hle10
    have hh : translate c (conv baseA f)
        = conv baseA (Pi.single g' 1 + Pi.single (g' + d) 1) := by rw [← hAf']; exact hg'
    have h2 : conv baseA f
        = translate (-c) (conv baseA (Pi.single g' 1 + Pi.single (g' + d) 1)) := by
      rw [← hh, translate_neg_translate]
    rw [h2, ← conv_translate, translate_add, translate_single, translate_single,
      show (g' + d) + c = (g' + c) + d from by abel]



/-! ## §J the x ↔ y swap (B-lighter case) and the assembly -/

/-- The coordinate swap `(a,b) ↦ (b,a)`, which exchanges `baseA` and `baseB`. -/
def swap (g : BaseGroup) : BaseGroup := (g.2, g.1)
def swapFn (v : BaseGroup → ZMod 2) : BaseGroup → ZMod 2 := fun g => v (swap g)

theorem swap_swap (g : BaseGroup) : swap (swap g) = g := rfl
theorem swapFn_apply (v : BaseGroup → ZMod 2) (g : BaseGroup) : swapFn v g = v (swap g) := rfl
theorem swapFn_zero : swapFn (0 : BaseGroup → ZMod 2) = 0 := rfl
theorem swapFn_add (u v : BaseGroup → ZMod 2) : swapFn (u + v) = swapFn u + swapFn v := rfl

theorem swapFn_injective {u v : BaseGroup → ZMod 2} (h : swapFn u = swapFn v) : u = v := by
  funext x
  have hx := congrFun h (swap x)
  rwa [swapFn_apply, swapFn_apply, swap_swap] at hx

theorem swapFn_single (g : BaseGroup) :
    swapFn (Pi.single g 1) = Pi.single (swap g) 1 := by
  funext x
  change (Pi.single g 1 : BaseGroup → ZMod 2) (swap x)
    = (Pi.single (swap g) 1 : BaseGroup → ZMod 2) x
  rw [Pi.single_apply, Pi.single_apply]
  congr 1
  apply propext
  constructor
  · intro h; rw [← h, swap_swap]
  · intro h; rw [h, swap_swap]

theorem funLift (M N : (BaseGroup → ZMod 2) → (BaseGroup → ZMod 2))
    (hM0 : M 0 = 0) (hN0 : N 0 = 0)
    (hMadd : ∀ a b, M (a + b) = M a + M b) (hNadd : ∀ a b, N (a + b) = N a + N b)
    (hbasis : ∀ g, M (Pi.single g 1) = N (Pi.single g 1)) (f : BaseGroup → ZMod 2) : M f = N f := by
  have key : ∀ S : Finset BaseGroup, M (ind S) = N (ind S) := by
    intro S
    induction S using Finset.induction with
    | empty => rw [ind_empty, hM0, hN0]
    | @insert p S hp ih => rw [ind_insert hp, hMadd, hNadd, hbasis p, ih]
  rw [self_eq_ind_filter f]; exact key _

theorem conv_zero_right (P : BaseGroup → ZMod 2) : conv P 0 = 0 := by
  funext g; simp [conv_apply]

theorem swap_basisA : ∀ g x : BaseGroup,
    conv baseA (swapFn (Pi.single g 1)) x = swapFn (conv baseB (Pi.single g 1)) x := by
  native_decide
theorem swap_basisB : ∀ g x : BaseGroup,
    conv baseB (swapFn (Pi.single g 1)) x = swapFn (conv baseA (Pi.single g 1)) x := by
  native_decide

theorem swap_convA (f : BaseGroup → ZMod 2) :
    conv baseA (swapFn f) = swapFn (conv baseB f) := by
  apply funLift (fun f => conv baseA (swapFn f)) (fun f => swapFn (conv baseB f))
  · show conv baseA (swapFn 0) = 0
    rw [swapFn_zero, conv_zero_right]
  · show swapFn (conv baseB 0) = 0
    rw [conv_zero_right, swapFn_zero]
  · intro a b; show conv baseA (swapFn (a + b)) = _
    rw [swapFn_add, conv_add_right]
  · intro a b; show swapFn (conv baseB (a + b)) = _
    rw [conv_add_right, swapFn_add]
  · intro g; funext x; exact swap_basisA g x

theorem swap_convB (f : BaseGroup → ZMod 2) :
    conv baseB (swapFn f) = swapFn (conv baseA f) := by
  apply funLift (fun f => conv baseB (swapFn f)) (fun f => swapFn (conv baseA f))
  · show conv baseB (swapFn 0) = 0
    rw [swapFn_zero, conv_zero_right]
  · show swapFn (conv baseA 0) = 0
    rw [conv_zero_right, swapFn_zero]
  · intro a b; show conv baseB (swapFn (a + b)) = _
    rw [swapFn_add, conv_add_right]
  · intro a b; show swapFn (conv baseA (a + b)) = _
    rw [conv_add_right, swapFn_add]
  · intro g; funext x; exact swap_basisB g x

theorem bwt_swapFn (v : BaseGroup → ZMod 2) : bwt (swapFn v) = bwt v := by
  unfold bwt
  apply Finset.card_bij' (fun g _ => swap g) (fun g _ => swap g)
  · intro g hg
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg ⊢
    rw [swapFn_apply] at hg; exact hg
  · intro g hg
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg ⊢
    rw [swapFn_apply, swap_swap]; exact hg
  · intro g _; exact swap_swap g
  · intro g _; exact swap_swap g

/-- B-side one-block lemma (via the swap): `conv baseB w = 0`, `conv baseA w ≠ 0`
forces `|conv baseA w| ≥ 16`. -/
theorem oneBlock_ge16_B (w : BaseGroup → ZMod 2) (hB : conv baseB w = 0)
    (hA : conv baseA w ≠ 0) : 16 ≤ bwt (conv baseA w) := by
  have hA' : conv baseA (swapFn w) = 0 := by rw [swap_convA, hB, swapFn_zero]
  have hB' : conv baseB (swapFn w) ≠ 0 := by
    rw [swap_convB]; intro h; exact hA (swapFn_injective (h.trans swapFn_zero.symm))
  have h16 := oneBlock_ge16 (swapFn w) hA' hB'
  rwa [swap_convB, bwt_swapFn] at h16

/-- Boundary-level swap: swap the cell coordinate and the A/B block. -/
def swapF2 (j : Fin 2) : Fin 2 := if j = 0 then 1 else 0
def bnSwap (b : BaseGroup × Fin 2 → ZMod 2) : BaseGroup × Fin 2 → ZMod 2 :=
  fun p => b (swap p.1, swapF2 p.2)

theorem boundary_swapFn (f : BaseGroup → ZMod 2) :
    bbBoundary2Fn baseA baseB (swapFn f) = bnSwap (bbBoundary2Fn baseA baseB f) := by
  funext p
  obtain ⟨h, j⟩ := p
  change (if j = 0 then conv baseA (swapFn f) h else conv baseB (swapFn f) h)
    = bbBoundary2Fn baseA baseB f (swap h, swapF2 j)
  have hA : conv baseA (swapFn f) h = conv baseB f (swap h) := by rw [swap_convA, swapFn_apply]
  have hB : conv baseB (swapFn f) h = conv baseA f (swap h) := by rw [swap_convB, swapFn_apply]
  rw [hA, hB]
  fin_cases j
  · change (if (0 : Fin 2) = 0 then conv baseB f (swap h) else conv baseA f (swap h))
      = bbBoundary2Fn baseA baseB f (swap h, swapF2 0)
    rw [if_pos rfl]; rfl
  · change (if (1 : Fin 2) = 0 then conv baseB f (swap h) else conv baseA f (swap h))
      = bbBoundary2Fn baseA baseB f (swap h, swapF2 1)
    rw [if_neg (by decide)]; rfl

theorem bnSwap_bnSwap (b : BaseGroup × Fin 2 → ZMod 2) : bnSwap (bnSwap b) = b := by
  funext p; obtain ⟨h, j⟩ := p
  change b (swap (swap h), swapF2 (swapF2 j)) = b (h, j)
  rw [swap_swap]; congr 1; fin_cases j <;> rfl

theorem bnSwap_card (b : BaseGroup × Fin 2 → ZMod 2) :
    (Finset.univ.filter fun p : BaseGroup × Fin 2 => bnSwap b p ≠ 0).card
      = (Finset.univ.filter fun p : BaseGroup × Fin 2 => b p ≠ 0).card := by
  apply Finset.card_bij' (fun p _ => (swap p.1, swapF2 p.2)) (fun p _ => (swap p.1, swapF2 p.2))
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, bnSwap] at hp ⊢; exact hp
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, bnSwap] at hp ⊢
    rw [swap_swap]; obtain ⟨h, j⟩ := p; fin_cases j <;> exact hp
  · intro p _; obtain ⟨h, j⟩ := p; change (swap (swap h), swapF2 (swapF2 j)) = (h, j)
    rw [swap_swap]; congr 1; fin_cases j <;> rfl
  · intro p _; obtain ⟨h, j⟩ := p; change (swap (swap h), swapF2 (swapF2 j)) = (h, j)
    rw [swap_swap]; congr 1; fin_cases j <;> rfl

theorem pairDirections_swap : ∀ d ∈ pairDirections, swap d ∈ pairDirections := by decide

/-- The B-lighter classification (transported from the A-side via the swap). -/
theorem classify_Blighter (f : BaseGroup → ZMod 2)
    (hBne : conv baseB f ≠ 0)
    (hle10 : (Finset.univ.filter fun j : BaseGroup × Fin 2 =>
      bbBoundary2Fn baseA baseB f j ≠ 0).card ≤ 10)
    (hBlight : bwt (conv baseB f) ≤ 5) :
    (∃ g : BaseGroup, bbBoundary2Fn baseA baseB f
        = bbBoundary2Fn baseA baseB (Pi.single g 1)) ∨
    (∃ g : BaseGroup, ∃ d ∈ pairDirections, bbBoundary2Fn baseA baseB f
        = bbBoundary2Fn baseA baseB (Pi.single g 1 + Pi.single (g + d) 1)) := by
  have hAne' : conv baseA (swapFn f) ≠ 0 := by
    rw [swap_convA]; intro h; exact hBne (swapFn_injective (h.trans swapFn_zero.symm))
  have hAlight' : bwt (conv baseA (swapFn f)) ≤ 5 := by rw [swap_convA, bwt_swapFn]; exact hBlight
  have hle10' : (Finset.univ.filter fun j : BaseGroup × Fin 2 =>
      bbBoundary2Fn baseA baseB (swapFn f) j ≠ 0).card ≤ 10 := by
    rw [boundary_swapFn, bnSwap_card]; exact hle10
  -- transport an `∂₂(swapFn f) = ∂₂ witness` back to `∂₂ f = ∂₂ (swapFn witness)`
  have htrans : ∀ wit : BaseGroup → ZMod 2,
      bbBoundary2Fn baseA baseB (swapFn f) = bbBoundary2Fn baseA baseB wit →
      bbBoundary2Fn baseA baseB f = bbBoundary2Fn baseA baseB (swapFn wit) := by
    intro wit hw
    rw [boundary_swapFn] at hw
    have h2 := congrArg bnSwap hw
    rw [bnSwap_bnSwap, ← boundary_swapFn] at h2
    exact h2
  rcases classify_Alighter (swapFn f) hAne' hle10' hAlight' with ⟨g, hg⟩ | ⟨g, d, hd, hg⟩
  · left
    refine ⟨swap g, ?_⟩
    have := htrans _ hg
    rwa [swapFn_single] at this
  · right
    refine ⟨swap g, swap d, pairDirections_swap d hd, ?_⟩
    have := htrans _ hg
    rw [swapFn_add, swapFn_single, swapFn_single,
      show swap (g + d) = swap g + swap d from rfl] at this
    exact this

/-! ## The main theorem: the light-stabilizer classification, unconditionally. -/

/-- **The light-stabilizer classification holds** (discharges the `hC` hypothesis):
every nonzero base boundary of weight ≤ 11 is a hexagon or a D-pair. -/
theorem lightStabilizerClassification_holds : LightStabilizerClassification := by
  intro f hne hle11
  have hle10 := boundary_weight_le_ten f hle11
  have hsum : bwt (conv baseA f) + bwt (conv baseB f) ≤ 10 :=
    le_trans (bwt_blocks_le_boundary f) hle10
  have hAne : conv baseA f ≠ 0 := by
    intro hA0
    have hBne0 : conv baseB f ≠ 0 := by
      intro hB0; apply hne; funext p; obtain ⟨h, j⟩ := p
      change (if j = 0 then conv baseA f h else conv baseB f h)
        = (0 : BaseGroup × Fin 2 → ZMod 2) (h, j)
      by_cases hj : j = 0
      · rw [if_pos hj, hA0]; rfl
      · rw [if_neg hj, hB0]; rfl
    have h16 := oneBlock_ge16 f hA0 hBne0
    have hble : bwt (conv baseB f) ≤ 10 := le_trans (bwt_baseB_le_boundary f) hle10
    omega
  have hBne : conv baseB f ≠ 0 := by
    intro hB0
    have hAne0 : conv baseA f ≠ 0 := hAne
    have h16 := oneBlock_ge16_B f hB0 hAne0
    have hale : bwt (conv baseA f) ≤ 10 := by
      have := bwt_blocks_le_boundary f; omega
    omega
  rcases le_total (bwt (conv baseA f)) (bwt (conv baseB f)) with hAB | hBA
  · exact classify_Alighter f hAne hle10 (by omega)
  · exact classify_Blighter f hBne hle10 (by omega)

/-- **The dangerous sector is now unconditional** (`hC` discharged): the (M)-bound
`DangerousSectorGe12` follows from `lightStabilizerClassification_holds`. -/
theorem dangerous_sector_unconditional : DangerousSectorGe12 :=
  dangerous_sector_of_classification lightStabilizerClassification_holds

end Quantum.Stabilizer.Homological.BB.LightStab
