import QEC.Stabilizer.Framework.Homological.BZCertificate
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace Quantum.Stabilizer.Homological.F2Mask.Trellis

open scoped BigOperators

/-- An elementary instruction of a binary trellis. New coefficients enter at
the high state bit; outputs read a parity; the final operation forgets a bit. -/
inductive Instruction
  | read (position : Nat)
  | emit (positions : List Nat) (offset : Bool)
  | forget (position width : Nat)
  deriving Repr

/-- Swap the selected bit with the highest active bit, then discard that highest bit. -/
def forgetBit (position width state : Nat) : Nat :=
  if position + 1 < width then
    ((state &&& (2 ^ position - 1)) ^^^
      (state &&& ((2 ^ (width - 1) - 1) ^^^ (2 ^ (position + 1) - 1)))) ^^^
      (((state >>> (width - 1)) &&& 1) <<< position)
  else state &&& (2 ^ (width - 1) - 1)

/-- The parity of the complemented active coefficients, matching the packed checker. -/
def outputBit (positions : List Nat) (offset : Bool) (state : Nat) : Bool :=
  positions.foldr (fun p b => (!state.testBit p) ^^ b) offset

/-- The number of independent binary coefficients consumed by a program. -/
def reads : List Instruction → Nat
  | [] => 0
  | .read _ :: rest => reads rest + 1
  | _ :: rest => reads rest

/-- The number of output coordinates emitted by a program. -/
def outputs : List Instruction → Nat
  | [] => 0
  | .emit _ _ :: rest => outputs rest + 1
  | _ :: rest => outputs rest

/-- Execute a trellis on a packed coefficient stream. -/
def runWord : List Instruction → Nat → Nat → Nat
  | [], _, _ => 0
  | .read p :: rest, input, state =>
      runWord rest (input >>> 1) (state ^^^ ((input &&& 1) <<< p))
  | .emit ps offset :: rest, input, state =>
      Nat.bit (outputBit ps offset state) (runWord rest input state)
  | .forget p w :: rest, input, state =>
      runWord rest input (forgetBit p w state)

/-- The Hamming weight emitted while executing a trellis. -/
def runWeight : List Instruction → Nat → Nat → Nat
  | [], _, _ => 0
  | .read p :: rest, input, state =>
      runWeight rest (input >>> 1) (state ^^^ ((input &&& 1) <<< p))
  | .emit ps offset :: rest, input, state =>
      (if outputBit ps offset state then 1 else 0) + runWeight rest input state
  | .forget p w :: rest, input, state =>
      runWeight rest input (forgetBit p w state)

/-- A backward weighted sum over all possible coefficient choices. -/
def branchSum {R : Type*} [Semiring R] (base : R) : List Instruction → Nat → R
  | [], _ => 1
  | .read p :: rest, state =>
      branchSum base rest state + branchSum base rest (state ^^^ 2 ^ p)
  | .emit ps offset :: rest, state =>
      (if outputBit ps offset state then base else 1) * branchSum base rest state
  | .forget p w :: rest, state => branchSum base rest (forgetBit p w state)

/-- Summing an even-length interval can be done by its consecutive pairs. -/
lemma sum_range_pairs {R : Type*} [AddCommMonoid R] (f : Nat → R) (n : Nat) :
    (∑ i ∈ Finset.range (2 * n), f i) =
      ∑ i ∈ Finset.range n, (f (2 * i) + f (2 * i + 1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) = (2 * n + 1) + 1 by omega,
      Finset.sum_range_succ, Finset.sum_range_succ, ih, Finset.sum_range_succ]
    simp [add_assoc]

/-- The backward recurrence sums the weight monomial of every coefficient stream. -/
theorem branchSum_eq_sum {R : Type*} [Semiring R] (base : R)
    (program : List Instruction) (state : Nat) :
    branchSum base program state =
      ∑ input ∈ Finset.range (2 ^ reads program), base ^ runWeight program input state := by
  induction program generalizing state with
  | nil => simp [branchSum, reads, runWeight]
  | cons inst rest ih =>
    cases inst with
    | read p =>
      simp only [reads, pow_succ, Nat.mul_comm (2 ^ reads rest) 2]
      rw [sum_range_pairs, Finset.sum_add_distrib]
      simp only [branchSum, ih, runWeight]
      congr 1 <;> apply Finset.sum_congr rfl <;> intro i hi
      · simp [Nat.shiftRight_eq_div_pow, Nat.and_one_is_mod]
      · simp [Nat.shiftRight_eq_div_pow, Nat.and_one_is_mod, Nat.shiftLeft_eq, Nat.add_div]
    | emit ps offset =>
      simp only [reads, branchSum, runWeight]
      rw [ih, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      split_ifs <;> simp [pow_succ, pow_add]
    | forget p w => simpa only [reads, branchSum, runWeight] using ih (forgetBit p w state)

/-- The executable weight equals the bit count of the emitted word. -/
theorem runWeight_eq_bitCount (program : List Instruction) (input state : Nat) :
    runWeight program input state = bitCount (outputs program) (runWord program input state) := by
  induction program generalizing input state with
  | nil => rfl
  | cons inst rest ih =>
    cases inst with
    | read p => exact ih _ _
    | emit ps offset =>
      simp only [runWeight, outputs, runWord, bitCount, Nat.bit_div_two]
      cases h : outputBit ps offset state <;> simp [Nat.bit, ih]
    | forget p w => exact ih _ _

/-- Forgetting a state coordinate is linear for exclusive-or. -/
lemma forgetBit_xor (p w a b : Nat) :
    forgetBit p w (a ^^^ b) = forgetBit p w a ^^^ forgetBit p w b := by
  simp only [forgetBit]
  split_ifs
  · simp only [Nat.and_xor_distrib_right, Nat.shiftRight_xor_distrib, Nat.shiftLeft_xor_distrib]
    ac_rfl
  · exact Nat.and_xor_distrib_right

/-- A parity with a constant offset preserves ternary exclusive-or. -/
lemma outputBit_xor3 (ps : List Nat) (offset : Bool) (a b c : Nat) :
    outputBit ps offset (a ^^^ b ^^^ c) =
      (outputBit ps offset a ^^ outputBit ps offset b ^^ outputBit ps offset c) := by
  induction ps with
  | nil => cases offset <;> rfl
  | cons p ps ih =>
    simp only [outputBit, List.foldr_cons, Nat.testBit_xor] at ih ⊢
    rw [ih]
    have key : ∀ a b c x y z : Bool,
        (!(a ^^ b ^^ c) ^^ (x ^^ y ^^ z)) =
          ((!a ^^ x) ^^ (!b ^^ y) ^^ (!c ^^ z)) := by decide
    exact key _ _ _ _ _ _

/-- Every trellis program is an affine binary map of its inputs and initial state. -/
theorem runWord_xor3 (program : List Instruction) (a b c s t u : Nat) :
    runWord program (a ^^^ b ^^^ c) (s ^^^ t ^^^ u) =
      runWord program a s ^^^ runWord program b t ^^^ runWord program c u := by
  induction program generalizing a b c s t u with
  | nil => simp [runWord]
  | cons inst rest ih =>
    cases inst with
    | read p =>
      simp only [runWord, Nat.shiftRight_xor_distrib, Nat.and_xor_distrib_right,
        Nat.shiftLeft_xor_distrib]
      have hstate : (s ^^^ t ^^^ u) ^^^
          ((a &&& 1) <<< p ^^^ (b &&& 1) <<< p ^^^ (c &&& 1) <<< p) =
          (s ^^^ (a &&& 1) <<< p) ^^^ (t ^^^ (b &&& 1) <<< p) ^^^
            (u ^^^ (c &&& 1) <<< p) := by ac_rfl
      rw [hstate, ih]
    | emit ps offset =>
      simp only [runWord, outputBit_xor3, ih, Nat.xor_bit]
    | forget p w =>
      simp only [runWord, forgetBit_xor]
      exact ih _ _ _ _ _ _

/-- Executing a program emits no bits beyond its output coordinates. -/
theorem runWord_lt (program : List Instruction) (input state : Nat) :
    runWord program input state < 2 ^ outputs program := by
  induction program generalizing input state with
  | nil => simp [runWord, outputs]
  | cons instruction rest ih =>
    cases instruction with
    | read p => exact ih _ _
    | forget p w => exact ih _ _
    | emit ps offset =>
      have h := ih input state
      simp only [runWord, outputs, Nat.bit_val, pow_succ]
      cases outputBit ps offset state <;> simp only [Bool.toNat_false, Bool.toNat_true] <;> omega

/-- Fixing the initial state to zero gives the usual affine exclusive-or identity. -/
theorem runWord_affine (program : List Instruction) (a b : Nat) :
    runWord program (a ^^^ b) 0 =
      runWord program a 0 ^^^ runWord program b 0 ^^^ runWord program 0 0 := by
  simpa using runWord_xor3 program a b 0 0 0 0

/-- An affine binary map contains the translated XOR-span of any certified generators. -/
theorem xorSpan_mem_affine_image (f : Nat → Nat) (bits : Nat)
    (haffine : ∀ a b, f (a ^^^ b) = f a ^^^ f b ^^^ f 0)
    (generators : List Nat)
    (hgen : ∀ g ∈ generators, ∃ input < 2 ^ bits, f input = g ^^^ f 0)
    {word : Nat} (hword : XorSpan generators word) :
    ∃ input < 2 ^ bits, f input = word ^^^ f 0 := by
  induction hword with
  | zero => exact ⟨0, Nat.two_pow_pos _, by simp⟩
  | @step g x hg hx ih =>
    obtain ⟨i, hi, hfi⟩ := hgen g hg
    obtain ⟨j, hj, hfj⟩ := ih
    refine ⟨i ^^^ j, Nat.xor_lt_two_pow hi hj, ?_⟩
    rw [haffine, hfi, hfj]
    simp only [Nat.xor_assoc]
    have hc : f 0 ^^^ (x ^^^ (f 0 ^^^ f 0)) = x ^^^ f 0 := by
      simp [Nat.xor_comm]
    rw [hc]

/-- Sum a doubled interval by its lower and upper halves. -/
lemma sum_range_halves {R : Type*} [AddCommMonoid R] (f : Nat → R) (n : Nat) :
    (∑ i ∈ Finset.range (2 * n), f i) =
      ∑ i ∈ Finset.range n, (f i + f (i + n)) := by
  rw [two_mul, Finset.sum_range_add, ← Finset.sum_add_distrib]
  simp [Nat.add_comm]

/-- Exclusive-or with a new high bit appends that bit without changing lower bits. -/
lemma xor_two_pow_of_lt {a w : Nat} (ha : a < 2 ^ w) : a ^^^ 2 ^ w = a + 2 ^ w := by
  have hmod : (a ^^^ 2 ^ w) % 2 ^ w = a := by
    rw [Nat.xor_mod_two_pow, Nat.mod_eq_of_lt ha, Nat.mod_self, Nat.xor_zero]
  have hdiv : (a ^^^ 2 ^ w) / 2 ^ w = 1 := by
    rw [Nat.xor_div_two_pow, Nat.div_eq_of_lt ha, Nat.div_self (Nat.two_pow_pos _), Nat.zero_xor]
  have h := Nat.mod_add_div (a ^^^ 2 ^ w) (2 ^ w)
  rw [hmod, hdiv, mul_one] at h
  exact h.symm

/-- An involution preserving a finite interval can reindex its sum. -/
lemma sum_range_involution {R : Type*} [AddCommMonoid R] (n : Nat)
    (swap : Nat → Nat) (hrange : ∀ i < n, swap i < n)
    (hinvol : ∀ i < n, swap (swap i) = i) (f : Nat → R) :
    (∑ i ∈ Finset.range n, f (swap i)) = ∑ i ∈ Finset.range n, f i := by
  apply Finset.sum_bij (fun i _ => swap i)
  · intro i hi
    exact Finset.mem_range.mpr (hrange i (Finset.mem_range.mp hi))
  · intro a ha b hb hab
    have h := congrArg swap hab
    simpa only [hinvol a (Finset.mem_range.mp ha), hinvol b (Finset.mem_range.mp hb)] using h
  · intro b hb
    exact ⟨swap b, Finset.mem_range.mpr (hrange b (Finset.mem_range.mp hb)),
      hinvol b (Finset.mem_range.mp hb)⟩
  · intro i hi
    rfl

/-- A weighted finite-state layer, with its forward and backward evaluation laws. -/
structure WeightedLayer (R : Type*) [CommSemiring R] (inputs outputs : Nat) where
  /-- Distribute prefix weights to successor states. -/
  forward : (Nat → R) → Nat → R
  /-- Sum suffix weights from a predecessor state. -/
  backward : (Nat → R) → Nat → R
  /-- Forward and backward evaluation give the same weighted path sum. -/
  adjoint : ∀ f g,
    (∑ i ∈ Finset.range outputs, forward f i * g i) =
      ∑ i ∈ Finset.range inputs, f i * backward g i

namespace WeightedLayer

variable {R : Type*} [CommSemiring R]

/-- A read branches into the two values of a new high coefficient bit. -/
def read (width : Nat) : WeightedLayer R (2 ^ width) (2 ^ (width + 1)) where
  forward f i := f (i % 2 ^ width)
  backward g i := g i + g (i ^^^ 2 ^ width)
  adjoint f g := by
    rw [pow_succ', sum_range_halves]
    apply Finset.sum_congr rfl
    intro i hi
    have hi := Finset.mem_range.mp hi
    rw [Nat.mod_eq_of_lt hi, Nat.add_mod_right, Nat.mod_eq_of_lt hi,
      xor_two_pow_of_lt hi, mul_add]

/-- An emitted bit multiplies a path weight by its weight-generating monomial. -/
def emit (size : Nat) (factor : Nat → R) : WeightedLayer R size size where
  forward f i := f i * factor i
  backward g i := factor i * g i
  adjoint f g := by simp only [mul_assoc]

/-- Forgetting a bit sums its two possible values after a certified state permutation. -/
def forget (half : Nat) (swap : Nat → Nat)
    (hrange : ∀ i < 2 * half, swap i < 2 * half)
    (hinvol : ∀ i < 2 * half, swap (swap i) = i) :
    WeightedLayer R (2 * half) half where
  forward f i := f (swap i) + f (swap (i + half))
  backward g i := g (swap i % half)
  adjoint f g := by
    rw [← sum_range_involution (2 * half) swap hrange hinvol
      (fun i => f i * g (swap i % half)), sum_range_halves]
    apply Finset.sum_congr rfl
    intro i hi
    have hi := Finset.mem_range.mp hi
    rw [hinvol i (by omega), hinvol (i + half) (by omega),
      Nat.mod_eq_of_lt hi, Nat.add_mod_right, Nat.mod_eq_of_lt hi, add_mul]

end WeightedLayer

universe u

/-- A sequence of compatible finite-state layers. -/
inductive Network (R : Type u) [CommSemiring R] : Nat → Nat → Type u
  | done (size : Nat) : Network R size size
  | cons {a b c : Nat} : WeightedLayer R a b → Network R b c → Network R a c

namespace Network

variable {R : Type*} [CommSemiring R]

/-- Apply all layers to a table of initial prefix weights. -/
def forward {a b : Nat} : Network R a b → (Nat → R) → Nat → R
  | .done _, f => f
  | .cons layer rest, f => forward rest (layer.forward f)

/-- Sum all suffix weights backward through a network. -/
def backward {a b : Nat} : Network R a b → (Nat → R) → Nat → R
  | .done _, g => g
  | .cons layer rest, g => layer.backward (backward rest g)

/-- A sequence of verified layers counts the same paths in either direction. -/
theorem adjoint {a b : Nat} (net : Network R a b) (f g : Nat → R) :
    (∑ i ∈ Finset.range b, net.forward f i * g i) =
      ∑ i ∈ Finset.range a, f i * net.backward g i := by
  induction net generalizing f with
  | done _ => rfl
  | cons layer rest ih =>
    change (∑ i ∈ Finset.range _, rest.forward (layer.forward f) i * g i) = _
    rw [ih, layer.adjoint]
    rfl

/-- With one initial state, summing the final table is the backward path count. -/
theorem total_eq_backward {b : Nat} (net : Network R 1 b) :
    (∑ i ∈ Finset.range b, net.forward (fun _ => 1) i) =
      net.backward (fun _ => 1) 0 := by
  simpa using net.adjoint (fun _ => 1) (fun _ => 1)

/-- Network outputs depend only on the declared finite input table. -/
theorem forward_congr {a b : Nat} (net : Network R a b) (f f' : Nat → R)
    (h : ∀ i < a, f i = f' i) (j : Nat) (hj : j < b) :
    net.forward f j = net.forward f' j := by
  have left := net.adjoint f (fun i => if i = j then 1 else 0)
  have right := net.adjoint f' (fun i => if i = j then 1 else 0)
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_range,
    if_pos hj] at left right
  rw [left, right]
  apply Finset.sum_congr rfl
  intro i hi
  rw [h i (Finset.mem_range.mp hi)]

end Network

namespace WeightedLayer

variable {R : Type*} [CommSemiring R]

/-- A bit-forgetting layer indexed by the number of remaining active bits. -/
def forgetPower (width : Nat) (swap : Nat → Nat)
    (hrange : ∀ i < 2 ^ (width + 1), swap i < 2 ^ (width + 1))
    (hinvol : ∀ i < 2 ^ (width + 1), swap (swap i) = i) :
    WeightedLayer R (2 ^ (width + 1)) (2 ^ width) where
  forward f i := f (swap i) + f (swap (i + 2 ^ width))
  backward g i := g (swap i % 2 ^ width)
  adjoint f g := by
    have hrange' : ∀ i < 2 * 2 ^ width, swap i < 2 * 2 ^ width := by
      simpa only [pow_succ'] using hrange
    have hinvol' : ∀ i < 2 * 2 ^ width, swap (swap i) = i := by
      simpa only [pow_succ'] using hinvol
    simpa only [pow_succ', forget] using
      (forget (R := R) (2 ^ width) swap hrange' hinvol').adjoint f g

end WeightedLayer

/-- A trellis program together with a finite-state network certifying its weighted semantics. -/
structure CertifiedProgram (R : Type*) [CommSemiring R] (base : R)
    (initialWidth finalWidth : Nat) where
  /-- The executable affine encoder. -/
  program : List Instruction
  /-- The corresponding weighted finite-state network. -/
  network : Network R (2 ^ initialWidth) (2 ^ finalWidth)
  /-- Summing all terminal states counts the coefficient branches of the encoder. -/
  backward_one : ∀ state < 2 ^ initialWidth,
    network.backward (fun _ => 1) state = branchSum base program state

namespace CertifiedProgram

variable {R : Type*} [CommSemiring R] {base : R}

/-- The empty program leaves every state unchanged. -/
def done (width : Nat) : CertifiedProgram R base width width where
  program := []
  network := .done (2 ^ width)
  backward_one _ _ := rfl

/-- Prepend an independent coefficient read to a certified program. -/
def read {width finalWidth : Nat} (tail : CertifiedProgram R base (width + 1) finalWidth) :
    CertifiedProgram R base width finalWidth where
  program := .read width :: tail.program
  network := .cons (WeightedLayer.read width) tail.network
  backward_one state hstate := by
    change tail.network.backward (fun _ => 1) state +
      tail.network.backward (fun _ => 1) (state ^^^ 2 ^ width) = _
    have hlow : state < 2 ^ (width + 1) := by
      rw [pow_succ']
      omega
    have hhigh : state ^^^ 2 ^ width < 2 ^ (width + 1) := by
      rw [xor_two_pow_of_lt hstate, pow_succ']
      omega
    rw [tail.backward_one state hlow, tail.backward_one _ hhigh]
    rfl

/-- Prepend an output parity to a certified program. -/
def emit {width finalWidth : Nat} (positions : List Nat) (offset : Bool)
    (tail : CertifiedProgram R base width finalWidth) :
    CertifiedProgram R base width finalWidth where
  program := .emit positions offset :: tail.program
  network := .cons (WeightedLayer.emit (2 ^ width)
    (fun state => if outputBit positions offset state then base else 1)) tail.network
  backward_one state hstate := by
    change (if outputBit positions offset state then base else 1) *
      tail.network.backward (fun _ => 1) state = _
    rw [tail.backward_one state hstate]
    rfl

/-- Prepend a certified swap-and-forget operation to a certified program. -/
def forget {width finalWidth : Nat} (position : Nat) (swap : Nat → Nat)
    (hrange : ∀ i < 2 ^ (width + 1), swap i < 2 ^ (width + 1))
    (hinvol : ∀ i < 2 ^ (width + 1), swap (swap i) = i)
    (hforget : ∀ i < 2 ^ (width + 1),
      forgetBit position (width + 1) i = swap i % 2 ^ width)
    (tail : CertifiedProgram R base width finalWidth) :
    CertifiedProgram R base (width + 1) finalWidth where
  program := .forget position (width + 1) :: tail.program
  network := .cons (WeightedLayer.forgetPower width swap hrange hinvol) tail.network
  backward_one state hstate := by
    change tail.network.backward (fun _ => 1) (swap state % 2 ^ width) = _
    rw [tail.backward_one _ (Nat.mod_lt _ (Nat.two_pow_pos _))]
    simp only [branchSum, hforget state hstate]

/-- A closed certified trellis computes the weighted sum of all encoded inputs. -/
theorem forward_eq_sum (C : CertifiedProgram R base 0 0) :
    C.network.forward (fun _ => 1) 0 =
      ∑ input ∈ Finset.range (2 ^ reads C.program),
        base ^ bitCount (outputs C.program) (runWord C.program input 0) := by
  have htotal := C.network.total_eq_backward
  simp only [pow_zero, Finset.range_one, Finset.sum_singleton] at htotal
  rw [C.backward_one 0 (by decide), branchSum_eq_sum] at htotal
  simpa only [runWeight_eq_bitCount] using htotal

end CertifiedProgram

#print axioms branchSum_eq_sum
#print axioms runWeight_eq_bitCount

end Quantum.Stabilizer.Homological.F2Mask.Trellis
