import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Tactic
import QEC.Stabilizer.Foundations.BinarySymplectic.Core
import QEC.Stabilizer.Foundations.PauliGroupSingle
import QEC.Stabilizer.Foundations.PauliGroupSingle.Commutation
import QEC.Stabilizer.Foundations.PauliGroup.NQubitOperator
import QEC.Stabilizer.Foundations.PauliGroup.NQubitElement
import QEC.Stabilizer.Foundations.PauliGroup.Commutation

/-!
# Symplectic inner product

The symplectic inner product of two symplectic vectors pairs the `X`-part of
each with the `Z`-part of the other, in `ZMod 2`. Two Pauli group elements
commute iff the symplectic inner product of their operator parts is `0`
(`commutes_iff_symplectic_inner_zero`) and anticommute iff it is `1`
(`anticommutes_iff_symplectic_inner_one`).
-/

namespace Quantum

open scoped BigOperators

variable {n : ℕ}

namespace PauliOperator

/-- The single-qubit symplectic product: `0` if `P` and `Q` commute and `1` if
they anticommute. -/
def symplecticProductSingle (P Q : PauliOperator) : ZMod 2 :=
  P.toSymplecticSingle.1 * Q.toSymplecticSingle.2 + P.toSymplecticSingle.2 * Q.toSymplecticSingle.1

lemma symplecticProductSingle_eq_zero_iff_commute (P Q : PauliOperator) :
    symplecticProductSingle P Q = 0 ↔ P.mulOp Q = Q.mulOp P := by
  cases P <;> cases Q <;> decide

/-- The single-qubit symplectic product is `1` exactly when swapping the factors
changes the phase of the product by `2`, i.e. when they anticommute. -/
lemma symplecticProductSingle_eq_ite (P Q : PauliOperator)
    {h : Decidable ((P.mulOp Q).phasePower = (Q.mulOp P).phasePower + 2)} :
    symplecticProductSingle P Q =
      if (P.mulOp Q).phasePower = (Q.mulOp P).phasePower + 2 then 1 else 0 := by
  cases P <;> cases Q <;> simp +decide [symplecticProductSingle]

/-! ### Single-qubit evaluations

`toSymplecticSingle P = (x-bit, z-bit)`. Pairing against `Z` reads off the
`X`-bit and pairing against `X` reads off the `Z`-bit — the single-qubit content
of "a `Z`-check detects `X`-errors and an `X`-check detects `Z`-errors". -/

@[simp] lemma symplecticProductSingle_I_left (Q : PauliOperator) :
    symplecticProductSingle I Q = 0 := by
  simp [symplecticProductSingle]

@[simp] lemma symplecticProductSingle_I_right (P : PauliOperator) :
    symplecticProductSingle P I = 0 := by
  simp [symplecticProductSingle]

/-- Against `Z`, the symplectic product reads off the `X`-bit of `P`. -/
@[simp] lemma symplecticProductSingle_Z_right (P : PauliOperator) :
    symplecticProductSingle P Z = P.toSymplecticSingle.1 := by
  simp [symplecticProductSingle]

/-- Against `X`, the symplectic product reads off the `Z`-bit of `P`. -/
@[simp] lemma symplecticProductSingle_X_right (P : PauliOperator) :
    symplecticProductSingle P X = P.toSymplecticSingle.2 := by
  simp [symplecticProductSingle]

/-- The `X`-bit of a single-qubit Pauli is `0` or `1`. -/
lemma toSymplecticSingle_fst_eq_zero_or_one (P : PauliOperator) :
    P.toSymplecticSingle.1 = 0 ∨ P.toSymplecticSingle.1 = 1 := by
  cases P <;> decide

/-- A non-identity Pauli with `X`-bit `0` is `Z`, so its `Z`-bit is `1`. -/
lemma toSymplecticSingle_snd_eq_one_of_fst_eq_zero {P : PauliOperator} (hP : P ≠ I)
    (h : P.toSymplecticSingle.1 = 0) : P.toSymplecticSingle.2 = 1 := by
  cases P
  · exact absurd rfl hP
  all_goals first | rfl | exact absurd h (by decide)

end PauliOperator

namespace NQubitPauliOperator

/-- The symplectic inner product of two n-qubit Pauli operators: the sum over
qubits of the single-qubit symplectic products, in `ZMod 2`. -/
def symplecticInner (op₁ op₂ : NQubitPauliOperator n) : ZMod 2 :=
  (Finset.univ : Finset (Fin n)).sum (fun i =>
    PauliOperator.symplecticProductSingle (op₁ i) (op₂ i))

end NQubitPauliOperator

/-! ## Group-element level: `⟪p, q⟫ₛ` and `symp`

Statements about Pauli group elements read the symplectic form off the operator
parts, `symplecticInner p.operators q.operators`, and the symplectic vector as
`toSymplectic g.operators`. The scoped notation `⟪p, q⟫ₛ` (scope
`Quantum.NQubitPauliGroupElement`: active in that namespace and under
`open NQubitPauliGroupElement` / `open scoped NQubitPauliGroupElement`) is a
**macro onto exactly that operator-level form** — so
`commutes_iff_symplectic_inner_zero`,
`unfold NQubitPauliOperator.symplecticInner` and every existing lemma apply
verbatim — and the delaborator prints the form back as `⟪p, q⟫ₛ`. The `ₛ` suffix
keeps it clear of mathlib's inner-product brackets `⟪x, y⟫_𝕜`.

The delaborator is `scoped` with the notation, so `⟪p, q⟫ₛ` only appears in
files that can parse it; elsewhere the operator-level form prints as is. There
is deliberately no group-level definition behind the notation: the
operator-level function is the single normal form every lemma is stated in. -/

namespace NQubitPauliGroupElement

/-- `⟪p, q⟫ₛ` is the symplectic inner product of the operator parts of the Pauli
group elements `p`, `q`: it elaborates to exactly
`NQubitPauliOperator.symplecticInner p.operators q.operators`. Scoped: enable
with `open scoped NQubitPauliGroupElement`. -/
scoped notation:max "⟪" p ", " q "⟫ₛ" =>
  NQubitPauliOperator.symplecticInner (NQubitPauliGroupElement.operators p)
    (NQubitPauliGroupElement.operators q)

open Lean PrettyPrinter Delaborator SubExpr in
/-- Display `NQubitPauliOperator.symplecticInner p.operators q.operators` as
`⟪p, q⟫ₛ`; any other application of `symplecticInner` keeps the default printer.
-/
@[scoped app_delab Quantum.NQubitPauliOperator.symplecticInner]
def delabSymplecticInner : Delab :=
  whenPPOption getPPNotation <| whenNotPPOption getPPExplicit do
    let e ← getExpr
    guard (e.isAppOfArity ``Quantum.NQubitPauliOperator.symplecticInner 3)
    guard ((e.getArg! 1).isAppOfArity ``Quantum.NQubitPauliGroupElement.operators 2)
    guard ((e.getArg! 2).isAppOfArity ``Quantum.NQubitPauliGroupElement.operators 2)
    let p ← withNaryArg 1 <| withNaryArg 1 delab
    let q ← withNaryArg 2 <| withNaryArg 1 delab
    `(⟪$p, $q⟫ₛ)

section RoundTrip

example (p q : NQubitPauliGroupElement n) :
    ⟪p, q⟫ₛ = NQubitPauliOperator.symplecticInner p.operators q.operators := rfl

open Lean Elab Command in
/-- Display test: elaborate `stx` and check that its pretty-printed text is
`expected` (`exact := false`: contains `expected`). Run through `run_cmd` so no
`#`-command is needed. -/
private def checkDisplay (stx : Syntax) (expected : String) (exact : Bool := true) :
    CommandElabM Unit :=
  liftTermElabM do
    let e ← Term.elabTerm stx none
    Term.synthesizeSyntheticMVarsNoPostponing
    let s := toString (← Meta.ppExpr (← instantiateMVars e))
    unless (if exact then s == expected else (s.splitOn expected).length > 1) do
      throwError "display test failed:{indentD s}\nexpected{indentD expected}"

run_cmd do
  checkDisplay (← `(fun (p q : NQubitPauliGroupElement 3) => ⟪p, q⟫ₛ))
    "⟪p, q⟫ₛ" (exact := false)
-- a bare operator on one side keeps the default printer
run_cmd do
  checkDisplay
    (← `(fun (op : NQubitPauliOperator 3) (q : NQubitPauliGroupElement 3) =>
          NQubitPauliOperator.symplecticInner op q.operators))
    "op.symplecticInner q.operators" (exact := false)

end RoundTrip

end NQubitPauliGroupElement

namespace NQubitPauliOperator

open scoped NQubitPauliGroupElement

/-- The symplectic vector of a product is the sum of the symplectic vectors of
the factors. -/
lemma toSymplectic_add (p q : NQubitPauliOperator n) (j : Fin (n + n)) :
    toSymplectic (NQubitPauliGroupElement.mulOp p q).operators j =
      toSymplectic p j + toSymplectic q j := by
  simp only [toSymplectic, NQubitPauliGroupElement.mulOp]
  split_ifs with hj
  · exact congr_arg Prod.fst
      (PauliOperator.toSymplecticSingle_add (p ⟨j.val, hj⟩) (q ⟨j.val, hj⟩))
  · exact congr_arg Prod.snd
      (PauliOperator.toSymplecticSingle_add (p ⟨j.val - n, by omega⟩) (q ⟨j.val - n, by omega⟩))

/-- The symplectic inner product counts, modulo `2`, the qubits at which the
two operators anticommute. -/
lemma symplecticInner_eq_card (p q : NQubitPauliOperator n)
    [DecidablePred (NQubitPauliGroupElement.anticommutesAt p q)] :
    symplecticInner p q =
      ((Finset.univ.filter (NQubitPauliGroupElement.anticommutesAt p q)).card : ZMod 2) := by
  have h : ∀ i, PauliOperator.symplecticProductSingle (p i) (q i) =
      if NQubitPauliGroupElement.anticommutesAt p q i then 1 else 0 :=
    fun i => PauliOperator.symplecticProductSingle_eq_ite (p i) (q i)
  simp only [symplecticInner, h, Finset.sum_boole]

/-- Two n-qubit Pauli group elements commute iff the symplectic inner product
of their operator parts is `0`. -/
theorem commutes_iff_symplectic_inner_zero (p q : NQubitPauliGroupElement n) :
    p * q = q * p ↔ ⟪p, q⟫ₛ = 0 := by
  classical
  rw [NQubitPauliGroupElement.commutes_iff_even_anticommutes, symplecticInner_eq_card,
    ZMod.natCast_eq_zero_iff_even]

/-- Two n-qubit Pauli group elements anticommute iff the symplectic inner
product of their operator parts is `1`. -/
theorem anticommutes_iff_symplectic_inner_one (p q : NQubitPauliGroupElement n) :
    NQubitPauliGroupElement.Anticommute p q ↔ ⟪p, q⟫ₛ = 1 := by
  classical
  rw [NQubitPauliGroupElement.anticommutes_iff_odd_anticommutes, symplecticInner_eq_card,
    ZMod.natCast_eq_one_iff_odd]

/-- The all-`X` and all-`Z` operators anticommute when `n` is odd: their
symplectic product is `1` at each qubit, so the inner product is `n` modulo
`2`. -/
theorem allX_allZ_anticommute (n : ℕ) (hn : Odd n) :
    NQubitPauliGroupElement.Anticommute (⟨0, X n⟩ : NQubitPauliGroupElement n)
      (⟨0, Z n⟩ : NQubitPauliGroupElement n) := by
  rw [anticommutes_iff_symplectic_inner_one]
  unfold symplecticInner
  simp only [X, Z, PauliOperator.symplecticProductSingle, PauliOperator.toSymplecticSingle_X,
    PauliOperator.toSymplecticSingle_Z, one_mul, zero_mul, add_zero]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, Nat.smul_one_eq_cast,
    ZMod.natCast_eq_one_iff_odd]
  exact hn

end NQubitPauliOperator

/-! ## Symplectic vectors of group elements

The symplectic vector is additive on products, so it sends the subgroup
generated by a set of Pauli group elements into the span of their symplectic
vectors. -/

open NQubitPauliOperator Submodule
open scoped NQubitPauliGroupElement

/-- The symplectic vector of a product is the sum of the symplectic vectors of
the factors. -/
lemma toSymplectic_mul (p q : NQubitPauliGroupElement n) (j : Fin (n + n)) :
    toSymplectic (p * q).operators j = toSymplectic p.operators j + toSymplectic q.operators j :=
  toSymplectic_add p.operators q.operators j

/-- The symplectic vector of the identity is zero. -/
lemma toSymplectic_one_operators :
    toSymplectic (1 : NQubitPauliGroupElement n).operators = 0 := by
  funext j
  simp [toSymplectic, NQubitPauliOperator.identity]

/-- An element and its inverse have the same symplectic vector. -/
lemma toSymplectic_inv_operators (g : NQubitPauliGroupElement n) :
    toSymplectic (g⁻¹).operators = toSymplectic g.operators :=
  rfl

/-- If an element lies in the subgroup generated by a set, its symplectic
vector lies in the span of the symplectic vectors of the set. -/
lemma toSymplectic_mem_span_of_mem_closure {S : Set (NQubitPauliGroupElement n)}
    {x : NQubitPauliGroupElement n} (hx : x ∈ Subgroup.closure S) :
    toSymplectic x.operators ∈ span (ZMod 2) ((fun g => toSymplectic g.operators) '' S) := by
  induction hx using Subgroup.closure_induction with
  | mem g hg => exact subset_span (Set.mem_image_of_mem _ hg)
  | one => rw [toSymplectic_one_operators]; exact zero_mem _
  | mul a b _ _ ha hb =>
    rw [show toSymplectic (a * b).operators = _ + _ from funext (toSymplectic_mul a b)]
    exact add_mem ha hb
  | inv a _ ha => rwa [toSymplectic_inv_operators]

end Quantum
