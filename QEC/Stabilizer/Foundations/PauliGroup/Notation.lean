import Lean.PrettyPrinter.Delaborator.Basic
import QEC.Stabilizer.Foundations.PauliGroup.NQubitElement

/-!
# Physics-style construction notation for `NQubitPauliGroupElement`

This file provides scoped notation for writing concrete n-qubit Pauli group elements the
way the physics literature does:

- `σ[XXIXII]` — phase `+1` (`phasePower = 0`)
- `iσ[XXIXII]` — phase `i` (`phasePower = 1`)
- `-σ[XXIXII]` — phase `-1` (`phasePower = 2`)
- `-iσ[XXIXII]` — phase `-i` (`phasePower = 3`)

The letters between the brackets form a single identifier over the alphabet `X`, `Y`,
`Z`, `I`, read left to right as qubits `0, 1, …`; the number of letters fixes the number
of qubits, so `σ[XIZ] : NQubitPauliGroupElement 3` with no ascription needed.

The notation is **scoped**: enable it with `open scoped Pauli`. It must be opt-in
because any notation whose leading token is `σ[` takes over that token from `GetElem`
indexing (`σ[i]`) for variables named `σ` (likewise `iσ[…]` for variables named `iσ`).
The phase prefixes are part of the leading token (`-σ[`, `iσ[`, `-iσ[`): write them with
no space before `σ[`, and keep spaces around a binary `-` (`a - σ[XX]`) when you mean
subtraction with the scope open.

## Elaboration guarantee

`σ[…]` elaborates to **exactly** the canonical literal normal form used throughout the
concrete code files:

```lean
⟨phase, ((NQubitPauliOperator.identity n).set i₀ op₀).set i₁ op₁ ⋯⟩
```

with `.set` applied only at the non-identity positions, in increasing index order. The
notation is a macro (pure syntax expansion into that form), so kernel-reduction behavior
and every existing `simp`/`decide`/`rfl` proof over such literals are unchanged. In
particular there is deliberately no `ofList`-style helper on the elaboration path: a list
lookup is an O(n) walk under kernel reduction (see the axiom-policy notes in
`CLAUDE.md`), whereas the `.set` chain is the form all existing proofs already consume.

## Delaborator

Terms of exactly that literal shape (literal phase, literal indices, `PauliOperator`
constructors, literal qubit count) display back as `σ[…]`/`iσ[…]`/`-σ[…]`/`-iσ[…]` in
goals and diagnostics. Anything else — variable phase or operators, symbolic indices, a
partially reduced chain — is left to the default printer. The delaborator is registered
globally, so the display is independent of whether the scope is open;
`set_option pp.notation false` (or `pp.explicit true`) recovers the raw term.
-/

namespace Pauli

open Lean

/-- `σ[XZIX]` is the `NQubitPauliGroupElement` with phase `+1` (`phasePower = 0`) whose
operator at qubit `k` is the `k`-th letter (letters `X`, `Y`, `Z`, `I`; qubit count =
letter count). Scoped: enable with `open scoped Pauli`. Elaborates to the literal
`⟨0, (NQubitPauliOperator.identity n).set i₀ op₀ …⟩` normal form. -/
scoped syntax:max (name := sigma) "σ[" ident "]" : term

/-- `iσ[XZIX]`: as `σ[XZIX]` but with phase `i` (`phasePower = 1`).
Scoped: enable with `open scoped Pauli`. -/
scoped syntax:max (name := iSigma) "iσ[" ident "]" : term

/-- `-σ[XZIX]`: as `σ[XZIX]` but with phase `-1` (`phasePower = 2`).
Scoped: enable with `open scoped Pauli`. -/
scoped syntax:max (name := negSigma) "-σ[" ident "]" : term

/-- `-iσ[XZIX]`: as `σ[XZIX]` but with phase `-i` (`phasePower = 3`).
Scoped: enable with `open scoped Pauli`. -/
scoped syntax:max (name := negISigma) "-iσ[" ident "]" : term

/-- Split the letters identifier of a `σ[…]`-family literal into its characters, checking
that the identifier is a single atomic name over the alphabet `X`, `Y`, `Z`, `I`. -/
def pauliLetters (stx : Syntax) : MacroM (List Char) := do
  let .str .anonymous s := stx.getId.eraseMacroScopes
    | Macro.throwErrorAt stx "expected a string of Pauli letters (X, Y, Z, I)"
  let cs := s.toList
  for c in cs do
    unless c == 'X' || c == 'Y' || c == 'Z' || c == 'I' do
      Macro.throwErrorAt stx s!"invalid Pauli letter '{c}': expected X, Y, Z, or I"
  return cs

/-- Expand a `σ[…]`-family literal with the given `phasePower` into the canonical normal
form `NQubitPauliGroupElement.mk phase ((NQubitPauliOperator.identity n).set i₀ op₀ …)`,
setting only the non-identity positions, in increasing index order. -/
def expandSigma (phase : Nat) (letters : Syntax) : MacroM Term := do
  let cs ← pauliLetters letters
  let mut ops : Term ← `(Quantum.NQubitPauliOperator.identity $(quote cs.length))
  let mut i : Nat := 0
  for c in cs do
    if c != 'I' then
      let opStx : Term ← match c with
        | 'X' => `(Quantum.PauliOperator.X)
        | 'Y' => `(Quantum.PauliOperator.Y)
        | _ => `(Quantum.PauliOperator.Z)
      ops ← `(Quantum.NQubitPauliOperator.set $ops $(quote i) $opStx)
    i := i + 1
  `(Quantum.NQubitPauliGroupElement.mk $(quote phase) $ops)

macro_rules
  | `(σ[$letters:ident]) => expandSigma 0 letters
  | `(iσ[$letters:ident]) => expandSigma 1 letters
  | `(-σ[$letters:ident]) => expandSigma 2 letters
  | `(-iσ[$letters:ident]) => expandSigma 3 letters

/-!
## Delaborator

Displays literal-shaped `NQubitPauliGroupElement.mk` applications back as `σ[…]`.
-/

section Delaborator

open PrettyPrinter Delaborator SubExpr

/-- Match a literal natural number: a raw `Nat` literal or an `OfNat.ofNat` application
of one (the form numerals elaborate to). -/
def natLitOf? (e : Expr) : Option Nat :=
  match e with
  | .lit (.natVal k) => some k
  | _ =>
    if e.isAppOfArity ``OfNat.ofNat 3 then
      match e.getArg! 1 with
      | .lit (.natVal k) => some k
      | _ => none
    else none

/-- Match a `PauliOperator` constructor constant, as its letter. -/
def pauliOpChar? (e : Expr) : Option Char :=
  match e with
  | .const c _ =>
    if c == ``Quantum.PauliOperator.X then some 'X'
    else if c == ``Quantum.PauliOperator.Y then some 'Y'
    else if c == ``Quantum.PauliOperator.Z then some 'Z'
    else if c == ``Quantum.PauliOperator.I then some 'I'
    else none
  | _ => none

/-- Match a literal `set`-chain `(NQubitPauliOperator.identity n).set i₀ op₀ …` with
literal indices and constructor operators. Returns the literal `n` together with the
`(index, letter)` assignments, innermost first. Returns `none` on any other shape. -/
partial def setChain? (e : Expr) (acc : List (Nat × Char) := []) :
    Option (Nat × List (Nat × Char)) :=
  if e.isAppOfArity ``Quantum.NQubitPauliOperator.set 4 then do
    let i ← natLitOf? (e.getArg! 2)
    let c ← pauliOpChar? (e.getArg! 3)
    setChain? (e.getArg! 1) ((i, c) :: acc)
  else if e.isAppOfArity ``Quantum.NQubitPauliOperator.identity 1 then do
    let n ← natLitOf? (e.getArg! 0)
    return (n, acc)
  else
    none

/-- Delaborate literal-shaped `NQubitPauliGroupElement.mk` applications back to the
`σ[…]`/`iσ[…]`/`-σ[…]`/`-iσ[…]` notation. Fires only when the phase is a literal
`0`–`3`, the operator part is a literal `set`-chain over `identity n` with in-range
literal indices, and `n > 0`; stays silent otherwise. -/
@[app_delab Quantum.NQubitPauliGroupElement.mk]
def delabSigma : Delab :=
  whenPPOption getPPNotation <| whenNotPPOption getPPExplicit do
    let e ← getExpr
    unless e.isAppOfArity ``Quantum.NQubitPauliGroupElement.mk 3 do failure
    let some phase := natLitOf? (e.getArg! 1) | failure
    let some (n, sets) := setChain? (e.getArg! 2) | failure
    unless 0 < n do failure
    unless sets.all (fun ic => ic.1 < n) do failure
    -- Later (outer) `.set`s override earlier ones, so fold innermost-first.
    let letters := String.ofList <| (List.range n).map fun j =>
      sets.foldl (fun acc ic => if ic.1 == j then ic.2 else acc) 'I'
    let letters := mkIdent (.mkSimple letters)
    match phase with
    | 0 => `(σ[$letters])
    | 1 => `(iσ[$letters])
    | 2 => `(-σ[$letters])
    | 3 => `(-iσ[$letters])
    | _ => failure

end Delaborator

end Pauli

/-!
## Round-trip tests

Each phase prefix elaborates to exactly the hand-written literal normal form.
-/

section RoundTrip

open Quantum
open scoped Pauli

example :
    σ[XIZ] =
      ⟨0, ((NQubitPauliOperator.identity 3).set 0 PauliOperator.X).set 2 PauliOperator.Z⟩ :=
  rfl

example :
    σ[XZZXI] =
      ⟨0, ((((NQubitPauliOperator.identity 5).set 0 PauliOperator.X).set 1
        PauliOperator.Z).set 2 PauliOperator.Z).set 3 PauliOperator.X⟩ :=
  rfl

example : σ[IIII] = ⟨0, NQubitPauliOperator.identity 4⟩ := rfl

example : iσ[Z] = ⟨1, (NQubitPauliOperator.identity 1).set 0 PauliOperator.Z⟩ := rfl

example :
    -σ[YY] =
      ⟨2, ((NQubitPauliOperator.identity 2).set 0 PauliOperator.Y).set 1 PauliOperator.Y⟩ :=
  rfl

example : -iσ[XI] = ⟨3, (NQubitPauliOperator.identity 2).set 0 PauliOperator.X⟩ := rfl

example : σ[XIZ].phasePower = 0 := rfl

example : σ[XIZ].operators 2 = PauliOperator.Z := rfl

example : σ[XIZ].operators 1 = PauliOperator.I := rfl

end RoundTrip
