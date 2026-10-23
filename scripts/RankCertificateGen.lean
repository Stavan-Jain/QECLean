/-
Rank-certificate generator for `rowsLinearIndependent`.

Untrusted: computes a right inverse `B` of a generator list's check matrix by
Gaussian elimination over `𝔽₂` and prints it as Lean source, in the bitmask
format that `NQubitPauliGroupElement.rankCertCheck`
(`QEC/Stabilizer/Foundations/BinarySymplectic/RankCertificate.lean`) checks in
the kernel. Nothing here is trusted: a wrong certificate fails the kernel
check, it does not prove anything false.

Run after building QEC, naming one or more registered codes (no argument
prints all of them):

  lake env lean --run scripts/RankCertificateGen.lean steane7 toric4

To certify a new code, add a `(name, emit …)` entry to `registry` and import
its module.

**Elimination.** Each row `r_i` is tagged with the bit `k + i` (`k = 2n`), and
the tagged rows are brought to reduced row-echelon form. Row `t` then reads
`R_t | T_t` with `R_t = Σ_i T_{t,i} r_i`, the pivot columns `p_t` of the `R_t`
form an identity block, and so `T (M P) = 1` for the pivot-selection matrix
`P`. Hence `(M P) T = 1`, i.e. `B = P T`: column `j` of `B` has bit `p_t` set
exactly when `T_{t,j} = 1`.
-/
import QEC.Stabilizer.Foundations.BinarySymplectic.RankCertificate
import QEC.Stabilizer.Codes.Small.Steane7
import QEC.Stabilizer.Codes.Small.Shor9
import QEC.Stabilizer.Codes.Toric.StabilizerCode

open Quantum Quantum.NQubitPauliGroupElement Quantum.RankCertificate

namespace QEC.RankCertificateGen

/-- Right inverse of the `m × k` matrix with bitmask rows `rows`, as bitmask
columns, or `none` if the rows are dependent. -/
def rightInverse (k : ℕ) (rows : List ℕ) : Option (List ℕ) := Id.run do
  let m := rows.length
  let mut a : Array ℕ := (rows.zipIdx.map fun (r, i) => r ||| (1 <<< (k + i))).toArray
  let mut pivots : Array ℕ := #[]
  let mut t := 0
  for c in [0:k] do
    if t < m then
      match (List.range m).find? (fun s => t ≤ s && a[s]!.testBit c) with
      | none => pure ()
      | some s =>
        a := a.swapIfInBounds t s
        let pivotRow := a[t]!
        for u in [0:m] do
          if u ≠ t && a[u]!.testBit c then
            a := a.set! u (a[u]! ^^^ pivotRow)
        pivots := pivots.push c
        t := t + 1
  if t < m then return none
  return some <| (List.range m).map fun j =>
    (List.range m).foldl (init := 0) fun acc t =>
      if (a[t]! >>> k).testBit j then acc ||| (1 <<< pivots[t]!) else acc

/-- Lowercase hex literal. -/
def hex (x : ℕ) : String := "0x" ++ String.ofList (Nat.toDigits 16 x)

/-- `bs` as a Lean list literal, two-space indented, lines under 100 columns. -/
def listLiteral (bs : List ℕ) : String := Id.run do
  let mut out := "  ["
  let mut line := "  ["
  let mut first := true
  for b in bs do
    let item := (if first then "" else ", ") ++ hex b
    if line.length + item.length + 1 > 99 && !first then
      out := out ++ ",\n   "
      line := "   "
      out := out ++ hex b
      line := line ++ hex b
    else
      out := out ++ item
      line := line ++ item
    first := false
  return out ++ "]"

/-- Print the certificate definition for `L`, after checking it with the same
`rankCertCheck` the kernel will run. -/
def emit {n : ℕ} (defName doc : String) (L : List (NQubitPauliGroupElement n)) : IO Unit := do
  let rows := L.map fun g => rowMask g.operators
  match rightInverse (n + n) rows with
  | none => throw <| IO.userError s!"{defName}: rows are dependent, no certificate"
  | some bs =>
    unless rankCertCheck L bs do
      throw <| IO.userError s!"{defName}: generated certificate fails rankCertCheck"
    IO.println s!"/-- {doc}\n(m = {L.length}, n = {n}; emitted by"
    IO.println "`scripts/RankCertificateGen.lean`). -/"
    IO.println s!"def {defName} : List ℕ :=\n{listLiteral bs}\n"

instance : Fact (0 < 4) := ⟨by decide⟩
instance : Fact (0 < 5) := ⟨by decide⟩
instance : Fact (0 < 6) := ⟨by decide⟩

open StabilizerGroup in
/-- The codes this script knows how to certify. -/
def registry : List (String × IO Unit) :=
  [("steane7", emit "rankCert" "Rank certificate for the Steane generators"
      Steane7.generatorsList),
   ("shor9", emit "rankCert" "Rank certificate for the Shor generators"
      Shor9.generatorsList),
   ("toric4", emit "rankCert4" "Rank certificate for the trimmed `L = 4` toric generators"
      (ToricCodeN.generatorsListPackaged 4)),
   ("toric5", emit "rankCert5" "Rank certificate for the trimmed `L = 5` toric generators"
      (ToricCodeN.generatorsListPackaged 5)),
   ("toric6", emit "rankCert6" "Rank certificate for the trimmed `L = 6` toric generators"
      (ToricCodeN.generatorsListPackaged 6))]

end QEC.RankCertificateGen

open QEC.RankCertificateGen in
def main (args : List String) : IO Unit := do
  let names := if args.isEmpty then registry.map (·.1) else args
  for name in names do
    match registry.lookup name with
    | some act => act
    | none => throw <| IO.userError s!"unknown code {name}; known: {registry.map (·.1)}"
