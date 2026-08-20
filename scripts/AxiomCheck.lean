/-
Axiom-policy enforcement for CI.

Every declaration defined in this repository must depend on exactly mathlib's
three standard axioms — `propext`, `Classical.choice`, `Quot.sound` — and
nothing else.  See CLAUDE.md § "Axiom policy".

This catches, without needing a hand-maintained list of capstones:

* `native_decide`, which seals a claim behind a compiler-trust axiom rather
  than checking it in the kernel.  As of v4.30 the axiom is named per
  declaration (`Your.Theorem._native.native_decide.ax_1_1`), so grepping for a
  fixed name such as `Lean.ofReduceBool` does **not** find it — reading the
  axiom set does.
* `sorry`, which emits `sorryAx`.
* bespoke `axiom` declarations, which are reported even when nothing uses them.

Run with `lake env lean scripts/AxiomCheck.lean`; it exits non-zero and prints
every offender on failure.  Not part of any `lean_lib`, so a normal
`lake build` does not pay for it.
-/
import QEC

open Lean

namespace QEC.AxiomCheck

/-- The three axioms mathlib accepts, and the only ones allowed here. -/
def allowed : NameSet :=
  NameSet.empty
    |>.insert ``propext
    |>.insert ``Classical.choice
    |>.insert ``Quot.sound

/-- Modules belonging to this repository (as opposed to mathlib/std/core). -/
def isOurModule (m : Name) : Bool := m.getRoot == `QEC

run_cmd do
  let env ← Lean.getEnv
  let hdr := env.header
  let mut offenders : Array (Name × Name × Array Name) := #[]
  let mut declaredAxioms : Array (Name × Name) := #[]
  let mut checked := 0
  for i in [0 : hdr.moduleNames.size] do
    let modName := hdr.moduleNames[i]!
    unless isOurModule modName do continue
    for c in hdr.moduleData[i]!.constNames do
      -- A bespoke `axiom` declared in our own modules is a violation in itself.
      if let some (.axiomInfo _) := env.find? c then
        unless allowed.contains c do
          declaredAxioms := declaredAxioms.push (modName, c)
      let axs ← Lean.collectAxioms c
      checked := checked + 1
      let extra := axs.filter (fun a => !allowed.contains a)
      unless extra.isEmpty do
        offenders := offenders.push (modName, c, extra)
  if offenders.isEmpty && declaredAxioms.isEmpty then
    let nmods := (hdr.moduleNames.filter isOurModule).size
    logInfo s!"axiom policy OK — {checked} declarations across {nmods} \
modules depend on only [propext, Classical.choice, Quot.sound]"
  else
    let mut msg := "AXIOM POLICY VIOLATION (see CLAUDE.md § \"Axiom policy\")\n"
    unless declaredAxioms.isEmpty do
      msg := msg ++ s!"\n{declaredAxioms.size} bespoke `axiom` declaration(s):\n"
      for (m, c) in declaredAxioms do
        msg := msg ++ s!"  {c}\n      declared in {m}\n"
    unless offenders.isEmpty do
      msg := msg ++ s!"\n{offenders.size} declaration(s) outside the allowed axiom set:\n"
      for (m, c, extra) in offenders do
        let tag :=
          if extra.any (· == ``sorryAx) then " [sorry]"
          else if extra.any (fun a => ((toString a).splitOn "native_decide").length > 1) then
            " [native_decide]"
          else ""
        msg := msg ++ s!"  {c}{tag}\n      in {m}\n      extra axioms: {extra}\n"
    throwError msg

end QEC.AxiomCheck
