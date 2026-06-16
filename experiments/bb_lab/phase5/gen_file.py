import json
d=json.load(open("experiments/bb_lab/phase5/data.json"))
def G(ab): return f"(({ab[0]} : ZMod 12), ({ab[1]} : ZMod 6))"
def E(e):  return f"((({e[0]} : ZMod 12), ({e[1]} : ZMod 6)), ({e[2]} : Fin 2))"
def Glist(lst): return "[" + ", ".join(G(x) for x in lst) + "]"
def Elist(lst): return "[" + ", ".join(E(x) for x in lst) + "]"
phiX='[' + ', '.join(f'({G(pp)}, {E(e)})' for pp,e in d['PhiX']) + ']'
phiZ='[' + ', '.join(f'({G(pp)}, {E(e)})' for pp,e in d['PhiZ']) + ']'
redP2='[' + ', '.join(Glist(b) for b in d['redP2']) + ']'
redCM='[' + ', '.join(Glist(b) for b in d['redCM']) + ']'
dropSet=Glist(d['dropFaces'])
dropVtx=Glist(d['dropVtx'])
logX='[' + ', '.join(Elist(c) for c in d['logX']) + ']'
logZ='[' + ', '.join(Elist(c) for c in d['logZ']) + ']'

HEADER='''/-
# The gross BB code as a `StabilizerCode 144 12`, with `HasCodeDistance`

Phase 5 of the gross `[[144, 12, 12]]` formalization: package
`grossComplex` (the `bbChainComplex grossA grossB` from `Defs.lean`) as a
genuine `StabilizerCode 144 12`, and transport the Phase-2 (`≥ 6`,
unconditional) and Phase-4 (`= 12`, conditional on the two CRT-engine Props)
distance theorems — stated against `grossComplex.homologicalStabilizerGroup`
— onto the packaged `HasCodeDistance` predicate via
`IsNontrivialLogicalOperator_of_toSubgroup_eq`.

This file embeds offline-validated `𝔽₂` linear-algebra data
(`experiments/bb_lab/phase5/`, `data.json`):
* `dropSet` — 6 faces / 6 vertices dropped to trim 144 generators to 132;
* `redP2` / `redCM` — reduced bases of `ker ∂₂` / `ker cutMap` (6 each),
  satisfying `redP2 j (dropSet i) = [i=j]`, giving both the closure relations
  and the independence kernel-collapse;
* `phiX` / `phiZ` — left-inverse "syndrome decoder" certificates proving the
  trimmed rows are independent (no rank theorem; see `decoder_identity_*`);
* `logX` / `logZ` — a symplectic basis of 12 X-cycles + 12 Z-dual-cycles
  with identity `12×12` intersection matrix (the 12 logical qubits).

Status: WIP skeleton. The two `native_decide` decoder identities (the
independence hard-core) are proven; the framework wiring is `sorry`-stubbed.
-/

import QEC.Stabilizer.Codes.BivariateBicycle.BaseDistance
import QEC.Stabilizer.Codes.BivariateBicycle.SafeSector
import QEC.Stabilizer.Framework.Homological.LogicalCorrespondence
import QEC.Stabilizer.Framework.Core.Logical.CodeDistance

namespace Quantum.Stabilizer.Homological.BB

open scoped BigOperators
open Quantum.Stabilizer.Homological

/-! ## §1  Offline-validated data (see `experiments/bb_lab/phase5/data.json`) -/

/-- The 6 faces / 6 vertices dropped to trim 144 generators down to 132. -/
def dropSet : List GrossGroup := %DROPSET%

/-- Reduced `ker ∂₂` basis (6 face-supports). `∂₂(redP2 j) = 0` and
`(redP2 j)(dropSet i) = [i=j]`. -/
def redP2 : List (List GrossGroup) := %REDP2%

/-- Reduced `ker cutMap` basis (6 vertex-supports). -/
def redCM : List (List GrossGroup) := %REDCM%

/-- Face-independence syndrome decoder: support list of (output-coord, qubit). -/
def phiX : List (GrossGroup × (GrossGroup × Fin 2)) := %PHIX%

/-- Vertex-independence syndrome decoder. -/
def phiZ : List (GrossGroup × (GrossGroup × Fin 2)) := %PHIZ%

/-- 12 X-logical cycle representatives (qubit supports). -/
def logX : List (List (GrossGroup × Fin 2)) := %LOGX%

/-- 12 Z-logical dual-cycle representatives (qubit supports). -/
def logZ : List (List (GrossGroup × Fin 2)) := %LOGZ%

/-! ## §2  Sparse boundary terms and the decoder identities

`∂₂(δ_f)` and `cutMap(δ_v)` are sparse point-mass images; evaluating them
through these few-term forms (rather than `conv`) keeps the `native_decide`
sweeps cheap. -/

/-- `∂₂(δ_f)` evaluated at qubit `(h, j)`:  `A(h-f)` on the left block,
`B(h-f)` on the right. -/
def d2term (f h : GrossGroup) (j : Fin 2) : ZMod 2 :=
  if j = 0 then grossA (h - f) else grossB (h - f)

/-- `cutMap(δ_v)` evaluated at qubit `(h, j)`:  `B(v-h)` on the left block,
`A(v-h)` on the right. -/
def cmTerm (v h : GrossGroup) (j : Fin 2) : ZMod 2 :=
  if j = 0 then grossB (v - h) else grossA (v - h)

/-- Apply the `phiX` decoder to `∂₂(δ_p)`, read at output face `p'`. -/
def decodeXAt (p p' : GrossGroup) : ZMod 2 :=
  (phiX.filter (fun pr => pr.1 = p')).foldl
    (fun acc pr => acc + d2term p pr.2.1 pr.2.2) 0

/-- Apply the `phiZ` decoder to `cutMap(δ_p)`, read at output vertex `p'`. -/
def decodeZAt (p p' : GrossGroup) : ZMod 2 :=
  (phiZ.filter (fun pr => pr.1 = p')).foldl
    (fun acc pr => acc + cmTerm p pr.2.1 pr.2.2) 0

/-- Kernel-basis correction term `Σ_j [p = dropSet j] · (red j)(p')`. -/
def kerCorrection (red : List (List GrossGroup)) (p p' : GrossGroup) : ZMod 2 :=
  ((List.range 6).filter (fun j => dropSet.getD j 0 = p)).foldl
    (fun acc j => acc + (if (red.getD j []).contains p' then 1 else 0)) 0

/-- **Face decoder identity** (validated `native_decide`, ~5 s): the `phiX`
decoder inverts `∂₂` on the trimmed face subspace, modulo the `redP2` kernel
basis. Over all `72×72` basis pairs. This is the independence hard-core for
the X block — it yields `∂₂ f = 0 ∧ f|_dropSet = 0 → f = 0` by linearity. -/
theorem decoder_identity_X :
    ∀ p p' : GrossGroup,
      decodeXAt p p' + kerCorrection redP2 p p' = (if p' = p then 1 else 0) := by
  native_decide

/-- **Vertex decoder identity** (validated `native_decide`): mirror of
`decoder_identity_X` for the Z block (`cutMap`, `phiZ`, `redCM`). -/
theorem decoder_identity_Z :
    ∀ p p' : GrossGroup,
      decodeZAt p p' + kerCorrection redCM p p' = (if p' = p then 1 else 0) := by
  native_decide

end Quantum.Stabilizer.Homological.BB
'''
body=HEADER
for k,v in [("%DROPSET%",dropSet),("%REDP2%",redP2),("%REDCM%",redCM),("%PHIX%",phiX),("%PHIZ%",phiZ),("%LOGX%",logX),("%LOGZ%",logZ)]:
    body=body.replace(k,v)
open("QEC/Stabilizer/Codes/BivariateBicycle/StabilizerCode.lean","w").write(body)
print("wrote StabilizerCode.lean", len(body), "chars")
