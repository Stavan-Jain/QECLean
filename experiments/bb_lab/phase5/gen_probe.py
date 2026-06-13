import json
d=json.load(open("experiments/bb_lab/phase5/data.json"))
# PhiX: list of [[a,b],[a,b,j]]  (pprime, edge). Emit as Lean list of (G x (G x Fin2)).
def gpair(ab): return f"(({ab[0]} : ZMod 12), ({ab[1]} : ZMod 6))"
def edge(e): return f"((({e[0]} : ZMod 12), ({e[1]} : ZMod 6)), ({e[2]} : Fin 2))"
phiX="[" + ", ".join(f"({gpair(pp)}, {edge(e)})" for pp,e in d["PhiX"]) + "]"
# redP2: 6 lists of C2 supports (G). dropFaces: 6 G's.
def glist(lst): return "[" + ", ".join(gpair(ab) for ab in lst) + "]"
redP2="[" + ", ".join(glist(b) for b in d["redP2"]) + "]"
dropFaces="[" + ", ".join(gpair(ab) for ab in d["dropFaces"]) + "]"
lean=f'''import QEC.Stabilizer.Codes.BivariateBicycle.Defs

namespace Quantum.Stabilizer.Homological.BB
open scoped BigOperators

/-- ∂₂ of a point mass at face f, evaluated at qubit (h,j): A or B shifted. -/
def d2term (f : GrossGroup) (h : GrossGroup) (j : Fin 2) : ZMod 2 :=
  if j = 0 then grossA (h - f) else grossB (h - f)

/-- Decoder PhiX as a support list of (output-coord, edge) pairs. -/
def phiXList : List (GrossGroup × (GrossGroup × Fin 2)) := {phiX}

/-- redP2 reduced kernel basis (6 C2 supports). -/
def redP2List : List (List GrossGroup) := {redP2}

def dropFacesList : List GrossGroup := {dropFaces}

/-- decodeX applied to ∂₂(δ_p), read at output coord p'. -/
def decodeAtD2delta (p p' : GrossGroup) : ZMod 2 :=
  (phiXList.filter (fun pr => pr.1 = p')).foldl
    (fun acc pr => acc + d2term p pr.2.1 pr.2.2) 0

/-- correction term: Σ_j [p = dropFaces j] redP2[j](p'). -/
def correction (p p' : GrossGroup) : ZMod 2 :=
  ((List.range 6).filter (fun j => dropFacesList.getD j 0 = p)).foldl
    (fun acc j => acc + (if (redP2List.getD j []).contains p' then 1 else 0)) 0

/-- THE PROBE: decoder identity on all 72×72 basis cases. -/
theorem probe_decoder_identity :
    ∀ p : GrossGroup, ∀ p' : GrossGroup,
      decodeAtD2delta p p' + correction p p' = (if p' = p then 1 else 0) := by
  native_decide

end Quantum.Stabilizer.Homological.BB
'''
open("experiments/bb_lab/phase5/Probe.lean","w").write(lean)
print("probe written; phiXList entries:", len(d["PhiX"]))
