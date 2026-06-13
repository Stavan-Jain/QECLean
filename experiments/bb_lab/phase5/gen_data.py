import json
d=json.load(open("experiments/bb_lab/phase5/data.json"))
def G(ab): return f"(({ab[0]} : ZMod 12), ({ab[1]} : ZMod 6))"
def E(e):  return f"((({e[0]} : ZMod 12), ({e[1]} : ZMod 6)), ({e[2]} : Fin 2))"
def Glist(lst): return "[" + ", ".join(G(x) for x in lst) + "]"
def Elist(lst): return "[" + ", ".join(E(x) for x in lst) + "]"
out=[]
out.append("/-- Face/vertex drop-set (6 group elements). -/")
out.append(f"def dropSet : List GrossGroup := {Glist(d['dropFaces'])}")
out.append("")
out.append("/-- Reduced ker ∂₂ basis: 6 face-supports (C2). `redP2 j (dropFaces i) = [i=j]`. -/")
out.append(f"def redP2 : List (List GrossGroup) := [{', '.join(Glist(b) for b in d['redP2'])}]")
out.append("")
out.append("/-- Reduced ker cutMap basis: 6 vertex-supports (C0). -/")
out.append(f"def redCM : List (List GrossGroup) := [{', '.join(Glist(b) for b in d['redCM'])}]")
out.append("")
out.append("/-- Face-independence decoder PhiX: support list of (output-coord, qubit) pairs. -/")
out.append(f"def phiX : List (GrossGroup × (GrossGroup × Fin 2)) := {Elist2(d['PhiX']) if False else '[' + ', '.join(f'({G(pp)}, {E(e)})' for pp,e in d['PhiX']) + ']'}")
out.append("")
out.append("/-- Vertex-independence decoder PhiZ. -/")
out.append(f"def phiZ : List (GrossGroup × (GrossGroup × Fin 2)) := {'[' + ', '.join(f'({G(pp)}, {E(e)})' for pp,e in d['PhiZ']) + ']'}")
out.append("")
out.append("/-- 12 X-logical cycle representatives (qubit supports). -/")
out.append(f"def logX : List (List (GrossGroup × Fin 2)) := [{', '.join(Elist(c) for c in d['logX'])}]")
out.append("")
out.append("/-- 12 Z-logical dual-cycle representatives (qubit supports). -/")
out.append(f"def logZ : List (List (GrossGroup × Fin 2)) := [{', '.join(Elist(c) for c in d['logZ'])}]")
open("experiments/bb_lab/phase5/data_section.lean","w").write("\n".join(out))
print("data_section.lean written:", sum(len(l) for l in out), "chars")
