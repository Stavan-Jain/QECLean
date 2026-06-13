import json
exec(open("experiments/bb_lab/phase5/compute2.py").read().split("import json")[0])  # reload defs
# Recompute needed pieces quickly
import json
d=json.load(open("experiments/bb_lab/phase5/data.json"))
NA,NB=12,6
Gl=[(a,b) for a in range(NA) for b in range(NB)]; idx={g:i for i,g in enumerate(Gl)}
def sub(g,h): return ((g[0]-h[0])%NA,(g[1]-h[1])%NB)
Asup={(3,0),(0,1),(0,2)}; Bsup={(0,3),(1,0),(2,0)}
def Aval(g): return 1 if (g[0]%NA,g[1]%NB) in Asup else 0
def Bval(g): return 1 if (g[0]%NA,g[1]%NB) in Bsup else 0
def cmterm(v,h,j): return Bval(sub(v,h)) if j==0 else Aval(sub(v,h))
# phiZ pairs: [[a,b],[ [a,b],j ]]
phiZ=d["PhiZ"]; redCM=d["redCM"]; dropVtx=d["dropVtx"]
def gtuple(x): return (x[0]%NA,x[1]%NB)
# decodeZ(cutMap delta_p)(p') = sum over phiZ pairs with first=p' of cmterm(p, edge.h, edge.j)
ok=True
for p in Gl:
    for pp in Gl:
        s=0
        for (ppair,e) in phiZ:
            if gtuple(ppair)==pp:
                eh=(e[0]%NA,e[1]%NB); ej=e[2]
                s^=cmterm(p,eh,ej)
        # correction: sum_j [p==dropVtx[j]] redCM[j] contains pp
        for j,dv in enumerate(dropVtx):
            if gtuple(dv)==p:
                if any(gtuple(x)==pp for x in redCM[j]): s^=1
        tgt=1 if pp==p else 0
        if s!=tgt: ok=False; break
    if not ok: break
print("Z decoder identity holds offline:", ok)
