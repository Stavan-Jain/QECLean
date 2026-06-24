import numpy as np, itertools
from bb_lab.group import ZmZn
from bb_lab.poly import Poly
from bb_lab.checks import bb_check_matrices
from bb_lab.linalg import nullspace_f2
Gb=ZmZn(6,6);Ab=Poly.from_string("x^3 + y + y^2",Gb);Bb=Poly.from_string("y^3 + x + x^2",Gb)
Gc=ZmZn(12,6);Ac=Poly.from_string("x^3 + y + y^2",Gc);Bc=Poly.from_string("y^3 + x + x^2",Gc)
HZb=bb_check_matrices(Ab,Bb).H_Z&1;HZc=bb_check_matrices(Ac,Bc).H_Z&1
nb=Gb.cardinality;nc=Gc.cardinality
def sheet(g):return 1 if g[0]>=6 else 0
def base_of(g):return (g[0]%6,g[1])
rp=np.empty(nc,int);cp=np.empty(2*nc,int)
for g in Gc:
    rp[Gc.index(g)]=sheet(g)*nb+Gb.index(base_of(g))
    for blk in(0,1):cp[blk*nc+Gc.index(g)]=sheet(g)*(2*nb)+blk*nb+Gb.index(base_of(g))
HZc_p=np.zeros_like(HZc);HZc_p[rp[:,None],cp[None,:]]=HZc
d2=(HZb.T)&1; d2c=((HZc_p[:nb,2*nb:]).T)&1
def mv(M,v):return (M@v)&1
def Tface(c,f):
    o=np.zeros(nb,int)
    for g in Gb:o[Gb.index(g)]=f[Gb.index(Gb.add(g,c))]
    return o
def Tqub(c,v):
    o=np.zeros(2*nb,int)
    for g in Gb:
        for blk in(0,1):o[blk*nb+Gb.index(g)]=v[blk*nb+Gb.index(Gb.add(g,c))]
    return o
def solve_f2(A,b):
    A=A.copy()&1;b=b.copy()&1;m,n=A.shape;M=np.hstack([A,b[:,None]])&1;piv=[];r=0
    for c in range(n):
        pr=next((i for i in range(r,m) if M[i,c]),None)
        if pr is None:continue
        M[[r,pr]]=M[[pr,r]]
        for i in range(m):
            if i!=r and M[i,c]:M[i]=(M[i]+M[r])&1
        piv.append(c);r+=1
        if r==m:break
    x=np.zeros(n,int)
    for i,c in enumerate(piv):x[c]=M[i,n]
    return x&1
free=[(4,4),(4,5),(5,2),(5,3),(5,4),(5,5)];fidx=[Gb.index(c) for c in free]
K=nullspace_f2(d2)
def inv_f2(A):
    n=A.shape[0];M=np.hstack([A&1,np.eye(n,dtype=int)])&1
    for c in range(n):
        pr=next(i for i in range(c,n) if M[i,c]);M[[c,pr]]=M[[pr,c]]
        for i in range(n):
            if i!=c and M[i,c]:M[i]=(M[i]+M[c])&1
    return M[:,n:]&1
Minv=inv_f2(K[:,fidx]&1);kb=[(Minv[i]@K)&1 for i in range(6)]
def kcombo(c):
    z=np.zeros(nb,int)
    for b,r_ in zip(c,kb):
        if b:z=(z+r_)&1
    return z
def coords(z): return tuple(int(z[fidx[j]]) for j in range(6))   # back to kb free-cell coords

# Y zreps (from the repo)
Yrep={0:(1,0,0,0,0,0),1:(0,0,1,0,0,0),2:(1,0,1,0,0,0),3:(0,1,1,0,0,0),4:(1,1,1,0,0,0),
      5:(0,0,1,1,0,0),6:(1,0,1,1,0,0),7:(0,1,1,1,0,0),8:(1,1,1,1,0,0),9:(0,0,0,1,1,0),
      10:(1,0,0,1,1,0),11:(0,1,0,1,1,0),12:(1,1,0,1,1,0)}
all_c=[tuple((i>>(5-t))&1 for t in range(6)) for i in range(64)]   # rcases order, c0 MSB
nonzero=[c for c in all_c if any(c)]
shifts=[(j,k) for j in range(6) for k in range(6)]

# full-2D orbits over nonzero classes; map class -> set of (shift, image-coords)
orbit_of={}; orbits=[]
for c in nonzero:
    if c in orbit_of: continue
    z=kcombo(c); members=set()
    for (j,k) in shifts:
        members.add(coords(Tface((j,k),z)))
    oid=len(orbits); orbits.append(members)
    for m in members: orbit_of[m]=oid
print(f"# full-2D orbits among 63 nonzero classes: {len(orbits)}")
# choose one Y rep per orbit (lowest Y index whose zrep is in the orbit)
kept={}   # oid -> Y index
for yi in range(13):
    o=orbit_of[Yrep[yi]]
    if o not in kept: kept[o]=yi
assert len(kept)==len(orbits), "every orbit must contain a Y rep"
kept_Y=sorted(kept.values())
print(f"# kept Y modules (one per orbit): {kept_Y}")
print(f"# dropped Y modules: {sorted(set(range(13))-set(kept_Y))}")

def find_shift(rep_c, cls_c):
    zr=kcombo(rep_c)
    for (j,k) in shifts:
        if coords(Tface((j,k),zr))==cls_c: return (j,k)
    return None

# emit dispatch bullets in rcases order (64 leaves)
lines=[]
for c in all_c:
    if not any(c):
        lines.append("  · rw [kcombo_zero, seamC_zero, zero_add] at hb; exact absurd ⟨f, rfl⟩ hb")
        continue
    oid=orbit_of[c]; yi=kept[oid]; rep_c=Yrep[yi]; (j,k)=find_shift(rep_c,c)
    # defect: w = seamC(kcombo c) + translate1 (j,k)(seamC(kcombo rep))
    zr=kcombo(rep_c)
    w=(mv(d2c,kcombo(c)) + Tqub((j,k),mv(d2c,zr)))&1
    delta=solve_f2(d2,w)
    # sanity
    assert np.array_equal(mv(d2,delta), w), f"defect solve failed {c}"
    # minimize defect weight over the kernel coset delta + ker d2 (any preimage works)
    best=delta; bw=int(delta.sum())
    for kbits in itertools.product([0,1],repeat=6):
        cand=delta.copy()
        for b,kr in zip(kbits,kb):
            if b: cand=(cand+kr)&1
        w2=int(cand.sum())
        if w2<bw: best,bw=cand,w2
    delta=best
    assert np.array_equal(mv(d2,delta), w), "min-weight defect broke preimage"
    supp=[ (int(g[0]),int(g[1])) for g in Gb if delta[Gb.index(g)] ]
    cstr=" ".join(str(x) for x in c)
    dlist="["+",".join(f"({a},{b})" for (a,b) in supp)+"]"
    lines.append(f"  · exact floor_transfer Y{yi}.zrep (kcombo {cstr}) (({j}, {k}) : BaseGroup)\n"
                 f"      (mkZeta {dlist})\n"
                 f"      (by native_decide) Y{yi}.floor f")
open("/tmp/dispatch_body.txt","w").write("\n".join(lines)+"\n")
print(f"# wrote 64 bullets to /tmp/dispatch_body.txt; defect support sizes "
      f"min={min(len([1 for g in Gb if solve_f2(d2,(mv(d2c,kcombo(c))+Tqub(find_shift(Yrep[kept[orbit_of[c]]],c),mv(d2c,kcombo(Yrep[kept[orbit_of[c]]]))))&1)[Gb.index(g)]]) for c in nonzero) if nonzero else 0}")
# kept module info for editing
import json
open("/tmp/kept_Y.json","w").write(json.dumps({"kept":kept_Y,"dropped":sorted(set(range(13))-set(kept_Y))}))
