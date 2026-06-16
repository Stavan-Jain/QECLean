import numpy as np
from itertools import product
from bb_lab.group import ZmZn
from bb_lab.poly import Poly
from bb_lab.checks import bb_check_matrices
from bb_lab.linalg import nullspace_f2
Gb=ZmZn(6,6); Ab=Poly.from_string("x^3 + y + y^2",Gb); Bb=Poly.from_string("y^3 + x + x^2",Gb)
cmb=bb_check_matrices(Ab,Bb); d2b=(cmb.H_Z&1).T; nb=36
A_steps=[(3,0),(0,1),(0,2)]; B_steps=[(0,3),(1,0),(2,0)]
def d2c_mat(j):
    d2c=np.zeros((72,nb),np.uint8)
    for g in Gb:
        col=Gb.index(g)
        for blk,steps in ((0,B_steps),(1,A_steps)):
            for (sx,sy) in steps:
                if ((g[0]-j)%6)+sx>=6: d2c[blk*nb+Gb.index(((g[0]+sx)%6,(g[1]+sy)%6)),col]^=1
    return d2c
D2C0=d2c_mat(0); ker2=nullspace_f2(d2b)
def span(rows):
    out=[]
    for m in range(1<<rows.shape[0]):
        v=np.zeros(rows.shape[1],np.uint8)
        for i in range(rows.shape[0]):
            if (m>>i)&1: v^=rows[i]
        out.append(v)
    return out
Z2all=[z for z in span(ker2) if z.any()]
F4=np.zeros((4,4),np.uint8)
for a in range(4):
    for b in range(4):
        a0,a1=a&1,a>>1; b0,b1=b&1,b>>1
        F4[a,b]=((a0&b0)^(a1&b1))|((((a0&b1)^(a1&b0)^(a1&b1))<<1))
OR5={0:(0,0),1:(0,1),2:(1,0),3:(1,1),4:(1,2)}; WP=[1,2,3]
def ch(v,j):
    o=[0,0,0,0]; c,d=OR5[j]
    for g in Gb:
        if v[Gb.index(g)]:
            s=(g[0]%2)|((g[1]%2)<<1); o[s]^=WP[(c*(g[0]%3)+d*(g[1]%3))%3]
    return tuple(o)
def rm(f,g):
    o=[0,0,0,0]
    for s1 in range(4):
        if f[s1]:
            for s2 in range(4):
                if g[s2]: o[s1^s2]^=int(F4[f[s1],g[s2]])
    return tuple(o)
def xo(a,b): return tuple(x^y for x,y in zip(a,b))
d0=np.eye(nb,dtype=np.uint8)[Gb.index((0,0))]
AH={j:ch((d2b[nb:,:]@d0)%2,j) for j in range(5)}
BH={j:ch((d2b[:nb,:]@d0)%2,j) for j in range(5)}
AF4=[tuple(t) for t in product(range(4),repeat=4)]; AF2=[e for e in AF4 if all(c<2 for c in e)]
def gamma(j):
    dom=AF2 if j==0 else AF4; out={}
    for t in dom: out[(rm(BH[j],t),rm(AH[j],t))]=True   # (left=Ahat t, right=Bhat t)
    return list(out)
G={j:gamma(j) for j in range(5)}
# value<->weight bijection
WT=np.full((2,4,4,4,4),-1,np.int8)
for fb in range(512):
    vv=[]
    for j,(c,d) in OR5.items():
        acc=0
        for t1 in range(3):
            for t2 in range(3):
                if (fb>>(3*t1+t2))&1: acc^=WP[(c*t1+d*t2)%3]
        vv.append(acc)
    WT[tuple(vv)]=bin(fb).count("1")
# d3v[v0*16+v3*4+v4][a1+2a2]
D3V=np.full((32,4),99,np.int8)
for v0 in range(2):
    for v3 in range(4):
        for v4 in range(4):
            for a1 in range(2):
                for a2 in range(2):
                    dom1=(0,) if a1==0 else (1,2,3); dom2=(0,) if a2==0 else (1,2,3)
                    D3V[v0*16+v3*4+v4,a1+2*a2]=min(int(WT[v0,v1,v2,v3,v4]) for v1 in dom1 for v2 in dom2)
def offs(w): return {j:(ch(w[:nb],j),ch(w[nb:],j)) for j in range(5)}
# orbits
def sw(z):
    out=np.zeros_like(z)
    for g in Gb: out[Gb.index((g[1],g[0]))]=z[Gb.index(g)]
    return out
def tr(z,dx,dy):
    out=np.zeros_like(z)
    for g in Gb: out[Gb.index(((g[0]+dx)%6,(g[1]+dy)%6))]=z[Gb.index(g)]
    return out
orbs={}
for z in Z2all:
    cands=[]
    for dx in range(6):
        for dy in range(6): cands.append(tr(z,dx,dy).tobytes()); cands.append(sw(tr(z,dx,dy)).tobytes())
    orbs.setdefault(min(cands),[]).append(z)
KEYS=sorted(orbs,key=lambda k:(int(np.frombuffer(k,np.uint8).sum()),len(orbs[k])))
# per-orbit: slab-min over (a0,a3,a4), count live slabs (<12), estimate work
print("orbit | slabs | live(<12) | livecost-est | maxlive-relaxedmin")
for key in KEYS:
    z=orbs[key][0]; o=offs((D2C0@z)%2)
    o0L,o0R=o[0]; o3L,o3R=o[3]; o4L,o4R=o[4]
    live=0; total=len(G[0])*len(G[3])*len(G[4]); wt=int(z.sum())
    livemins=[]
    for (p0L,p0R) in G[0]:
        for (p3L,p3R) in G[3]:
            for (p4L,p4R) in G[4]:
                sm=0
                for (oL,oR,pL,pR) in [(o0L,o0R,p0L,p0R)]:  # placeholder
                    pass
                # slab-min = sum over block,slot of d3v(v0,v3,v4; 0,0) (comps1,2 dead = min)
                for (bL,bR) in [(0,1)]:
                    pass
                # compute directly:
                sm=0
                for b in (0,1):
                    oo=[o0L,o3L,o4L] if b==0 else [o0R,o3R,o4R]
                    pp=[p0L,p3L,p4L] if b==0 else [p0R,p3R,p4R]
                    for s in range(4):
                        v0=oo[0][s]^pp[0][s]; v3=oo[1][s]^pp[1][s]; v4=oo[2][s]^pp[2][s]
                        sm+=min(int(D3V[v0*16+v3*4+v4,k]) for k in range(4))  # min over a1,a2
                if sm<12: live+=1; livemins.append(sm)
    # each live slab costs <= 53*53 relaxed + completions(<=#cheap*324); estimate fiber-only
    print(f"  wt={wt:2d} | {total} | {live:5d} | ~{live*2809} relaxed-iters | "
          f"livemin range {min(livemins) if livemins else '-'}..{max(livemins) if livemins else '-'}")

print("\n=== EXACT min on live slabs (brute over Gamma1 x Gamma2) ===")
# precompute Gamma1, Gamma2 value arrays (left/right slot tuples)
G1L=np.array([p[0] for p in G[1]],dtype=np.int64); G1R=np.array([p[1] for p in G[1]],dtype=np.int64)
G2L=np.array([p[0] for p in G[2]],dtype=np.int64); G2R=np.array([p[1] for p in G[2]],dtype=np.int64)
# WT as flat index v0+2*(v1+4*(v2+4*(v3+4*v4)))
WTF=np.full(512,-1,np.int64)
for v0 in range(2):
 for v1 in range(4):
  for v2 in range(4):
   for v3 in range(4):
    for v4 in range(4):
     WTF[v0+2*(v1+4*(v2+4*(v3+4*v4)))]=int(WT[v0,v1,v2,v3,v4])
for key in KEYS:
    z=orbs[key][0]; o=offs((D2C0@z)%2); wt=int(z.sum())
    o0L,o0R=o[0]; o3L,o3R=o[3]; o4L,o4R=o[4]
    gmin=99
    for (p0L,p0R) in G[0]:
     for (p3L,p3R) in G[3]:
      for (p4L,p4R) in G[4]:
        sm=0
        for b in (0,1):
            oo=[o0L,o3L,o4L] if b==0 else [o0R,o3R,o4R]; pp=[p0L,p3L,p4L] if b==0 else [p0R,p3R,p4R]
            for s in range(4):
                v0=oo[0][s]^pp[0][s]; v3=oo[1][s]^pp[1][s]; v4=oo[2][s]^pp[2][s]
                sm+=min(int(D3V[v0*16+v3*4+v4,k]) for k in range(4))
        if sm>=12: continue   # safe slab
        # live slab: exact min over p1(256) x p2(256), vectorized over p2 for each p1
        # left block cost: sum_s WTF[v0L^.. ]; v0,v3,v4 from comps0,3,4 (left), v1=G1L, v2=G2L
        bestslab=99
        for b,(o0,o3,o4,p0,p3,p4,G1,G2) in enumerate([
            (o0L,o3L,o4L,p0L,p3L,p4L,G1L,G2L),(o0R,o3R,o4R,p0R,p3R,p4R,G1R,G2R)]):
            pass
        # do exact: for each p1 in 256, cost_left(p1) depends on p1.L and p2.L; need joint p1,p2
        # brute 256x256:
        # left cost matrix L[p1,p2], right R[p1,p2]; total = L+R; but p1.L,p1.R share index p1
        # build per-(p1,p2): sum over slot of WTF
        # vectorize: for fixed p1, compute over all p2
        for p1 in range(256):
            # left: v0L,v3L,v4L fixed (from p0L,p3L,p4L + off), v1L=G1L[p1], v2L=G2L[:, s]
            cl=np.zeros(256,np.int64); cr=np.zeros(256,np.int64)
            for s in range(4):
                v0L=o0L[s]^p0L[s]; v3L=o3L[s]^p3L[s]; v4L=o4L[s]^p4L[s]; v1L=G1L[p1,s]
                cl+=WTF[v0L+2*(v1L+4*(G2L[:,s]+4*(v3L+4*v4L)))]
                v0R=o0R[s]^p0R[s]; v3R=o3R[s]^p3R[s]; v4R=o4R[s]^p4R[s]; v2R=G2R[:,s]
                # right depends on p2 (v2R=G2R[p2]) and p1 (v1R=G1R[p1])
                v1R=G1R[p1,s]
                cr+=WTF[v0R+2*(v1R+4*(v2R+4*(v3R+4*v4R)))]
            tot=cl+cr; m=int(tot.min())
            if m<bestslab: bestslab=m
        if bestslab<gmin: gmin=bestslab
    print(f"  wt={wt:2d}: exact min over ALL coset (slab-filtered) = {gmin}  -> {'OK >=12' if gmin>=12 else 'FAIL'}")
