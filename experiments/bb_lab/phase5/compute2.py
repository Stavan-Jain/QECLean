# Full data extraction for gross BB code Phase 5 packaging.
NA, NB = 12, 6
G = [(a,b) for a in range(NA) for b in range(NB)]
NG = len(G); idx = {g:i for i,g in enumerate(G)}
def sub(g,h): return ((g[0]-h[0])%NA, (g[1]-h[1])%NB)
def addg(g,h): return ((g[0]+h[0])%NA, (g[1]+h[1])%NB)
Asup={(3,0),(0,1),(0,2)}; Bsup={(0,3),(1,0),(2,0)}
def poly(sup):
    v=[0]*NG
    for g in sup: v[idx[g]]=1
    return v
A=poly(Asup); B=poly(Bsup)
def conv(a,b):
    out=[0]*NG
    for gi,g in enumerate(G):
        s=0
        for hi,h in enumerate(G):
            if a[hi] and b[idx[sub(g,h)]]: s^=1
        out[gi]=s
    return out
NC1=2*NG
def q(hi,j): return j*NG+hi
def partial2(f):
    Af=conv(A,f); Bf=conv(B,f); out=[0]*NC1
    for hi in range(NG): out[q(hi,0)]=Af[hi]; out[q(hi,1)]=Bf[hi]
    return out
def cutMap(s):
    out=[0]*NC1
    for hi,h in enumerate(G):
        s0=0;s1=0
        for vi,v in enumerate(G):
            if s[vi]:
                if B[idx[sub(v,h)]]: s0^=1
                if A[idx[sub(v,h)]]: s1^=1
        out[q(hi,0)]=s0; out[q(hi,1)]=s1
    return out
def partial1(c):
    cL=[c[q(hi,0)] for hi in range(NG)]; cR=[c[q(hi,1)] for hi in range(NG)]
    BcL=conv(B,cL); AcR=conv(A,cR)
    return [BcL[g]^AcR[g] for g in range(NG)]
P2cols=[partial2(poly({G[f]})) for f in range(NG)]
def dualBoundary(c):
    out=[0]*NG
    for f in range(NG):
        col=P2cols[f]; s=0
        for e in range(NC1):
            if c[e] and col[e]: s^=1
        out[f]=s
    return out

def rref(rows,ncols):
    M=[r[:] for r in rows]; piv=[]; r=0
    for col in range(ncols):
        sel=None
        for i in range(r,len(M)):
            if M[i][col]: sel=i;break
        if sel is None: continue
        M[r],M[sel]=M[sel],M[r]
        for i in range(len(M)):
            if i!=r and M[i][col]: M[i]=[a^b for a,b in zip(M[i],M[r])]
        piv.append(col); r+=1
        if r==len(M): break
    return M[:r],piv
def nullspace(cols):
    # cols: list of codomain-vectors (image of each basis vector). domain=len(cols)
    dom=len(cols); cod=len(cols[0])
    Mat=[[cols[i][r] for i in range(dom)] for r in range(cod)]
    R,piv=rref(Mat,dom); pivset=set(piv)
    free=[c for c in range(dom) if c not in pivset]; basis=[]
    for fcol in free:
        x=[0]*dom; x[fcol]=1
        for ri,pc in enumerate(piv):
            if R[ri][fcol]: x[pc]^=1
        basis.append(x)
    return basis,piv,free

# reduced kernel basis + drop-set via RREF of the kernel basis matrix
def reduce_kernel(basis):
    # basis: list of vectors (len NG). RREF -> pivot columns = drop-set, reduced rows.
    R,piv=rref([b[:] for b in basis], NG)
    return R, piv  # R[i] has pivot at piv[i]; R[i][piv[j]]=delta_ij guaranteed by rref

kerP2,_,_=nullspace(P2cols)
redP2,dropFaces=reduce_kernel(kerP2)
CMcols=[cutMap(poly({G[v]})) for v in range(NG)]
kerCM,_,_=nullspace(CMcols)
redCM,dropVtx=reduce_kernel(kerCM)
print("dropFaces (idx):",dropFaces,"=",[G[i] for i in dropFaces])
print("dropVtx (idx):",dropVtx,"=",[G[i] for i in dropVtx])
# verify reduced form: redP2[j] in ker, redP2[j][dropFaces[i]]=delta
for j,b in enumerate(redP2):
    assert all(v==0 for v in partial2(b)), "redP2 not in ker"
    for i,d in enumerate(dropFaces):
        assert b[d]==(1 if i==j else 0)
for j,b in enumerate(redCM):
    assert all(v==0 for v in cutMap(b))
    for i,d in enumerate(dropVtx):
        assert b[d]==(1 if i==j else 0)
print("reduced kernel bases OK (in ker, reduced wrt drop-set)")

# support sizes of reduced kernel vectors (these become the closure relations)
print("redP2 supports:", [[G[i] for i in range(NG) if b[i]] for b in redP2])
print("redCM supports:", [[G[i] for i in range(NG) if b[i]] for b in redCM])

import json
# ---- Independence decoder Phi_X (faces): linear map C1(144)->C2(72) with
#      Phi(partial2 f) + sum_j f(d_j) b_j = f   for all f.
# Build the injective map T(f) = (partial2 f, f|_D) : C2 -> C1 (+) F2^D, find left inverse on partial2 part.
# Concretely: we want Phi (72x144) s.t. for basis delta_p: Phi(partial2 delta_p) = delta_p - sum_j [p=d_j] b_j.
# Let target_p = delta_p - sum_j [p in D, p=d_j] redP2[j]   (a C2 vector, len 72) which has D-support zero.
# And partial2 delta_p = P2cols[p] (C1 vector). We need a linear Phi with Phi(P2cols[p]) = target_p for all p.
# Since {P2cols[p]} spans range(partial2)=66-dim and the map p->target_p factors through partial2
# (target_p depends only on partial2 delta_p? target is the f0-rep; yes consistent), Phi exists.
# Solve: stack equations. Unknown Phi is 72x144. For each output coord p' (0..71):
#   row vector phi_{p'} in F2^144 with <phi_{p'}, P2cols[p]> = target_p[p'] for all p (72 eqns).
# That's solving a 72x144 system per p'. The coefficient matrix Mc[p][e]=P2cols[p][e] (72x144), rhs target[:,p'].
# Solve Mc^T? We need phi (144) with Mc @ phi = rhs (72). Mc is 72x144 rank 66; rhs in column space (consistent).
def solve(Mc_rows, rhs):
    # Mc_rows: list of 72 rows length 144; rhs length 72. Find x length 144 with Mc x = rhs (any solution).
    ncol=len(Mc_rows[0]); nrow=len(Mc_rows)
    aug=[Mc_rows[i][:]+[rhs[i]] for i in range(nrow)]
    piv=[]; r=0
    for col in range(ncol):
        sel=None
        for i in range(r,nrow):
            if aug[i][col]: sel=i;break
        if sel is None: continue
        aug[r],aug[sel]=aug[sel],aug[r]
        for i in range(nrow):
            if i!=r and aug[i][col]: aug[i]=[a^b for a,b in zip(aug[i],aug[r])]
        piv.append(col); r+=1
        if r==nrow: break
    # check consistency
    for i in range(r,nrow):
        if aug[i][ncol]: return None
    x=[0]*ncol
    for ri,pc in enumerate(piv): x[pc]=aug[ri][ncol]
    return x

def build_decoder(P2cols_, redKer, dropSet):
    Mc=[[P2cols_[p][e] for e in range(NC1)] for p in range(NG)]  # 72x144
    Phi=[]  # 72 rows (one per output coord p'), each length 144
    for pprime in range(NG):
        rhs=[0]*NG
        for p in range(NG):
            t = 1 if p==pprime else 0
            # minus sum_j [p=d_j] redKer[j][pprime]
            for j,d in enumerate(dropSet):
                if p==d: t^=redKer[j][pprime]
            rhs[p]=t
        x=solve(Mc,rhs)
        assert x is not None, "decoder row inconsistent"
        Phi.append(x)
    return Phi
PhiX=build_decoder(P2cols, redP2, dropFaces)
# verify: for all f basis delta_p: Phi(partial2 delta_p) + sum_j delta_p(d_j) redP2[j] == delta_p
def applyPhi(Phi,c1vec):  # Phi 72x144, c1vec 144 -> 72
    return [sum(Phi[pp][e] for e in range(NC1) if c1vec[e]&Phi[pp][e])%2 for pp in range(NG)]
def applyPhi2(Phi,c1vec):
    out=[0]*NG
    for pp in range(NG):
        s=0
        for e in range(NC1):
            if c1vec[e] and Phi[pp][e]: s^=1
        out[pp]=s
    return out
ok=True
for p in range(NG):
    lhs=applyPhi2(PhiX,P2cols[p])
    for j,d in enumerate(dropFaces):
        if p==d: lhs=[lhs[i]^redP2[j][i] for i in range(NG)]
    tgt=[1 if i==p else 0 for i in range(NG)]
    if lhs!=tgt: ok=False;break
print("PhiX decoder identity holds:",ok)

CMcols_=[cutMap(poly({G[v]})) for v in range(NG)]
PhiZ=build_decoder(CMcols_, redCM, dropVtx)
ok2=True
for p in range(NG):
    lhs=applyPhi2(PhiZ,CMcols_[p])
    for j,d in enumerate(dropVtx):
        if p==d: lhs=[lhs[i]^redCM[j][i] for i in range(NG)]
    tgt=[1 if i==p else 0 for i in range(NG)]
    if lhs!=tgt: ok2=False;break
print("PhiZ decoder identity holds:",ok2)
print("PhiX density (nonzeros):", sum(sum(r) for r in PhiX), "of", NG*NC1)
print("PhiZ density (nonzeros):", sum(sum(r) for r in PhiZ), "of", NG*NC1)

# ---- 12+12 symplectic logical basis ----
# cycles Z = ker partial1 (dim 78); boundaries Bd = im partial2 (66); H1=Z/Bd (12).
# dualCycles Zd = ker dualBoundary (78); dualBoundaries Bdd = im cutMap (66); H1d (12).
def basis_im(cols):
    R,piv=rref([c[:] for c in cols], len(cols[0]))
    return R  # row space basis of the image (span of cols) -- but we need actual image vectors
# image basis: take columns, rref the matrix with columns as rows
def image_basis(cols):
    # span of the cols vectors
    R,piv=rref([c[:] for c in cols], len(cols[0]))
    return R
def kernel(cols):
    b,_,_=nullspace(cols); return b
P1cols=[partial1([1 if e==i else 0 for e in range(NC1)]) for i in range(NC1)]
DBcols=[dualBoundary([1 if e==i else 0 for e in range(NC1)]) for i in range(NC1)]
Z=kernel(P1cols)        # 78 vectors len 144
Bd=image_basis(P2cols)  # boundaries, vectors len 144 (span of partial2 columns)
Zd=kernel(DBcols)       # 78
Bdd=image_basis(CMcols_)
print("dims: Z",len(Z),"Bd",len(Bd),"Zd",len(Zd),"Bdd",len(Bdd))
# H1 reps: extend Bd to a basis of Z; extra vectors are reps.
def extend_to(sub, full):
    # sub, full: lists of vectors (len NC1). Return vectors in full not in span(sub so far), building basis of span(full).
    cur=[v[:] for v in sub]
    reps=[]
    # maintain rref of cur
    def in_span(v, basisrows):
        # reduce v by basisrows (already rref-ish); use fresh rref
        rows=[r[:] for r in basisrows]+[v[:]]
        R,piv=rref(rows, NC1)
        return len(R)==len(basisrows)  # rank unchanged => v in span
    basisrows,_=rref([v[:] for v in cur], NC1)
    for v in full:
        if not in_span(v, basisrows):
            reps.append(v[:])
            basisrows,_=rref(basisrows+[v[:]], NC1)
        if len(reps)==12: break
    return reps
H1=extend_to(Bd, Z)
H1d=extend_to(Bdd, Zd)
print("H1 reps:",len(H1),"H1d reps:",len(H1d))
def ip(a,b): 
    s=0
    for e in range(NC1):
        if a[e] and b[e]: s^=1
    return s
M=[[ip(H1[i],H1d[j]) for j in range(12)] for i in range(12)]
# invert M over F2
def invF2(Min):
    n=len(Min); aug=[Min[i][:]+[1 if j==i else 0 for j in range(n)] for i in range(n)]
    for col in range(n):
        sel=next((i for i in range(col,n) if aug[i][col]),None)
        assert sel is not None,"singular"
        aug[col],aug[sel]=aug[sel],aug[col]
        for i in range(n):
            if i!=col and aug[i][col]: aug[i]=[a^b for a,b in zip(aug[i],aug[col])]
    return [row[n:] for row in aug]
Minv=invF2(M)
# d'_j = sum_k Minv[k][j] H1d[k]
H1d2=[]
for j in range(12):
    v=[0]*NC1
    for k in range(12):
        if Minv[k][j]:
            for e in range(NC1): v[e]^=H1d[k][e]
    H1d2.append(v)
M2=[[ip(H1[i],H1d2[j]) for j in range(12)] for i in range(12)]
print("intersection matrix now identity:", M2==[[1 if i==j else 0 for j in range(12)] for i in range(12)])
# sanity: H1[i] in cycles (partial1=0), H1d2 in dualcycles (dualBoundary=0)
print("H1 all cycles:", all(all(x==0 for x in partial1(c)) for c in H1))
print("H1d2 all dualcycles:", all(all(x==0 for x in dualBoundary(c)) for c in H1d2))
# weights
print("H1 weights:", [sum(c) for c in H1])
print("H1d2 weights:", [sum(c) for c in H1d2])

def vec_to_coords(v):  # C1 vector -> list of (a,b,j)
    out=[]
    for e in range(NC1):
        if v[e]:
            j=e//NG; hi=e%NG; a,b=G[hi]; out.append([a,b,j])
    return out
def c2_to_coords(v):  # C2/C0 vector -> list (a,b)
    return [[G[i][0],G[i][1]] for i in range(NG) if v[i]]
def phi_to_coords(Phi):  # list of (pprime(a,b), edge(a,b,j))
    out=[]
    for pp in range(NG):
        for e in range(NC1):
            if Phi[pp][e]:
                j=e//NG; hi=e%NG; out.append([[G[pp][0],G[pp][1]],[G[hi][0],G[hi][1],j]])
    return out

data={
 "dropFaces":[list(G[i]) for i in dropFaces],
 "dropVtx":[list(G[i]) for i in dropVtx],
 "redP2":[c2_to_coords(b) for b in redP2],   # ker partial2 reduced basis (C2 supports)
 "redCM":[c2_to_coords(b) for b in redCM],   # ker cutMap reduced basis (C0 supports)
 "PhiX":phi_to_coords(PhiX),
 "PhiZ":phi_to_coords(PhiZ),
 "logX":[vec_to_coords(c) for c in H1],       # 12 X-logical cycles
 "logZ":[vec_to_coords(c) for c in H1d2],      # 12 Z-logical dualcycles
}
json.dump(data, open("experiments/bb_lab/phase5/data.json","w"))
print("WROTE data.json ; sizes: redP2",len(data["redP2"]),"PhiX pairs",len(data["PhiX"]),"PhiZ pairs",len(data["PhiZ"]),"logX",len(data["logX"]))
