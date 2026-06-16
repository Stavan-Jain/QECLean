import itertools, sys

# Group G = Z12 x Z6, elements (a,b)
NA, NB = 12, 6
G = [(a,b) for a in range(NA) for b in range(NB)]   # 72 elements, fixed order
NG = len(G)
idx = {g:i for i,g in enumerate(G)}
def add(g,h): return ((g[0]+h[0])%NA, (g[1]+h[1])%NB)
def sub(g,h): return ((g[0]-h[0])%NA, (g[1]-h[1])%NB)

# Polynomials as sets (support), value 1 on support
Asup = {(3,0),(0,1),(0,2)}
Bsup = {(0,3),(1,0),(2,0)}
def poly(sup):
    v=[0]*NG
    for g in sup: v[idx[g]]=1
    return v
A=poly(Asup); B=poly(Bsup)

def conv(a,b):
    # (a*b)(g)=sum_h a(h)b(g-h)
    out=[0]*NG
    for gi,g in enumerate(G):
        s=0
        for hi,h in enumerate(G):
            if a[hi]:
                s^=b[idx[sub(g,h)]]
        out[gi]=s
    return out

# ---- matrices as lists of rows (each row a bit-list over the codomain) ----
# C0 = G (72), C1 = G x Fin2 (144), C2 = G (72)
# qubit index: (h,j) -> j*NG + h_index  (j in {0,1})
NC1 = 2*NG
def q(hi,j): return j*NG+hi

# partial2 : C2(72) -> C1(144).  Column f = delta_f.  partial2(delta_f) as a C1 vector.
# partial2(f)(h,0)=conv(A,f)(h); (h,1)=conv(B,f)(h)
def partial2(f):
    Af=conv(A,f); Bf=conv(B,f)
    out=[0]*NC1
    for hi in range(NG):
        out[q(hi,0)]=Af[hi]
        out[q(hi,1)]=Bf[hi]
    return out

# partial1 : C1(144) -> C0(72). partial1(c)(g)=conv(B,c_L)(g)+conv(A,c_R)(g)
def partial1(c):
    cL=[c[q(hi,0)] for hi in range(NG)]
    cR=[c[q(hi,1)] for hi in range(NG)]
    BcL=conv(B,cL); AcR=conv(A,cR)
    return [BcL[g]^AcR[g] for g in range(NG)]

# cutMap : C0(72) -> C1(144). cutMap(s)(h,0)=sum_v s(v) B(v-h); (h,1)=sum_v s(v) A(v-h)
def cutMap(s):
    out=[0]*NC1
    for hi,h in enumerate(G):
        s0=0; s1=0
        for vi,v in enumerate(G):
            if s[vi]:
                s0^=B[idx[sub(v,h)]]
                s1^=A[idx[sub(v,h)]]
        out[q(hi,0)]=s0
        out[q(hi,1)]=s1
    return out

# dualBoundary : C1(144)->C2(72). dualBoundary(c)(f)=sum_e c(e) partial2(delta_f)(e)
# Precompute partial2 columns
P2cols=[partial2(poly({G[fi]})) for fi in range(NG)]  # P2cols[f] is C1 vector
def dualBoundary(c):
    out=[0]*NG
    for fi in range(NG):
        col=P2cols[fi]
        s=0
        for e in range(NC1):
            if c[e]&col[e]: s^=1
        out[fi]=s
    return out

# ---- GF(2) linear algebra ----
def rref(rows, ncols):
    # returns (rref_rows, pivots) ; rows list of bit-lists
    M=[r[:] for r in rows]
    piv=[]
    r=0
    for col in range(ncols):
        sel=None
        for i in range(r,len(M)):
            if M[i][col]: sel=i;break
        if sel is None: continue
        M[r],M[sel]=M[sel],M[r]
        for i in range(len(M)):
            if i!=r and M[i][col]:
                M[i]=[a^b for a,b in zip(M[i],M[r])]
        piv.append(col); r+=1
        if r==len(M): break
    return M[:r], piv

def kernel_of_columns(colmat, ncols, dom):
    # colmat: function dom-index -> codomain vector (the image of basis vector e_i)
    # We want ker of the linear map T: F2^dom -> codomain, T(x)=sum x_i colmat[i].
    # Build matrix with rows = colmat[i] (dom rows, codomain cols), kernel of T = left null? 
    # Actually T(x)=sum_i x_i * col_i. ker T = {x : sum x_i col_i =0}.
    # Set up augmented: treat as solving M^T x =0 where columns are col_i.
    # Equivalent: rows of A are col_i (dom x codim). Solve A^T x = 0 -> nullspace of A^T.
    # Standard: nullspace of the matrix whose COLUMNS are col_i. That matrix is codim x dom.
    # Build Mat (codim rows, dom cols): Mat[r][i]=col_i[r]
    codim=len(colmat[0])
    Mat=[[colmat[i][r] for i in range(dom)] for r in range(codim)]
    R,piv=rref(Mat, dom)
    pivset=set(piv)
    free=[c for c in range(dom) if c not in pivset]
    basis=[]
    for f in free:
        x=[0]*dom
        x[f]=1
        # back-substitute: for each pivot row, pivot col value determined
        for ri,pc in enumerate(piv):
            # R[ri] has pivot at pc; value at free col f
            if R[ri][f]:
                x[pc]^=1
        basis.append(x)
    return basis, piv, free

# ker partial2 : columns are P2cols (image of delta_f), dom=72
kerP2, pivP2, freeP2 = kernel_of_columns(P2cols, NG, NG)
print("dim ker partial2 =", len(kerP2), " (expect 6)")

# ker cutMap : columns are cutMap(delta_v), dom=72
CMcols=[cutMap(poly({G[vi]})) for vi in range(NG)]
kerCM, pivCM, freeCM = kernel_of_columns(CMcols, NG, NG)
print("dim ker cutMap =", len(kerCM), " (expect 6)")

# rank checks
print("rank partial2 =", len(pivP2), " (expect 66)")
print("rank cutMap   =", len(pivCM), " (expect 66)")

# cycles = ker partial1 (dom C1=144). columns are partial1(delta_e)
P1cols=[partial1(poly2(e)) if False else None for e in range(NC1)]
def delta1(e):
    v=[0]*NC1; v[e]=1; return v
P1cols=[partial1(delta1(e)) for e in range(NC1)]
kerP1, pivP1, freeP1 = kernel_of_columns(P1cols, NC1, NG)  # codomain C0=72
print("dim cycles (ker partial1) =", len(kerP1), " (expect 78)")
# boundaries = im partial2, dim = rank partial2 = 66
# dualCycles = ker dualBoundary (dom C1=144 -> C2=72)
DBcols=[dualBoundary(delta1(e)) for e in range(NC1)]
kerDB, pivDB, freeDB = kernel_of_columns(DBcols, NC1, NG)
print("dim dualCycles (ker dualBoundary) =", len(kerDB), " (expect 78)")
print("H1 = cycles - boundaries =", len(kerP1), "-", len(pivP2), "=", len(kerP1)-len(pivP2), " (expect 12)")

print("---- DEBUG ----")
print("len piv partial1 =", len(pivP1), "len free =", len(freeP1), "dom=",NC1)
# verify kernel vectors actually in kernel
def applycols(cols, x):
    cod=len(cols[0]); out=[0]*cod
    for i,xi in enumerate(x):
        if xi:
            for r in range(cod): out[r]^=cols[i][r]
    return out
bad=sum(1 for x in kerP1 if any(applycols(P1cols,x)))
print("kerP1 vectors failing membership:", bad, "of", len(kerP1))
