# S3.9 packaging data for the [[72,4,8]] doubling cover (Z6xZ6, doc pair).
#
# Adapts phase5/compute2.py (gross [[144,12,12]] packaging) to the pair72
# instance of `QEC/Stabilizer/Codes/BivariateBicycle/Z3Z6/`:
#   cover group G72 = Z6 x Z6,  A = x^2 + y + y^3,  B = 1 + x + y^2
# (repo convention throughout: d2 f = (A*f | B*f), d1 c = B*c_L + A*c_R,
#  cutMap(delta_v) at (h,j) = (B(v-h) | A(v-h)) — same as compute2.py, no
#  lab-convention flip needed).
#
# Emits (after an ALL-PASS validation gate):
#   1. dropFaces / dropVtx — pivot coordinates trimming 36+36 natural
#      generators to 68 = n - k (expect 2 + 2);
#   2. redP2 / redCM — reduced kernel bases with red[j][drop[i]] = [i=j];
#   3. PhiX / PhiZ — decoder left-inverse certificates (independence);
#   4. logX / logZ — symplectic 4+4 logical basis, identity intersection.
#
# Output: data JSON (gitignored) + the Lean §1–§2 skeleton for
# `QEC/Stabilizer/Codes/BivariateBicycle/Z3Z6/StabilizerCode.lean`
# (written only with --emit-lean, and refuses to clobber an existing file
# unless --force).
#
# Run from experiments/bb_lab/:  uv run python scripts/gen_pair72_packaging_data.py [--emit-lean [--force]]

import json
import os
import sys

NA, NB = 6, 6
K_EXPECT = 4          # logical qubits
KERDIM_EXPECT = 2     # dim ker d2 = dim ker cutMap
D_CHAIN = 8           # proven chain distance (weight sanity floor for logicals)

G = [(a, b) for a in range(NA) for b in range(NB)]
NG = len(G)
idx = {g: i for i, g in enumerate(G)}


def sub(g, h):
    return ((g[0] - h[0]) % NA, (g[1] - h[1]) % NB)


# Repo polynomials (Z3Z6/Defs.lean a72/b72): A = x^2 + y + y^3, B = 1 + x + y^2.
Asup = {(2, 0), (0, 1), (0, 3)}
Bsup = {(0, 0), (1, 0), (0, 2)}


def poly(sup):
    v = [0] * NG
    for g in sup:
        v[idx[g]] = 1
    return v


A = poly(Asup)
B = poly(Bsup)


def conv(a, b):
    out = [0] * NG
    for gi, g in enumerate(G):
        s = 0
        for hi, h in enumerate(G):
            if a[hi] and b[idx[sub(g, h)]]:
                s ^= 1
        out[gi] = s
    return out


NC1 = 2 * NG


def q(hi, j):
    return j * NG + hi


def partial2(f):
    Af = conv(A, f)
    Bf = conv(B, f)
    out = [0] * NC1
    for hi in range(NG):
        out[q(hi, 0)] = Af[hi]
        out[q(hi, 1)] = Bf[hi]
    return out


def cutMap(s):
    out = [0] * NC1
    for hi, h in enumerate(G):
        s0 = 0
        s1 = 0
        for vi, v in enumerate(G):
            if s[vi]:
                if B[idx[sub(v, h)]]:
                    s0 ^= 1
                if A[idx[sub(v, h)]]:
                    s1 ^= 1
        out[q(hi, 0)] = s0
        out[q(hi, 1)] = s1
    return out


def partial1(c):
    cL = [c[q(hi, 0)] for hi in range(NG)]
    cR = [c[q(hi, 1)] for hi in range(NG)]
    BcL = conv(B, cL)
    AcR = conv(A, cR)
    return [BcL[g] ^ AcR[g] for g in range(NG)]


P2cols = [partial2(poly({G[f]})) for f in range(NG)]
CMcols = [cutMap(poly({G[v]})) for v in range(NG)]


def dualBoundary(c):
    out = [0] * NG
    for f in range(NG):
        col = P2cols[f]
        s = 0
        for e in range(NC1):
            if c[e] and col[e]:
                s ^= 1
        out[f] = s
    return out


def rref(rows, ncols):
    M = [r[:] for r in rows]
    piv = []
    r = 0
    for col in range(ncols):
        sel = None
        for i in range(r, len(M)):
            if M[i][col]:
                sel = i
                break
        if sel is None:
            continue
        M[r], M[sel] = M[sel], M[r]
        for i in range(len(M)):
            if i != r and M[i][col]:
                M[i] = [a ^ b for a, b in zip(M[i], M[r])]
        piv.append(col)
        r += 1
        if r == len(M):
            break
    return M[:r], piv


def nullspace(cols):
    dom = len(cols)
    cod = len(cols[0])
    Mat = [[cols[i][r] for i in range(dom)] for r in range(cod)]
    R, piv = rref(Mat, dom)
    pivset = set(piv)
    free = [c for c in range(dom) if c not in pivset]
    basis = []
    for fcol in free:
        x = [0] * dom
        x[fcol] = 1
        for ri, pc in enumerate(piv):
            if R[ri][fcol]:
                x[pc] ^= 1
        basis.append(x)
    return basis, piv, free


def reduce_kernel(basis):
    R, piv = rref([b[:] for b in basis], NG)
    return R, piv


checks = []


def check(name, ok):
    checks.append((name, ok))
    print(("PASS" if ok else "FAIL"), name)


kerP2, _, _ = nullspace(P2cols)
redP2, dropFaces = reduce_kernel(kerP2)
kerCM, _, _ = nullspace(CMcols)
redCM, dropVtx = reduce_kernel(kerCM)
print("dim ker d2 =", len(kerP2), "; dim ker cutMap =", len(kerCM))
print("dropFaces:", [G[i] for i in dropFaces])
print("dropVtx:  ", [G[i] for i in dropVtx])
check("kernel dims = expected", len(kerP2) == KERDIM_EXPECT and len(kerCM) == KERDIM_EXPECT)
check("dropFaces == dropVtx (single dropSet in Lean)", dropFaces == dropVtx)

ok_red = True
for j, b in enumerate(redP2):
    if any(v != 0 for v in partial2(b)):
        ok_red = False
    for i, d in enumerate(dropFaces):
        if b[d] != (1 if i == j else 0):
            ok_red = False
for j, b in enumerate(redCM):
    if any(v != 0 for v in cutMap(b)):
        ok_red = False
    for i, d in enumerate(dropVtx):
        if b[d] != (1 if i == j else 0):
            ok_red = False
check("reduced kernel bases (in ker, indicator-normalized)", ok_red)
print("redP2 supports:", [[G[i] for i in range(NG) if b[i]] for b in redP2])
print("redCM supports:", [[G[i] for i in range(NG) if b[i]] for b in redCM])


def solve(Mc_rows, rhs):
    ncol = len(Mc_rows[0])
    nrow = len(Mc_rows)
    aug = [Mc_rows[i][:] + [rhs[i]] for i in range(nrow)]
    piv = []
    r = 0
    for col in range(ncol):
        sel = None
        for i in range(r, nrow):
            if aug[i][col]:
                sel = i
                break
        if sel is None:
            continue
        aug[r], aug[sel] = aug[sel], aug[r]
        for i in range(nrow):
            if i != r and aug[i][col]:
                aug[i] = [a ^ b for a, b in zip(aug[i], aug[r])]
        piv.append(col)
        r += 1
        if r == nrow:
            break
    for i in range(r, nrow):
        if aug[i][ncol]:
            return None
    x = [0] * ncol
    for ri, pc in enumerate(piv):
        x[pc] = aug[ri][ncol]
    return x


def build_decoder(cols, redKer, dropSet):
    Mc = [[cols[p][e] for e in range(NC1)] for p in range(NG)]
    Phi = []
    for pprime in range(NG):
        rhs = [0] * NG
        for p in range(NG):
            t = 1 if p == pprime else 0
            for j, d in enumerate(dropSet):
                if p == d:
                    t ^= redKer[j][pprime]
            rhs[p] = t
        x = solve(Mc, rhs)
        assert x is not None, "decoder row inconsistent"
        Phi.append(x)
    return Phi


def applyPhi(Phi, c1vec):
    out = [0] * NG
    for pp in range(NG):
        s = 0
        for e in range(NC1):
            if c1vec[e] and Phi[pp][e]:
                s ^= 1
        out[pp] = s
    return out


def verify_decoder(Phi, cols, redKer, dropSet):
    for p in range(NG):
        lhs = applyPhi(Phi, cols[p])
        for j, d in enumerate(dropSet):
            if p == d:
                lhs = [lhs[i] ^ redKer[j][i] for i in range(NG)]
        if lhs != [1 if i == p else 0 for i in range(NG)]:
            return False
    return True


PhiX = build_decoder(P2cols, redP2, dropFaces)
PhiZ = build_decoder(CMcols, redCM, dropVtx)
check("PhiX decoder identity (all 36x36 basis pairs)", verify_decoder(PhiX, P2cols, redP2, dropFaces))
check("PhiZ decoder identity (all 36x36 basis pairs)", verify_decoder(PhiZ, CMcols, redCM, dropVtx))
print("PhiX density:", sum(sum(r) for r in PhiX), "of", NG * NC1)
print("PhiZ density:", sum(sum(r) for r in PhiZ), "of", NG * NC1)


# ---- symplectic logical basis ----
def image_basis(cols):
    R, piv = rref([c[:] for c in cols], len(cols[0]))
    return R


def kernel(cols):
    b, _, _ = nullspace(cols)
    return b


P1cols = [partial1([1 if e == i else 0 for e in range(NC1)]) for i in range(NC1)]
DBcols = [dualBoundary([1 if e == i else 0 for e in range(NC1)]) for i in range(NC1)]
Z = kernel(P1cols)
Bd = image_basis(P2cols)
Zd = kernel(DBcols)
Bdd = image_basis(CMcols)
print("dims: cycles", len(Z), "boundaries", len(Bd), "dual-cycles", len(Zd), "dual-boundaries", len(Bdd))
check("homology dims give k = 4", len(Z) - len(Bd) == K_EXPECT and len(Zd) - len(Bdd) == K_EXPECT)


def extend_to(subspace, full, count):
    reps = []
    basisrows, _ = rref([v[:] for v in subspace], NC1)

    def in_span(v, rows):
        R, _ = rref([r[:] for r in rows] + [v[:]], NC1)
        return len(R) == len(rows)

    for v in full:
        if not in_span(v, basisrows):
            reps.append(v[:])
            basisrows, _ = rref(basisrows + [v[:]], NC1)
        if len(reps) == count:
            break
    return reps


H1 = extend_to(Bd, Z, K_EXPECT)
H1d = extend_to(Bdd, Zd, K_EXPECT)
check("found 4 H1 reps and 4 H1-dual reps", len(H1) == K_EXPECT and len(H1d) == K_EXPECT)


def ip(a, b):
    s = 0
    for e in range(NC1):
        if a[e] and b[e]:
            s ^= 1
    return s


def invF2(Min):
    n = len(Min)
    aug = [Min[i][:] + [1 if j == i else 0 for j in range(n)] for i in range(n)]
    for col in range(n):
        sel = next((i for i in range(col, n) if aug[i][col]), None)
        assert sel is not None, "intersection matrix singular"
        aug[col], aug[sel] = aug[sel], aug[col]
        for i in range(n):
            if i != col and aug[i][col]:
                aug[i] = [a ^ b for a, b in zip(aug[i], aug[col])]
    return [row[n:] for row in aug]


M = [[ip(H1[i], H1d[j]) for j in range(K_EXPECT)] for i in range(K_EXPECT)]
Minv = invF2(M)
H1d2 = []
for j in range(K_EXPECT):
    v = [0] * NC1
    for k in range(K_EXPECT):
        if Minv[k][j]:
            for e in range(NC1):
                v[e] ^= H1d[k][e]
    H1d2.append(v)
M2 = [[ip(H1[i], H1d2[j]) for j in range(K_EXPECT)] for i in range(K_EXPECT)]
check("intersection matrix = identity 4x4",
      M2 == [[1 if i == j else 0 for j in range(K_EXPECT)] for i in range(K_EXPECT)])
check("logX all cycles (d1 = 0)", all(all(x == 0 for x in partial1(c)) for c in H1))
check("logZ all dual-cycles (dualBoundary = 0)", all(all(x == 0 for x in dualBoundary(c)) for c in H1d2))
# Nontriviality is by construction (reps extend the boundary basis); the proven
# chain distance d = 8 then forces weight >= 8 — a free cross-check.
check("logical rep weights >= chain distance 8",
      all(sum(c) >= D_CHAIN for c in H1) and all(sum(c) >= D_CHAIN for c in H1d2))
print("logX weights:", [sum(c) for c in H1])
print("logZ weights:", [sum(c) for c in H1d2])


def vec_to_coords(v):
    out = []
    for e in range(NC1):
        if v[e]:
            j = e // NG
            hi = e % NG
            a, b = G[hi]
            out.append([a, b, j])
    return out


def c2_to_coords(v):
    return [[G[i][0], G[i][1]] for i in range(NG) if v[i]]


def phi_to_coords(Phi):
    out = []
    for pp in range(NG):
        for e in range(NC1):
            if Phi[pp][e]:
                j = e // NG
                hi = e % NG
                out.append([[G[pp][0], G[pp][1]], [G[hi][0], G[hi][1], j]])
    return out


# ---- closure-relation data (gross §4b/§4c analogues) ----
# keptCoords = row-major complement of the drop-set (34 coords);
# keptPart{X,Z}[j] = supp(red[j]) \ {drop[j]} — the kept-generator product
# reproducing the dropped generator's boundary column (kernel relation).
dropset_g = [G[i] for i in dropFaces]
keptCoords = [g for g in G if g not in dropset_g]
keptPartX = [[G[i] for i in range(NG) if b[i] and G[i] != dropset_g[j]]
             for j, b in enumerate(redP2)]
keptPartZ = [[G[i] for i in range(NG) if b[i] and G[i] != dropset_g[j]]
             for j, b in enumerate(redCM)]
check("keptCoords size = 34 (= n - k - 34 kept twice)", len(keptCoords) == NG - len(dropFaces))
check("keptPartX/Z subsets of keptCoords",
      all(g in keptCoords for part in keptPartX + keptPartZ for g in part))


def d2term_py(f, h, j):
    return (A if j == 0 else B)[idx[sub(h, f)]]


def cmterm_py(v, h, j):
    return (B if j == 0 else A)[idx[sub(v, h)]]


check("keptPartX drop relations (d2term column identities)",
      all(d2term_py(dropset_g[j], h, jj)
          == sum(d2term_py(f, h, jj) for f in keptPartX[j]) % 2
          for j in range(len(dropFaces)) for h in G for jj in range(2)))
check("keptPartZ drop relations (cmTerm column identities)",
      all(cmterm_py(dropset_g[j], h, jj)
          == sum(cmterm_py(v, h, jj) for v in keptPartZ[j]) % 2
          for j in range(len(dropVtx)) for h in G for jj in range(2)))

failed = [name for name, ok in checks if not ok]
if failed:
    print("\nVALIDATION FAILED:", failed)
    sys.exit(1)
print("\nALL CHECKS PASS (", len(checks), ")")

data = {
    "dropFaces": [list(G[i]) for i in dropFaces],
    "dropVtx": [list(G[i]) for i in dropVtx],
    "redP2": [c2_to_coords(b) for b in redP2],
    "redCM": [c2_to_coords(b) for b in redCM],
    "PhiX": phi_to_coords(PhiX),
    "PhiZ": phi_to_coords(PhiZ),
    "logX": [vec_to_coords(c) for c in H1],
    "logZ": [vec_to_coords(c) for c in H1d2],
    "keptCoords": [list(g) for g in keptCoords],
    "keptPartX": [[list(g) for g in part] for part in keptPartX],
    "keptPartZ": [[list(g) for g in part] for part in keptPartZ],
}
os.makedirs("data/a9", exist_ok=True)
out_json = "data/a9/pair72_packaging_data.json"
json.dump(data, open(out_json, "w"))
print("WROTE", out_json)


# ---- Lean §1–§2 skeleton emission ----
def Glean(ab):
    return f"(({ab[0]} : ZMod 6), ({ab[1]} : ZMod 6))"


def Elean(e):
    return f"((({e[0]} : ZMod 6), ({e[1]} : ZMod 6)), ({e[2]} : Fin 2))"


def Glist(lst):
    return "[" + ", ".join(Glean(x) for x in lst) + "]"


def Elist(lst):
    return "[" + ", ".join(Elean(x) for x in lst) + "]"


HEADER = '''/-
# The `[[72,4,8]]` doubling cover as a `StabilizerCode`, with distance 8

S3.9 packaging: bundle `pair72Complex` (the `bbChainComplex a72 b72` of
`Defs.lean`) as a genuine `StabilizerCode 72 4`, transport the Pauli-level
distance theorem `pair72_pauli_distance_eq_8` onto `HasCodeDistance`, and
expose `pair72StabilizerCodeWithDistance : StabilizerCodeWithDistance 72 4 8`.
Mirrors the gross Phase-5 packaging
(`QEC/Stabilizer/Codes/BivariateBicycle/StabilizerCode.lean`) at pair72 scale.

This file embeds offline-validated `𝔽₂` linear-algebra data
(`experiments/bb_lab/scripts/gen_pair72_packaging_data.py`, ALL-PASS gate):
* `dropSet` — 2 faces / 2 vertices dropped to trim 72 generators to 68;
* `redP2` / `redCM` — reduced bases of `ker ∂₂` / `ker cutMap` (2 each),
  satisfying `redP2 j (dropSet i) = [i=j]`, giving both the closure relations
  and the independence kernel-collapse;
* `phiX` / `phiZ` — left-inverse "syndrome decoder" certificates proving the
  trimmed rows are independent (no rank theorem; see `decoder_identity_*`);
* `logX` / `logZ` — a symplectic basis of 4 X-cycles + 4 Z-dual-cycles
  with identity `4×4` intersection matrix (the 4 logical qubits).

Status: WIP skeleton — §1 data + §2 decoder identities (the independence
hard-core); the framework wiring (§3–§6) follows.
-/

import QEC.Stabilizer.Codes.BivariateBicycle.Z3Z6.Distance
import QEC.Stabilizer.Framework.Homological.LogicalCorrespondence
import QEC.Stabilizer.Framework.Core.Logical.CodeDistance
import Mathlib.Data.List.GetD

namespace Quantum.Stabilizer.Homological.BB.Z3Z6

open scoped BigOperators
open Quantum.Stabilizer.Homological

/-! ## §1  Offline-validated data (`gen_pair72_packaging_data.py`) -/

/-- The 2 faces / 2 vertices dropped to trim 72 generators down to 68.
(The face and vertex drop-sets coincide, as they did for gross.) -/
def dropSet : List G72 :=
  %DROPSET%

/-- Reduced `ker ∂₂` basis (2 face-supports). `∂₂(redP2 j) = 0` and
`(redP2 j)(dropSet i) = [i=j]`. -/
def redP2 : List (List G72) :=
  %REDP2%

/-- Reduced `ker cutMap` basis (2 vertex-supports). -/
def redCM : List (List G72) :=
  %REDCM%

/-- Face-independence syndrome decoder: support list of (output-coord, qubit). -/
def phiX : List (G72 × (G72 × Fin 2)) :=
  %PHIX%

/-- Vertex-independence syndrome decoder. -/
def phiZ : List (G72 × (G72 × Fin 2)) :=
  %PHIZ%

/-- 4 X-logical cycle representatives (qubit supports). -/
def logX : List (List (G72 × Fin 2)) :=
  %LOGX%

/-- 4 Z-logical dual-cycle representatives (qubit supports). -/
def logZ : List (List (G72 × Fin 2)) :=
  %LOGZ%

/-- The 34 kept coordinates (row-major complement of `dropSet`). -/
def keptCoords : List G72 :=
  %KEPTCOORDS%

/-- Per-dropped-face closure relation: `keptPartX j = supp (redP2 j) \\ {dropSet j}`,
the kept faces whose boundary columns sum to the dropped face's column. -/
def keptPartX : List (List G72) :=
  %KEPTPARTX%

/-- Per-dropped-vertex closure relation (mirror, from `redCM`). -/
def keptPartZ : List (List G72) :=
  %KEPTPARTZ%

/-! ## §2  Sparse boundary terms and the decoder identities

`∂₂(δ_f)` and `cutMap(δ_v)` are sparse point-mass images; evaluating them
through these few-term forms (rather than `conv`) keeps the kernel sweeps
cheap. -/

/-- `∂₂(δ_f)` evaluated at qubit `(h, j)`:  `A(h-f)` on the left block,
`B(h-f)` on the right. -/
def d2term (f h : G72) (j : Fin 2) : ZMod 2 :=
  if j = 0 then a72 (h - f) else b72 (h - f)

/-- `cutMap(δ_v)` evaluated at qubit `(h, j)`:  `B(v-h)` on the left block,
`A(v-h)` on the right. -/
def cmTerm (v h : G72) (j : Fin 2) : ZMod 2 :=
  if j = 0 then b72 (v - h) else a72 (v - h)

/-- Apply the `phiX` decoder to `∂₂(δ_p)`, read at output face `p'`. -/
def decodeXAt (p p' : G72) : ZMod 2 :=
  (phiX.filter (fun pr => pr.1 = p')).foldl
    (fun acc pr => acc + d2term p pr.2.1 pr.2.2) 0

/-- Apply the `phiZ` decoder to `cutMap(δ_p)`, read at output vertex `p'`. -/
def decodeZAt (p p' : G72) : ZMod 2 :=
  (phiZ.filter (fun pr => pr.1 = p')).foldl
    (fun acc pr => acc + cmTerm p pr.2.1 pr.2.2) 0

/-- Kernel-basis correction term `Σ_j [p = dropSet j] · (red j)(p')`. -/
def kerCorrection (red : List (List G72)) (p p' : G72) : ZMod 2 :=
  ((List.range 2).filter (fun j => dropSet.getD j 0 = p)).foldl
    (fun acc j => acc + (if (red.getD j []).contains p' then 1 else 0)) 0

/-- **Face decoder identity**: the `phiX` decoder inverts `∂₂` on the trimmed
face subspace, modulo the `redP2` kernel basis, over all `36×36` basis pairs.
This is the independence hard-core for the X block — it yields
`∂₂ f = 0 ∧ f|_dropSet = 0 → f = 0` by linearity. -/
theorem decoder_identity_X :
    ∀ p p' : G72,
      decodeXAt p p' + kerCorrection redP2 p p' = (if p' = p then 1 else 0) := by
  native_decide

/-- **Vertex decoder identity**: mirror of `decoder_identity_X` for the Z
block (`cutMap`, `phiZ`, `redCM`). -/
theorem decoder_identity_Z :
    ∀ p p' : G72,
      decodeZAt p p' + kerCorrection redCM p p' = (if p' = p then 1 else 0) := by
  native_decide

end Quantum.Stabilizer.Homological.BB.Z3Z6
'''

def wrap_literal(s, width=95, indent="  "):
    # Wrap a one-line Lean literal at ", " boundaries (mathlib longLine linter).
    parts = s.split(", ")
    lines = []
    cur = parts[0]
    for p in parts[1:]:
        if len(cur) + 2 + len(p) <= width:
            cur += ", " + p
        else:
            lines.append(cur + ",")
            cur = indent + p
    lines.append(cur)
    return "\n".join(lines)


if "--emit-lean" in sys.argv:
    if dropFaces != dropVtx:
        print("dropFaces != dropVtx — the skeleton's single `dropSet` is wrong; adapt the template first.")
        sys.exit(1)
    target = "../../QEC/Stabilizer/Codes/BivariateBicycle/Z3Z6/StabilizerCode.lean"
    if os.path.exists(target) and "--force" not in sys.argv:
        print("refusing to clobber existing", target, "(use --force)")
        sys.exit(1)
    body = HEADER
    for k, v in [("%DROPSET%", Glist(data["dropFaces"])),
                 ("%REDP2%", "[" + ", ".join(Glist(b) for b in data["redP2"]) + "]"),
                 ("%REDCM%", "[" + ", ".join(Glist(b) for b in data["redCM"]) + "]"),
                 ("%PHIX%", "[" + ", ".join(f"({Glean(pp)}, {Elean(e)})" for pp, e in data["PhiX"]) + "]"),
                 ("%PHIZ%", "[" + ", ".join(f"({Glean(pp)}, {Elean(e)})" for pp, e in data["PhiZ"]) + "]"),
                 ("%KEPTCOORDS%", Glist(data["keptCoords"])),
                 ("%KEPTPARTX%", "[" + ", ".join(Glist(p) for p in data["keptPartX"]) + "]"),
                 ("%KEPTPARTZ%", "[" + ", ".join(Glist(p) for p in data["keptPartZ"]) + "]"),
                 ("%LOGX%", "[" + ", ".join(Elist(c) for c in data["logX"]) + "]"),
                 ("%LOGZ%", "[" + ", ".join(Elist(c) for c in data["logZ"]) + "]")]:
        body = body.replace(k, wrap_literal(v))
    open(target, "w").write(body)
    print("WROTE", target, len(body), "chars")
