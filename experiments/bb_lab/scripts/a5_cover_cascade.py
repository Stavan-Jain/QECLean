"""A5 (goal 2) — the cover-cascade screen.

"Which BB codes admit a gross-like distance proof?"  This script wraps the
per-instance Theorem-A checker (`a5_instance_hypotheses.py`) with the two
gates it was missing — G1 (cover-search) and the tier classifier — and runs
the full cascade over the BB corpus (`data/bb_instances.duckdb`).

The methodology (see the cover-cascade write-up):

  G0  BB shape + parity     |A|=|B|=3, k>0, weights odd          [corpus cols]
  G1  Cover-search          even-axis ℤ₂ quotients → base        [THIS MODULE]
  G2  Base anchoring        frame floor-bearing ∧ (ii) ∧ (iii)   [reuses checker]
       (+ (i) engine components on a Z₂×Z₂ frame)
  G3  Dangerous sector      light-stabilizer classification      [hand-proof]
  G4  Confined floor        (R)-homotopy + ρ-link confinement     [research]

Output tiers for a code C = (Z_ℓ × Z_m, A, B):

  DIRECT            C's own frame is floor-bearing AND anchorable  → d(C) ≥ 6
  COVER             C is an (iterated) free-ℤ₂ cover of an
                    anchorable base                                → d(C) ≥ 6
  DOUBLE_CANDIDATE  C is a *single* ℤ₂ cover of a Z₂×Z₂-frame
                    anchorable (gross-like) base                   → d(C) = 12  (G3+G4 hand-proof)
  none              no anchorable base reachable

The certified analytic floor is c = 6 (the developed Theorem-A small-cycle
bound: no nonzero 1-cycle of weight ≤ 5).  The DOUBLE_CANDIDATE value 2c = 12
is a *research target* — it still needs the per-instance light-stabilizer
classification (G3) and the confined-floor / (R)-homotopy analysis (G4).

Everything here is discovery/validation (A_HANDOFF §1): the tiers say which
instances are *candidates* for a hand run, nothing is load-bearing.

Usage:
    uv run python scripts/a5_cover_cascade.py                 # full corpus sweep
    uv run python scripts/a5_cover_cascade.py --limit 2000
    uv run python scripts/a5_cover_cascade.py --self-test     # known-code validation
    uv run python scripts/a5_cover_cascade.py --jsonl out.jsonl
"""

from __future__ import annotations

import argparse
import collections
import json
import sys
from dataclasses import dataclass
from functools import lru_cache
from math import gcd
from pathlib import Path

LAB_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(LAB_ROOT / "src"))
sys.path.insert(0, str(LAB_ROOT / "scripts"))

from bb_lab.checks import bb_check_matrices
from bb_lab.codeparams import code_params
from bb_lab.group import AbelianGroup
from bb_lab.poly import Poly

from a5_instance_hypotheses import (
    ENGINE_RADICAL,
    UNIT,
    InstanceReport,
    component_table,
    crt_frame,
    diff_set_report,
    kill_vectors,
    orbit_fields,
    projection_report,
)

CERTIFIED_FLOOR = 6  # the developed Theorem-A small-cycle bound (no cycle wt ≤ 5)


# ---------------------------------------------------------------------------
# Evaluate a (G, A, B) instance into an InstanceReport (mirrors check_instance,
# but takes Poly objects so derived bases can be evaluated without re-parsing).
# ---------------------------------------------------------------------------


@lru_cache(maxsize=None)
def _fields(odd_orders: tuple[int, ...]):
    return orbit_fields(odd_orders)


def evaluate(label: str, G: AbelianGroup, A: Poly, B: Poly) -> InstanceReport:
    frame = crt_frame(G)
    fields = _fields(frame.odd_orders)
    comps_A = component_table(A, frame, fields)
    comps_B = component_table(B, frame, fields)
    rep = InstanceReport(
        label=label,
        G=G,
        A=A,
        B=B,
        frame=frame,
        comps_A=comps_A,
        comps_B=comps_B,
        diff=diff_set_report(A, B, G),
        proj=projection_report(A, B, G),
    )
    rep.kvs = kill_vectors("A", comps_A, frame) + kill_vectors("B", comps_B, frame)
    return rep


def is_anchorable(rep: InstanceReport) -> bool:
    """G2: a base is anchorable iff its frame is floor-bearing, the
    difference sets pass (ii), and the projections are mirrored (iii).
    On a Z₂×Z₂ frame we additionally require the engine-grade components (i).
    Weight-3 both blocks is required (the developed Theorem-A grid)."""
    if len(rep.A.support) != 3 or len(rep.B.support) != 3:
        return False
    if rep.frame.shape == "deeper":
        return False
    if not (rep.verdict_ii and rep.verdict_iii):
        return False
    if rep.frame.shape == "Z2xZ2" and not rep.verdict_i:
        return False
    return True


# ---------------------------------------------------------------------------
# G1 — cover-search.  A BB code over Z_ℓ × Z_m with one even axis is the
# free-ℤ₂ cover of the BB code over the halved-axis group with the reduced
# polynomials (deck = translation by half the axis).  The reduction is the
# ring hom F₂[G] → F₂[G/⟨half⟩]; coefficients XOR-cancel (char 2).
# ---------------------------------------------------------------------------


def _reduce_poly(A: Poly, base_G: AbelianGroup, axis: int, half: int) -> Poly:
    counts: dict[tuple[int, ...], int] = {}
    for g in A.support:
        h = list(g)
        h[axis] %= half
        key = tuple(h)
        counts[key] = counts.get(key, 0) ^ 1  # XOR: char-2 cancellation
    supp = frozenset(g for g, c in counts.items() if c)
    return Poly(support=supp, group=base_G)


def _halvings(ell: int, m: int, A: Poly, B: Poly):
    """One-step even-axis ℤ₂ quotients: (axis, base_ell, base_m, A_b, B_b)."""
    out = []
    if ell % 2 == 0:
        bG = AbelianGroup((ell // 2, m))
        out.append(("x", ell // 2, m, _reduce_poly(A, bG, 0, ell // 2),
                    _reduce_poly(B, bG, 0, ell // 2), bG))
    if m % 2 == 0:
        bG = AbelianGroup((ell, m // 2))
        out.append(("y", ell, m // 2, _reduce_poly(A, bG, 1, m // 2),
                    _reduce_poly(B, bG, 1, m // 2), bG))
    return out


@dataclass
class CoverResult:
    tier: str  # DIRECT | COVER | DOUBLE_CANDIDATE | none
    floor: int  # certified analytic lower bound (6) or 0
    double_target: int  # 12 for DOUBLE_CANDIDATE else 0
    base_group: str  # "ZaxZb" of the anchoring base, or "self"
    base_frame: str  # frame shape of the anchoring base
    cover_degree: int  # 1 = direct, 2 = single ℤ₂ cover, 4 = two halvings, ...


def classify(ell: int, m: int, A_str: str, B_str: str, max_depth: int = 3) -> CoverResult:
    G = AbelianGroup((ell, m))
    A = Poly.from_string(A_str, G)
    B = Poly.from_string(B_str, G)
    rep = evaluate(f"Z{ell}xZ{m}", G, A, B)

    # Direct: the code is its own anchorable base.
    if is_anchorable(rep):
        gl = rep.frame.shape == "Z2xZ2"
        return CoverResult(
            tier="DIRECT", floor=CERTIFIED_FLOOR, double_target=0,
            base_group="self", base_frame=rep.frame.shape, cover_degree=1,
        )

    # Cover-search: BFS over iterated even-axis halvings for an anchorable base.
    # degree = product of halving factors (each ℤ₂ → ×2).
    best: CoverResult | None = None
    # frontier items: (ell, m, A, B, degree)
    seen: set[tuple[int, int]] = {(ell, m)}
    frontier = [(ell, m, A, B, 1)]
    depth = 0
    while frontier and depth < max_depth:
        depth += 1
        nxt = []
        for (e, mm, a, b, deg) in frontier:
            for (axis, be, bm, ab, bb, bG) in _halvings(e, mm, a, b):
                if (be, bm) in seen:
                    continue
                seen.add((be, bm))
                brep = evaluate(f"Z{be}xZ{bm}", bG, ab, bb)
                bdeg = deg * 2
                if is_anchorable(brep):
                    gl = brep.frame.shape == "Z2xZ2"
                    # DOUBLE_CANDIDATE only for a *single* ℤ₂ cover (deg 2) of a
                    # gross-like (Z₂×Z₂) base — the developed confined-floor regime.
                    if bdeg == 2 and gl:
                        cand = CoverResult(
                            tier="DOUBLE_CANDIDATE", floor=CERTIFIED_FLOOR,
                            double_target=2 * CERTIFIED_FLOOR, base_group=f"Z{be}xZ{bm}",
                            base_frame=brep.frame.shape, cover_degree=bdeg,
                        )
                    else:
                        cand = CoverResult(
                            tier="COVER", floor=CERTIFIED_FLOOR, double_target=0,
                            base_group=f"Z{be}xZ{bm}", base_frame=brep.frame.shape,
                            cover_degree=bdeg,
                        )
                    # prefer DOUBLE_CANDIDATE, then smallest degree
                    if best is None or _better(cand, best):
                        best = cand
                else:
                    nxt.append((be, bm, ab, bb, bdeg))
        frontier = nxt

    if best is not None:
        return best
    return CoverResult(tier="none", floor=0, double_target=0,
                       base_group="", base_frame="", cover_degree=0)


def _rank(t: str) -> int:
    return {"DOUBLE_CANDIDATE": 3, "DIRECT": 2, "COVER": 1, "none": 0}[t]


def _better(a: CoverResult, b: CoverResult) -> bool:
    if _rank(a.tier) != _rank(b.tier):
        return _rank(a.tier) > _rank(b.tier)
    return a.cover_degree < b.cover_degree


# ---------------------------------------------------------------------------
# G2 up to presentation — Aut(Z_ℓ × Z_m) × (A↔B swap) orbit search.
#
# The corpus stores one Aut-canonical representative per orbit, but the
# mirrored-projection gate (iii) and coordinate-disjointness are NOT
# Aut-invariant — so a base that anchors in *some* presentation can be
# stored in coordinates where the stored-presentation cascade misses it.
# This searches the orbit for an anchorable representative.  (i) and the
# translation-invariant parts of (ii) — frame, mult-free, dA∩dB=∅ — are
# Aut-invariant, so they pre-filter the search hard.
# ---------------------------------------------------------------------------


def _elt_order(g: tuple[int, ...], orders: tuple[int, ...]) -> int:
    """Order of g in Z_{orders[0]} × … : lcm_i(n_i / gcd(g_i, n_i))."""
    o = 1
    for gi, n in zip(g, orders):
        k = n // gcd(gi % n, n) if gi % n else 1
        o = o * k // gcd(o, k)
    return o


def _subgroup_order(gens, G: AbelianGroup) -> int:
    zero = tuple([0] * G.rank)
    seen = {zero}
    frontier = [zero]
    while frontier:
        x = frontier.pop()
        for g in gens:
            y = G.add(x, g)
            if y not in seen:
                seen.add(y)
                frontier.append(y)
    return len(seen)


@lru_cache(maxsize=None)
def automorphisms(ell: int, m: int) -> tuple:
    """Aut(Z_ℓ × Z_m): all (φ(e₁), φ(e₂)) with φ(e₁) order ℓ, φ(e₂) order m,
    and ⟨φ(e₁), φ(e₂)⟩ = G (bijective)."""
    G = AbelianGroup((ell, m))
    N = ell * m
    ord1 = [(a, c) for a in range(ell) for c in range(m)
            if _elt_order((a, c), (ell, m)) == ell]
    ord2 = [(b, d) for b in range(ell) for d in range(m)
            if _elt_order((b, d), (ell, m)) == m]
    autos = []
    for e1 in ord1:
        for e2 in ord2:
            if _subgroup_order([e1, e2], G) == N:
                autos.append((e1, e2))
    return tuple(autos)


def _scal(k: int, g: tuple[int, ...], orders: tuple[int, ...]) -> tuple[int, ...]:
    return tuple((k * gi) % n for gi, n in zip(g, orders))


def apply_auto(A: Poly, auto, G: AbelianGroup) -> Poly:
    e1, e2 = auto
    orders = G.orders
    counts: dict[tuple[int, ...], int] = {}
    for (gx, gy) in A.support:
        img = G.add(_scal(gx, e1, orders), _scal(gy, e2, orders))
        counts[img] = counts.get(img, 0) ^ 1
    return Poly(support=frozenset(g for g, c in counts.items() if c), group=G)


def presentation_anchorable(ell: int, m: int, A: Poly, B: Poly):
    """Search Aut(G) × swap for an anchorable representative.  Returns
    (True, witness_report) on the first hit, else (False, None)."""
    G = AbelianGroup((ell, m))
    autos = automorphisms(ell, m)
    for (AA, BB) in ((A, B), (B, A)):
        for auto in autos:
            pa = apply_auto(AA, auto, G)
            pb = apply_auto(BB, auto, G)
            rep = evaluate(f"Z{ell}xZ{m}*", G, pa, pb)
            if is_anchorable(rep):
                return True, rep
    return False, None


# ---------------------------------------------------------------------------
# Hunt for genuinely-new doubling targets:  Z₂×Z₂-frame codes that anchor
# in *some* presentation, classified gross-equivalent vs new.  Their single-
# ℤ₂ covers are the DOUBLE_CANDIDATEs (predicted d=12).
# ---------------------------------------------------------------------------


def hunt_doubling(db_path: Path, jsonl: Path | None) -> None:
    import duckdb

    con = duckdb.connect(str(db_path), read_only=True)
    rows = con.execute(
        "select ell, m, n, k, A_poly, B_poly, d_exact, d_lb, d_ub "
        "from bb_instances where A_weight=3 and B_weight=3 and k>0"
    ).fetchall()

    # Aut-INVARIANT pre-filter: Z₂×Z₂ frame, (i) engine components,
    # mult-free, dA∩dB=∅.  Only these can anchor in any presentation.
    prospects = []
    for (ell, m, n, k, A_str, B_str, dx, dlb, dub) in rows:
        try:
            G = AbelianGroup((ell, m))
            A = Poly.from_string(A_str, G)
            B = Poly.from_string(B_str, G)
            rep = evaluate(f"Z{ell}xZ{m}", G, A, B)
        except Exception:
            continue
        if rep.frame.shape != "Z2xZ2":
            continue
        if not (rep.verdict_i and rep.diff.dA_mult_free
                and rep.diff.dB_mult_free and rep.diff.disjoint):
            continue
        prospects.append((ell, m, n, k, A, B, A_str, B_str, dx, dlb, dub))

    print(f"Z₂×Z₂-frame Aut-invariant prospects (frame+i+mult-free+disjoint): "
          f"{len(prospects)}")

    anchorable = []  # bases that anchor in SOME presentation
    stored_only = 0  # anchor already in stored coords
    for (ell, m, n, k, A, B, A_str, B_str, dx, dlb, dub) in prospects:
        rep0 = evaluate(f"Z{ell}xZ{m}", AbelianGroup((ell, m)), A, B)
        stored = is_anchorable(rep0)
        if stored:
            ok, wit = True, rep0
        else:
            ok, wit = presentation_anchorable(ell, m, A, B)
        if ok:
            anchorable.append({
                "group": f"Z{ell}xZ{m}", "ell": ell, "m": m, "n": n, "k": k,
                "A": A_str, "B": B_str, "d_exact": dx, "d_lb": dlb, "d_ub": dub,
                "stored_presentation": stored,
                "witness_A": wit.A.canonical_string(),
                "witness_B": wit.B.canonical_string(),
            })
            if stored:
                stored_only += 1

    print(f"\n=== ANCHORABLE Z₂×Z₂ BASES (up to presentation): {len(anchorable)} "
          f"({stored_only} already mirrored in stored coords, "
          f"{len(anchorable)-stored_only} ONLY found by the orbit search) ===")

    # Classify gross-family vs genuinely new.  The gross base is [[72,12,6]]
    # over Z₆×Z₆; covers are [[144,12,12]].  A base outside that param/group
    # class is a genuinely-new doubling target.
    def is_gross_family(b) -> bool:
        return b["n"] == 72 and b["k"] == 12 and (b["d_exact"] in (6, None)) \
            and sorted((b["ell"], b["m"])) == [6, 6]

    gross = [b for b in anchorable if is_gross_family(b)]
    new = [b for b in anchorable if not is_gross_family(b)]
    print(f"  gross-family bases ([[72,12,6]] / Z₆×Z₆): {len(gross)}")
    print(f"  GENUINELY-NEW anchorable bases: {len(new)}")
    by_pk = collections.Counter((b["group"], b["n"], b["k"], b["d_exact"]) for b in new)
    for (grp, n, k, d), cnt in sorted(by_pk.items()):
        print(f"     {grp:10s} [[{n},{k},{d}]]  ×{cnt}  → cover targets [[{2*n},{k},?]]")
    print("\n  sample new bases (with the anchoring presentation found):")
    for b in new[:20]:
        print(f"     {b['group']:10s} [[{b['n']},{b['k']},{b['d_exact']}]] "
              f"stored={b['A']} | {b['B']}   ⇒ mirrored={b['witness_A']} | {b['witness_B']}")

    if jsonl:
        with open(jsonl, "w") as fh:
            for b in anchorable:
                b2 = dict(b)
                b2["gross_family"] = is_gross_family(b)
                fh.write(json.dumps(b2) + "\n")
        print(f"\nwrote {len(anchorable)} anchorable bases → {jsonl}")


# ---------------------------------------------------------------------------
# Direct (corpus-independent) hunt: enumerate anchorable Z₂×Z₂-frame bases
# over EVERY Z₂×Z₂ group up to a cardinality cap — not just the ones the
# corpus happens to contain (which is only Z₆×Z₆).  WLOG both A and B contain
# the origin (independent translation of the two qubit blocks), and (iii)
# forces one block monomial-in-x and the other monomial-in-y, so we pre-split
# by projection shape and only pair across orientations.
# ---------------------------------------------------------------------------


def _two_part(n: int) -> int:
    p = 1
    while n % 2 == 0:
        n //= 2
        p *= 2
    return p


def zz_groups(max_card: int):
    """Z_ℓ × Z_m with 2-part exactly Z₂ on each axis (ℓ, m = 2·odd, odd ≥ 3),
    ℓ ≤ m, |G| ≤ max_card."""
    vals = [v for v in range(6, max_card + 1) if _two_part(v) == 2 and v // 2 >= 3]
    out = []
    for i, e in enumerate(vals):
        for m in vals[i:]:
            if e * m <= max_card:
                out.append((e, m))
    return out


def _weight3_origin(G: AbelianGroup):
    """All weight-3 polys {0, p, q} containing the origin, split by (iii)
    projection shape: monoX (π_x singleton) and monoY (π_y singleton)."""
    elems = [g for g in G if g != (0, 0)]
    zero = (0, 0)
    monoX, monoY = [], []
    for i in range(len(elems)):
        for j in range(i + 1, len(elems)):
            supp = frozenset((zero, elems[i], elems[j]))
            A = Poly(support=supp, group=G)
            px = collections.Counter()
            py = collections.Counter()
            for (gx, gy) in supp:
                px[gx] ^= 1
                py[gy] ^= 1
            sx = sum(px.values())
            sy = sum(py.values())
            if sx == 1:
                monoX.append(A)
            if sy == 1:
                monoY.append(A)
    return monoX, monoY


def code_k(A: Poly, B: Poly) -> int:
    """k of the BB code (A, B).  k = 0 ⟹ NOT a code (no logical qubits) — the
    structural gates (i)/(ii)/(iii) do NOT enforce this, so an explicit check
    is required before calling any structural hit a 'base'."""
    try:
        return code_params(bb_check_matrices(A, B)).k
    except Exception:
        return -1


def _passes_i_alone(A: Poly, frame, fields) -> bool:
    """Gate (i) for a single block: every CRT component of Â is a unit or an
    engine-grade radical.  Aut-/translation-invariant; prunes the pairing."""
    return all(c.kind in (UNIT, ENGINE_RADICAL)
               for c in component_table(A, frame, fields))


def enumerate_anchorable_direct(ell: int, m: int, cap_pairs: int | None = None):
    """All anchorable (A, B) bases over Z_ℓ×Z_m with both blocks origin-anchored.
    Pre-filters each mono-list by the per-block engine gate (i) before pairing —
    (i) is a per-block property, so most weight-3 blocks are dropped up front."""
    G = AbelianGroup((ell, m))
    frame = crt_frame(G)
    fields = _fields(frame.odd_orders)
    monoX, monoY = _weight3_origin(G)
    monoX = [A for A in monoX if _passes_i_alone(A, frame, fields)]
    monoY = [B for B in monoY if _passes_i_alone(B, frame, fields)]
    hits = []  # (A_str, B_str, k) for STRUCTURALLY anchorable AND k>0 (real codes)
    n_struct = 0  # structural-only hits (incl. k=0 degenerates)
    n_pairs = 0
    for A in monoX:
        for B in monoY:
            n_pairs += 1
            if cap_pairs and n_pairs > cap_pairs:
                return hits, n_pairs, True, (len(monoX), len(monoY), n_struct)
            rep = evaluate(f"Z{ell}xZ{m}", G, A, B)
            if is_anchorable(rep):
                n_struct += 1
                k = code_k(A, B)
                if k > 0:  # reject k=0 degenerates — they are not codes
                    hits.append((A.canonical_string(), B.canonical_string(), k))
    return hits, n_pairs, False, (len(monoX), len(monoY), n_struct)


def hunt_direct(max_card: int, jsonl: Path | None) -> None:
    groups = zz_groups(max_card)
    print(f"Z₂×Z₂-frame groups with |G| ≤ {max_card}: "
          f"{[f'Z{e}xZ{m}' for e, m in groups]}")
    all_hits = []
    for (ell, m) in groups:
        hits, npairs, capped, (nx, ny, n_struct) = enumerate_anchorable_direct(
            ell, m, cap_pairs=4_000_000)
        status = "CAPPED" if capped else "complete"
        tag = "gross-family" if sorted((ell, m)) == [6, 6] else "NEW-GROUP"
        ks = collections.Counter(k for (_, _, k) in hits)
        print(f"  Z{ell}xZ{m:<3d} |G|={ell*m:3d}  (i)-blocks {nx}×{ny}  "
              f"pairs={npairs:7d} ({status})  structural={n_struct:5d}  "
              f"REAL(k>0)={len(hits):4d}  k-dist={dict(sorted(ks.items()))}  "
              f"[{tag if hits else '—'}]", flush=True)
        for (a, b, k) in hits:
            all_hits.append({"group": f"Z{ell}xZ{m}", "base_n": 2 * ell * m,
                             "cover_n": 4 * ell * m, "A": a, "B": b, "k": k,
                             "new_group": sorted((ell, m)) != [6, 6]})

    new = [h for h in all_hits if h["new_group"]]
    new_groups = sorted({h["group"] for h in new})
    print(f"\n=== RESULT ===")
    print(f"  total REAL (k>0) anchorable hits: {len(all_hits)}")
    print(f"  groups with ANY real anchorable base: "
          f"{sorted({h['group'] for h in all_hits})}")
    print(f"  GENUINELY-NEW groups (≠ Z₆×Z₆) hosting a REAL anchorable base: "
          f"{new_groups if new_groups else 'NONE'}")
    if new:
        print("  → new anchorable-base candidates (structural+k>0; distance NOT yet checked):")
        for h in new[:20]:
            print(f"     {h['group']:10s} k={h['k']} base[[{h['base_n']},{h['k']},?]] "
                  f"cover[[{h['cover_n']},{h['k']},?]]  A={h['A']} | B={h['B']}")
    if jsonl:
        with open(jsonl, "w") as fh:
            for h in all_hits:
                fh.write(json.dumps(h) + "\n")
        print(f"\nwrote {len(all_hits)} hits → {jsonl}")


# ---------------------------------------------------------------------------
# Corpus sweep
# ---------------------------------------------------------------------------


def sweep(db_path: Path, limit: int | None, jsonl: Path | None) -> None:
    import duckdb

    con = duckdb.connect(str(db_path), read_only=True)
    q = ("select instance_id, code_id, ell, m, n, k, A_poly, B_poly, "
         "d_exact, d_lb, d_ub from bb_instances "
         "where A_weight=3 and B_weight=3 and k>0")
    if limit:
        q += f" limit {limit}"
    rows = con.execute(q).fetchall()
    print(f"BB corpus rows (G0: |A|=|B|=3, k>0): {len(rows)}")

    tier_counts: collections.Counter = collections.Counter()
    out_rows = []
    skipped = 0
    # validation: DIRECT/COVER predicts d ≥ 6; flag any known d < 6 (false positive)
    false_pos = []
    # utility: predicted floor 6 > current known lower bound (improvement)
    improvements = []

    for (iid, cid, ell, m, n, k, A_str, B_str, dx, dlb, dub) in rows:
        try:
            res = classify(int(ell), int(m), A_str, B_str)
        except Exception as exc:  # unparseable poly / degenerate group
            skipped += 1
            continue
        tier_counts[res.tier] += 1
        rec = {
            "instance_id": iid, "code_id": cid, "group": f"Z{ell}xZ{m}",
            "n": n, "k": k, "A": A_str, "B": B_str,
            "tier": res.tier, "floor": res.floor, "double_target": res.double_target,
            "base": res.base_group, "base_frame": res.base_frame,
            "cover_degree": res.cover_degree,
            "d_exact": dx, "d_lb": dlb, "d_ub": dub,
        }
        out_rows.append(rec)
        if res.tier in ("DIRECT", "COVER", "DOUBLE_CANDIDATE"):
            if dx is not None and dx < res.floor:
                false_pos.append(rec)
            cur_lb = dlb if dlb is not None else (dx if dx is not None else 0)
            if dx is None and (cur_lb or 0) < res.floor:
                improvements.append(rec)

    print("\n=== TIER FUNNEL ===")
    for t in ("DOUBLE_CANDIDATE", "DIRECT", "COVER", "none"):
        print(f"  {t:18s}: {tier_counts[t]}")
    print(f"  (skipped/unparseable): {skipped}")

    print("\n=== VALIDATION ===")
    print(f"  false positives (tier∈{{DIRECT,COVER,DOUBLE}} but known d<6): {len(false_pos)}")
    for r in false_pos[:12]:
        print(f"     ! {r['group']} A={r['A']} B={r['B']} tier={r['tier']} "
              f"base={r['base']} d_exact={r['d_exact']}")
    # cross-tab anchored tiers vs known d_exact
    by_tier_d = collections.defaultdict(collections.Counter)
    for r in out_rows:
        if r["tier"] in ("DIRECT", "COVER", "DOUBLE_CANDIDATE") and r["d_exact"] is not None:
            by_tier_d[r["tier"]][r["d_exact"]] += 1
    for t in ("DOUBLE_CANDIDATE", "DIRECT", "COVER"):
        if by_tier_d[t]:
            print(f"  {t} d_exact dist: {dict(sorted(by_tier_d[t].items()))}")

    print("\n=== NEW LOWER-BOUND PREDICTIONS (no d_exact in DB, certified d≥6) ===")
    print(f"  count: {len(improvements)}")

    # ranked double-candidate list (the prize)
    dcs = [r for r in out_rows if r["tier"] == "DOUBLE_CANDIDATE"]
    print(f"\n=== DOUBLE_CANDIDATES (predicted d=12 research targets): {len(dcs)} ===")
    seen_codes = set()
    shown = 0
    for r in sorted(dcs, key=lambda x: (x["n"], x["group"])):
        key = (r["group"], r["A"], r["B"])
        print(f"   {r['group']:10s} n={r['n']:4d} k={r['k']:2d} A={r['A']:22s} "
              f"B={r['B']:22s} base={r['base']} d_exact={r['d_exact']} d_ub={r['d_ub']}")
        shown += 1
        if shown >= 40:
            print(f"   ... ({len(dcs)-40} more)")
            break

    if jsonl:
        with open(jsonl, "w") as fh:
            for r in out_rows:
                fh.write(json.dumps(r) + "\n")
        print(f"\nwrote {len(out_rows)} rows → {jsonl}")


# ---------------------------------------------------------------------------
# Self-test: the known codes must land in the right tier.
# ---------------------------------------------------------------------------

SELF_TESTS = [
    # (label, ell, m, A, B, expected_tier)
    ("base [[72,12,6]]", 6, 6, "x^3 + y + y^2", "y^3 + x + x^2", "DIRECT"),
    ("gross [[144,12,12]]", 12, 6, "x^3 + y + y^2", "y^3 + x + x^2", "DOUBLE_CANDIDATE"),
    ("two-gross [[288,12,18]]", 12, 12, "x^3 + y + y^2", "y^3 + x + x^2", "COVER"),
    ("bb_108 [[108,8,10]]", 9, 6, "x^3 + y + y^2", "y^3 + x + x^2", "DIRECT"),
    ("bb_90 [[90,8,10]]", 15, 3, "x^9 + y + y^2", "1 + x^2 + x^7", "DIRECT"),
    # falsifiers — must be REJECTED (not anchorable / out of scope)
    ("Z3xZ5 d=4 (no mirror)", 3, 5, "x + y^2 + y^3", "x^2 + y + y^4", "none"),
]


def self_test() -> None:
    print("=== SELF-TEST (known codes) ===")
    ok = True
    for (label, ell, m, A, B, expected) in SELF_TESTS:
        try:
            res = classify(ell, m, A, B)
            got = res.tier
        except Exception as exc:
            got = f"ERROR({exc})"
        mark = "✓" if got == expected else "✗"
        if got != expected:
            ok = False
        print(f"  {mark} {label:26s} Z{ell}xZ{m:<3d} → {got:18s} "
              f"(expected {expected}; base={getattr(res,'base_group','-')}, "
              f"deg={getattr(res,'cover_degree','-')})")
    print(f"\n  {'ALL PASS' if ok else 'FAILURES PRESENT'}")


def presentation_self_test() -> None:
    """A scrambled gross base (Aut-transformed out of mirrored coords) must
    still be found anchorable by the orbit search, and a genuine non-base
    must not."""
    print("=== PRESENTATION-SEARCH SELF-TEST ===")
    G = AbelianGroup((6, 6))
    A = Poly.from_string("x^3 + y + y^2", G)
    B = Poly.from_string("y^3 + x + x^2", G)
    # scramble by a non-trivial automorphism so (iii) breaks in stored coords
    autos = automorphisms(6, 6)
    scrambled = None
    for auto in autos:
        sa, sb = apply_auto(A, auto, G), apply_auto(B, auto, G)
        if not is_anchorable(evaluate("s", G, sa, sb)):
            scrambled = (sa, sb)
            break
    ok1 = scrambled is not None
    print(f"  found a non-mirrored presentation of gross base: {ok1}")
    if ok1:
        sa, sb = scrambled
        stored = is_anchorable(evaluate("s", G, sa, sb))
        found, _ = presentation_anchorable(6, 6, sa, sb)
        print(f"  scrambled stored-coords anchorable: {stored} (expect False)")
        print(f"  orbit search recovers anchorability: {found} (expect True)")
    # a non-base Z₂×Z₂ code: A=B (the A=B ⟹ d=2 trap) must NOT anchor
    nb = Poly.from_string("x^3 + y + y^2", G)
    found_nb, _ = presentation_anchorable(6, 6, nb, nb)
    print(f"  A=B trap anchorable (expect False): {found_nb}")


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--limit", type=int, default=None)
    ap.add_argument("--jsonl", type=Path, default=None)
    ap.add_argument("--self-test", action="store_true")
    ap.add_argument("--pres-self-test", action="store_true")
    ap.add_argument("--hunt-doubling", action="store_true")
    ap.add_argument("--hunt-direct", action="store_true")
    ap.add_argument("--max-card", type=int, default=120)
    ap.add_argument("--db", type=Path, default=LAB_ROOT / "data" / "bb_instances.duckdb")
    args = ap.parse_args()

    if args.self_test:
        self_test()
        return
    if args.pres_self_test:
        presentation_self_test()
        return
    if args.hunt_doubling:
        hunt_doubling(args.db, args.jsonl)
        return
    if args.hunt_direct:
        hunt_direct(args.max_card, args.jsonl)
        return
    sweep(args.db, args.limit, args.jsonl)


if __name__ == "__main__":
    main()
