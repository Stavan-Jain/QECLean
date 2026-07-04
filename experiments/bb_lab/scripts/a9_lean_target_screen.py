"""A9 — the Lean-target screen: rank free-Z2 doubling pairs by Lean cost.

Purpose (plan stage 1): pick the next Lean formalization target for the
parametric doubling layer.  Unlike the A5 cascade — whose anchorability gate
selects for the *analytic* Theorem-A recipe (weight-3 grid, disjoint
difference sets, mirrored projections) — this screen selects for
*formalizability by direct kernel computation*: at small base-cell counts
every per-instance obligation (base floor, light-boundary census, safe-class
coset floors) is a `native_decide` sweep, and no CRT/F4 engine is needed.
The verified [[36,4,4]] -> [[72,4,8]] pair (which FAILS the cascade's D2
gate, yet is perfectly formalizable) is the motivating example.

Tiers reported:

  T1  direct-sweep doubling pairs: base on a small frame (cells <= 24),
      k > 0 preserved, d(cover) = 2*d(base) SAT-exact.  Ranked by Lean cost
      (leaf-sweep bits = base cells, Smith-dispatch size = 2^dim ker d2,
      census size), with the homotopy-R / sq-ideal / tight-witness
      obligations checked per pair.
  T2  engine-necessity census on the Z6xZ6 frame: how many corpus bases are
      cascade-anchorable (the analytic-engine regime), i.e. is there any
      in-frame engine-necessary second target beyond gross at weight 3?

Subcommands:
    uv run python scripts/a9_lean_target_screen.py hunt [--jsonl PATH] [--limit N]
    uv run python scripts/a9_lean_target_screen.py profile [--jsonl PATH] [--md PATH]
    uv run python scripts/a9_lean_target_screen.py t2 [--md PATH]

`hunt` is the slow part (SAT ladders; ~30-90 min over ~640 candidate covers)
and appends one JSON line per candidate as it goes, so it is safe to run in
the background and tail.  `profile` + `t2` are fast and (re)generate the
notes document from the hunt output.
"""

from __future__ import annotations

import argparse
import json
import sys
import time
from pathlib import Path

import numpy as np

LAB_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(LAB_ROOT / "src"))
sys.path.insert(0, str(LAB_ROOT / "scripts"))

from bb_lab.checks import bb_check_matrices, circulant
from bb_lab.codeparams import code_params
from bb_lab.group import AbelianGroup
from bb_lab.linalg import nullspace_f2, rank_f2, rref_f2, quotient_complement_basis
from bb_lab.poly import Poly
from bb_lab.sat_distance import x_distance, find_logical_z, _solve_at_weight

# T1 base frames: every per-instance Lean obligation is a sweep over
# F2[H] (2^cells), so cells <= 24 keeps the largest single native_decide
# leaf at ~1.7e7 * O(cells) kernel ops (the gross leaves were far larger).
T1_FRAMES: list[tuple[int, int]] = [(3, 3), (3, 4), (3, 5), (3, 6), (4, 6)]
DEFAULT_JSONL = LAB_ROOT / "data" / "a9" / "t1_hunt.jsonl"
DEFAULT_MD = LAB_ROOT / "notes" / "A9_lean_target_screen.md"


# ---------------------------------------------------------------------------
# F2 helpers (verifier-style, chunked so Z4xZ6-scale spaces stay cheap)
# ---------------------------------------------------------------------------


def in_rowspace(M: np.ndarray, x: np.ndarray) -> bool:
    r0 = rank_f2(M)
    r1 = rank_f2(np.vstack([M, x[None, :] & 1]))
    return r1 == r0


def rowspace_basis(M: np.ndarray) -> np.ndarray:
    R, piv = rref_f2(M)
    return R[: len(piv)].copy()


def span_iter(basis: np.ndarray, chunk_bits: int = 16):
    """Yield the F2 span of `basis` in chunks (2^chunk_bits rows each),
    including the zero vector."""
    d = basis.shape[0]
    total = 1 << d
    step = 1 << min(chunk_bits, d)
    exps = np.arange(d, dtype=np.uint64)
    for start in range(0, total, step):
        idx = np.arange(start, min(start + step, total), dtype=np.uint64)
        coeffs = ((idx[:, None] >> exps[None, :]) & 1).astype(np.uint8)
        yield (coeffs @ basis) % 2


def min_weight_in_span(basis: np.ndarray) -> int | None:
    """Minimum nonzero weight in the span (None if basis empty)."""
    if basis.shape[0] == 0:
        return None
    best: int | None = None
    for block in span_iter(basis):
        w = block.sum(axis=1)
        w = w[w > 0]
        if w.size:
            m = int(w.min())
            best = m if best is None or m < best else best
    return best


def coset_min_weight(rep: np.ndarray, basis: np.ndarray) -> int:
    best = None
    for block in span_iter(basis):
        w = ((block ^ rep[None, :]).sum(axis=1)).min()
        best = int(w) if best is None or w < best else best
    return best


# ---------------------------------------------------------------------------
# Cover construction (either axis) — generalizes verify_doubling_pair_z3z6.py
# ---------------------------------------------------------------------------


def lift_poly(P: Poly, Gc: AbelianGroup) -> Poly:
    """The same polynomial on the doubled group (supports embed literally:
    exponents in [0,l)x[0,m) remain valid coordinates of the cover group)."""
    return Poly(support=frozenset(P.support), group=Gc)


def cover_group(ell: int, m: int, axis: str) -> AbelianGroup:
    return AbelianGroup((2 * ell, m) if axis == "x" else (ell, 2 * m))


def cover_maps(Gb: AbelianGroup, Gc: AbelianGroup, axis: str):
    """(p_blk, tau_blk, sig_blk) on group cells; deck = translation by the
    half-axis element."""
    ell_b, m_b = Gb.orders
    nb, nc = Gb.cardinality, Gc.cardinality
    p_blk = np.zeros((nb, nc), dtype=np.uint8)
    for h in Gc:
        base_h = (h[0] % ell_b, h[1]) if axis == "x" else (h[0], h[1] % m_b)
        p_blk[Gb.index(base_h), Gc.index(h)] = 1
    deck = (ell_b, 0) if axis == "x" else (0, m_b)
    sig_blk = np.zeros((nc, nc), dtype=np.uint8)
    ell_c, m_c = Gc.orders
    for h in Gc:
        sig_blk[Gc.index(((h[0] + deck[0]) % ell_c, (h[1] + deck[1]) % m_c)), Gc.index(h)] = 1
    return p_blk, p_blk.T.copy(), sig_blk, deck


def blkdiag(M: np.ndarray) -> np.ndarray:
    z = np.zeros_like(M)
    return np.block([[M, z], [z, M]])


# ---------------------------------------------------------------------------
# Per-pair obligations
# ---------------------------------------------------------------------------


def sq_ideal_solve(Ac: Poly, Bc: Poly, Gc: AbelianGroup, deck: tuple[int, int]):
    """Solve q1*A^2 + q2*B^2 = 1 + x^deck over F2[Gc] (the generic
    deck-homotopy witness `deck_homotopy_of_sq_ideal`).  Returns
    (solvable, q1_zero_solvable)."""
    MA = circulant(Ac).astype(np.uint8)
    MB = circulant(Bc).astype(np.uint8)
    MA2 = (MA @ MA) % 2
    MB2 = (MB @ MB) % 2
    n = Gc.cardinality
    target = np.zeros(n, dtype=np.uint8)
    target[Gc.index((0, 0))] ^= 1
    target[Gc.index(deck)] ^= 1

    def solvable(M: np.ndarray) -> bool:
        return rank_f2(M.T) == rank_f2(np.vstack([M.T, target[None, :]]))

    both = np.hstack([MA2, MB2])  # (q1;q2) stacked -> columns
    return solvable(both), solvable(MB2)


def light_boundary_census(MA: np.ndarray, MB: np.ndarray, threshold: int):
    """Weight histogram (<= threshold) of nonzero Z-boundaries
    b = (B z, A z), plus mu_Z (global min nonzero boundary weight)."""
    n = MA.shape[0]
    # image basis: columns of stacked convolution matrix, independent set
    stacked = np.hstack([MB.T, MA.T])  # row i = boundary of delta_i, shape (n, 2n)
    basis = rowspace_basis(stacked)
    hist: dict[int, int] = {}
    mu = None
    for block in span_iter(basis):
        w = block.sum(axis=1)
        nz = w[w > 0]
        if nz.size:
            m = int(nz.min())
            mu = m if mu is None or m < mu else mu
        for wt in range(2, threshold + 1, 2):
            c = int((w == wt).sum())
            if c:
                hist[wt] = hist.get(wt, 0) + c
    return hist, mu, int(basis.shape[0])


def tight_witness_check(Gb, ustar, tau_blk, HZc, HXc) -> bool:
    """Does some translate of the min-weight base logical u* lift to a
    nontrivial cover logical (tau(u*) not a cover Z-stabilizer)?"""
    nb = Gb.cardinality
    T = blkdiag(tau_blk)
    for g in Gb:
        # translate u* by g on both blocks
        perm = np.array([Gb.index(((h[0] + g[0]) % Gb.orders[0], (h[1] + g[1]) % Gb.orders[1])) for h in Gb])
        tr = np.zeros_like(ustar)
        for i, h in enumerate(Gb):
            tr[perm[i]] = ustar[i]
            tr[nb + perm[i]] = ustar[nb + i]
        tau_u = (T @ tr) % 2
        if not ((HXc @ tau_u) % 2).any() and not in_rowspace(HZc, tau_u):
            return True
    return False


# ---------------------------------------------------------------------------
# The hunt (slow, incremental)
# ---------------------------------------------------------------------------


def load_t1_rows(db_path: Path, limit: int | None):
    import duckdb

    con = duckdb.connect(str(db_path), read_only=True)
    frames = [f"Z{l}xZ{m}" for (l, m) in T1_FRAMES]
    q = (
        "SELECT instance_id, group_struct, ell, m, A_poly, B_poly, k, d_exact "
        "FROM bb_instances WHERE group_struct IN ("
        + ",".join("?" * len(frames))
        + ") AND k > 0 AND d_exact >= 4 ORDER BY ell*m ASC, d_exact DESC, k DESC"
    )
    rows = con.execute(q, frames).fetchall()
    con.close()
    return rows[:limit] if limit else rows


def hunt(db_path: Path, jsonl: Path, limit: int | None) -> None:
    rows = load_t1_rows(db_path, limit)
    print(f"T1 hunt: {len(rows)} bases (frames {T1_FRAMES}, k>0, d>=4), 2 axes each", flush=True)
    jsonl.parent.mkdir(parents=True, exist_ok=True)
    t0 = time.time()
    n_double = 0
    with jsonl.open("w") as fh:
        for i, (iid, gs, ell, m, A_str, B_str, k, d_base) in enumerate(rows):
            for axis in ("x", "y"):
                rec = {
                    "instance_id": iid, "group": gs, "ell": ell, "m": m,
                    "A": A_str, "B": B_str, "k": k, "d_base": d_base, "axis": axis,
                }
                try:
                    Gb = AbelianGroup((ell, m))
                    Gc = cover_group(ell, m, axis)
                    Ab = Poly.from_string(A_str, Gb)
                    Bb = Poly.from_string(B_str, Gb)
                    chc = bb_check_matrices(lift_poly(Ab, Gc), lift_poly(Bb, Gc))
                    pc = code_params(chc)
                    rec["k_cover"] = pc.k
                    if pc.k != k:
                        rec["verdict"] = "k_changed"
                    else:
                        try:
                            res = x_distance(chc, weight_upper_bound=2 * d_base)
                            rec["d_cover"] = res.distance
                            rec["verdict"] = "DOUBLES" if res.distance == 2 * d_base else "short"
                        except RuntimeError:
                            rec["d_cover"] = f">{2 * d_base}"
                            rec["verdict"] = "over"
                except Exception as e:  # pragma: no cover — record and continue
                    rec["verdict"] = f"error: {e}"
                if rec.get("verdict") == "DOUBLES":
                    n_double += 1
                fh.write(json.dumps(rec) + "\n")
                fh.flush()
            if (i + 1) % 25 == 0:
                print(f"  [{i+1}/{len(rows)}] {time.time()-t0:.0f}s, doubles so far: {n_double}", flush=True)
    print(f"hunt done: {n_double} doubling covers in {time.time()-t0:.0f}s -> {jsonl}", flush=True)


# ---------------------------------------------------------------------------
# The profile (fast, survivors only)
# ---------------------------------------------------------------------------


def profile_pair(rec: dict) -> dict:
    ell, m, axis = rec["ell"], rec["m"], rec["axis"]
    d_base = rec["d_base"]
    Gb = AbelianGroup((ell, m))
    Gc = cover_group(ell, m, axis)
    Ab = Poly.from_string(rec["A"], Gb)
    Bb = Poly.from_string(rec["B"], Gb)
    Ac, Bc = lift_poly(Ab, Gc), lift_poly(Bb, Gc)
    chb, chc = bb_check_matrices(Ab, Bb), bb_check_matrices(Ac, Bc)
    HXb, HZb = chb.H_X.astype(np.uint8), chb.H_Z.astype(np.uint8)
    HXc, HZc = chc.H_X.astype(np.uint8), chc.H_Z.astype(np.uint8)
    MA, MB = circulant(Ab).astype(np.uint8), circulant(Bb).astype(np.uint8)

    out = dict(rec)
    nb = Gb.cardinality
    out["base_cells"] = nb

    # Smith domain / annihilators
    kerd2 = nullspace_f2(np.vstack([MA, MB]) % 2)
    annA, annB = nullspace_f2(MA), nullspace_f2(MB)
    out["dim_ker_d2"] = int(kerd2.shape[0])
    out["dispatch_cases"] = 1 << int(kerd2.shape[0])
    out["mu_annA"] = min_weight_in_span(annA)
    out["mu_annB"] = min_weight_in_span(annB)

    # light-boundary census up to 2d-1 + mu_Z
    hist, mu_z, rank_d2 = light_boundary_census(MA, MB, 2 * d_base - 1)
    out["boundary_census_le_2d_minus_1"] = hist
    out["mu_Z"] = mu_z
    out["rank_d2"] = rank_d2

    # cover maps + induced structure
    p_blk, tau_blk, sig_blk, deck = cover_maps(Gb, Gc, axis)
    P, T, S = blkdiag(p_blk), blkdiag(tau_blk), blkdiag(sig_blk)
    LZc = find_logical_z(chc)
    out["homotopy_R"] = all(in_rowspace(HZc, ((S @ LZc[i]) % 2) ^ LZc[i]) for i in range(LZc.shape[0]))
    out["linchpin_imp_in_kertau"] = all(
        in_rowspace(HZc, (T @ ((P @ LZc[i]) % 2)) % 2) for i in range(LZc.shape[0])
    )
    sq_all, sq_q1zero = sq_ideal_solve(Ac, Bc, Gc, deck)
    out["sq_ideal_solvable"] = sq_all
    out["sq_ideal_q1_zero"] = sq_q1zero

    # safe classes: reps of im p_* mod base boundaries + coset minima
    p_imgs = np.array([(P @ LZc[i]) % 2 for i in range(LZc.shape[0])], dtype=np.uint8)
    reps: list[np.ndarray] = []
    for i in range(p_imgs.shape[0]):
        stackA = np.vstack([HZb] + ([np.array(reps)] if reps else []))
        if rank_f2(np.vstack([stackA, p_imgs[i][None, :]])) > rank_f2(stackA):
            reps.append(p_imgs[i])
    out["rank_p_star"] = len(reps)
    Sb = rowspace_basis(HZb)
    minima = []
    if reps:
        combos = [c for c in span_iter(np.array(reps), chunk_bits=len(reps))][0]
        for row in combos:
            if row.any():
                minima.append(coset_min_weight(row, Sb))
    out["safe_class_minima"] = minima
    out["safe_floor_ok"] = all(w >= 2 * d_base for w in minima) if minima else True

    # tight witness (u* at weight d whose diagonal lift is nontrivial)
    LXb = quotient_complement_basis(HXb, nullspace_f2(HZb))
    wit, _ = _solve_at_weight(HXb, LXb, d_base)
    out["tight_witness"] = bool(
        wit is not None and tight_witness_check(Gb, (wit & 1).astype(np.uint8), tau_blk, HZc, HXc)
    )

    # Lean cost proxies
    out["leaf_sweep_bits"] = nb                     # per-leaf: 2^cells kernel sweep
    out["n_cover"] = 2 * chb.num_qubits // 1        # = 2 * n_base
    return out


def profile(jsonl: Path, md: Path) -> None:
    recs = [json.loads(line) for line in jsonl.open()]
    doubles = [r for r in recs if r.get("verdict") == "DOUBLES"]
    print(f"profiling {len(doubles)} doubling pairs (of {len(recs)} candidates)")
    profiles = []
    for r in doubles:
        t0 = time.time()
        profiles.append(profile_pair(r))
        print(f"  {r['group']} {r['axis']}-cover A={r['A']!r} d={r['d_base']}->{r['d_cover']} ({time.time()-t0:.1f}s)", flush=True)

    # rank: all obligations green first, then leaf bits, dispatch, census size, bigger d last
    def key(p):
        green = p["homotopy_R"] and p["linchpin_imp_in_kertau"] and p["safe_floor_ok"] and p["tight_witness"]
        census = sum(p["boundary_census_le_2d_minus_1"].values())
        return (not green, p["leaf_sweep_bits"], p["dim_ker_d2"], census, -p["d_base"], p["n_cover"])

    profiles.sort(key=key)
    write_markdown(profiles, md)
    out_json = jsonl.with_name("t1_profiles.json")
    out_json.write_text(json.dumps(profiles, indent=1, default=str))
    print(f"wrote {md} and {out_json}")


def write_markdown(profiles: list[dict], md: Path) -> None:
    md.parent.mkdir(parents=True, exist_ok=True)
    lines = [
        "# A9 — Lean-target screen (stage-1 of the doubling-layer plan)",
        "",
        "T1 = free-Z2 doubling pairs on direct-sweep frames (base cells <= 24,",
        "k > 0 preserved, d(cover) = 2 d(base) SAT-exact), ranked by Lean cost.",
        "Obligations per pair: homotopy R (sigma_* = id), linchpin (im p_* in ker tau_*),",
        "safe-class coset minima >= 2d, tight diagonal witness, sq-ideal homotopy",
        "witness (the generic `deck_homotopy_of_sq_ideal` route).",
        "",
        "Generated by `scripts/a9_lean_target_screen.py`; raw data in `data/a9/`.",
        "",
        "| # | base | axis | pair | A ; B | kerd2 | census<=2d-1 | muZ | annA/annB | R | linch | safe | wit | sqIdeal(q1=0) | leaf bits |",
        "|--:|------|------|------|-------|------:|--------------|----:|-----------|---|-------|------|-----|---------------|----------:|",
    ]
    for i, p in enumerate(profiles, 1):
        pair = f"[[{2*p['base_cells']},{p['k']},{p['d_base']}]] -> [[{4*p['base_cells']},{p['k']},{2*p['d_base']}]]"
        census = ",".join(f"{w}:{c}" for w, c in sorted(p["boundary_census_le_2d_minus_1"].items())) or "-"
        lines.append(
            f"| {i} | Z{p['ell']}xZ{p['m']} | {p['axis']} | {pair} | `{p['A']}` ; `{p['B']}` "
            f"| {p['dim_ker_d2']} | {census} | {p['mu_Z']} | {p['mu_annA']}/{p['mu_annB']} "
            f"| {'Y' if p['homotopy_R'] else 'N'} | {'Y' if p['linchpin_imp_in_kertau'] else 'N'} "
            f"| {'Y' if p['safe_floor_ok'] else 'N'} ({','.join(map(str,p['safe_class_minima']))}) "
            f"| {'Y' if p['tight_witness'] else 'N'} "
            f"| {'Y' if p['sq_ideal_solvable'] else 'N'}({'Y' if p['sq_ideal_q1_zero'] else 'N'}) "
            f"| {p['leaf_sweep_bits']} |"
        )
    lines += ["", "Ranking key: all-obligations-green first, then leaf-sweep bits,",
              "dim ker d2, census size, larger d(base), cover size.", ""]
    md.write_text("\n".join(lines))


# ---------------------------------------------------------------------------
# T2 — engine-necessity census on Z6xZ6
# ---------------------------------------------------------------------------


def t2_census(db_path: Path, md: Path) -> None:
    import duckdb
    from a5_cover_cascade import evaluate, is_anchorable

    con = duckdb.connect(str(db_path), read_only=True)
    rows = con.execute(
        "SELECT instance_id, A_poly, B_poly, k, d_exact FROM bb_instances "
        "WHERE group_struct = 'Z6xZ6' AND k > 0"
    ).fetchall()
    con.close()
    G = AbelianGroup((6, 6))
    anchorable = []
    for iid, A_str, B_str, k, d in rows:
        rep = evaluate("Z6xZ6", G, Poly.from_string(A_str, G), Poly.from_string(B_str, G))
        if is_anchorable(rep):
            anchorable.append((iid, A_str, B_str, k, d))
    lines = [
        "",
        "## T2 — engine-necessity census (Z6xZ6 frame)",
        "",
        f"Corpus Z6xZ6 k>0 codes: {len(rows)}.  Cascade-anchorable (analytic",
        f"Theorem-A regime, engine-grade components + (ii) + (iii)): {len(anchorable)}.",
        "",
    ]
    for iid, A_str, B_str, k, d in anchorable:
        lines.append(f"- `{iid}`  A=`{A_str}`  B=`{B_str}`  k={k} d={d}")
    lines += [
        "",
        "Z6xZ6 bases have 36 cells: the direct-sweep route (2^36 leaf) is out of",
        "reach, so any non-anchorable Z6xZ6 doubling pair needs the CRT/F4 engine",
        "(or new reductions) — the engine-necessity boundary for this program.",
        "",
    ]
    with md.open("a") as fh:
        fh.write("\n".join(lines))
    print(f"T2: {len(anchorable)} anchorable of {len(rows)}; appended to {md}")


# ---------------------------------------------------------------------------


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("cmd", choices=["hunt", "profile", "t2"])
    ap.add_argument("--db", type=Path, default=LAB_ROOT / "data" / "bb_instances.duckdb")
    ap.add_argument("--jsonl", type=Path, default=DEFAULT_JSONL)
    ap.add_argument("--md", type=Path, default=DEFAULT_MD)
    ap.add_argument("--limit", type=int, default=None)
    args = ap.parse_args()
    if args.cmd == "hunt":
        hunt(args.db, args.jsonl, args.limit)
    elif args.cmd == "profile":
        profile(args.jsonl, args.md)
    else:
        t2_census(args.db, args.md)


if __name__ == "__main__":
    main()
