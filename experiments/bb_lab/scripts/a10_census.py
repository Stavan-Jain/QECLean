"""A10 census — aggregate the screen JSONLs into the notes tables.

Reads data/a10/*.jsonl and prints (a) the hit2/hit5 per-class verdict
grids with rescue twist-sets, (b) the S3 rescue-rate table by frame,
(c) the Sidon(B) discriminator cross-tab, and (d) extracts
`data/a10/s3_unrescued_certificates.jsonl` — the full per-cover witness
rows of every unrescued S3 base (the finite counterexample
certificates, small enough to commit).

    uv run python scripts/a10_census.py
"""

from __future__ import annotations

import glob
import json
import sys
from collections import Counter, defaultdict
from pathlib import Path

LAB_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(LAB_ROOT / "src"))

from bb_lab.group import AbelianGroup
from bb_lab.poly import Poly
from bb_lab.diffset_predicates import is_sidon


def load(base: str) -> list[dict]:
    rows, seen = [], set()
    for f in sorted(glob.glob(str(LAB_ROOT / "data" / "a10" / f"{base}_descent_screen*.jsonl"))):
        for line in open(f):
            if not line.strip():
                continue
            r = json.loads(line)
            key = (tuple(r["cls"]), tuple(r["epsA"]), tuple(r["epsB"]))
            if key not in seen:
                seen.add(key)
                rows.append(r)
    return rows


def eps_str(e) -> str:
    return "".join(map(str, e))


def hit_census(base: str) -> None:
    rows = load(base)
    print(f"\n### {base}: {len(rows)}/256 covers screened")
    per = defaultdict(list)
    for r in rows:
        per[r["cls_name"]].append(r)
    for cls in ("x", "y", "mixed", "split"):
        rs = per.get(cls, [])
        if not rs:
            continue
        c = Counter(r["verdict"] for r in rs)
        rescues = sorted(
            (eps_str(r["epsA"]), eps_str(r["epsB"]))
            for r in rs
            if r["verdict"] in ("rescue", "super")
        )
        d_fails = Counter(
            r.get("d") or r.get("d_ub") for r in rs if r["verdict"] == "fail"
        )
        print(
            f"  {cls:>6} [{len(rs):>3}/64]: {dict(c)}; fail-d {dict(sorted(d_fails.items()))}"
        )
        if rescues:
            print(f"         rescuers (epsA,epsB): {rescues}")


def s3_census() -> None:
    path = LAB_ROOT / "data" / "a10" / "s3_smallframe_sweep.jsonl"
    if not path.exists():
        return
    by = defaultdict(list)
    for line in open(path):
        r = json.loads(line)
        by[r["base_id"]].append(r)
    complete = {b: rs for b, rs in by.items() if len(rs) == 256}
    import duckdb

    con = duckdb.connect(str(LAB_ROOT / "data" / "bb_instances.duckdb"), read_only=True)
    meta = {
        r[0]: r
        for r in con.execute(
            "SELECT instance_id, group_struct, ell, m, A_poly, B_poly, d_exact, k "
            "FROM bb_instances"
        ).fetchall()
    }
    con.close()

    stats = defaultdict(Counter)     # frame -> status counts
    sidon_tab = defaultdict(Counter)  # status -> sidonB counts
    unrescued_rows = []
    unrescued_meta = []
    rescue_cls = defaultdict(Counter)  # frame -> rescue-class counts
    for b, rs in sorted(complete.items()):
        _, frame, ell, m, A_str, B_str, d, k = meta[b]
        lit = [
            r
            for r in rs
            if r["cls_name"] in ("x", "y")
            and all(e == 0 for e in r["epsA"])
            and all(e == 0 for e in r["epsB"])
        ]
        ld = any(r["verdict"] == "rescue" for r in lit)
        rescues = [r for r in rs if r["verdict"] in ("rescue", "super")]
        status = "literal" if ld else ("rescued" if rescues else "unrescued")
        stats[frame][status] += 1
        G = AbelianGroup((ell, m))
        sidon_tab[status][is_sidon(Poly.from_string(B_str, G))] += 1
        if status == "rescued":
            for r in rescues:
                rescue_cls[frame][r["cls_name"]] += 1
        if status == "unrescued":
            unrescued_rows.extend(rs)
            unrescued_meta.append(
                {"instance_id": b, "frame": frame, "A": A_str, "B": B_str,
                 "d_base": d, "k": k,
                 "max_descent_d": max(
                     (r.get("d") or r.get("d_ub") or 0)
                     for r in rs if r["verdict"] == "fail")}
            )

    print(f"\n### S3 census ({len(complete)} complete bases)")
    print(f"| frame | literal-doubles | twist-rescued | UNRESCUED |")
    print(f"|---|---|---|---|")
    for frame in sorted(stats):
        s = stats[frame]
        print(
            f"| {frame} | {s['literal']} | {s['rescued']} | {s['unrescued']} |"
        )
    print("\nSidon(B) cross-tab (status: {is_sidon(B): count}):")
    for st, c in sorted(sidon_tab.items()):
        print(f"  {st}: {dict(c)}")
    print("\nrescue classes by frame:")
    for frame, c in sorted(rescue_cls.items()):
        print(f"  {frame}: {dict(c)}")
    print(f"\nunrescued bases ({len(unrescued_meta)}):")
    for u in unrescued_meta:
        print(
            f"  {u['frame']} {u['instance_id']} A=`{u['A']}` B=`{u['B']}` "
            f"d={u['d_base']} max-descent-d={u['max_descent_d']}"
        )
    cert = LAB_ROOT / "data" / "a10" / "s3_unrescued_certificates.jsonl"
    with cert.open("w") as fh:
        for r in unrescued_rows:
            fh.write(json.dumps(r) + "\n")
    meta_path = LAB_ROOT / "data" / "a10" / "s3_unrescued_bases.json"
    meta_path.write_text(json.dumps(unrescued_meta, indent=2))
    print(f"\nwrote {cert} ({len(unrescued_rows)} rows) and {meta_path}")


def main() -> None:
    for base in ("toric3", "toric4", "hit2", "hit5"):
        hit_census(base)
    s3_census()


if __name__ == "__main__":
    main()
