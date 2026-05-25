"""bb-lab CLI.

Subcommands:
  bb-lab bravyi-check [--full]   reproduce the Bravyi table; --full runs n=144, n=288
  bb-lab distance <yaml>         compute exact distance for a state.yaml entry
  bb-lab lean-import <yaml>      print the JSON descriptor for a state.yaml row
  bb-lab lean-emit <yaml> <out>  emit a Lean skeleton from a state.yaml row

`enumerate` is reserved for v1 (canonical-form deduper + weight-bounded
enumeration); calling it raises NotImplementedError today.
"""

from __future__ import annotations

import time
from pathlib import Path

import click
import yaml

from .checks import bb_check_matrices
from .codeparams import code_params
from .group import ZmZn
from .lean_bridge import descriptor_from_state_yaml, emit_skeleton
from .poly import Poly
from .sat_distance import x_distance


LAB_ROOT = Path(__file__).resolve().parent.parent.parent  # experiments/bb_lab
INSTANCES_YAML = LAB_ROOT / "instances" / "bravyi_table.yaml"


@click.group(help="bb-lab: bivariate-bicycle code laboratory (Tier 1).")
def main() -> None:
    pass


@main.command(name="bravyi-check")
@click.option(
    "--full/--quick",
    default=False,
    help="Run all five instances (--full, multi-minute to multi-hour) or only the three small ones (--quick).",
)
@click.option(
    "--emit-proofs/--no-emit-proofs",
    default=False,
    help="Emit LRAT proofs + DIMACS CNFs into certificates/<code_id>/ (requires the cadical CLI).",
)
def bravyi_check(full: bool, emit_proofs: bool) -> None:
    """Reproduce the Bravyi-table distances via SAT."""
    from .certificate import make_certificate, write_certificate, verify_certificate
    from .sat_distance import find_logical_z

    CERTS = LAB_ROOT / "certificates"
    rows = yaml.safe_load(INSTANCES_YAML.read_text())["instances"]
    small = {"bb_72_12_6", "bb_90_8_10", "bb_108_8_10"}
    for row in rows:
        if not full and row["code_id"] not in small:
            click.echo(f"  skip  {row['display_name']}  (heroic; pass --full)")
            continue
        code_id = row["code_id"]
        G = ZmZn(row["group"]["ell"], row["group"]["m"])
        A = Poly.from_string(row["polynomials"]["A"], G)
        B = Poly.from_string(row["polynomials"]["B"], G)
        checks = bb_check_matrices(A, B)
        params = code_params(checks)
        proof_dir = CERTS / code_id if emit_proofs else None
        if proof_dir is not None and proof_dir.exists():
            import shutil as _sh
            _sh.rmtree(proof_dir)
        t = time.time()
        res = x_distance(checks, proof_dir=proof_dir, code_id=code_id)
        dt = time.time() - t
        ok = (
            params.n == row["parameters"]["n"]
            and params.k == row["parameters"]["k"]
            and res.distance == row["parameters"]["d"]
        )
        marker = "OK " if ok else "FAIL"
        proof_note = ""
        if emit_proofs and res.unsat_proof_paths:
            L_Z = find_logical_z(checks)
            cert = make_certificate(
                code_id=code_id, H_check=checks.H_Z, L_logical=L_Z,
                witness=res.witness, distance=res.distance,
                direction="X", solver="cadical@3.0.0", wall_seconds=dt,
                unsat_drat_paths=res.unsat_proof_paths,
                cert_dir=CERTS,
            )
            verify_certificate(cert, checks.H_Z, L_Z)
            write_certificate(cert, CERTS / f"{code_id}.cert.json")
            total = sum(p.stat().st_size for p in res.unsat_proof_paths) / 1024
            proof_note = f"  +{len(res.unsat_proof_paths)} drat ({total:.0f} KB)"
        click.echo(
            f"  {marker}  {row['display_name']:30s}  "
            f"n={params.n:3d} k={params.k:2d} d={res.distance:2d}  "
            f"({dt:6.2f}s){proof_note}"
        )


@main.command(name="distance")
@click.argument("state_yaml", type=click.Path(exists=True, path_type=Path))
def distance(state_yaml: Path) -> None:
    """Compute exact SAT distance for one state.yaml row."""
    desc = descriptor_from_state_yaml(state_yaml)
    G = ZmZn(*desc.group_orders)
    A = Poly.from_support(desc.A_support, G)
    B = Poly.from_support(desc.B_support, G)
    checks = bb_check_matrices(A, B)
    params = code_params(checks)
    click.echo(f"{desc.code_id}: n={params.n}, k={params.k}; computing distance via SAT...")
    t = time.time()
    res = x_distance(checks)
    dt = time.time() - t
    click.echo(f"  d_X = {res.distance}  (witness weight {int(res.witness.sum())})  in {dt:.2f}s")


@main.command(name="lean-import")
@click.argument("state_yaml", type=click.Path(exists=True, path_type=Path))
def lean_import(state_yaml: Path) -> None:
    """Print the canonical JSON descriptor for a state.yaml row."""
    desc = descriptor_from_state_yaml(state_yaml)
    click.echo(desc.to_json())


@main.command(name="lean-emit")
@click.argument("state_yaml", type=click.Path(exists=True, path_type=Path))
@click.argument("out", type=click.Path(path_type=Path))
def lean_emit(state_yaml: Path, out: Path) -> None:
    """Emit a Lean skeleton from a state.yaml row to `out`."""
    desc = descriptor_from_state_yaml(state_yaml)
    written = emit_skeleton(desc, out)
    click.echo(f"wrote {written}")


@main.command(name="enumerate")
@click.option(
    "--ell", type=int, required=True, help="First cyclic factor ℓ for G = ZMod ℓ × ZMod m.",
)
@click.option(
    "--m", "m_arg", type=int, required=True, help="Second cyclic factor m.",
)
@click.option(
    "--weight", type=int, default=3,
    help="Hamming weight of A and B (Bravyi uses 3).",
)
@click.option(
    "--only-k-geq", type=int, default=2,
    help="Drop canonical BB codes with k < this (k=0 codes have no logicals).",
)
@click.option(
    "--db", type=click.Path(path_type=Path), default=None,
    help="DuckDB output path (default: data/bb_instances.duckdb).",
)
@click.option(
    "--verbose/--no-verbose", default=True,
)
def enumerate_cmd(
    ell: int, m_arg: int, weight: int, only_k_geq: int,
    db: Path | None, verbose: bool,
) -> None:
    """Canonical-form enumeration over BB instances → DuckDB corpus."""
    import time
    from .enumerate_bb import enumerate_canonical_pairs
    from .group import ZmZn
    from .poly import Poly
    from .store import StoredInstance, canonical_hash, connect, upsert_instance

    G = ZmZn(ell, m_arg)
    db_path = db or (LAB_ROOT / "data" / "bb_instances.duckdb")

    t = time.time()
    n_added = 0
    k_dist: dict[int, int] = {}
    with connect(db_path) as con:
        for inst in enumerate_canonical_pairs(
            G, weight=weight, only_k_geq=only_k_geq, verbose=verbose,
        ):
            A_poly_str = Poly(
                support=frozenset(inst.canonical.A_support), group=G
            ).canonical_string()
            B_poly_str = Poly(
                support=frozenset(inst.canonical.B_support), group=G
            ).canonical_string()
            iid = canonical_hash(G.label(), A_poly_str, B_poly_str)
            stored = StoredInstance(
                instance_id=iid,
                code_id=f"bb_enum_{G.label()}_{iid[:8]}",
                group_struct=G.label(),
                ell=ell, m=m_arg,
                n=inst.n, k=inst.k,
                A_poly=A_poly_str, B_poly=B_poly_str,
                A_weight=inst.A_weight, B_weight=inst.B_weight,
                rank_HX=inst.rank_HX, rank_HZ=inst.rank_HZ,
                dim_ker_A=inst.dim_ker_A, dim_ker_B=inst.dim_ker_B,
                orbit_size=inst.canonical.orbit_size,
            )
            upsert_instance(con, stored)
            n_added += 1
            k_dist[inst.k] = k_dist.get(inst.k, 0) + 1
    dt = time.time() - t
    click.echo(
        f"  enumerate Z_{ell}xZ_{m_arg} weight={weight} k≥{only_k_geq}: "
        f"{n_added} canonical instances in {dt:.1f}s → {db_path}"
    )
    for k in sorted(k_dist):
        click.echo(f"    k={k:3d}: {k_dist[k]} codes")


@main.command(name="fill-distances")
@click.option(
    "--db", type=click.Path(path_type=Path), default=None,
    help="DuckDB store path (default: data/bb_instances.duckdb).",
)
@click.option(
    "--max-n", type=int, default=48,
    help="Skip instances with n > this (SAT cost ≈ exponential in d).",
)
@click.option(
    "--min-k", type=int, default=2,
    help="Skip instances with k < this (no logicals to find).",
)
@click.option(
    "--limit", type=int, default=None,
    help="Stop after this many instances.",
)
@click.option(
    "--timeout-per-instance", type=int, default=120,
    help="Per-instance wall-time cap; instances exceeding this get d_ub recorded.",
)
def fill_distances(
    db: Path | None, max_n: int, min_k: int, limit: int | None,
    timeout_per_instance: int,
) -> None:
    """Compute exact SAT distance for corpus instances without a stored
    `d_exact`. Walks `bb_instances` in (n, k) order so the cheap ones
    land first."""
    import multiprocessing as _mp
    import time
    from .checks import bb_check_matrices
    from .group import ZmZn
    from .poly import Poly
    from .sat_distance import x_distance
    from .store import connect

    db_path = db or (LAB_ROOT / "data" / "bb_instances.duckdb")
    if not db_path.exists():
        raise click.ClickException(
            f"corpus DB {db_path} not found — run `bb-lab enumerate` first"
        )

    with connect(db_path) as con:
        rows = con.execute(
            """
            SELECT instance_id, group_struct, ell, m, A_poly, B_poly, n, k
              FROM bb_instances
             WHERE d_exact IS NULL
               AND n <= ?
               AND k >= ?
             ORDER BY n, k
            """,
            [max_n, min_k],
        ).fetchall()
        if limit is not None:
            rows = rows[:limit]
        click.echo(f"  pending: {len(rows)} instances (n ≤ {max_n}, k ≥ {min_k})")
        n_done = 0
        n_timeout = 0
        for iid, gstruct, ell, m_, A_str, B_str, n_q, k_q in rows:
            G = ZmZn(ell, m_)
            A = Poly.from_string(A_str, G)
            B = Poly.from_string(B_str, G)
            checks = bb_check_matrices(A, B)

            # Subprocess for hard timeout; SAT can be long-tailed even
            # for "small" n.
            t = time.time()
            try:
                with _mp.get_context("spawn").Pool(processes=1) as pool:
                    res = pool.apply_async(_sat_d_worker, (checks.H_X, checks.H_Z))
                    distance = res.get(timeout=timeout_per_instance)
            except _mp.TimeoutError:
                con.execute(
                    "UPDATE bb_instances SET d_method = ?, updated_at = now() WHERE instance_id = ?",
                    [f"sat-timeout@{timeout_per_instance}s", iid],
                )
                n_timeout += 1
                click.echo(f"  TIMEOUT  [[{n_q},{k_q}]]  G={gstruct}  iid={iid[:8]}")
                continue
            dt = time.time() - t

            con.execute(
                """
                UPDATE bb_instances
                   SET d_exact = ?, d_method = ?, updated_at = now()
                 WHERE instance_id = ?
                """,
                [distance, "sat-cadical@1.9.5 (pysat)", iid],
            )
            n_done += 1
            click.echo(
                f"  OK      [[{n_q},{k_q},{distance}]]  G={gstruct}  ({dt:5.1f}s)"
            )
        click.echo(f"\n  done: {n_done} solved, {n_timeout} timed out")


def _sat_d_worker(H_X, H_Z) -> int:
    """Top-level worker so multiprocessing can pickle it."""
    from .checks import CheckMatrices
    from .group import AbelianGroup
    import numpy as np
    n_qubits = H_X.shape[1]
    # We don't have the AbelianGroup back here, but x_distance only
    # uses its cardinality (via checks.num_qubits) and shape — so build
    # a stub CheckMatrices with a placeholder group of the right size.
    stub_G = AbelianGroup((n_qubits // 2,))  # rank-1 group of right cardinality
    cm = CheckMatrices(
        group=stub_G,
        H_X=np.ascontiguousarray(H_X, dtype=np.uint8),
        H_Z=np.ascontiguousarray(H_Z, dtype=np.uint8),
    )
    from .sat_distance import x_distance
    return x_distance(cm).distance


@main.command(name="verify-cert")
@click.argument("cert_path", type=click.Path(exists=True, path_type=Path))
@click.option(
    "--instances",
    type=click.Path(exists=True, path_type=Path),
    default=None,
    help="Path to instances YAML for code_id lookup (default: instances/bravyi_table.yaml).",
)
@click.option(
    "--drat-trim",
    default=None,
    help="Path to drat-trim binary (default: searches PATH, then /tmp/drat-trim/drat-trim).",
)
@click.option(
    "--emit-lrat/--no-emit-lrat",
    default=False,
    help="Also emit LRAT files (via drat-trim -L) alongside each DRAT — "
         "the format a Lean LRAT consumer ultimately wants.",
)
def verify_cert(cert_path: Path, instances: Path | None, drat_trim: str | None, emit_lrat: bool) -> None:
    """Independently re-verify a distance certificate.

    This is the user-facing version of "fully validate the certificate"
    that the eventual Lean LRAT consumer will mirror inside the kernel.
    Re-derives H_check / L_logical from the code's (G, A, B), checks the
    stored hashes match, validates the witness, and runs drat-trim on
    every recorded UNSAT proof.
    """
    import shutil
    import subprocess as _sp
    from .certificate import read_certificate, verify_certificate
    from .certificate import _matrix_hash, _file_hash
    from .checks import bb_check_matrices
    from .sat_distance import find_logical_z

    cert = read_certificate(cert_path)
    cert_dir = cert_path.parent

    instances = instances or INSTANCES_YAML
    rows = yaml.safe_load(instances.read_text())["instances"]
    row = next((r for r in rows if r["code_id"] == cert.code_id), None)
    if row is None:
        raise click.ClickException(
            f"code_id {cert.code_id!r} not in {instances} — "
            "pass --instances <path> to point at the right table"
        )

    G = ZmZn(row["group"]["ell"], row["group"]["m"])
    A = Poly.from_string(row["polynomials"]["A"], G)
    B = Poly.from_string(row["polynomials"]["B"], G)
    checks = bb_check_matrices(A, B)
    L_Z = find_logical_z(checks)

    # 1) Hashes must agree — the certificate is *about* this code.
    h_check_h = _matrix_hash(checks.H_Z)
    l_logical_h = _matrix_hash(L_Z)
    click.echo(f"certificate code_id     {cert.code_id}")
    click.echo(f"claimed distance        {cert.distance}")
    if h_check_h != cert.h_check_sha256:
        raise click.ClickException(
            f"H_check hash mismatch: cert claims {cert.h_check_sha256[:16]}…, "
            f"recomputed {h_check_h[:16]}…. This certificate is for a different code."
        )
    if l_logical_h != cert.l_logical_sha256:
        raise click.ClickException(
            f"L_logical hash mismatch: cert claims {cert.l_logical_sha256[:16]}…, "
            f"recomputed {l_logical_h[:16]}…"
        )
    click.echo("matrix hashes           OK")

    # 2) Witness validity — independent re-check.
    verify_certificate(cert, checks.H_Z, L_Z)
    click.echo(f"witness (w={cert.distance}) valid    OK")

    # 3) UNSAT proofs — re-hash and run drat-trim.
    drat_trim_path = (
        drat_trim
        or shutil.which("drat-trim")
        or "/tmp/drat-trim/drat-trim"
    )
    if not Path(drat_trim_path).exists():
        click.echo("drat-trim binary NOT FOUND; skipping DRAT verification")
        return

    n_pass = 0
    for ref in sorted(cert.unsat_proofs, key=lambda r: r.weight_bound):
        drat = cert_dir / ref.drat_path
        cnf = cert_dir / ref.cnf_path
        if not drat.exists() or not cnf.exists():
            click.echo(f"  w={ref.weight_bound:3d}  MISSING  {drat.name} or {cnf.name}")
            continue
        if _file_hash(drat) != ref.drat_sha256:
            click.echo(f"  w={ref.weight_bound:3d}  HASH-DRIFT (drat sha256 changed)")
            continue
        if _file_hash(cnf) != ref.cnf_sha256:
            click.echo(f"  w={ref.weight_bound:3d}  HASH-DRIFT (cnf sha256 changed)")
            continue
        cmd = [drat_trim_path, str(cnf), str(drat)]
        if emit_lrat:
            lrat = drat.with_suffix(".lrat")
            cmd.extend(["-L", str(lrat)])
        proc = _sp.run(cmd, capture_output=True, text=True, timeout=600)
        if "s VERIFIED" in proc.stdout and "s NOT VERIFIED" not in proc.stdout:
            extra = ""
            if emit_lrat:
                lrat = drat.with_suffix(".lrat")
                extra = f"  +lrat {lrat.stat().st_size/1024:.1f} KB"
            click.echo(f"  w={ref.weight_bound:3d}  VERIFIED  ({drat.stat().st_size/1024:8.1f} KB){extra}")
            n_pass += 1
        else:
            click.echo(f"  w={ref.weight_bound:3d}  REJECTED:\n{proc.stdout[-1000:]}")

    click.echo(f"drat-trim verifications PASS  {n_pass}/{len(cert.unsat_proofs)}")
    if n_pass == len(cert.unsat_proofs):
        click.echo(
            f"\n{cert.code_id}: distance ≥ {cert.distance} (DRAT-verified at every w<{cert.distance})\n"
            f"{cert.code_id}: distance ≤ {cert.distance} (witness of weight {cert.distance})\n"
            f"=> d_{cert.direction}({cert.code_id}) = {cert.distance}"
        )


if __name__ == "__main__":
    main()
