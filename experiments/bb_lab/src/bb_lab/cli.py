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


@main.command(name="fill-features")
@click.option("--db", type=click.Path(path_type=Path), default=None)
def fill_features(db: Path | None) -> None:
    """Compute combinatorial + algebraic features for every corpus
    instance lacking them: Tanner girth, support diameter, and
    `min_wt_ker_A` / `min_wt_ker_B` (minimum non-zero Hamming weight of
    the F₂-kernel of multiplication-by-A / B).  The last is the
    classical cyclic-code min distance — and the key BB-distance
    bound `d_X(BB(A,B)) ≤ min(min_wt_ker_A, min_wt_ker_B)`."""
    from .checks import bb_check_matrices, circulant
    from .features import tanner_girth, support_diameter, min_weight_in_kernel
    from .group import ZmZn
    from .poly import Poly
    from .store import connect
    import math

    db_path = db or (LAB_ROOT / "data" / "bb_instances.duckdb")
    with connect(db_path) as con:
        for col in (
            "tanner_girth", "supp_diameter_A", "supp_diameter_B",
            "min_wt_ker_A", "min_wt_ker_B",
        ):
            try:
                con.execute(f"ALTER TABLE bb_instances ADD COLUMN {col} INTEGER")
            except Exception:
                pass
        rows = con.execute(
            "SELECT instance_id, ell, m, A_poly, B_poly, dim_ker_A, dim_ker_B "
            "FROM bb_instances "
            "WHERE tanner_girth IS NULL OR min_wt_ker_A IS NULL"
        ).fetchall()
        click.echo(f"  filling features for {len(rows)} instances...")
        for iid, ell, m_, A_str, B_str, dim_kA, dim_kB in rows:
            G = ZmZn(ell, m_)
            A = Poly.from_string(A_str, G)
            B = Poly.from_string(B_str, G)
            checks = bb_check_matrices(A, B)
            g = tanner_girth(checks.H_X)
            g_int = -1 if g == math.inf else int(g)
            diam_A = support_diameter(A.support, G)
            diam_B = support_diameter(B.support, G)
            # Min-weight-in-ker: skip if dim too large (brute force is
            # exponential). For our corpus dim_ker ≤ 24.
            mw_A = min_weight_in_kernel(circulant(A)) if dim_kA <= 22 else None
            mw_B = min_weight_in_kernel(circulant(B)) if dim_kB <= 22 else None
            con.execute(
                """
                UPDATE bb_instances
                   SET tanner_girth = ?, supp_diameter_A = ?, supp_diameter_B = ?,
                       min_wt_ker_A = ?, min_wt_ker_B = ?, updated_at = now()
                 WHERE instance_id = ?
                """,
                [g_int, diam_A, diam_B, mw_A, mw_B, iid],
            )
        click.echo(f"  done.")


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


def _orbit_contains_no_swap(
    target_supp: frozenset, candidate_supp: frozenset, G, auts,
) -> bool:
    """Return True iff `target_supp` is in the orbit of `candidate_supp`
    under translations + automorphisms ALONE (block-swap excluded).

    Used to detect, after a `canonical_pair` migration, whether the new
    A-poly's support comes from the old A-poly's orbit (no swap) or
    from the old B-poly's orbit (swap happened — the A/B-asymmetric
    fields then need transposition).
    """
    for phi in auts:
        phi_supp = phi.apply_support(candidate_supp)
        for h in G:
            shifted = frozenset(G.add(g, h) for g in phi_supp)
            if shifted == target_supp:
                return True
    return False


@main.command(name="migrate-canonical-ids")
@click.option(
    "--db", type=click.Path(path_type=Path), default=None,
    help="DuckDB store path (default: data/bb_instances.duckdb).",
)
@click.option(
    "--dry-run/--apply", default=True,
    help="By default just report what would change; pass --apply to commit the UPDATEs.",
)
def migrate_canonical_ids(db: Path | None, dry_run: bool) -> None:
    """Recompute every row's `instance_id`, `A_poly`, `B_poly` using the
    current `canonical_pair` rule.

    Needed after the canonical-form lex order changes (e.g. the Move 1
    bitset rewrite, which picks a different orbit representative
    within each equivalence class). When the new canonical rep is
    block-swapped relative to the old, the A/B-asymmetric feature
    columns (`dim_ker_A` ↔ `dim_ker_B`, `supp_diameter_A` ↔ `…_B`,
    `min_wt_ker_A` ↔ `min_wt_ker_B`, `A_weight` ↔ `B_weight`) are
    transposed in the same UPDATE. Idempotent: rows already in the
    current canonical form are no-ops. Use `--apply` to commit.
    """
    from collections import defaultdict
    from .automorphism import automorphisms
    from .canonical import build_perm_table, canonical_pair
    from .group import ZmZn
    from .poly import Poly
    from .store import canonical_hash, connect

    db_path = db or (LAB_ROOT / "data" / "bb_instances.duckdb")
    if not db_path.exists():
        raise click.ClickException(f"corpus DB {db_path} not found")

    # Cache automorphism + permutation tables per (ell, m) so we pay
    # the build cost once per group instead of once per row.
    perm_cache: dict[tuple[int, int], tuple] = {}

    def get_group_data(ell: int, m_: int):
        key = (ell, m_)
        if key not in perm_cache:
            G = ZmZn(ell, m_)
            auts = automorphisms(G)
            perm_cache[key] = (G, auts, build_perm_table(G, auts=auts))
        return perm_cache[key]

    n_total = 0
    n_changed = 0
    n_swapped = 0
    n_collisions = 0
    by_group: dict[str, list[int]] = defaultdict(lambda: [0, 0])  # [seen, changed]

    with connect(db_path) as con:
        rows = con.execute(
            "SELECT instance_id, group_struct, ell, m, A_poly, B_poly FROM bb_instances"
        ).fetchall()
        click.echo(f"  scanning {len(rows)} rows...")

        # First pass: compute (old_id, new_id, new_A, new_B, swapped)
        # tuples; detect collisions before applying any UPDATE.
        updates: list[tuple[str, str, str, str, bool]] = []
        new_ids_seen: set[str] = set()
        for iid, gstruct, ell, m_, A_str, B_str in rows:
            n_total += 1
            by_group[gstruct][0] += 1
            G, auts, perms = get_group_data(ell, m_)
            A = Poly.from_string(A_str, G)
            B = Poly.from_string(B_str, G)
            canon = canonical_pair(A.support, B.support, G, perms=perms)
            new_A_supp = frozenset(canon.A_support)
            new_B_supp = frozenset(canon.B_support)
            new_A_str = Poly(support=new_A_supp, group=G).canonical_string()
            new_B_str = Poly(support=new_B_supp, group=G).canonical_string()
            new_id = canonical_hash(gstruct, new_A_str, new_B_str)
            if new_id == iid and new_A_str == A_str and new_B_str == B_str:
                continue
            # Detect whether the new canonical rep came from the swap
            # orientation: new_A is in the orbit of old A under
            # (aut × translation) alone iff no swap happened.
            no_swap = _orbit_contains_no_swap(new_A_supp, A.support, G, auts)
            swapped = not no_swap
            if swapped:
                n_swapped += 1
            if new_id in new_ids_seen:
                n_collisions += 1
                click.echo(
                    f"  COLLISION  old={iid[:8]} → new={new_id[:8]} "
                    f"(already claimed by another row in {gstruct})"
                )
                continue
            new_ids_seen.add(new_id)
            updates.append((iid, new_id, new_A_str, new_B_str, swapped))
            n_changed += 1
            by_group[gstruct][1] += 1

        click.echo(
            f"\n  summary: {n_total} rows scanned, "
            f"{n_changed} need updates ({n_swapped} via block-swap), "
            f"{n_collisions} collisions"
        )
        for gstruct in sorted(by_group):
            seen, changed = by_group[gstruct]
            click.echo(f"    {gstruct:10s}  {seen:4d} seen  {changed:4d} changed")

        if n_collisions > 0:
            raise click.ClickException(
                "collisions detected; aborting before any UPDATE. "
                "This means two orbit-distinct rows are mapping to the same "
                "new canonical hash, which should not happen — investigate."
            )

        if dry_run:
            click.echo("\n  --dry-run (default); pass --apply to commit the UPDATEs")
            return

        if not updates:
            click.echo("\n  nothing to do (DB already in current canonical form).")
            return

        # Detect which A/B-paired feature columns actually exist (some
        # are added by `bb-lab fill-features` and may not be present
        # in a v0-only DB).
        feat_cols = {
            r[0] for r in con.execute(
                "SELECT column_name FROM information_schema.columns "
                "WHERE table_name = 'bb_instances'"
            ).fetchall()
        }
        swap_pairs = [
            ("dim_ker_A", "dim_ker_B"),
            ("A_weight", "B_weight"),
            ("supp_diameter_A", "supp_diameter_B"),
            ("min_wt_ker_A", "min_wt_ker_B"),
        ]
        active_pairs = [(a, b) for (a, b) in swap_pairs if a in feat_cols and b in feat_cols]
        swap_set_clause = ", ".join(
            f"{a} = old.{b}, {b} = old.{a}" for (a, b) in active_pairs
        )

        for old_id, new_id, new_A, new_B, swapped in updates:
            if swapped and active_pairs:
                # Two-step UPDATE: capture the old A/B-paired values, then
                # swap them as we write the new id + polys.
                old_vals = con.execute(
                    f"SELECT {', '.join(c for pair in active_pairs for c in pair)} "
                    f"FROM bb_instances WHERE instance_id = ?",
                    [old_id],
                ).fetchone()
                set_pieces = [
                    "instance_id = ?", "A_poly = ?", "B_poly = ?", "updated_at = now()",
                ]
                params: list[object] = [new_id, new_A, new_B]
                for (a_col, b_col), (a_val, b_val) in zip(
                    active_pairs, [tuple(old_vals[i:i+2]) for i in range(0, len(old_vals), 2)],
                ):
                    set_pieces.append(f"{a_col} = ?")
                    params.append(b_val)
                    set_pieces.append(f"{b_col} = ?")
                    params.append(a_val)
                params.append(old_id)
                con.execute(
                    f"UPDATE bb_instances SET {', '.join(set_pieces)} WHERE instance_id = ?",
                    params,
                )
            else:
                con.execute(
                    """
                    UPDATE bb_instances
                       SET instance_id = ?, A_poly = ?, B_poly = ?, updated_at = now()
                     WHERE instance_id = ?
                    """,
                    [new_id, new_A, new_B, old_id],
                )
        click.echo(f"\n  applied {len(updates)} UPDATEs ({n_swapped} with A/B field swap).")


if __name__ == "__main__":
    main()
