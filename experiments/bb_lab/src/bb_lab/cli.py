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
def enumerate_cmd() -> None:
    """Canonical-form enumeration over BB instances (v1; not in v0)."""
    raise NotImplementedError(
        "enumerate is part of v1 (canonical-form deduper + weight-bounded "
        "enumeration). v0 only validates the substrate against the Bravyi "
        "table; run `bb-lab bravyi-check` instead."
    )


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
