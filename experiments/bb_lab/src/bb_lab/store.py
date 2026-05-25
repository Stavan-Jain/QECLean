"""DuckDB store for BB code instances.

Single table `bb_instances`, single file `data/bb_instances.duckdb`
(gitignored). v0 only fills `(code_id, group, n, k, d_exact)` for the
five Bravyi rows; feature columns are placeholders for v1.
"""

from __future__ import annotations

import datetime as _dt
import hashlib
import json
from contextlib import contextmanager
from dataclasses import dataclass
from pathlib import Path
from typing import Iterator

import duckdb


DEFAULT_DB = Path("data") / "bb_instances.duckdb"


SCHEMA_SQL = """
CREATE TABLE IF NOT EXISTS bb_instances (
  instance_id           TEXT PRIMARY KEY,
  code_id               TEXT,
  group_struct          TEXT,
  ell                   INTEGER,
  m                     INTEGER,
  n                     INTEGER,
  k                     INTEGER,
  A_poly                TEXT,
  B_poly                TEXT,
  A_weight              INTEGER,
  B_weight              INTEGER,
  rank_HX               INTEGER,
  rank_HZ               INTEGER,
  dim_ker_A             INTEGER,
  dim_ker_B             INTEGER,
  orbit_size            INTEGER,
  tanner_girth          INTEGER,
  supp_diameter_A       INTEGER,
  supp_diameter_B       INTEGER,
  d_lb                  INTEGER,
  d_ub                  INTEGER,
  d_exact               INTEGER,
  d_method              TEXT,
  cert_path             TEXT,
  inserted_at           TIMESTAMP,
  updated_at            TIMESTAMP
);

CREATE INDEX IF NOT EXISTS idx_bb_group_struct ON bb_instances(group_struct);
CREATE INDEX IF NOT EXISTS idx_bb_n_k        ON bb_instances(n, k);
"""


@dataclass(frozen=True, slots=True)
class StoredInstance:
    instance_id: str
    code_id: str
    group_struct: str
    ell: int
    m: int
    n: int
    k: int
    A_poly: str
    B_poly: str
    A_weight: int
    B_weight: int
    rank_HX: int | None = None
    rank_HZ: int | None = None
    dim_ker_A: int | None = None
    dim_ker_B: int | None = None
    orbit_size: int | None = None
    d_lb: int | None = None
    d_ub: int | None = None
    d_exact: int | None = None
    d_method: str | None = None
    cert_path: str | None = None


def canonical_hash(group_struct: str, A_poly: str, B_poly: str) -> str:
    """Deterministic ID over (group, canonical A, canonical B). Same
    structure is used by `lean_bridge.BBDescriptor`; instances with
    distinct canonical strings get distinct IDs."""
    payload = json.dumps(
        {"g": group_struct, "A": A_poly, "B": B_poly},
        sort_keys=True,
    ).encode()
    return hashlib.sha256(payload).hexdigest()[:16]


@contextmanager
def connect(db_path: str | Path = DEFAULT_DB) -> Iterator[duckdb.DuckDBPyConnection]:
    """Open (and lazily create) the DuckDB store."""
    p = Path(db_path)
    p.parent.mkdir(parents=True, exist_ok=True)
    con = duckdb.connect(str(p))
    try:
        con.execute(SCHEMA_SQL)
        yield con
    finally:
        con.close()


def upsert_instance(con: duckdb.DuckDBPyConnection, inst: StoredInstance) -> None:
    """Insert or update `inst` keyed by `instance_id`.

    Distance fields (`d_lb`, `d_ub`, `d_exact`, `d_method`, `cert_path`)
    use COALESCE on conflict: a None passed in does NOT clobber an
    existing non-None value. This keeps `bb-lab enumerate` safe to re-
    run over a corpus that already has SAT distances filled in.
    Structural fields (group, n, k, polys, ranks) always get the new
    value on conflict.
    """
    now = _dt.datetime.now(_dt.UTC)
    con.execute(
        """
        INSERT INTO bb_instances (
          instance_id, code_id, group_struct, ell, m, n, k,
          A_poly, B_poly, A_weight, B_weight,
          rank_HX, rank_HZ, dim_ker_A, dim_ker_B, orbit_size,
          d_lb, d_ub, d_exact, d_method, cert_path,
          inserted_at, updated_at
        ) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
        ON CONFLICT (instance_id) DO UPDATE SET
          code_id      = excluded.code_id,
          group_struct = excluded.group_struct,
          ell          = excluded.ell,
          m            = excluded.m,
          n            = excluded.n,
          k            = excluded.k,
          A_poly       = excluded.A_poly,
          B_poly       = excluded.B_poly,
          A_weight     = excluded.A_weight,
          B_weight     = excluded.B_weight,
          rank_HX      = excluded.rank_HX,
          rank_HZ      = excluded.rank_HZ,
          dim_ker_A    = excluded.dim_ker_A,
          dim_ker_B    = excluded.dim_ker_B,
          orbit_size   = excluded.orbit_size,
          -- Distance fields: COALESCE preserves the existing value if
          -- the new row passes NULL. fill-distances passes non-NULL to
          -- update; enumerate passes NULL to avoid clobbering.
          d_lb         = COALESCE(excluded.d_lb, bb_instances.d_lb),
          d_ub         = COALESCE(excluded.d_ub, bb_instances.d_ub),
          d_exact      = COALESCE(excluded.d_exact, bb_instances.d_exact),
          d_method     = COALESCE(excluded.d_method, bb_instances.d_method),
          cert_path    = COALESCE(excluded.cert_path, bb_instances.cert_path),
          updated_at   = excluded.updated_at
        """,
        [
            inst.instance_id, inst.code_id, inst.group_struct,
            inst.ell, inst.m, inst.n, inst.k,
            inst.A_poly, inst.B_poly, inst.A_weight, inst.B_weight,
            inst.rank_HX, inst.rank_HZ, inst.dim_ker_A, inst.dim_ker_B, inst.orbit_size,
            inst.d_lb, inst.d_ub, inst.d_exact, inst.d_method, inst.cert_path,
            now, now,
        ],
    )


def mark_distance(
    con: duckdb.DuckDBPyConnection,
    instance_id: str,
    *,
    d_exact: int,
    d_method: str,
    cert_path: str | None = None,
) -> None:
    """Record the exact distance for an instance (and the method used)."""
    now = _dt.datetime.now(_dt.UTC)
    con.execute(
        """
        UPDATE bb_instances
           SET d_exact = ?, d_method = ?, cert_path = ?, updated_at = ?
         WHERE instance_id = ?
        """,
        [d_exact, d_method, cert_path, now, instance_id],
    )
