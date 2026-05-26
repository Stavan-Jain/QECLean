"""Read-only query interface for the BB corpus DuckDB.

A thin layer on top of `data/bb_instances.duckdb` for Tier-2 conjecture
work. Construct a `Corpus` once, chain `.filter(...)` calls to narrow
down the rows, then materialise via `.fetchall()`, `.to_arrow()`,
`.to_pandas()`, `.column(name)`, or `.count()`.

Read-only by design: opens the DB with `read_only=True`, so it can run
concurrently with a long `bb-lab fill-distances` or `enumerate` writer
without deadlocking on the workspace lock (see HANDOFF.md §6d).

Example::

    from bb_lab.corpus import Corpus

    corpus = Corpus()
    # All instances with d ≤ 8 and k ≥ 4, on Z_3 × Z_6 specifically:
    rows = (
        corpus
        .filter(group_struct="Z3xZ6", d_exact_lte=8, k_gte=4)
        .order_by("d_exact", "n")
        .fetchall()
    )
    # Or pull a single column for plotting / fitting:
    d_arr = corpus.filter(d_exact_lte=8).column("d_exact")
"""

from __future__ import annotations

from dataclasses import dataclass, field, replace
from pathlib import Path
from typing import Any, Iterator

import duckdb

DEFAULT_DB = Path(__file__).resolve().parent.parent.parent / "data" / "bb_instances.duckdb"


# Mapping of filter kwarg → SQL fragment. Each filter is a (column, op) pair.
# `_gte`/`_lte`/`_gt`/`_lt`/`_in` suffixes map to ≥, ≤, >, <, IN.  Bare names
# map to equality.
_OP_SUFFIX = {
    "_gte": ">=",
    "_lte": "<=",
    "_gt":  ">",
    "_lt":  "<",
    "_in":  "IN",
    "_is_null": "IS NULL",
    "_is_not_null": "IS NOT NULL",
}


def _parse_filter(kwarg: str) -> tuple[str, str]:
    """Return (column, sql_op) for a filter kwarg like `d_exact_lte`."""
    for suffix, op in _OP_SUFFIX.items():
        if kwarg.endswith(suffix):
            return kwarg[: -len(suffix)], op
    return kwarg, "="


@dataclass(frozen=True, slots=True)
class _Predicate:
    column: str
    op: str
    value: Any


@dataclass(frozen=True, slots=True)
class Corpus:
    """Chainable, read-only view over `bb_instances`."""

    db_path: Path = DEFAULT_DB
    predicates: tuple[_Predicate, ...] = field(default_factory=tuple)
    order: tuple[str, ...] = field(default_factory=tuple)
    limit: int | None = None

    # --- chaining -----------------------------------------------------------

    def filter(self, **kwargs: Any) -> "Corpus":
        """Return a new Corpus with extra predicates AND-ed in.

        Recognised kwarg suffixes:
          * ``_gte`` / ``_lte`` / ``_gt`` / ``_lt`` — numeric inequalities
          * ``_in``  — value is an iterable; emits ``col IN (?, ?, …)``
          * ``_is_null`` / ``_is_not_null`` — boolean; value ignored
          * bare name — equality (e.g. ``group_struct="Z3xZ6"``)
        """
        new_preds = list(self.predicates)
        for kwarg, value in kwargs.items():
            col, op = _parse_filter(kwarg)
            new_preds.append(_Predicate(col, op, value))
        return replace(self, predicates=tuple(new_preds))

    def order_by(self, *cols: str) -> "Corpus":
        """Return a new Corpus with ORDER BY appended (later calls override)."""
        return replace(self, order=tuple(cols))

    def limited(self, n: int) -> "Corpus":
        """Return a new Corpus with LIMIT clamp."""
        return replace(self, limit=int(n))

    # --- query construction -------------------------------------------------

    def _build_query(
        self, select: str = "*", *, suppress_order: bool = False,
    ) -> tuple[str, list[Any]]:
        where_parts: list[str] = []
        params: list[Any] = []
        for p in self.predicates:
            if p.op in ("IS NULL", "IS NOT NULL"):
                where_parts.append(f"{p.column} {p.op}")
            elif p.op == "IN":
                vals = list(p.value)
                if not vals:
                    where_parts.append("1 = 0")  # empty IN → false
                else:
                    where_parts.append(
                        f"{p.column} IN ({', '.join('?' for _ in vals)})"
                    )
                    params.extend(vals)
            else:
                where_parts.append(f"{p.column} {p.op} ?")
                params.append(p.value)
        sql = f"SELECT {select} FROM bb_instances"
        if where_parts:
            sql += " WHERE " + " AND ".join(where_parts)
        if self.order and not suppress_order:
            sql += " ORDER BY " + ", ".join(self.order)
        if self.limit is not None:
            sql += f" LIMIT {self.limit}"
        return sql, params

    def _connect(self) -> duckdb.DuckDBPyConnection:
        if not self.db_path.exists():
            raise FileNotFoundError(
                f"corpus DB {self.db_path} does not exist; "
                "run `bb-lab enumerate` first"
            )
        return duckdb.connect(str(self.db_path), read_only=True)

    # --- terminal methods ---------------------------------------------------

    def count(self) -> int:
        """Number of rows matching the current filters (capped by `limit`
        if set). DuckDB rejects ORDER BY on aggregate-only selects, so
        we wrap in a subquery whenever a LIMIT is in play."""
        if self.limit is not None:
            inner_sql, params = self._build_query(select="instance_id")
            sql = f"SELECT COUNT(*) FROM ({inner_sql})"
        else:
            sql, params = self._build_query(
                select="COUNT(*)", suppress_order=True,
            )
        with self._connect() as con:
            return int(con.execute(sql, params).fetchone()[0])

    def fetchall(self) -> list[tuple]:
        """Return all rows as a list of tuples (column order: see `columns()`)."""
        sql, params = self._build_query()
        with self._connect() as con:
            return con.execute(sql, params).fetchall()

    def fetchone(self) -> tuple | None:
        sql, params = self._build_query()
        with self._connect() as con:
            return con.execute(sql, params).fetchone()

    def column(self, name: str) -> "list[Any]":
        sql, params = self._build_query(select=name)
        with self._connect() as con:
            return [r[0] for r in con.execute(sql, params).fetchall()]

    def columns(self) -> list[str]:
        """Return the column names of `bb_instances` (full schema)."""
        with self._connect() as con:
            return [
                r[0] for r in con.execute(
                    "SELECT column_name FROM information_schema.columns "
                    "WHERE table_name = 'bb_instances' ORDER BY ordinal_position"
                ).fetchall()
            ]

    def __iter__(self) -> Iterator[dict[str, Any]]:
        """Iterate as dicts (one per row, column-named)."""
        cols = self.columns()
        for row in self.fetchall():
            yield dict(zip(cols, row))

    def to_arrow(self):
        """Materialise as a pyarrow.Table. Requires pyarrow (already a
        bb_lab dependency)."""
        sql, params = self._build_query()
        with self._connect() as con:
            return con.execute(sql, params).to_arrow_table()

    def to_pandas(self):
        """Materialise as a pandas.DataFrame. pandas is *not* a hard
        dependency of bb_lab; install separately if you want this."""
        try:
            import pandas as _pd  # noqa: F401
        except ImportError as e:
            raise RuntimeError(
                "pandas is not installed; run `uv pip install pandas` "
                "in the bb_lab venv, or use `to_arrow()`."
            ) from e
        return self.to_arrow().to_pandas()

    # --- summary helpers ----------------------------------------------------

    def summary(self) -> dict[str, Any]:
        """Quick statistics over the current filtered view."""
        sql, params = self._build_query(
            "COUNT(*), MIN(n), MAX(n), MIN(k), MAX(k), "
            "MIN(d_exact), MAX(d_exact), "
            "COUNT(d_exact), COUNT(d_ub), "
            "COUNT(DISTINCT group_struct)"
        )
        with self._connect() as con:
            row = con.execute(sql, params).fetchone()
        return {
            "n_rows": int(row[0]),
            "n_range": (row[1], row[2]) if row[0] > 0 else None,
            "k_range": (row[3], row[4]) if row[0] > 0 else None,
            "d_exact_range": (row[5], row[6]),
            "n_with_d_exact": int(row[7]),
            "n_with_d_ub": int(row[8]),
            "n_distinct_groups": int(row[9]),
        }

    def groupby_counts(self, column: str) -> list[tuple[Any, int]]:
        """Return ``[(value, count)]`` rows ordered by descending count."""
        sql, params = self._build_query(
            select=f"{column}, COUNT(*) AS c"
        )
        sql += f" GROUP BY {column} ORDER BY c DESC, {column}"
        # The inner _build_query already appended ORDER BY / LIMIT if
        # set, but we wanted ours instead — re-build directly here.
        # Re-issue without inherited order/limit by clearing them.
        new = replace(self, order=(), limit=None)
        sql, params = new._build_query(select=f"{column}, COUNT(*) AS c")
        sql += f" GROUP BY {column} ORDER BY c DESC, {column}"
        with self._connect() as con:
            return list(con.execute(sql, params).fetchall())
