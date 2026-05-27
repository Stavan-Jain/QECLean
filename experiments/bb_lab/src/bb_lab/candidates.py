"""Persistent candidate registry for the round-2 conjecture mill.

Stores every proposed distance bound as a queryable row, replacing the
prose-in-`notes/*.md` pattern that made round-1 lineage reconstruction
expensive. Each candidate carries its Tier-0 classification, optional
Tier-2/3 statistics, and a lineage link (`parent_id`) so attempt
histories can be walked with one SQL query.

Workflow:

    from bb_lab.candidates import CandidateRegistry, Status
    from bb_lab.obstructions import classify, LIN_PRYADKO_STMT_12

    reg = CandidateRegistry()                                  # default DB path
    rec = reg.register(c, classify(c))                         # Tier 0 done
    reg.update_status(c.id, Status.TIER2_RUNNING)              # state machine
    reg.attach_stats(c.id, corpus_stats={"tight": 4, ...})     # Tier 2 result
    reg.update_status(c.id, Status.TIER3_RUNNING)
    reg.update_status(c.id, Status.SURVIVED)                   # Tier 3 verdict
    reg.lineage(c.id)                                          # ancestry walk

The DB is separate from `bb_instances.duckdb` (the corpus) to avoid
write-lock contention during long-running corpus enumeration. Cross-DB
joins on `falsifier_id` are doable via `ATTACH` if needed.

See `HANDOFF_R2.md` §11 for the schema rationale and §3 for the wider
architecture.
"""

from __future__ import annotations

import datetime as _dt
import json
from contextlib import contextmanager
from dataclasses import dataclass
from enum import Enum
from pathlib import Path
from typing import Any, Iterator

import duckdb

from .obstructions import Candidate, Classification, Verdict


DEFAULT_DB = (
    Path(__file__).resolve().parent.parent.parent / "data" / "bb_candidates.duckdb"
)


class Status(str, Enum):
    """Lifecycle status of a candidate.

    Two terminal states (SHELVED, FORMALIZED); transitions are
    constrained by `_VALID_TRANSITIONS` to prevent illegal jumps
    (e.g. CLASSIFIED → FORMALIZED skipping Tier 2/3).
    """

    PROPOSED = "proposed"
    """Newly drafted; not yet classified. Rarely used in practice
    because `register()` always classifies."""

    CLASSIFIED = "classified"
    """Passed Tier 0 with verdict PROCEED; awaiting Tier 2 evaluation."""

    RESEARCH_SEED = "research-seed"
    """Tier 0 verdict NEEDS-NEW-THEORY. Tagged for future work when
    the underlying mathematics becomes available."""

    TIER2_RUNNING = "tier2-running"
    """Currently being evaluated on the corpus / by the conjecture mill."""

    TIER3_RUNNING = "tier3-running"
    """Passed Tier 2; running the three Tier-3 batteries."""

    SHELVED = "shelved"
    """Terminal. Falsified at some tier, or SHELVED-A-PRIORI by Tier 0."""

    SURVIVED = "survived"
    """Passed all Tier-3 batteries. Eligible for Tier-4 (Lean) formalization."""

    FORMALIZED = "formalized"
    """Terminal. Lean proof landed on `BBChainComplex`."""


_VALID_TRANSITIONS: dict[Status, frozenset[Status]] = {
    Status.PROPOSED: frozenset({Status.CLASSIFIED, Status.SHELVED, Status.RESEARCH_SEED}),
    Status.CLASSIFIED: frozenset({Status.TIER2_RUNNING, Status.SHELVED}),
    Status.RESEARCH_SEED: frozenset({Status.CLASSIFIED, Status.SHELVED}),
    Status.TIER2_RUNNING: frozenset({Status.TIER3_RUNNING, Status.SHELVED}),
    Status.TIER3_RUNNING: frozenset({Status.SURVIVED, Status.SHELVED}),
    Status.SURVIVED: frozenset({Status.FORMALIZED, Status.SHELVED}),
    Status.SHELVED: frozenset(),
    Status.FORMALIZED: frozenset(),
}


SCHEMA_SQL = """
CREATE TABLE IF NOT EXISTS bb_candidates (
    candidate_id            TEXT PRIMARY KEY,
    name                    TEXT NOT NULL,
    family                  TEXT NOT NULL,
    rhs_type                TEXT NOT NULL,
    bound_formula           TEXT,
    citation                TEXT,
    parent_id               TEXT,
    source_paper            TEXT,
    generation_method       TEXT,
    requires_non_degenerate BOOLEAN DEFAULT FALSE,
    requires_semisimple     BOOLEAN DEFAULT FALSE,
    requires_cover_coprime  BOOLEAN DEFAULT FALSE,
    needs_new_theory        BOOLEAN DEFAULT FALSE,
    hypothesis_predicates   TEXT,    -- JSON object
    obstructions_hit        TEXT,    -- JSON array of obstruction IDs
    bravyi_blast_radius     TEXT,    -- JSON array of "<obs_id>@<instance_id>"
    tier0_verdict           TEXT,
    tier0_reasoning         TEXT,    -- JSON array
    corpus_stats_json       TEXT,    -- JSON object: tight/loose/violations breakdown
    adversarial_stats_json  TEXT,    -- JSON object: per-attack-mode results
    status                  TEXT NOT NULL DEFAULT 'proposed',
    falsifier_id            TEXT,    -- instance_id from bb_instances (or generated)
    created_at              TIMESTAMP,
    updated_at              TIMESTAMP
);

CREATE INDEX IF NOT EXISTS idx_candidates_family   ON bb_candidates(family);
CREATE INDEX IF NOT EXISTS idx_candidates_status   ON bb_candidates(status);
CREATE INDEX IF NOT EXISTS idx_candidates_parent   ON bb_candidates(parent_id);
CREATE INDEX IF NOT EXISTS idx_candidates_rhs_type ON bb_candidates(rhs_type);
"""


@dataclass(frozen=True, slots=True)
class CandidateRecord:
    """A row of `bb_candidates`, fully hydrated.

    Equality is structural; two records with the same fields compare
    equal. JSON-typed columns (`hypothesis_predicates`, stats,
    `obstructions_hit`) are deserialized into Python containers on
    read, so callers don't see raw JSON strings.
    """

    candidate_id: str
    name: str
    family: str
    rhs_type: str
    bound_formula: str
    citation: str
    parent_id: str | None
    source_paper: str | None
    generation_method: str
    requires_non_degenerate: bool
    requires_semisimple: bool
    requires_cover_coprime: bool
    needs_new_theory: bool
    hypothesis_predicates: dict[str, Any] | None
    obstructions_hit: tuple[str, ...]
    bravyi_blast_radius: tuple[str, ...]
    tier0_verdict: str
    tier0_reasoning: tuple[str, ...]
    corpus_stats: dict[str, Any] | None
    adversarial_stats: dict[str, Any] | None
    status: str
    falsifier_id: str | None
    created_at: str | None
    updated_at: str | None


def _initial_status_from_verdict(verdict: Verdict) -> Status:
    if verdict == Verdict.SHELVED_A_PRIORI:
        return Status.SHELVED
    if verdict == Verdict.NEEDS_NEW_THEORY:
        return Status.RESEARCH_SEED
    return Status.CLASSIFIED


def _dumps_or_none(value: Any) -> str | None:
    return json.dumps(value) if value is not None else None


def _loads_or_none(value: str | None) -> Any:
    return json.loads(value) if value else None


def _tuple_from_json(value: str | None) -> tuple[str, ...]:
    if not value:
        return ()
    parsed = json.loads(value)
    return tuple(parsed) if parsed else ()


def _row_to_record(columns: list[str], row: tuple[Any, ...]) -> CandidateRecord:
    d = dict(zip(columns, row))
    return CandidateRecord(
        candidate_id=d["candidate_id"],
        name=d["name"],
        family=d["family"],
        rhs_type=d["rhs_type"],
        bound_formula=d.get("bound_formula") or "",
        citation=d.get("citation") or "",
        parent_id=d.get("parent_id"),
        source_paper=d.get("source_paper"),
        generation_method=d.get("generation_method") or "",
        requires_non_degenerate=bool(d.get("requires_non_degenerate")),
        requires_semisimple=bool(d.get("requires_semisimple")),
        requires_cover_coprime=bool(d.get("requires_cover_coprime")),
        needs_new_theory=bool(d.get("needs_new_theory")),
        hypothesis_predicates=_loads_or_none(d.get("hypothesis_predicates")),
        obstructions_hit=_tuple_from_json(d.get("obstructions_hit")),
        bravyi_blast_radius=_tuple_from_json(d.get("bravyi_blast_radius")),
        tier0_verdict=d.get("tier0_verdict") or "",
        tier0_reasoning=_tuple_from_json(d.get("tier0_reasoning")),
        corpus_stats=_loads_or_none(d.get("corpus_stats_json")),
        adversarial_stats=_loads_or_none(d.get("adversarial_stats_json")),
        status=d["status"],
        falsifier_id=d.get("falsifier_id"),
        created_at=str(d["created_at"]) if d.get("created_at") else None,
        updated_at=str(d["updated_at"]) if d.get("updated_at") else None,
    )


class CandidateRegistry:
    """Persistent registry of conjecture candidates.

    Thread-unsafe (relies on DuckDB's single-writer model). Opens a
    fresh connection per call; safe to share an instance across
    sequential operations.
    """

    def __init__(self, db_path: str | Path = DEFAULT_DB) -> None:
        self.db_path = Path(db_path)
        self.db_path.parent.mkdir(parents=True, exist_ok=True)
        with self._connect() as con:
            con.execute(SCHEMA_SQL)

    @contextmanager
    def _connect(self, *, read_only: bool = False) -> Iterator[duckdb.DuckDBPyConnection]:
        con = duckdb.connect(str(self.db_path), read_only=read_only)
        try:
            yield con
        finally:
            con.close()

    # --- write operations ----------------------------------------------------

    def register(
        self,
        candidate: Candidate,
        classification: Classification,
        *,
        parent_id: str | None = None,
        source_paper: str | None = None,
        generation_method: str = "",
        hypothesis_predicates: dict[str, Any] | None = None,
    ) -> CandidateRecord:
        """Insert a new candidate with its Tier-0 classification.

        Initial status is derived from `classification.verdict`:

        * `PROCEED` → `CLASSIFIED` (ready for Tier 2)
        * `SHELVED_A_PRIORI` → `SHELVED` (terminal)
        * `NEEDS_NEW_THEORY` → `RESEARCH_SEED`

        Raises if `candidate.id` is already registered.
        """
        status = _initial_status_from_verdict(classification.verdict)
        now = _dt.datetime.now(_dt.UTC)
        with self._connect() as con:
            con.execute(
                """
                INSERT INTO bb_candidates (
                    candidate_id, name, family, rhs_type, bound_formula, citation,
                    parent_id, source_paper, generation_method,
                    requires_non_degenerate, requires_semisimple,
                    requires_cover_coprime, needs_new_theory,
                    hypothesis_predicates,
                    obstructions_hit, bravyi_blast_radius,
                    tier0_verdict, tier0_reasoning,
                    corpus_stats_json, adversarial_stats_json,
                    status, falsifier_id,
                    created_at, updated_at
                ) VALUES (
                    ?, ?, ?, ?, ?, ?,
                    ?, ?, ?,
                    ?, ?, ?, ?,
                    ?,
                    ?, ?,
                    ?, ?,
                    ?, ?,
                    ?, ?,
                    ?, ?
                )
                """,
                [
                    candidate.id,
                    candidate.name,
                    candidate.family.value,
                    candidate.rhs_type.value,
                    candidate.bound_formula,
                    candidate.citation,
                    parent_id,
                    source_paper,
                    generation_method,
                    candidate.requires_non_degenerate,
                    candidate.requires_semisimple,
                    candidate.requires_cover_coprime,
                    candidate.needs_new_theory,
                    _dumps_or_none(hypothesis_predicates),
                    _dumps_or_none(list(classification.obstructions_hit)),
                    _dumps_or_none(list(classification.bravyi_blast_radius)),
                    classification.verdict.value,
                    _dumps_or_none(list(classification.reasoning)),
                    None,  # corpus_stats_json
                    None,  # adversarial_stats_json
                    status.value,
                    None,  # falsifier_id
                    now,
                    now,
                ],
            )
        record = self.get(candidate.id)
        assert record is not None, "row missing after insert"
        return record

    def update_status(
        self,
        candidate_id: str,
        new_status: Status,
        *,
        falsifier_id: str | None = None,
    ) -> CandidateRecord:
        """Transition a candidate to `new_status`, validating the state machine.

        Pass `falsifier_id` when transitioning to SHELVED with a known
        counterexample instance.

        Raises:
            KeyError if the candidate isn't registered.
            ValueError if the transition is not in `_VALID_TRANSITIONS`.
        """
        current = self.get(candidate_id)
        if current is None:
            raise KeyError(f"candidate {candidate_id!r} not registered")
        try:
            current_status = Status(current.status)
        except ValueError:
            raise ValueError(
                f"candidate {candidate_id!r} has unknown stored status {current.status!r}"
            ) from None
        if new_status not in _VALID_TRANSITIONS[current_status]:
            allowed = sorted(s.value for s in _VALID_TRANSITIONS[current_status])
            raise ValueError(
                f"invalid transition {current_status.value} → {new_status.value}; "
                f"allowed from {current_status.value}: {allowed or '∅ (terminal)'}"
            )
        now = _dt.datetime.now(_dt.UTC)
        with self._connect() as con:
            if falsifier_id is not None:
                con.execute(
                    """UPDATE bb_candidates
                       SET status = ?, falsifier_id = ?, updated_at = ?
                       WHERE candidate_id = ?""",
                    [new_status.value, falsifier_id, now, candidate_id],
                )
            else:
                con.execute(
                    """UPDATE bb_candidates
                       SET status = ?, updated_at = ?
                       WHERE candidate_id = ?""",
                    [new_status.value, now, candidate_id],
                )
        record = self.get(candidate_id)
        assert record is not None
        return record

    def attach_stats(
        self,
        candidate_id: str,
        *,
        corpus_stats: dict[str, Any] | None = None,
        adversarial_stats: dict[str, Any] | None = None,
    ) -> CandidateRecord:
        """Attach (or overwrite) corpus or adversarial battery results.

        Pass either argument or both. Passing `None` for both is a no-op.

        Raises KeyError if the candidate isn't registered.
        """
        if self.get(candidate_id) is None:
            raise KeyError(f"candidate {candidate_id!r} not registered")
        updates: list[str] = []
        params: list[Any] = []
        if corpus_stats is not None:
            updates.append("corpus_stats_json = ?")
            params.append(json.dumps(corpus_stats))
        if adversarial_stats is not None:
            updates.append("adversarial_stats_json = ?")
            params.append(json.dumps(adversarial_stats))
        if not updates:
            record = self.get(candidate_id)
            assert record is not None
            return record
        updates.append("updated_at = ?")
        params.append(_dt.datetime.now(_dt.UTC))
        params.append(candidate_id)
        with self._connect() as con:
            con.execute(
                f"UPDATE bb_candidates SET {', '.join(updates)} WHERE candidate_id = ?",
                params,
            )
        record = self.get(candidate_id)
        assert record is not None
        return record

    # --- read operations -----------------------------------------------------

    def get(self, candidate_id: str) -> CandidateRecord | None:
        """Fetch a single candidate by ID, or None if not registered."""
        with self._connect(read_only=True) as con:
            cursor = con.execute(
                "SELECT * FROM bb_candidates WHERE candidate_id = ?",
                [candidate_id],
            )
            row = cursor.fetchone()
            if row is None:
                return None
            columns = [d[0] for d in cursor.description]
            return _row_to_record(columns, row)

    def query(
        self,
        *,
        family: str | None = None,
        not_family: str | None = None,
        status: str | Status | None = None,
        rhs_type: str | None = None,
        parent_id: str | None = None,
        obstruction_hit: str | None = None,
    ) -> list[CandidateRecord]:
        """Return candidates matching ALL given predicates.

        `obstruction_hit` matches any candidate whose `obstructions_hit`
        JSON array contains the given ID (substring match against the
        JSON-encoded array — sufficient for the small ID space).

        Returns rows ordered by `created_at DESC` (newest first).
        """
        clauses: list[str] = []
        params: list[Any] = []
        if family is not None:
            clauses.append("family = ?")
            params.append(family)
        if not_family is not None:
            clauses.append("family != ?")
            params.append(not_family)
        if status is not None:
            clauses.append("status = ?")
            params.append(status.value if isinstance(status, Status) else status)
        if rhs_type is not None:
            clauses.append("rhs_type = ?")
            params.append(rhs_type)
        if parent_id is not None:
            clauses.append("parent_id = ?")
            params.append(parent_id)
        if obstruction_hit is not None:
            clauses.append("obstructions_hit LIKE ?")
            params.append(f'%"{obstruction_hit}"%')
        sql = "SELECT * FROM bb_candidates"
        if clauses:
            sql += " WHERE " + " AND ".join(clauses)
        sql += " ORDER BY created_at DESC"
        with self._connect(read_only=True) as con:
            cursor = con.execute(sql, params)
            rows = cursor.fetchall()
            columns = [d[0] for d in cursor.description]
            return [_row_to_record(columns, r) for r in rows]

    def lineage(self, candidate_id: str) -> list[CandidateRecord]:
        """Walk `parent_id` recursively and return the ancestry chain.

        Returns the list ordered from oldest ancestor to the requested
        candidate (inclusive). Returns `[]` if the candidate isn't
        registered.
        """
        if self.get(candidate_id) is None:
            return []
        with self._connect(read_only=True) as con:
            cursor = con.execute(
                """
                WITH RECURSIVE ancestry(candidate_id, parent_id, depth) AS (
                    SELECT candidate_id, parent_id, 0 AS depth
                    FROM bb_candidates WHERE candidate_id = ?
                  UNION ALL
                    SELECT c.candidate_id, c.parent_id, a.depth + 1
                    FROM bb_candidates c
                    JOIN ancestry a ON c.candidate_id = a.parent_id
                )
                SELECT bb.*, ancestry.depth
                FROM bb_candidates bb
                JOIN ancestry USING (candidate_id)
                ORDER BY ancestry.depth DESC
                """,
                [candidate_id],
            )
            rows = cursor.fetchall()
            columns = [d[0] for d in cursor.description]
            # Strip the `depth` column added for ordering.
            depth_idx = columns.index("depth")
            base_columns = columns[:depth_idx] + columns[depth_idx + 1 :]
            return [
                _row_to_record(base_columns, r[:depth_idx] + r[depth_idx + 1 :])
                for r in rows
            ]

    def count(self, **filters: Any) -> int:
        """Count rows matching the same filter kwargs as `query()`.

        Equivalent to `len(self.query(**filters))` but cheaper for large
        registries.
        """
        if not filters:
            with self._connect(read_only=True) as con:
                return con.execute("SELECT COUNT(*) FROM bb_candidates").fetchone()[0]
        return len(self.query(**filters))
