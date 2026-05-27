"""Tests for the round-2 candidate registry.

Exit criteria for the module:

* Roundtrip: register → get returns equal record.
* Tier-0 verdict → initial status mapping is correct.
* State machine: valid transitions succeed; invalid raise ValueError.
* Stats attachment round-trips through JSON.
* Query filters: family / status / obstruction-hit / parent.
* Lineage walks `parent_id` recursively and returns
  oldest-to-newest order.
* Round-1 historical replay: all five round-1 candidates land in the
  expected statuses.

Each test uses an isolated tmp_path DB to avoid cross-test pollution.
"""

from __future__ import annotations

import pytest

from bb_lab.candidates import CandidateRegistry, Status
from bb_lab.obstructions import (
    CV1_ORIGINAL_JACOBSON_SUM,
    CV1_W1_REFINED,
    HT_ROOS,
    LIN_PRYADKO_STMT_12,
    SRB_COVER_GRAPH,
    Candidate,
    Family,
    RHSType,
    Verdict,
    classify,
)


@pytest.fixture
def registry(tmp_path):
    """Fresh registry per test, in a tmp_path DuckDB file."""
    return CandidateRegistry(db_path=tmp_path / "test_candidates.duckdb")


# --- register + get roundtrip -----------------------------------------


def test_register_and_get_roundtrip(registry: CandidateRegistry) -> None:
    candidate = LIN_PRYADKO_STMT_12
    inserted = registry.register(candidate, classify(candidate))

    retrieved = registry.get(candidate.id)
    assert retrieved == inserted
    assert retrieved is not None
    assert retrieved.name == candidate.name
    assert retrieved.family == candidate.family.value
    assert retrieved.bound_formula == candidate.bound_formula


def test_get_missing_returns_none(registry: CandidateRegistry) -> None:
    assert registry.get("never-registered") is None


def test_duplicate_registration_raises(registry: CandidateRegistry) -> None:
    candidate = LIN_PRYADKO_STMT_12
    registry.register(candidate, classify(candidate))
    with pytest.raises(Exception):
        # DuckDB raises a PRIMARY KEY violation; the exception type varies
        # by binding version, so we catch broadly.
        registry.register(candidate, classify(candidate))


# --- Tier-0 verdict → initial status mapping --------------------------


def test_proceed_verdict_maps_to_classified(registry: CandidateRegistry) -> None:
    rec = registry.register(LIN_PRYADKO_STMT_12, classify(LIN_PRYADKO_STMT_12))
    assert rec.status == Status.CLASSIFIED.value


def test_shelved_a_priori_verdict_maps_to_shelved(registry: CandidateRegistry) -> None:
    # Cv1-original has dimension RHS → SHELVED-A-PRIORI via §6h
    rec = registry.register(CV1_ORIGINAL_JACOBSON_SUM, classify(CV1_ORIGINAL_JACOBSON_SUM))
    assert rec.tier0_verdict == Verdict.SHELVED_A_PRIORI.value
    assert rec.status == Status.SHELVED.value


def test_needs_new_theory_verdict_maps_to_research_seed(registry: CandidateRegistry) -> None:
    seed = Candidate(
        id="family-a-seed",
        name="Family A research seed",
        family=Family.RADICAL_WEIGHT,
        rhs_type=RHSType.WEIGHT,
        needs_new_theory=True,
    )
    rec = registry.register(seed, classify(seed))
    assert rec.status == Status.RESEARCH_SEED.value


# --- obstruction + classification data persistence --------------------


def test_obstructions_persisted_through_json(registry: CandidateRegistry) -> None:
    rec = registry.register(HT_ROOS, classify(HT_ROOS))
    assert "6j" in rec.obstructions_hit
    # bb_90 should NOT be in blast radius (it's the §6j exception); the
    # other four Bravyi instances should be.
    blast_instances = {b.split("@")[1] for b in rec.bravyi_blast_radius}
    assert "gross_144_12_12" in blast_instances
    assert "bb_90_8_10" not in blast_instances


def test_tier0_reasoning_persisted(registry: CandidateRegistry) -> None:
    rec = registry.register(CV1_ORIGINAL_JACOBSON_SUM, classify(CV1_ORIGINAL_JACOBSON_SUM))
    # §6h reasoning should mention the type mismatch.
    assert any("§6h" in line for line in rec.tier0_reasoning)


# --- state machine ----------------------------------------------------


def test_state_machine_valid_chain(registry: CandidateRegistry) -> None:
    candidate = LIN_PRYADKO_STMT_12
    registry.register(candidate, classify(candidate))
    # CLASSIFIED → TIER2_RUNNING → TIER3_RUNNING → SURVIVED → FORMALIZED
    for next_status in (
        Status.TIER2_RUNNING,
        Status.TIER3_RUNNING,
        Status.SURVIVED,
        Status.FORMALIZED,
    ):
        rec = registry.update_status(candidate.id, next_status)
        assert rec.status == next_status.value


def test_state_machine_rejects_jump(registry: CandidateRegistry) -> None:
    candidate = LIN_PRYADKO_STMT_12
    registry.register(candidate, classify(candidate))
    # CLASSIFIED → FORMALIZED is illegal (must pass Tier 2/3 first).
    with pytest.raises(ValueError) as exc:
        registry.update_status(candidate.id, Status.FORMALIZED)
    assert "invalid transition" in str(exc.value)


def test_state_machine_shelved_is_terminal(registry: CandidateRegistry) -> None:
    # Cv1-original is SHELVED on registration.
    candidate = CV1_ORIGINAL_JACOBSON_SUM
    registry.register(candidate, classify(candidate))
    with pytest.raises(ValueError):
        registry.update_status(candidate.id, Status.TIER2_RUNNING)


def test_state_machine_formalized_is_terminal(registry: CandidateRegistry) -> None:
    candidate = LIN_PRYADKO_STMT_12
    registry.register(candidate, classify(candidate))
    # Walk to FORMALIZED.
    for s in (Status.TIER2_RUNNING, Status.TIER3_RUNNING, Status.SURVIVED, Status.FORMALIZED):
        registry.update_status(candidate.id, s)
    with pytest.raises(ValueError):
        registry.update_status(candidate.id, Status.SHELVED)


def test_state_machine_missing_candidate_raises(registry: CandidateRegistry) -> None:
    with pytest.raises(KeyError):
        registry.update_status("never-registered", Status.SHELVED)


def test_update_status_records_falsifier_id(registry: CandidateRegistry) -> None:
    candidate = LIN_PRYADKO_STMT_12
    registry.register(candidate, classify(candidate))
    registry.update_status(candidate.id, Status.TIER2_RUNNING)
    rec = registry.update_status(
        candidate.id, Status.SHELVED, falsifier_id="z3xz15-counterexample"
    )
    assert rec.falsifier_id == "z3xz15-counterexample"


# --- stats attachment -------------------------------------------------


def test_attach_corpus_stats(registry: CandidateRegistry) -> None:
    candidate = LIN_PRYADKO_STMT_12
    registry.register(candidate, classify(candidate))
    stats = {
        "applicable": 3836,
        "tight": 4,
        "violations": 0,
        "mean_looseness": 4.30,
        "per_group": {"Z3xZ3": 12, "Z6xZ6": 812},
    }
    rec = registry.attach_stats(candidate.id, corpus_stats=stats)
    assert rec.corpus_stats == stats


def test_attach_adversarial_stats(registry: CandidateRegistry) -> None:
    candidate = HT_ROOS
    registry.register(candidate, classify(candidate))
    stats = {
        "attacks_run": 50,
        "violations": 3,
        "per_attack_mode": {"mixed_rank_multi_prime": {"violations": 3, "tested": 25}},
    }
    rec = registry.attach_stats(candidate.id, adversarial_stats=stats)
    assert rec.adversarial_stats == stats


def test_attach_both_stats_in_one_call(registry: CandidateRegistry) -> None:
    candidate = LIN_PRYADKO_STMT_12
    registry.register(candidate, classify(candidate))
    rec = registry.attach_stats(
        candidate.id,
        corpus_stats={"tight": 4},
        adversarial_stats={"violations": 0},
    )
    assert rec.corpus_stats == {"tight": 4}
    assert rec.adversarial_stats == {"violations": 0}


def test_attach_stats_missing_candidate_raises(registry: CandidateRegistry) -> None:
    with pytest.raises(KeyError):
        registry.attach_stats("never-registered", corpus_stats={"tight": 0})


# --- query ------------------------------------------------------------


def test_query_by_family(registry: CandidateRegistry) -> None:
    registry.register(HT_ROOS, classify(HT_ROOS))  # char-theoretic
    registry.register(LIN_PRYADKO_STMT_12, classify(LIN_PRYADKO_STMT_12))  # lifted-product
    registry.register(SRB_COVER_GRAPH, classify(SRB_COVER_GRAPH))  # chain-map

    chars = registry.query(family=Family.CHAR_THEORETIC.value)
    assert len(chars) == 1
    assert chars[0].candidate_id == HT_ROOS.id


def test_query_by_status(registry: CandidateRegistry) -> None:
    # CV1-original is SHELVED; the others CLASSIFIED.
    registry.register(CV1_ORIGINAL_JACOBSON_SUM, classify(CV1_ORIGINAL_JACOBSON_SUM))
    registry.register(LIN_PRYADKO_STMT_12, classify(LIN_PRYADKO_STMT_12))
    registry.register(HT_ROOS, classify(HT_ROOS))

    shelved = registry.query(status=Status.SHELVED)
    assert {r.candidate_id for r in shelved} == {CV1_ORIGINAL_JACOBSON_SUM.id}
    classified = registry.query(status=Status.CLASSIFIED)
    assert {r.candidate_id for r in classified} == {LIN_PRYADKO_STMT_12.id, HT_ROOS.id}


def test_query_by_obstruction_hit(registry: CandidateRegistry) -> None:
    registry.register(HT_ROOS, classify(HT_ROOS))  # hits 6j
    registry.register(SRB_COVER_GRAPH, classify(SRB_COVER_GRAPH))  # hits 6k
    registry.register(LIN_PRYADKO_STMT_12, classify(LIN_PRYADKO_STMT_12))  # hits nothing

    hits_6j = registry.query(obstruction_hit="6j")
    assert {r.candidate_id for r in hits_6j} == {HT_ROOS.id}
    hits_6k = registry.query(obstruction_hit="6k")
    assert {r.candidate_id for r in hits_6k} == {SRB_COVER_GRAPH.id}


def test_query_by_not_family(registry: CandidateRegistry) -> None:
    registry.register(HT_ROOS, classify(HT_ROOS))
    registry.register(LIN_PRYADKO_STMT_12, classify(LIN_PRYADKO_STMT_12))

    non_char = registry.query(not_family=Family.CHAR_THEORETIC.value)
    assert {r.candidate_id for r in non_char} == {LIN_PRYADKO_STMT_12.id}


def test_query_by_rhs_type(registry: CandidateRegistry) -> None:
    registry.register(CV1_ORIGINAL_JACOBSON_SUM, classify(CV1_ORIGINAL_JACOBSON_SUM))  # dim
    registry.register(LIN_PRYADKO_STMT_12, classify(LIN_PRYADKO_STMT_12))  # weight

    dim = registry.query(rhs_type=RHSType.DIMENSION.value)
    assert {r.candidate_id for r in dim} == {CV1_ORIGINAL_JACOBSON_SUM.id}


def test_count(registry: CandidateRegistry) -> None:
    assert registry.count() == 0
    registry.register(HT_ROOS, classify(HT_ROOS))
    registry.register(LIN_PRYADKO_STMT_12, classify(LIN_PRYADKO_STMT_12))
    assert registry.count() == 2
    assert registry.count(family=Family.CHAR_THEORETIC.value) == 1


# --- lineage ----------------------------------------------------------


def test_lineage_walks_parent_chain(registry: CandidateRegistry) -> None:
    """Build a Cv1 → Cv2 → Cv3 chain via parent_id and walk it."""
    cv1 = CV1_W1_REFINED
    cv2 = Candidate(
        id="Cv2-radical-weight",
        name="Cv2 — radical-weight conjecture (falsified round 1)",
        family=Family.RADICAL_WEIGHT,
        rhs_type=RHSType.WEIGHT,
        bound_formula="d_X ≥ (1/c) · min_O w_1(A, O)",
    )
    cv3 = Candidate(
        id="Cv3-radical-weight-narrowed",
        name="Cv3 — narrowed to elem-ab G_odd + c ≥ 3",
        family=Family.RADICAL_WEIGHT,
        rhs_type=RHSType.WEIGHT,
        bound_formula="d_X ≥ (1/c) · min_O w_1(A, O) | elem-ab G_odd ∧ c ≥ 3",
    )

    registry.register(cv1, classify(cv1))
    registry.register(cv2, classify(cv2), parent_id=cv1.id)
    registry.register(cv3, classify(cv3), parent_id=cv2.id)

    chain = registry.lineage(cv3.id)
    assert [r.candidate_id for r in chain] == [cv1.id, cv2.id, cv3.id]


def test_lineage_root_has_single_element(registry: CandidateRegistry) -> None:
    registry.register(LIN_PRYADKO_STMT_12, classify(LIN_PRYADKO_STMT_12))
    chain = registry.lineage(LIN_PRYADKO_STMT_12.id)
    assert len(chain) == 1
    assert chain[0].candidate_id == LIN_PRYADKO_STMT_12.id


def test_lineage_missing_returns_empty(registry: CandidateRegistry) -> None:
    assert registry.lineage("never-registered") == []


# --- round-1 historical replay ----------------------------------------


def test_round1_historical_replay(registry: CandidateRegistry) -> None:
    """Replay the five round-1 candidates and verify their landed
    statuses match the historical record. This is the headline
    end-to-end test of the registry + obstructions module integration."""
    expected = [
        (CV1_ORIGINAL_JACOBSON_SUM, Status.SHELVED),  # §6h category error
        (CV1_W1_REFINED, Status.CLASSIFIED),  # weight RHS, no obstruction
        (HT_ROOS, Status.CLASSIFIED),  # PROCEED on bb_90, blocked elsewhere
        (SRB_COVER_GRAPH, Status.CLASSIFIED),  # PROCEED on 4/5, blocked on gross
        (LIN_PRYADKO_STMT_12, Status.CLASSIFIED),  # textbook, no obstruction
    ]
    for c, expected_status in expected:
        rec = registry.register(c, classify(c))
        assert rec.status == expected_status.value, (
            f"{c.id}: expected {expected_status.value}, got {rec.status}"
        )
    assert registry.count() == 5
    assert registry.count(status=Status.SHELVED) == 1
    assert registry.count(status=Status.CLASSIFIED) == 4


# --- persistence across registry instances ----------------------------


def test_registry_persists_across_instances(tmp_path) -> None:
    """A second CandidateRegistry pointed at the same file sees the
    rows written by the first. Sanity check for cross-process workflows."""
    db = tmp_path / "shared.duckdb"
    reg1 = CandidateRegistry(db_path=db)
    reg1.register(LIN_PRYADKO_STMT_12, classify(LIN_PRYADKO_STMT_12))
    reg2 = CandidateRegistry(db_path=db)
    rec = reg2.get(LIN_PRYADKO_STMT_12.id)
    assert rec is not None
    assert rec.candidate_id == LIN_PRYADKO_STMT_12.id
