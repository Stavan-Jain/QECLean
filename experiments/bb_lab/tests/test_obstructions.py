"""Tests for the Tier-0 pre-flight obstruction gate.

The exit criterion for the obstruction-registry module is that every
round-1 conjecture round classifies the way the historical record says
it should:

  * Cv1-original (Jacobson dimension sum): SHELVED-A-PRIORI via §6h.
  * HT-Roos (char-theoretic): SHELVED-A-PRIORI on the four §6j-hit
    Bravyi instances; PROCEED-with-blast-radius is also acceptable
    given bb_90 is the §6j exception, but the verdict for "tight on
    gross" is shelved.
  * SRB cover-graph (chain-map): blocked on gross via §6k; survives
    on the other Bravyi instances.
  * Lin-Pryadko Statement 12 (lifted-product, weight RHS, no
    degeneracy/semisimple/cover hypothesis): PROCEED.
  * Cv1 w_1 (radical-weight, weight RHS): PROCEED.

These tests anchor the §6 registry to the round-1 historical record;
any future edit that changes a verdict needs to update the
corresponding HANDOFF.md §6 entry (or vice versa) explicitly.
"""

from __future__ import annotations

import pytest

from bb_lab.obstructions import (
    BRAVYI_FINGERPRINTS,
    CV1_ORIGINAL_JACOBSON_SUM,
    CV1_W1_REFINED,
    HT_ROOS,
    LIN_PRYADKO_STMT_12,
    OBSTRUCTIONS,
    SRB_COVER_GRAPH,
    Candidate,
    Family,
    InstanceFingerprint,
    RHSType,
    Verdict,
    classify,
)


# --- §6h: dimension RHS is a category error -----------------------------


def test_6h_fires_on_dimension_rhs() -> None:
    """A candidate that puts a dimension quantity on the RHS of a
    distance bound is structurally wrong (HANDOFF.md §6h)."""
    result = classify(CV1_ORIGINAL_JACOBSON_SUM)
    assert "6h" in result.obstructions_hit
    assert result.verdict == Verdict.SHELVED_A_PRIORI
    assert any("§6h" in line for line in result.reasoning)


def test_6h_does_not_fire_on_weight_rhs() -> None:
    """The refined w_1 invariant uses weight, not dimension, on the RHS;
    it must not hit §6h."""
    result = classify(CV1_W1_REFINED)
    assert "6h" not in result.obstructions_hit


def test_6h_short_circuits_other_checks() -> None:
    """§6h is a category error; once it fires, no other obstructions
    need to be evaluated. The Classification carries §6h only."""
    bad = Candidate(
        id="dim-rhs-everything",
        name="Hypothetical dim-RHS candidate with extra hypotheses",
        family=Family.CHAR_THEORETIC,  # would also fire §6j
        rhs_type=RHSType.DIMENSION,
        requires_non_degenerate=True,  # would also fire §6i
        requires_cover_coprime=True,  # would also fire §6k
    )
    result = classify(bad)
    assert result.obstructions_hit == ("6h",)
    assert result.verdict == Verdict.SHELVED_A_PRIORI


# --- §6i: non-degenerate hypothesis excludes Bravyi --------------------


def test_6i_fires_on_non_degenerate_hypothesis() -> None:
    """A candidate that requires c = 1 cannot be tight on any Bravyi
    code (all have c = 3 per HANDOFF.md §6i)."""
    candidate = Candidate(
        id="hypothetical-non-degenerate",
        name="Hypothetical non-degenerate-only bound",
        family=Family.LIFTED_PRODUCT,
        rhs_type=RHSType.WEIGHT,
        requires_non_degenerate=True,
    )
    result = classify(candidate)
    assert "6i" in result.obstructions_hit
    # Every Bravyi instance is degenerate, so all 5 should be blocked.
    blocked = {b.split("@")[1] for b in result.bravyi_blast_radius}
    assert len(blocked) == len(BRAVYI_FINGERPRINTS)
    assert result.verdict == Verdict.SHELVED_A_PRIORI


# --- §6j: character-theoretic blocked when F[G] non-semisimple ---------


def test_6j_fires_on_char_theoretic_against_non_semisimple_bravyi() -> None:
    """HT-Roos is char-theoretic; gross has |G| = 72 with 2 | |G|, so
    F_2[G] is non-semisimple and §6j fires on gross."""
    result = classify(HT_ROOS)
    assert "6j" in result.obstructions_hit
    blocked = {b.split("@")[1] for b in result.bravyi_blast_radius if b.startswith("6j@")}
    # 4 of 5 Bravyi instances have |G| even: bb_72(36), bb_108(54),
    # gross(72), bb_288(144). Only bb_90_8_10 (|G| = 45) escapes §6j.
    assert "gross_144_12_12" in blocked
    assert "bb_72_12_6" in blocked
    assert "bb_108_8_10" in blocked
    assert "bb_288_12_18" in blocked
    assert "bb_90_8_10" not in blocked


def test_6j_does_not_fire_on_bb_90() -> None:
    """bb_90_8_10 has |G| = 45 = 3² · 5; F_2[G] is semisimple here.
    A char-theoretic bound can in principle be tight on bb_90."""
    bb90 = next(i for i in BRAVYI_FINGERPRINTS if i.id == "bb_90_8_10")
    # |G_order| should be coprime to char F = 2.
    from math import gcd
    assert gcd(bb90.G_order, bb90.char_F) == 1


def test_6j_ht_roos_proceeds_with_blast_radius() -> None:
    """HT-Roos survives §6j on bb_90, so the verdict is PROCEED with
    blast radius, NOT a blanket shelf. The downstream tester must
    know which instances are still in scope."""
    result = classify(HT_ROOS)
    assert result.verdict == Verdict.PROCEED
    # Survivors should include bb_90.
    blocked = {b.split("@")[1] for b in result.bravyi_blast_radius}
    survivors = {i.id for i in BRAVYI_FINGERPRINTS} - blocked
    assert "bb_90_8_10" in survivors


# --- §6k: chain-map blocked when cover index shares char F factor ------


def test_6k_fires_on_chain_map_against_gross() -> None:
    """SRB cover-graph is chain-map family; gross is an h=2 cover over
    F_2, so §6k fires on gross."""
    result = classify(SRB_COVER_GRAPH)
    assert "6k" in result.obstructions_hit
    blocked = {b.split("@")[1] for b in result.bravyi_blast_radius if b.startswith("6k@")}
    assert "gross_144_12_12" in blocked


def test_6k_only_fires_on_known_chain_map_blockers() -> None:
    """§6k requires the instance to be explicitly flagged as a known
    h-cover with `gcd(h, char F) > 1`. By default, only gross carries
    that flag in round-1's registry."""
    result = classify(SRB_COVER_GRAPH)
    blocked_by_6k = {b.split("@")[1] for b in result.bravyi_blast_radius if b.startswith("6k@")}
    assert blocked_by_6k == {"gross_144_12_12"}


def test_6k_srb_proceeds_with_blast_radius() -> None:
    """SRB blocked on gross only; survives the other four. Verdict is
    PROCEED with blast radius."""
    result = classify(SRB_COVER_GRAPH)
    assert result.verdict == Verdict.PROCEED


# --- Lin-Pryadko Statement 12: textbook valid bound --------------------


def test_lin_pryadko_proceeds() -> None:
    """Lin-Pryadko Statement 12 is a textbook lifted-product weight
    bound with no §6 obstruction. PROCEED. (Note: it's loose by 4-10
    on the Bravyi codes per T2R2.4_evaluation.md, but looseness is a
    Tier-3 concern, not a Tier-0 concern.)"""
    result = classify(LIN_PRYADKO_STMT_12)
    assert result.obstructions_hit == ()
    assert result.bravyi_blast_radius == ()
    assert result.verdict == Verdict.PROCEED


# --- Cv1 w_1 refined: weight invariant, no obstruction -----------------


def test_cv1_w1_refined_proceeds() -> None:
    """The refined `w_1` invariant is a weight quantity in the
    radical-weight family. It hits no §6 obstruction. (It was later
    falsified at Tier 3 for OTHER reasons — joint-vanishing-orbit
    restriction unsoundness — but that's downstream of Tier 0.)"""
    result = classify(CV1_W1_REFINED)
    assert result.verdict == Verdict.PROCEED


# --- needs_new_theory escape hatch -------------------------------------


def test_needs_new_theory_short_circuits() -> None:
    """A candidate explicitly tagged as research-seed gets
    NEEDS-NEW-THEORY regardless of other predicates."""
    seed = Candidate(
        id="family-a-radical-weight-v2-seed",
        name="Family A research seed: weight invariant distinguishing R_O-unit equivalents",
        family=Family.RADICAL_WEIGHT,
        rhs_type=RHSType.WEIGHT,
        needs_new_theory=True,
    )
    result = classify(seed)
    assert result.verdict == Verdict.NEEDS_NEW_THEORY


# --- Adding a new obstruction (regression on the §6 schema) -----------


def test_obstruction_ids_are_unique() -> None:
    ids = [o.id for o in OBSTRUCTIONS]
    assert len(ids) == len(set(ids))


def test_each_obstruction_has_section_ref() -> None:
    for o in OBSTRUCTIONS:
        assert o.section_ref, f"obstruction {o.id} has no section_ref"
        assert "HANDOFF" in o.section_ref


def test_bravyi_fingerprints_match_table() -> None:
    """The fingerprints must match the published Bravyi (n, k, d)
    table. Concretely: |G| = ell * m for each (ell, m) in
    instances/bravyi_table.yaml, and the canonical IDs are stable."""
    expected_g_orders = {
        "bb_72_12_6": 36,
        "bb_90_8_10": 45,
        "bb_108_8_10": 54,
        "gross_144_12_12": 72,
        "bb_288_12_18": 144,
    }
    actual = {i.id: i.G_order for i in BRAVYI_FINGERPRINTS}
    assert actual == expected_g_orders


# --- Custom fingerprints ------------------------------------------------


def test_classify_accepts_custom_instances() -> None:
    """The classifier should work against any tuple of fingerprints,
    not just the Bravyi-table defaults. Tier 3's parameterized
    adversarial generator will pass its own."""
    custom = (
        InstanceFingerprint(
            id="hypothetical-semisimple",
            G_order=15,  # 3 * 5, coprime to char F = 2
        ),
    )
    result = classify(HT_ROOS, instances=custom)
    # §6j should NOT fire on a semisimple instance.
    assert "6j" not in result.obstructions_hit
    assert result.verdict == Verdict.PROCEED
