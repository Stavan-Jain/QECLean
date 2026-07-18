"""Tests for the Tier-0 pre-flight obstruction gate.

The exit criterion for the obstruction-registry module is that every
round-1 / round-2 / round-2-v2 conjecture round classifies the way
the historical record says it should:

  * Cv1-original (Jacobson dimension sum): SHELVED-A-PRIORI via §6h.
  * HT-Roos (char-theoretic): SHELVED-A-PRIORI on the four §6j-hit
    Bravyi instances; PROCEED-with-blast-radius is also acceptable
    given bb_90 is the §6j exception, but the verdict for "tight on
    gross" is shelved.
  * SRB cover-graph (chain-map): blocked on gross via §6k; survives
    on the other Bravyi instances.
  * Family C v1 (spectral): SHELVED-A-PRIORI via §6l (vacuous on
    every BB code with k ≥ 2).
  * Family D v1 (Koszul H_2 min weight): SHELVED-A-PRIORI via §6m
    (round-2 v2 first session; the iso witness in
    `scripts/family_d_v1_koszul_h2_iso_witness.py` shows min_wt is
    not a module-iso invariant).
  * Lin-Pryadko Statement 12 (lifted-product, weight RHS, no
    degeneracy/semisimple/cover hypothesis): PROCEED.
  * Cv1 w_1 (radical-weight, weight RHS): PROCEED.

These tests anchor the §6 registry to the round-1 / round-2 historical
record; any future edit that changes a verdict needs to update the
corresponding HANDOFF.md §6 entry (or vice versa) explicitly.
"""

from __future__ import annotations

import pytest

from bb_lab.obstructions import (
    BRAVYI_FINGERPRINTS,
    CV1_ORIGINAL_JACOBSON_SUM,
    CV1_W1_REFINED,
    FAMILY_C_V1_SPECTRAL,
    FAMILY_D_V1_CM_REGULARITY,
    FAMILY_D_V1_HILBERT_SERIES_MIN_DEGREE,
    FAMILY_D_V1_KOSZUL_H_2_MIN_WEIGHT,
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


# --- §6l: Cayley-graph spectral bounds vacuous on BB codes with k ≥ 2 --


def test_6l_fires_on_spectral_candidate() -> None:
    """Family C v1 (Cayley spectral) hits §6l on every Bravyi instance
    because all have k ≥ 2 by construction. Joint vanishing on a
    non-trivial character forces λ_2 = weight, so the spectral gap
    is identically zero."""
    result = classify(FAMILY_C_V1_SPECTRAL)
    assert "6l" in result.obstructions_hit
    blocked = {b.split("@")[1] for b in result.bravyi_blast_radius if b.startswith("6l@")}
    # All 5 Bravyi instances are blocked since all have k ≥ 2.
    assert blocked == {i.id for i in BRAVYI_FINGERPRINTS}


def test_6l_implies_shelved_a_priori() -> None:
    """Since §6l blocks every Bravyi instance (all have k ≥ 2), a
    spectral candidate cannot be tight on any engineering target.
    Verdict: SHELVED-A-PRIORI."""
    result = classify(FAMILY_C_V1_SPECTRAL)
    assert result.verdict == Verdict.SHELVED_A_PRIORI


def test_6l_does_not_fire_without_spectral_flag() -> None:
    """The default Candidate has uses_cayley_spectral_bound=False;
    §6l only fires when the flag is set explicitly."""
    candidate = Candidate(
        id="non-spectral",
        name="A non-spectral combinatorial bound",
        family=Family.COMBINATORIAL,
        rhs_type=RHSType.WEIGHT,
    )
    result = classify(candidate)
    assert "6l" not in result.obstructions_hit


def test_6l_can_be_dodged_by_an_instance_without_k_geq_2() -> None:
    """An instance with `has_k_geq_2=False` (a hypothetical k=0 BB
    code) doesn't trigger §6l. Useful for confirming the predicate
    really gates on the joint-vanishing precondition, not just the
    candidate's flag."""
    k_zero_instance = (
        InstanceFingerprint(
            id="hypothetical-k-zero",
            G_order=36,
            has_k_geq_2=False,
        ),
    )
    result = classify(FAMILY_C_V1_SPECTRAL, instances=k_zero_instance)
    # No instance triggers §6l, so the candidate proceeds.
    assert "6l" not in result.obstructions_hit
    assert result.verdict == Verdict.PROCEED


# --- §6m: F_2[G]-module-iso-class invariants cannot bound min weight ---


def test_6m_fires_on_koszul_h2_min_weight() -> None:
    """The round-2 v2 first session's Koszul H_2 candidate is the
    historical anchor for §6m. It defines `d_X ≥ min_wt(H_2(K(A, B)))`
    but H_2's iso class doesn't determine its min weight (witness:
    H_0(K_gross) ≅ H_2(K_gross) as F_2[G]-modules with min_wt 1 vs 32).
    Falls to §6m structurally, in addition to being empirically wrong-
    signed."""
    result = classify(FAMILY_D_V1_KOSZUL_H_2_MIN_WEIGHT)
    assert "6m" in result.obstructions_hit
    assert result.verdict == Verdict.SHELVED_A_PRIORI
    assert any("§6m" in line for line in result.reasoning)


def test_6m_fires_on_hilbert_series_min_degree() -> None:
    """A hypothetical 4a-style candidate that bounds d_X by the
    minimum non-vanishing degree of the Hilbert series of syz(A, B).
    Hilbert series coefficients are dimensions of graded pieces of
    an F_2[G]-module, so the min degree is iso-class invariant.
    §6m fires structurally; the candidate cannot be tight."""
    result = classify(FAMILY_D_V1_HILBERT_SERIES_MIN_DEGREE)
    assert "6m" in result.obstructions_hit
    assert result.verdict == Verdict.SHELVED_A_PRIORI


def test_6m_fires_on_cm_regularity() -> None:
    """Castelnuovo-Mumford regularity is defined via Tor dimensions
    (Aramova-Herzog), all iso-class invariants. Any 4b-style bound
    `d_X ≥ φ(reg((A, B)))` falls to §6m."""
    result = classify(FAMILY_D_V1_CM_REGULARITY)
    assert "6m" in result.obstructions_hit
    assert result.verdict == Verdict.SHELVED_A_PRIORI


def test_6m_is_structural_not_per_instance() -> None:
    """§6m, like §6h, is instance-independent — the obstruction holds
    regardless of which Bravyi instance the candidate is evaluated on.
    The `bravyi_blast_radius` should therefore be EMPTY (no per-instance
    fire), and the verdict should be SHELVED-A-PRIORI directly."""
    result = classify(FAMILY_D_V1_KOSZUL_H_2_MIN_WEIGHT)
    assert result.bravyi_blast_radius == ()
    assert result.verdict == Verdict.SHELVED_A_PRIORI


def test_6m_does_not_fire_without_module_natural_flag() -> None:
    """A candidate that uses NON-module data (e.g., explicit Hamming
    weight, classical dual distance, set-theoretic support) is not
    subject to §6m. The default Candidate has
    is_module_natural_invariant=False; §6m only fires when the flag is
    set explicitly. Lin-Pryadko (uses d_A^⊥) is the canonical
    non-firing example."""
    result = classify(LIN_PRYADKO_STMT_12)
    assert "6m" not in result.obstructions_hit
    # LP12 also doesn't have the flag set, so let's also test a generic
    # weight bound that explicitly does NOT use module data.
    non_module_candidate = Candidate(
        id="hypothetical-weight-enumerator-bound",
        name="Hypothetical weight-enumerator-coefficient bound",
        family=Family.COMBINATORIAL,
        rhs_type=RHSType.WEIGHT,
        bound_formula="d_X ≥ φ(weight-enumerator coefficient at degree w)",
        is_module_natural_invariant=False,
    )
    result = classify(non_module_candidate)
    assert "6m" not in result.obstructions_hit
    assert result.verdict == Verdict.PROCEED


def test_6m_does_not_fire_on_radical_weight_w1() -> None:
    """The round-1 w_1 invariant is in the RADICAL_WEIGHT family but
    is fundamentally a *weight* quantity in the standard F_2-basis,
    not an iso-class invariant of the radical filtration. §6m does
    NOT fire on w_1 even though w_1 mentions radical structure."""
    result = classify(CV1_W1_REFINED)
    assert "6m" not in result.obstructions_hit


def test_6m_short_circuits_after_6h() -> None:
    """If a candidate triggers both §6h (dimension RHS) and §6m (module
    natural), §6h reports first because dimension-RHS is the more
    elementary category error. The Classification carries only §6h
    (since §6h short-circuits, §6m is never evaluated)."""
    bad = Candidate(
        id="dim-rhs-and-module-natural",
        name="Hypothetical dim-RHS candidate that's also iso-class invariant",
        family=Family.MODULE_THEORETIC,
        rhs_type=RHSType.DIMENSION,
        is_module_natural_invariant=True,
    )
    result = classify(bad)
    assert result.obstructions_hit == ("6h",)
    assert result.verdict == Verdict.SHELVED_A_PRIORI


def test_6m_short_circuits_before_per_instance_obstructions() -> None:
    """§6m short-circuits like §6h: if it fires, per-instance
    obstructions (§6i/§6j/§6k/§6l) are NOT evaluated. The Classification
    carries only §6m and the blast radius is empty."""
    # A candidate that would also trigger §6j and §6l, but has the
    # module-natural flag set so §6m fires first.
    bad = Candidate(
        id="module-natural-plus-spectral-plus-char-theoretic",
        name="Hypothetical multi-failure candidate",
        family=Family.MODULE_THEORETIC,
        rhs_type=RHSType.WEIGHT,
        is_module_natural_invariant=True,
        requires_semisimple=True,        # would trigger §6j on most Bravyi
        uses_cayley_spectral_bound=True,  # would trigger §6l on all Bravyi
    )
    result = classify(bad)
    assert result.obstructions_hit == ("6m",)
    assert result.bravyi_blast_radius == ()
    assert result.verdict == Verdict.SHELVED_A_PRIORI


def test_6m_is_added_to_obstructions_registry() -> None:
    """Regression: §6m appears in the OBSTRUCTIONS registry with the
    correct HANDOFF reference. Catches forgetting to register a new
    obstruction after defining its predicate."""
    obs_ids = {o.id for o in OBSTRUCTIONS}
    assert "6m" in obs_ids
    obs_6m = next(o for o in OBSTRUCTIONS if o.id == "6m")
    assert obs_6m.section_ref == "HANDOFF.md §6m"


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
