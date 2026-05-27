"""Tests for the `bb-lab classify` CLI subcommand.

Uses `click.testing.CliRunner` to invoke the entry point in-process; no
subprocess overhead. Each test exercises one verdict path:

  * §6h (dimension RHS) → SHELVED-A-PRIORI
  * §6j (char-theoretic + non-semisimple Bravyi) → PROCEED with blast
    radius
  * §6k (chain-map + gross) → PROCEED with blast radius
  * No obstructions (lifted-product weight) → PROCEED, empty blast
  * needs-new-theory flag → NEEDS-NEW-THEORY
  * --json flag → machine-readable output
"""

from __future__ import annotations

import json

import pytest
from click.testing import CliRunner

from bb_lab.cli import main


@pytest.fixture
def runner() -> CliRunner:
    return CliRunner()


# --- §6h: dimension RHS → SHELVED-A-PRIORI ---------------------------------


def test_dimension_rhs_is_shelved_a_priori(runner: CliRunner) -> None:
    result = runner.invoke(
        main,
        [
            "classify",
            "--family", "radical-weight",
            "--rhs", "dimension",
        ],
    )
    assert result.exit_code == 0, result.output
    assert "SHELVED-A-PRIORI" in result.output
    assert "6h" in result.output


# --- §6j: char-theoretic + non-semisimple Bravyi ---------------------------


def test_char_theoretic_hits_6j_on_gross_but_not_bb_90(runner: CliRunner) -> None:
    result = runner.invoke(
        main,
        [
            "classify",
            "--family", "char-theoretic",
            "--rhs", "weight",
        ],
    )
    assert result.exit_code == 0, result.output
    assert "6j" in result.output
    # gross is blocked; bb_90 is the §6j exception (|G|=45 odd).
    assert "gross_144_12_12" in result.output
    # The blast radius should NOT include bb_90 (it survives §6j).
    blast_section = result.output.split("bravyi blast radius:")[1].split("\n\nReasoning")[0]
    assert "6j@bb_90_8_10" not in blast_section
    # Verdict is PROCEED-with-blast (not all Bravyi blocked).
    assert "PROCEED" in result.output


# --- §6k: chain-map + gross ------------------------------------------------


def test_chain_map_hits_6k_on_gross(runner: CliRunner) -> None:
    result = runner.invoke(
        main,
        [
            "classify",
            "--family", "chain-map",
            "--rhs", "weight",
        ],
    )
    assert result.exit_code == 0, result.output
    assert "6k" in result.output
    assert "6k@gross_144_12_12" in result.output
    assert "PROCEED" in result.output


# --- no obstruction (Lin-Pryadko shape) ------------------------------------


def test_lifted_product_weight_proceeds_with_no_obstruction(runner: CliRunner) -> None:
    result = runner.invoke(
        main,
        [
            "classify",
            "--family", "lifted-product",
            "--rhs", "weight",
            "--name", "Lin-Pryadko Statement 12",
            "--citation", "arXiv:2306.16400",
        ],
    )
    assert result.exit_code == 0, result.output
    assert "PROCEED" in result.output
    assert "(none)" in result.output  # obstructions hit + blast radius both empty


# --- needs-new-theory flag --------------------------------------------------


def test_needs_new_theory_flag_short_circuits(runner: CliRunner) -> None:
    result = runner.invoke(
        main,
        [
            "classify",
            "--family", "radical-weight",
            "--rhs", "weight",
            "--needs-new-theory",
            "--name", "Family A radical-weight v2 seed",
        ],
    )
    assert result.exit_code == 0, result.output
    assert "NEEDS-NEW-THEORY" in result.output


# --- --json flag ------------------------------------------------------------


def test_json_output_is_parseable(runner: CliRunner) -> None:
    result = runner.invoke(
        main,
        [
            "classify",
            "--family", "char-theoretic",
            "--rhs", "weight",
            "--json",
        ],
    )
    assert result.exit_code == 0, result.output
    data = json.loads(result.output)
    assert data["verdict"] == "PROCEED"
    assert "6j" in data["obstructions_hit"]
    assert any(
        entry.startswith("6j@") and "gross" in entry
        for entry in data["bravyi_blast_radius"]
    )
    assert isinstance(data["reasoning"], list)


def test_json_output_for_shelved_candidate(runner: CliRunner) -> None:
    result = runner.invoke(
        main,
        ["classify", "--family", "radical-weight", "--rhs", "dimension", "--json"],
    )
    assert result.exit_code == 0
    data = json.loads(result.output)
    assert data["verdict"] == "SHELVED-A-PRIORI"
    assert data["obstructions_hit"] == ["6h"]


# --- input validation -------------------------------------------------------


def test_unknown_family_is_rejected(runner: CliRunner) -> None:
    result = runner.invoke(
        main,
        ["classify", "--family", "not-a-real-family", "--rhs", "weight"],
    )
    assert result.exit_code != 0
    assert "Invalid value for '--family'" in result.output


def test_unknown_rhs_is_rejected(runner: CliRunner) -> None:
    result = runner.invoke(
        main,
        ["classify", "--family", "char-theoretic", "--rhs", "not-a-type"],
    )
    assert result.exit_code != 0


def test_missing_required_flags(runner: CliRunner) -> None:
    result = runner.invoke(main, ["classify"])
    assert result.exit_code != 0
    # Either --family or --rhs missing; click reports the first one.
    assert "Missing option" in result.output


# --- help text covers the subcommand ----------------------------------------


def test_classify_appears_in_top_level_help(runner: CliRunner) -> None:
    result = runner.invoke(main, ["--help"])
    assert result.exit_code == 0
    assert "classify" in result.output


def test_classify_subcommand_help(runner: CliRunner) -> None:
    result = runner.invoke(main, ["classify", "--help"])
    assert result.exit_code == 0
    assert "Tier-0" in result.output
    assert "--family" in result.output
    assert "--rhs" in result.output
