"""Regression tests for the A5 goal-2 instance-hypothesis checker.

The contract is the A4 write-up's hand-derived data for the base code
`[[72,12,6]]` (notes/A4_writeup.md §3, §10.1):

  * the five-orbit component table (units / radicals of Â_j, B̂_j),
  * the kill vectors m = κ(B̂) = (ω², ω, 1, 0), m′ = κ(Â₃),
    κ(Â₄) = ω²·m,
  * the layer dictionary rows d₃({triv}) = 9, d₃(single) = 6,
    d₃({triv, single}) = 3,
  * the (ii)/(iii) verdicts.

If any of these change, that is a checker bug — the A4 values are
hand-proven and frozen.
"""

from __future__ import annotations

import importlib.util
import sys
from pathlib import Path

SCRIPT = (
    Path(__file__).resolve().parent.parent
    / "scripts"
    / "a5_instance_hypotheses.py"
)
spec = importlib.util.spec_from_file_location("a5_instance_hypotheses", SCRIPT)
a5 = importlib.util.module_from_spec(spec)
sys.modules["a5_instance_hypotheses"] = a5
spec.loader.exec_module(a5)

OMEGA = (0, 1)
OMEGA2 = (1, 1)
ONE = (1, 0)
ZERO2 = (0, 0)


def base_report(with_dictionary: bool = False):
    return a5.check_instance(
        "bb_72_12_6", 6, 6, "x^3 + y + y^2", "y^3 + x + x^2",
        with_dictionary=with_dictionary,
    )


def test_base_frame_and_verdicts():
    rep = base_report()
    assert rep.frame.shape == "Z2xZ2"
    assert rep.frame.odd_orders == (3, 3)
    assert rep.verdict_i and rep.verdict_ii and rep.verdict_iii


def test_base_component_table_matches_a4_section3():
    rep = base_report()
    kinds = {
        c.orbit_rep: (ca.kind, cb.kind)
        for c, ca, cb in zip(rep.comps_A, rep.comps_A, rep.comps_B)
    }
    # A4 §3 table: j=0 both units; j=1 (ψ=ω^{t_y}) Â radical / B̂ unit;
    # j=2 (ψ=ω^{t_x}) Â unit / B̂ radical; j=3, j=4 both radical.
    assert kinds[(0, 0)] == (a5.UNIT, a5.UNIT)
    assert kinds[(0, 1)] == (a5.ENGINE_RADICAL, a5.UNIT)
    assert kinds[(1, 0)] == (a5.UNIT, a5.ENGINE_RADICAL)
    assert kinds[(1, 1)] == (a5.ENGINE_RADICAL, a5.ENGINE_RADICAL)
    assert kinds[(1, 2)] == (a5.ENGINE_RADICAL, a5.ENGINE_RADICAL)


def test_base_kill_vectors_match_a4_section10_1():
    rep = base_report()
    kv = {(k.poly_name, k.orbit_rep): k for k in rep.kvs}
    m = (OMEGA2, OMEGA, ONE, ZERO2)
    m_prime = (OMEGA2, ONE, OMEGA, ZERO2)
    omega2_m = (OMEGA, ONE, OMEGA2, ZERO2)  # ω²·m entrywise
    # B̂₂ = B̂₃ = B̂₄ = ωX + Y → κ = m on all three radical orbits.
    for orbit in [(1, 0), (1, 1), (1, 2)]:
        assert kv[("B", orbit)].kappa == m
        assert kv[("B", orbit)].is_bijection
    # Â₁ = Â₃ = X + ωY → κ = m′;  κ(Â₄) = m′² = ω²·m.
    assert kv[("A", (0, 1))].kappa == m_prime
    assert kv[("A", (1, 1))].kappa == m_prime
    assert kv[("A", (1, 2))].kappa == omega2_m


def test_base_layer_dictionary_rows():
    rep = base_report(with_dictionary=True)
    d = rep.dictionary
    assert d["{triv}"] == 9  # (0,T) → 9
    for orbit in [(0, 1), (1, 0), (1, 1), (1, 2)]:
        assert d[f"{{{orbit}}}"] == 6  # (1,F) → 6
        assert d[f"{{triv,{orbit}}}"] == 3  # (1,T) → 3


def test_degenerate_instance_fails_ii():
    # A = B makes dA = dB: maximally non-disjoint difference sets.
    rep = a5.check_instance("deg", 6, 6, "1 + y + y^2", "1 + y + y^2")
    assert not rep.diff.disjoint
    assert not rep.verdict_ii


def test_semisimple_frame_classification():
    # Z15×Z3 (bb_90's group): odd order, no 2-part, no radical at all.
    rep = a5.check_instance("bb90_grp", 15, 3, "x^9 + y + y^2", "1 + x^2 + x^7")
    assert rep.frame.shape == "semisimple"
    for c in rep.comps_A + rep.comps_B:
        assert c.kind in (a5.UNIT, a5.ZERO)
