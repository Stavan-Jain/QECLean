"""A5 (goal 2) — per-instance hypothesis checker for the Theorem-A template.

A4 §7 "Generalization (goal 2)" identifies the three per-instance
hypotheses that the small-cycle proof (A4 Theorem A) consumed:

  (i)   CRT component structure of F₂[G_base]: every Frobenius-orbit
        component of Â and B̂ is a unit or an "engine-grade" radical
        (value vector over the Z₂² layers with exactly one zero and
        three pairwise-distinct nonzero values — the §3 engine lemma's
        rigidity input);
  (ii)  multiplicity-free difference sets with dA ∩ dB = ∅, disjoint
        in BOTH coordinates;
  (iii) the coordinate projections π_x, π_y follow the gross pattern
        (each polynomial collapses to a monomial in one coordinate and
        survives multiplicity-free in the other, in the mirrored
        arrangement).

This script computes, for a BB instance (group Z_ℓ × Z_m, polynomials
A, B over F₂):

  * the CRT frame shape (2-part of the group: trivial / Z₂ / Z₂×Z₂ /
    deeper) — the A4 frame needs Z₂×Z₂;
  * the per-orbit component table (unit / engine radical / other
    radical / zero), the analogue of A4 §3's Â_j/B̂_j table;
  * the difference-set verdicts of (ii);
  * the coordinate-projection verdicts of (iii);
  * goal-2 labeling data when applicable (kill vectors κ(Â_j), κ(B̂_j)
    of A4 §10.1, with slot-bijection flags — the "m-analogue");
  * the layer-dictionary d_H rows for the odd part (the d₃ analogue of
    A4 §3, single-orbit Fourier-support classes) — DISCOVERY ONLY.

Hard-constraint note (A_HANDOFF §1): everything this script outputs is
discovery/validation data.  No number computed here is load-bearing in
any theorem; instances that "pass" are candidates for a hand run of the
Theorem-A case grid, nothing more.

Usage:
    uv run python scripts/a5_instance_hypotheses.py --bravyi
    uv run python scripts/a5_instance_hypotheses.py --code-id bb_108_8_10
    uv run python scripts/a5_instance_hypotheses.py --ell 9 --m 6 \
        --A 'x^3 + y + y^2' --B 'y^3 + x + x^2'
    uv run python scripts/a5_instance_hypotheses.py --db-sweep Z6xZ6 \
        [--limit N] [--jsonl out.jsonl]
"""

from __future__ import annotations

import argparse
import json
import sys
from dataclasses import dataclass, field
from itertools import product
from math import gcd, lcm
from pathlib import Path

LAB_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(LAB_ROOT / "src"))

import numpy as np
import yaml

from bb_lab.algebraic_features import (
    _PRIM_POLYS,
    _fld_mul,
    _fld_pow,
    _odd_part,
    _order_2_mod,
    frobenius_orbits,
)
from bb_lab.group import AbelianGroup
from bb_lab.linalg import nullspace_f2
from bb_lab.poly import Poly

# ---------------------------------------------------------------------------
# Group frame: 2-part × odd part per axis
# ---------------------------------------------------------------------------


def _two_part(n: int) -> int:
    return n // _odd_part(n)


@dataclass(frozen=True)
class CRTFrame:
    """Per-axis CRT split of G = Z_ℓ × Z_m into 2-part × odd part."""

    orders: tuple[int, ...]
    two_orders: tuple[int, ...]  # per-axis 2-part order (1, 2, 4, ...)
    odd_orders: tuple[int, ...]  # per-axis odd part

    @property
    def shape(self) -> str:
        """Frame classification: the A4 engine needs 'Z2xZ2'."""
        nontriv = tuple(t for t in self.two_orders if t > 1)
        if any(t > 2 for t in self.two_orders):
            return "deeper"  # radical depth > 2: A4 engine does not apply
        if nontriv == (2, 2):
            return "Z2xZ2"
        if nontriv == (2,):
            return "Z2"
        return "semisimple"  # odd |G|: no radical at all

    @property
    def layers(self) -> list[tuple[int, ...]]:
        """2-part elements in lexicographic order; for Z₂×Z₂ this is
        (e, s_x, s_y, s_x s_y) — the slot order of A4 §10.1."""
        ranges = [range(t) for t in self.two_orders]
        # product(*ranges) with the LAST axis varying fastest would give
        # (0,0),(0,1),(1,0),(1,1); A4 slot order is (e, x, y, xy), i.e.
        # first axis varies fastest.
        out = [tuple(reversed(t)) for t in product(*reversed(ranges))]
        return out


def crt_frame(G: AbelianGroup) -> CRTFrame:
    return CRTFrame(
        orders=G.orders,
        two_orders=tuple(_two_part(n) for n in G.orders),
        odd_orders=tuple(_odd_part(n) for n in G.orders),
    )


def split_element(g: tuple[int, ...], frame: CRTFrame) -> tuple[tuple[int, ...], tuple[int, ...]]:
    """g ↦ (layer, odd part), per-axis CRT."""
    s = tuple(gi % t for gi, t in zip(g, frame.two_orders))
    t = tuple(gi % o for gi, o in zip(g, frame.odd_orders))
    return s, t


def layer_slices(
    poly: Poly, frame: CRTFrame
) -> dict[tuple[int, ...], frozenset[tuple[int, ...]]]:
    """Partition supp(poly) by 2-part layer; values are odd-part supports.

    The per-axis CRT Z_n ≅ Z_{2^a} × Z_{n_odd} is a bijection, so no two
    support cells collide — slices are honest subsets of the odd group.
    """
    slices: dict[tuple[int, ...], set[tuple[int, ...]]] = {
        s: set() for s in frame.layers
    }
    for g in poly.support:
        s, t = split_element(g, frame)
        slices[s].add(t)
    return {s: frozenset(ts) for s, ts in slices.items()}


# ---------------------------------------------------------------------------
# Per-orbit component value vectors  V_j(f)[s] = ψ_j(f_s) ∈ F_{2^r}
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class OrbitField:
    """A Frobenius orbit on the odd character group with its field data."""

    rep: tuple[int, ...]  # representative character k_odd
    size: int  # orbit size = r (for the component field F_{2^r})
    char_order: int  # d = order of χ_rep
    prim_poly: tuple[int, ...]  # F_{2^r} modulus
    # ψ(t) lookup: alpha_powers[exp] as tuples, exp ∈ Z/d
    alpha_powers: tuple[tuple[int, ...], ...]
    # per-axis reduced character data for exponent computation
    k_red: tuple[int, ...]
    d_axes: tuple[int, ...]

    @property
    def r(self) -> int:
        return len(self.prim_poly) - 1

    def psi_exp(self, t: tuple[int, ...]) -> int:
        """Exponent e with ψ(t) = α^e, α the chosen primitive d-th root."""
        e = 0
        for kr, da, ti in zip(self.k_red, self.d_axes, t):
            e += kr * ti * (self.char_order // da)
        return e % self.char_order

    def char_sum(self, ts: frozenset[tuple[int, ...]]) -> tuple[int, ...]:
        """Σ_{t ∈ ts} ψ(t) as an F₂-vector of length r."""
        acc = [0] * self.r
        for t in ts:
            ap = self.alpha_powers[self.psi_exp(t)]
            for i in range(self.r):
                acc[i] ^= ap[i]
        return tuple(acc)


def _chi_order(k_odd: tuple[int, ...], odd_orders: tuple[int, ...]) -> int:
    d = 1
    for ki, no in zip(k_odd, odd_orders):
        if ki:
            d = lcm(d, no // gcd(ki, no))
    return d


def orbit_fields(odd_orders: tuple[int, ...]) -> list[OrbitField]:
    """All Frobenius orbits on the odd character group, with field data.

    Sorted canonically: trivial orbit first, then by (size, sorted reps).
    """
    H = AbelianGroup(odd_orders)
    orbits = sorted(frobenius_orbits(H), key=lambda o: (len(o), sorted(o)))
    out: list[OrbitField] = []
    for orb in orbits:
        rep = min(orb)
        d = _chi_order(rep, odd_orders)
        r = _order_2_mod(d)
        assert r == len(orb), f"orbit size {len(orb)} != ord_d(2) = {r} (d={d})"
        if r not in _PRIM_POLYS:
            raise NotImplementedError(f"no primitive polynomial of degree {r}")
        p = _PRIM_POLYS[r]
        # α := X^((2^r − 1)/d) has multiplicative order exactly d.
        X = [0] * r
        if r > 1:
            X[1] = 1
        else:
            X[0] = 1  # F₂: only α = 1 (d = 1 forced)
        alpha = _fld_pow(X, (2**r - 1) // d, p) if d > 1 else _fld_pow(X, 0, p)
        powers: list[tuple[int, ...]] = []
        cur = [0] * r
        cur[0] = 1
        for _ in range(d):
            powers.append(tuple(cur))
            cur = _fld_mul(cur, alpha, p)
        k_red: list[int] = []
        d_axes: list[int] = []
        for ki, no in zip(rep, odd_orders):
            if ki == 0:
                k_red.append(0)
                d_axes.append(1)
            else:
                g = gcd(ki, no)
                k_red.append(ki // g)
                d_axes.append(no // g)
        out.append(
            OrbitField(
                rep=rep,
                size=len(orb),
                char_order=d,
                prim_poly=tuple(p),
                alpha_powers=tuple(powers),
                k_red=tuple(k_red),
                d_axes=tuple(d_axes),
            )
        )
    return out


# ---------------------------------------------------------------------------
# Component classification (the §3 table analogue)
# ---------------------------------------------------------------------------

ZERO = "zero"
UNIT = "unit"
ENGINE_RADICAL = "engine_radical"
# A15 Entry-8.1b widening: the engine's SUPPORT dichotomy needs only the
# four slot values pairwise distinct (⟺ {0,a,b,a+b} distinct in the
# U,V-coordinates) — field-generic, no |F₄ˣ| = 3 input.  ENGINE_RADICAL
# ("one zero + three distinct") is the sub-case with a zero slot; the
# label below marks the distinct-no-zero radicals the widened one-sided
# floor also covers.  Additive: no pre-existing classification changes.
ENGINE_RADICAL_WIDENED = "engine_radical_widened"
RADICAL_OTHER = "radical_other"


@dataclass(frozen=True)
class Component:
    """One Frobenius-orbit component of one polynomial."""

    orbit_rep: tuple[int, ...]
    field_r: int
    value_vector: tuple[tuple[int, ...], ...]  # per layer, F₂-vectors
    kind: str  # ZERO | UNIT | ENGINE_RADICAL | RADICAL_OTHER

    def vec_str(self) -> str:
        return "(" + ", ".join(_f2vec_str(v) for v in self.value_vector) + ")"


def _f2vec_str(v: tuple[int, ...]) -> str:
    """Pretty-print an F_{2^r} element. For r = 2 use 0/1/ω/ω²
    (with the t² + t + 1 modulus: ω = t, ω² = t + 1)."""
    if not any(v):
        return "0"
    if len(v) == 1:
        return "1"
    if len(v) == 2:
        return {(1, 0): "1", (0, 1): "ω", (1, 1): "ω²"}[tuple(v)]
    # generic: bit string, LSB first
    return "[" + "".join(str(b) for b in v) + "]"


def classify_component(
    vec: tuple[tuple[int, ...], ...], frame_shape: str
) -> str:
    """Classify a component from its value vector over the layers.

    unit  ⟺ augmentation Σ_s V[s] ≠ 0 (invertible in the local ring
            K[G₂]); zero ⟺ all V[s] = 0; otherwise radical.
    Engine grade (Z₂×Z₂ frames only): exactly one zero value and three
    pairwise-distinct nonzero values — the §3 engine lemma's co-point
    rigidity input.
    """
    r = len(vec[0])
    nonzero = [v for v in vec if any(v)]
    if not nonzero:
        return ZERO
    aug = [0] * r
    for v in vec:
        for i in range(r):
            aug[i] ^= v[i]
    if any(aug):
        return UNIT
    if frame_shape == "Z2xZ2" and len(vec) == 4:
        n_zero = len(vec) - len(nonzero)
        if n_zero == 1 and len(set(nonzero)) == 3:
            return ENGINE_RADICAL
        if len(set(vec)) == 4:
            return ENGINE_RADICAL_WIDENED
    return RADICAL_OTHER


def component_table(
    poly: Poly, frame: CRTFrame, fields: list[OrbitField]
) -> list[Component]:
    slices = layer_slices(poly, frame)
    out: list[Component] = []
    for of in fields:
        vec = tuple(of.char_sum(slices[s]) for s in frame.layers)
        out.append(
            Component(
                orbit_rep=of.rep,
                field_r=of.size,
                value_vector=vec,
                kind=classify_component(vec, frame.shape),
            )
        )
    return out


# ---------------------------------------------------------------------------
# (ii) difference sets
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class DiffSetReport:
    dA: frozenset[tuple[int, ...]]
    dB: frozenset[tuple[int, ...]]
    dA_mult_free: bool
    dB_mult_free: bool
    disjoint: bool  # dA ∩ dB = ∅
    coord_disjoint: tuple[bool, ...]  # per axis: π_axis(dA) ∩ π_axis(dB) = ∅

    @property
    def verdict(self) -> bool:
        return (
            self.dA_mult_free
            and self.dB_mult_free
            and self.disjoint
            and all(self.coord_disjoint)
        )


def diff_set_report(A: Poly, B: Poly, G: AbelianGroup) -> DiffSetReport:
    def diffs(p: Poly) -> tuple[list[tuple[int, ...]], frozenset[tuple[int, ...]]]:
        lst = [
            G.sub(a, b)
            for a in p.support
            for b in p.support
            if a != b
        ]
        return lst, frozenset(lst)

    dA_list, dA = diffs(A)
    dB_list, dB = diffs(B)
    rank = G.rank
    coord_disjoint = tuple(
        not ({d[ax] for d in dA} & {d[ax] for d in dB}) for ax in range(rank)
    )
    return DiffSetReport(
        dA=dA,
        dB=dB,
        dA_mult_free=len(dA_list) == len(dA),
        dB_mult_free=len(dB_list) == len(dB),
        disjoint=not (dA & dB),
        coord_disjoint=coord_disjoint,
    )


# ---------------------------------------------------------------------------
# (iii) coordinate projections
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class ProjectionReport:
    # supports of π_axis(poly) ⊂ Z_{n_axis}, with mod-2 collapse
    proj_A: tuple[frozenset[int], ...]
    proj_B: tuple[frozenset[int], ...]

    @property
    def pattern(self) -> str:
        """'gross' if A is a monomial in exactly one axis and B is a
        monomial in exactly the other, with both surviving at full
        weight on their non-monomial axis."""
        mono_A = [i for i, s in enumerate(self.proj_A) if len(s) == 1]
        mono_B = [i for i, s in enumerate(self.proj_B) if len(s) == 1]
        if len(mono_A) == 1 and len(mono_B) == 1 and mono_A[0] != mono_B[0]:
            return "gross"
        return "other"

    @property
    def verdict(self) -> bool:
        return self.pattern == "gross"


def projection_report(A: Poly, B: Poly, G: AbelianGroup) -> ProjectionReport:
    def proj(p: Poly, axis: int) -> frozenset[int]:
        counts: dict[int, int] = {}
        for g in p.support:
            counts[g[axis]] = counts.get(g[axis], 0) + 1
        return frozenset(x for x, c in counts.items() if c % 2)

    return ProjectionReport(
        proj_A=tuple(proj(A, ax) for ax in range(G.rank)),
        proj_B=tuple(proj(B, ax) for ax in range(G.rank)),
    )


# ---------------------------------------------------------------------------
# Goal-2 labeling data (§10.1 m-analogue) — Z₂×Z₂ frames only
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class KillVector:
    """κ(v) = slot function modulo the constant shift (A4 §10.1)."""

    orbit_rep: tuple[int, ...]
    poly_name: str
    kappa: tuple[tuple[int, ...], ...]  # length-4, last entry 0
    is_bijection: bool  # κ: slots → F₄ bijective (needs r = 2)


def kill_vectors(
    name: str, comps: list[Component], frame: CRTFrame
) -> list[KillVector]:
    """Kill vectors of the radical components (the labeling candidates).

    From the coefficient vector (c_e, c_x, c_y, c_xy) over the slot
    order (e, s_x, s_y, s_xy):  κ = (c_e+c_xy, c_x+c_xy, c_y+c_xy, 0).
    """
    if frame.shape != "Z2xZ2":
        return []
    out: list[KillVector] = []
    for c in comps:
        if c.kind not in (ENGINE_RADICAL, ENGINE_RADICAL_WIDENED,
                          RADICAL_OTHER):
            continue
        ce, cx, cy, cxy = c.value_vector
        r = len(ce)
        kap = tuple(
            tuple(a ^ b for a, b in zip(v, cxy)) for v in (ce, cx, cy)
        ) + (tuple([0] * r),)
        distinct = len(set(kap)) == 4
        out.append(
            KillVector(
                orbit_rep=c.orbit_rep,
                poly_name=name,
                kappa=kap,
                is_bijection=(r == 2 and distinct),
            )
        )
    return out


# ---------------------------------------------------------------------------
# Layer dictionary d_H (the d₃ analogue) — DISCOVERY ONLY
# ---------------------------------------------------------------------------


def layer_dictionary(
    odd_orders: tuple[int, ...],
    fields: list[OrbitField],
    dim_cap: int = 16,
) -> dict[str, int | None]:
    """min weight of nonzero f ∈ F₂[H] with Fourier support ⊆ W, for
    W = {trivial}, each single nontrivial orbit, and each
    {trivial, nontrivial-orbit} pair.  None where the ideal dimension
    exceeds dim_cap (enumeration would be too large) — refine later if
    a template run actually needs that row.
    """
    H = AbelianGroup(odd_orders)
    elems = list(H)
    n = len(elems)

    def constraint_rows(excluded: list[OrbitField]) -> np.ndarray:
        rows: list[list[int]] = []
        for of in excluded:
            for i in range(of.r):
                rows.append(
                    [of.alpha_powers[of.psi_exp(t)][i] for t in elems]
                )
        return np.array(rows, dtype=np.uint8) if rows else np.zeros((0, n), dtype=np.uint8)

    def min_weight(W_idx: set[int]) -> int | None:
        excluded = [of for i, of in enumerate(fields) if i not in W_idx]
        basis = nullspace_f2(constraint_rows(excluded))
        k = basis.shape[0]
        if k == 0:
            return None  # zero ideal
        if k > dim_cap:
            return None
        best = n + 1
        for mask in range(1, 2**k):
            v = np.zeros(n, dtype=np.uint8)
            mm = mask
            i = 0
            while mm:
                if mm & 1:
                    v ^= basis[i]
                mm >>= 1
                i += 1
            w = int(v.sum())
            if 0 < w < best:
                best = w
        return best

    out: dict[str, int | None] = {}
    trivial_idx = next(
        i for i, of in enumerate(fields) if of.char_order == 1
    )
    out["{triv}"] = min_weight({trivial_idx})
    for i, of in enumerate(fields):
        if i == trivial_idx:
            continue
        label = f"{{{of.rep}}}"
        out[label] = min_weight({i})
        out[f"{{triv,{of.rep}}}"] = min_weight({trivial_idx, i})
    return out


# ---------------------------------------------------------------------------
# Instance report
# ---------------------------------------------------------------------------


@dataclass
class InstanceReport:
    label: str
    G: AbelianGroup
    A: Poly
    B: Poly
    frame: CRTFrame
    comps_A: list[Component]
    comps_B: list[Component]
    diff: DiffSetReport
    proj: ProjectionReport
    kvs: list[KillVector] = field(default_factory=list)
    dictionary: dict[str, int | None] = field(default_factory=dict)

    @property
    def verdict_i(self) -> bool:
        """(i): every component of Â and B̂ is a unit or engine-grade
        radical.  Only claims Theorem-A applicability on Z₂×Z₂ frames."""
        return all(
            c.kind in (UNIT, ENGINE_RADICAL)
            for c in self.comps_A + self.comps_B
        )

    @property
    def verdict_i_widened(self) -> bool:
        """(i) with the A15 Entry-8.1b field-generic predicate: every
        component a unit or a pairwise-distinct-slot radical.  Licenses
        the widened one-sided floor μ(Ann) ≥ 6 on Z₂×Z₂ frames with
        ANY odd part (the classification layers stay F₄-only)."""
        return all(
            c.kind in (UNIT, ENGINE_RADICAL, ENGINE_RADICAL_WIDENED)
            for c in self.comps_A + self.comps_B
        )

    @property
    def verdict_ii(self) -> bool:
        return self.diff.verdict

    @property
    def verdict_iii(self) -> bool:
        return self.proj.verdict

    def summary_row(self) -> dict:
        kinds_A = [c.kind for c in self.comps_A]
        kinds_B = [c.kind for c in self.comps_B]
        return {
            "label": self.label,
            "group": "x".join(f"Z{n}" for n in self.G.orders),
            "A": self.A.canonical_string(),
            "B": self.B.canonical_string(),
            "frame": self.frame.shape,
            "i": self.verdict_i,
            "i_widened": self.verdict_i_widened,
            "ii": self.verdict_ii,
            "iii": self.verdict_iii,
            "ii_mult_free": self.diff.dA_mult_free and self.diff.dB_mult_free,
            "ii_disjoint": self.diff.disjoint,
            "ii_coord_disjoint": all(self.diff.coord_disjoint),
            "n_unit_A": kinds_A.count(UNIT),
            "n_engine_A": kinds_A.count(ENGINE_RADICAL),
            "n_other_A": kinds_A.count(RADICAL_OTHER) + kinds_A.count(ZERO),
            "n_unit_B": kinds_B.count(UNIT),
            "n_engine_B": kinds_B.count(ENGINE_RADICAL),
            "n_other_B": kinds_B.count(RADICAL_OTHER) + kinds_B.count(ZERO),
        }


def check_instance(
    label: str,
    ell: int,
    m: int,
    A_str: str,
    B_str: str,
    with_dictionary: bool = False,
) -> InstanceReport:
    G = AbelianGroup((ell, m))
    A = Poly.from_string(A_str, G)
    B = Poly.from_string(B_str, G)
    frame = crt_frame(G)
    fields = orbit_fields(frame.odd_orders)
    comps_A = component_table(A, frame, fields)
    comps_B = component_table(B, frame, fields)
    rep = InstanceReport(
        label=label,
        G=G,
        A=A,
        B=B,
        frame=frame,
        comps_A=comps_A,
        comps_B=comps_B,
        diff=diff_set_report(A, B, G),
        proj=projection_report(A, B, G),
    )
    rep.kvs = kill_vectors("A", comps_A, frame) + kill_vectors("B", comps_B, frame)
    if with_dictionary:
        rep.dictionary = layer_dictionary(frame.odd_orders, fields)
    return rep


# ---------------------------------------------------------------------------
# Reporting
# ---------------------------------------------------------------------------


def print_report(rep: InstanceReport, verbose: bool = True) -> None:
    g = "×".join(f"Z{n}" for n in rep.G.orders)
    print(f"== {rep.label}  ({g}, A = {rep.A.canonical_string()}, "
          f"B = {rep.B.canonical_string()})")
    print(
        f"   frame: 2-part {'×'.join(f'Z{t}' for t in rep.frame.two_orders)}"
        f" → {rep.frame.shape}; odd part "
        f"{'×'.join(f'Z{o}' for o in rep.frame.odd_orders)}"
    )
    v = lambda b: "PASS" if b else "FAIL"
    print(
        f"   (i) components {v(rep.verdict_i)} | (ii) diff sets "
        f"{v(rep.verdict_ii)} | (iii) projections {v(rep.verdict_iii)}"
    )
    if verbose:
        print("   component table (value vectors over layers "
              f"{rep.frame.layers}):")
        for ca, cb in zip(rep.comps_A, rep.comps_B):
            print(
                f"     orbit {str(ca.orbit_rep):10s} r={ca.field_r}:  "
                f"Â {ca.kind:15s} {ca.vec_str():28s} "
                f"B̂ {cb.kind:15s} {cb.vec_str()}"
            )
        d = rep.diff
        print(
            f"   diff sets: |dA|={len(d.dA)} mult-free={d.dA_mult_free}, "
            f"|dB|={len(d.dB)} mult-free={d.dB_mult_free}, "
            f"dA∩dB=∅:{d.disjoint}, coord-disjoint={d.coord_disjoint}"
        )
        p = rep.proj
        for ax, nm in enumerate("xy"):
            print(
                f"   π_{nm}(A) = {sorted(p.proj_A[ax])}  "
                f"π_{nm}(B) = {sorted(p.proj_B[ax])}"
            )
        print(f"   projection pattern: {p.pattern}")
        for kv in rep.kvs:
            print(
                f"   κ({kv.poly_name}, orbit {kv.orbit_rep}) = "
                f"({', '.join(_f2vec_str(x) for x in kv.kappa)})"
                f"  bijection={kv.is_bijection}"
            )
        if rep.dictionary:
            print("   layer dictionary d_H (discovery only):")
            for k_, v_ in rep.dictionary.items():
                print(f"     d_H({k_}) = {v_}")
    print()


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------


def _load_bravyi() -> list[dict]:
    data = yaml.safe_load((LAB_ROOT / "instances" / "bravyi_table.yaml").read_text())
    return data["instances"]


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--bravyi", action="store_true")
    ap.add_argument("--code-id", type=str)
    ap.add_argument("--ell", type=int)
    ap.add_argument("--m", type=int)
    ap.add_argument("--A", type=str)
    ap.add_argument("--B", type=str)
    ap.add_argument("--db-sweep", type=str, metavar="GROUP_STRUCT")
    ap.add_argument("--require-exact-d", action="store_true", default=True)
    ap.add_argument("--no-require-exact-d", dest="require_exact_d",
                    action="store_false")
    ap.add_argument("--limit", type=int, default=None)
    ap.add_argument("--jsonl", type=Path, default=None)
    ap.add_argument("--dictionary", action="store_true",
                    help="compute the d_H layer dictionary (slower)")
    args = ap.parse_args()

    if args.bravyi or args.code_id:
        insts = _load_bravyi()
        if args.code_id:
            insts = [i for i in insts if i["code_id"] == args.code_id]
            if not insts:
                ap.error(f"code_id {args.code_id!r} not in bravyi_table.yaml")
        for inst in insts:
            rep = check_instance(
                inst["code_id"],
                inst["group"]["ell"],
                inst["group"]["m"],
                inst["polynomials"]["A"],
                inst["polynomials"]["B"],
                with_dictionary=args.dictionary,
            )
            print_report(rep)
        return

    if args.ell and args.m and args.A and args.B:
        rep = check_instance(
            f"Z{args.ell}xZ{args.m}", args.ell, args.m, args.A, args.B,
            with_dictionary=args.dictionary,
        )
        print_report(rep)
        return

    if args.db_sweep:
        import duckdb

        con = duckdb.connect(str(LAB_ROOT / "data" / "bb_instances.duckdb"),
                             read_only=True)
        q = (
            "select instance_id, ell, m, A_poly, B_poly, n, k, d_exact "
            "from bb_instances where group_struct = ?"
        )
        if args.require_exact_d:
            q += " and d_exact is not null"
        q += " order by instance_id"
        if args.limit:
            q += f" limit {args.limit}"
        rows = con.execute(q, [args.db_sweep]).fetchall()
        print(f"# sweep {args.db_sweep}: {len(rows)} instances")
        out_f = args.jsonl.open("w") if args.jsonl else None
        # cross-tab: verdict triple → list of d_exact
        xtab: dict[tuple, list] = {}
        for iid, ell, m, A_str, B_str, n, k, d_exact in rows:
            rep = check_instance(iid, ell, m, A_str, B_str)
            row = rep.summary_row()
            row.update({"n": n, "k": k, "d_exact": d_exact})
            key = (row["frame"], row["i"], row["ii"], row["iii"])
            xtab.setdefault(key, []).append(d_exact)
            if out_f:
                out_f.write(json.dumps(row) + "\n")
        if out_f:
            out_f.close()
        print(f"\n# cross-tab  (frame, i, ii, iii) → d_exact distribution")
        for key in sorted(xtab, key=str):
            ds = xtab[key]
            from collections import Counter

            cnt = Counter(d for d in ds)
            dist = ", ".join(f"d={d}:{c}" for d, c in sorted(cnt.items(),
                             key=lambda t: (t[0] is None, t[0])))
            print(f"  {key}: n={len(ds)}  [{dist}]")
        return

    ap.print_help()


if __name__ == "__main__":
    main()
