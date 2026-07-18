"""Pre-flight obstruction gate for candidate BB-code distance bounds (Tier 0).

Encodes the §6h–§6m structural obstructions from
`experiments/bb_lab/HANDOFF.md` as machine-checkable predicates on a
`Candidate` descriptor, evaluated against canonical Bravyi-table
fingerprints. `classify(candidate)` returns a `Classification` that
shapes the round-2 generation loop (see `HANDOFF_R2.md` §4).

Why this exists: round 1 ran four shelved conjecture rounds before
the §6h–§6k structural patterns were articulated as standalone
obstructions. Three of those four rounds would have been blocked at
proposal time by the predicates encoded here.

Encoded obstructions:

  §6h  dimension invariants bound `k`, not `d`. Fires on candidates
       whose RHS is a dimension quantity (rank, dim ker, orbit-size
       sum) claimed as a distance lower bound. Category error;
       SHELVED-A-PRIORI regardless of instance.

  §6i  Bravyi engineers degeneracy (every Bravyi-table code has c = 3).
       Fires on candidates whose hypothesis requires non-degeneracy
       (c = 1 or ⟨supp(A)⟩ = G). Excludes the engineering target.

  §6j  Character-theoretic bounds blocked when F[G] is non-semisimple
       (`gcd(|G|, char F) > 1`). Fires on `char-theoretic` family
       candidates against instances with `2 | |G|`. Bravyi has 4 of
       5 instances with `2 | |G|`; bb_90_8_10 (|G| = 45) is the lone
       exception.

  §6k  Chain-map / cover-graph bounds blocked when cover index shares
       a factor with char F. Fires on `chain-map` family candidates
       against instances known to be h-covers with `gcd(h, char F) > 1`.
       gross_144_12_12 is the canonical case (h = 2 cover of bb_72
       over F_2).

  §6l  Cayley-graph spectral bounds are vacuous on BB codes with
       k ≥ 2. For any BB code with k > 0, A and B jointly vanish on a
       non-trivial character χ of G (Bravyi 2024 Lemma 1), which forces
       the Cayley-graph eigenvalue `λ_A(χ) = weight(A)`. The spectral
       gap `weight − λ_2` is therefore ≤ 0, making any Sipser-Spielman /
       Tanner / Cheeger-style spectral lower bound identically zero on
       every Bravyi instance. Round-2 Tier 2 Family C v1 (empirical
       Pearson correlation −0.020 across 4,364 SAT-verified rows).

  §6m  F_2[G]-module-isomorphism-class invariants cannot lower-bound
       d_X. Min Hamming weight is not a module-iso invariant: for
       gross, H_0(K) ≅ H_2(K) as F_2[G]-modules (Frobenius duality)
       but min_wt(H_0) = 1 and min_wt(H_2) = 32 (32× gap). Any
       function ψ([M(A, B)]) that depends only on the F_2[G]-module
       iso class of a construction M(A, B) — Hilbert series, CM
       regularity, Betti / Tor / Ext dimensions, projective dimension,
       depth — collapses to the minimum d_X over the iso-orbit, which
       can be small. Structural; SHELVED-A-PRIORI regardless of
       instance. Round-2 v2 Tier 0; the witness lives at
       `scripts/family_d_v1_koszul_h2_iso_witness.py`.

See `experiments/bb_lab/HANDOFF.md` §6h–§6m for the full math and
the round-1 / round-2 failures that motivated each entry.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from enum import Enum
from math import gcd
from typing import Callable


class Family(str, Enum):
    """Categorical family of a candidate distance bound.

    Determines which obstructions can fire. Add a new family only when
    a candidate's mathematical machinery is structurally distinct from
    every existing family (e.g. not a re-parameterization).
    """

    CHAR_THEORETIC = "char-theoretic"
    """Bounds derived from Fourier/character decomposition of F[G].
    Blocked by §6j when F[G] is non-semisimple."""

    CHAIN_MAP = "chain-map"
    """Bounds via cover-graph chain-map injectivity. Blocked by §6k
    when `gcd(h, char F) > 1` for the cover index h."""

    COMBINATORIAL = "combinatorial"
    """Tanner girth, expansion, percolation bounds. Char-agnostic;
    no §6 obstruction fires structurally. Typically loose."""

    RADICAL_WEIGHT = "radical-weight"
    """Weight invariants on the Jacobson-radical filtration of F[G].
    The §6k surviving direction; not obstruction-blocked by §6j/§6k."""

    MODULE_THEORETIC = "module-theoretic"
    """Direct F[G]-module / syzygy / Gröbner-style. Bypasses Fourier;
    not blocked by §6j."""

    SYZYGY = "syzygy"
    """Specifically uses the second syzygy module of (A, B). Distinct
    from MODULE_THEORETIC if a candidate is built specifically around
    syzygy-degree arguments."""

    COMPUTATIONAL_LP = "computational-LP"
    """Closed-form LP/SDP-relaxation bounds. Char-agnostic if the
    LP doesn't go through Fourier internally."""

    LIFTED_PRODUCT = "lifted-product"
    """Generic lifted-product bounds (Lin–Pryadko, Tillich–Zémor,
    Kovalev–Pryadko Thm 5). Char-agnostic by construction; not
    blocked by §6j/§6k structurally, but historically loose on
    engineered polynomials."""


class RHSType(str, Enum):
    """What kind of quantity the bound's right-hand side is.

    Distance is a weight quantity. §6h fires when a candidate claims
    a dimension quantity bounds it.
    """

    WEIGHT = "weight"
    """Hamming weight or a minimum thereof. The correct type for
    bounding `d`."""

    DIMENSION = "dimension"
    """Vector-space dimension, rank, orbit-size sum, or similar.
    Bounds `k` (the coset-space size) but NOT `d` (the minimum
    weight in a coset). §6h fires."""

    MIXED = "mixed"
    """A combination — e.g. `weight / structural_index`. Generally
    safe; treat as WEIGHT unless the dimension part dominates."""


class Verdict(str, Enum):
    """Outcome of pre-flight classification."""

    PROCEED = "PROCEED"
    """No obstruction blocks every Bravyi instance. Advance to
    Tier 2/3."""

    SHELVED_A_PRIORI = "SHELVED-A-PRIORI"
    """Either §6h category error, or every Bravyi instance is
    blocked. Do not generate code; archive with citation."""

    NEEDS_NEW_THEORY = "NEEDS-NEW-THEORY"
    """Candidate explicitly requires unbuilt mathematics. Mark as
    a research seed; do not pursue formally yet."""


@dataclass(frozen=True, slots=True)
class Candidate:
    """A proposed analytic distance lower bound for BB codes."""

    id: str
    name: str
    family: Family
    rhs_type: RHSType
    bound_formula: str = ""
    citation: str = ""

    # Hypothesis predicates the bound requires.
    requires_non_degenerate: bool = False
    """If True, the bound is only valid when ⟨supp(A)⟩ = G (i.e.
    c = 1). Fires §6i on degenerate Bravyi instances."""

    requires_semisimple: bool = False
    """If True, the bound's derivation requires F[G] semisimple
    (`gcd(|G|, char F) = 1`). Implied by `family == CHAR_THEORETIC`
    but may also be true for other families that locally use
    Fourier."""

    requires_cover_coprime: bool = False
    """If True, the bound requires `gcd(h, char F) = 1` for the
    cover index h. Implied by `family == CHAIN_MAP` but may also
    be true for other families that use chain-map transfer."""

    uses_cayley_spectral_bound: bool = False
    """If True, the bound's derivation relies on the spectral radius
    (Cheeger / Sipser-Spielman / Tanner-spectral) of `M_A` or `M_B`'s
    Cayley graph. Fires §6l on every BB code with k ≥ 2 — joint
    vanishing on a non-trivial character forces `λ_2 = weight`, so any
    spectral gap-based lower bound is identically vacuous."""

    is_module_natural_invariant: bool = False
    """If True, the bound's RHS is a numerical invariant of the F_2[G]-
    module isomorphism class of some functorially constructed
    F_2[G]-module M(A, B) — e.g., Hilbert series coefficients,
    Castelnuovo-Mumford regularity, Betti / Tor / Ext dimensions,
    projective dimension, depth, multiset of indecomposable summands.
    Fires §6m structurally because min Hamming weight is not an
    F_2[G]-module-isomorphism-class invariant (witness: H_0(K_gross) ≅
    H_2(K_gross) as F_2[G]-modules, but min_wt(H_0) = 1 and
    min_wt(H_2) = 32, a 32× gap).

    Importantly: this flag is INDEPENDENT of `rhs_type`. §6m fires
    even on `rhs_type = WEIGHT` candidates if the LHS / module M(A, B)
    is only used through its iso class. Example: "d_X ≥ min weight in
    H_2(K(A, B))" is `rhs_type = WEIGHT` but H_2's iso class doesn't
    determine min_wt(H_2), so any candidate that DEFINES min_wt(H_2)
    via H_2's iso class alone falls to §6m.

    §6m does NOT fire when the bound mixes module data with explicit
    non-module data (Hamming weight on specific vectors, the standard
    F_2-basis {e_g}, set-theoretic supports, classical dual distances).
    See HANDOFF.md §6m "Escape clause" for the precise boundary.
    """

    needs_new_theory: bool = False
    """If True, the bound is a research seed — its mathematical
    foundation isn't yet built. Always returns NEEDS-NEW-THEORY."""


@dataclass(frozen=True, slots=True)
class InstanceFingerprint:
    """Minimal description of a BB-code instance for obstruction matching.

    Only the properties needed to evaluate §6h–§6k. Full instance data
    lives in `bb_lab.store` / `bb_lab.corpus`.
    """

    id: str
    G_order: int
    char_F: int = 2
    is_known_chain_map_blocker: bool = False
    """True if this instance is known to be an h-fold cover with
    `gcd(h, char F) > 1`. Currently only gross (h = 2 over F_2)."""

    is_non_degenerate: bool = False
    """True if c = ⟨supp(A) ∩ supp(B)⟩ index is 1. None of the
    Bravyi instances are non-degenerate (all have c = 3)."""

    has_k_geq_2: bool = True
    """True if the code has at least one logical qubit (k ≥ 2 in CSS;
    k ≥ 1 since BB k is always even). All Bravyi-table instances have
    k ≥ 2 by construction (engineered specifically for k > 0).
    §6l fires only on instances with k ≥ 2."""


BRAVYI_FINGERPRINTS: tuple[InstanceFingerprint, ...] = (
    # |G| = ell * m, from instances/bravyi_table.yaml.
    # All Bravyi codes have c = 3 (non_degenerate = False) per HANDOFF.md §6i.
    InstanceFingerprint(
        id="bb_72_12_6",
        G_order=36,  # 6 * 6 = 2^2 * 3^2
    ),
    InstanceFingerprint(
        id="bb_90_8_10",
        G_order=45,  # 15 * 3 = 3^2 * 5 — the §6j exception (2 ∤ 45)
    ),
    InstanceFingerprint(
        id="bb_108_8_10",
        G_order=54,  # 9 * 6 = 2 * 3^3
    ),
    InstanceFingerprint(
        id="gross_144_12_12",
        G_order=72,  # 12 * 6 = 2^3 * 3^2
        is_known_chain_map_blocker=True,  # h=2 cover of bb_72, per HANDOFF.md §6k
    ),
    InstanceFingerprint(
        id="bb_288_12_18",
        G_order=144,  # 12 * 12 = 2^4 * 3^2
    ),
)


@dataclass(frozen=True, slots=True)
class Obstruction:
    """A §6-class structural obstruction encoded for machine checking.

    `predicate(candidate, instance) -> bool` returns True if the
    obstruction fires on that (candidate, instance) pair. §6h is
    instance-independent; the others are per-instance.
    """

    id: str
    section_ref: str
    short_description: str
    triggers_when: str
    predicate: Callable[[Candidate, InstanceFingerprint], bool] = field(repr=False)


def _fires_6h(c: Candidate, _i: InstanceFingerprint) -> bool:
    return c.rhs_type == RHSType.DIMENSION


def _fires_6i(c: Candidate, i: InstanceFingerprint) -> bool:
    return c.requires_non_degenerate and not i.is_non_degenerate


def _fires_6j(c: Candidate, i: InstanceFingerprint) -> bool:
    needs_semisimple = (
        c.family == Family.CHAR_THEORETIC or c.requires_semisimple
    )
    return needs_semisimple and gcd(i.G_order, i.char_F) > 1


def _fires_6k(c: Candidate, i: InstanceFingerprint) -> bool:
    needs_cover_coprime = (
        c.family == Family.CHAIN_MAP or c.requires_cover_coprime
    )
    return needs_cover_coprime and i.is_known_chain_map_blocker


def _fires_6l(c: Candidate, i: InstanceFingerprint) -> bool:
    return c.uses_cayley_spectral_bound and i.has_k_geq_2


def _fires_6m(c: Candidate, _i: InstanceFingerprint) -> bool:
    """§6m is structural / instance-independent.

    Fires when the candidate's RHS is a numerical F_2[G]-module-
    isomorphism-class invariant of some construction M(A, B). The
    obstruction is independent of the specific Bravyi instance — it
    holds because min Hamming weight is not such an invariant in
    general (witness: gross's H_0 ≅ H_2 with min_wt 1 vs 32).

    Follows the §6h pattern (structural / instance-independent) in
    that it returns SHELVED-A-PRIORI regardless of which instances
    are checked.
    """
    return c.is_module_natural_invariant


OBSTRUCTIONS: tuple[Obstruction, ...] = (
    Obstruction(
        id="6h",
        section_ref="HANDOFF.md §6h",
        short_description="Dimension invariants bound k, not d.",
        triggers_when="candidate.rhs_type == DIMENSION",
        predicate=_fires_6h,
    ),
    Obstruction(
        id="6i",
        section_ref="HANDOFF.md §6i",
        short_description=(
            "Bravyi engineers degeneracy; non-degenerate hypothesis "
            "excludes the engineering target."
        ),
        triggers_when="requires_non_degenerate AND not instance.is_non_degenerate",
        predicate=_fires_6i,
    ),
    Obstruction(
        id="6j",
        section_ref="HANDOFF.md §6j",
        short_description=(
            "Character-theoretic bounds require F[G] semisimple; "
            "blocked when gcd(|G|, char F) > 1."
        ),
        triggers_when="char-theoretic family AND gcd(|G|, char F) > 1",
        predicate=_fires_6j,
    ),
    Obstruction(
        id="6k",
        section_ref="HANDOFF.md §6k",
        short_description=(
            "Chain-map / cover-graph bounds require gcd(h, char F) = 1; "
            "blocked when the instance is a known chain-map blocker."
        ),
        triggers_when="chain-map family AND instance.is_known_chain_map_blocker",
        predicate=_fires_6k,
    ),
    Obstruction(
        id="6l",
        section_ref="HANDOFF.md §6l",
        short_description=(
            "Cayley-graph spectral bounds are vacuous on BB codes with "
            "k ≥ 2 (joint vanishing forces λ_2 = weight, so spectral gap = 0)."
        ),
        triggers_when="candidate.uses_cayley_spectral_bound AND instance.has_k_geq_2",
        predicate=_fires_6l,
    ),
    Obstruction(
        id="6m",
        section_ref="HANDOFF.md §6m",
        short_description=(
            "F_2[G]-module-isomorphism-class invariants cannot lower-bound "
            "d_X: min Hamming weight depends on embedding, not iso class. "
            "Witness: gross has H_0 ≅ H_2 as F_2[G]-modules but min_wt(H_0) = 1 "
            "and min_wt(H_2) = 32."
        ),
        triggers_when="candidate.is_module_natural_invariant",
        predicate=_fires_6m,
    ),
)


@dataclass(frozen=True, slots=True)
class Classification:
    """Result of pre-flight classification.

    `bravyi_blast_radius` lists `"<obs_id>@<instance_id>"` pairs for
    every per-instance obstruction fire. Type-level obstructions
    (§6h) appear in `obstructions_hit` without an instance suffix.
    """

    candidate_id: str
    obstructions_hit: tuple[str, ...]
    bravyi_blast_radius: tuple[str, ...]
    verdict: Verdict
    reasoning: tuple[str, ...]

    def is_proceed(self) -> bool:
        return self.verdict == Verdict.PROCEED


_STRUCTURAL_OBS_IDS: tuple[str, ...] = ("6h", "6m")
"""Obstruction IDs whose predicates are instance-independent / structural.

§6h: dimension RHS is a category error regardless of instance.
§6m: an F_2[G]-module-iso-class numerical invariant cannot lower-bound
     min Hamming weight regardless of instance — see HANDOFF.md §6m.

These short-circuit `classify` with SHELVED-A-PRIORI; per-instance
obstructions (§6i, §6j, §6k, §6l) are evaluated separately.
"""


def classify(
    candidate: Candidate,
    instances: tuple[InstanceFingerprint, ...] = BRAVYI_FINGERPRINTS,
    obstructions: tuple[Obstruction, ...] = OBSTRUCTIONS,
) -> Classification:
    """Run the §6 obstruction gate on a candidate.

    Decision tree:

    1. If `candidate.needs_new_theory`, returns NEEDS-NEW-THEORY.
    2. If §6h fires, returns SHELVED-A-PRIORI (category error: RHS is
       a dimension quantity, but d_X is a weight quantity).
    3. If §6m fires, returns SHELVED-A-PRIORI (structural: RHS is a
       module-iso-class invariant, but min weight depends on embedding).
    4. Else evaluate every (per-instance obstruction, instance) pair.
    5. If every instance in `instances` is blocked by ≥1 per-instance
       obstruction, returns SHELVED-A-PRIORI.
    6. Else returns PROCEED. `bravyi_blast_radius` lists which instances
       are blocked so the downstream tester knows where the candidate
       can possibly be tight.
    """
    obstructions_hit: list[str] = []
    blast: list[str] = []
    reasoning: list[str] = []

    if candidate.needs_new_theory:
        reasoning.append(
            "Candidate is explicitly flagged as needing new theory. "
            "Tag as a research seed; do not generate code or proofs yet."
        )
        return Classification(
            candidate_id=candidate.id,
            obstructions_hit=(),
            bravyi_blast_radius=(),
            verdict=Verdict.NEEDS_NEW_THEORY,
            reasoning=tuple(reasoning),
        )

    # Structural / instance-independent obstructions: §6h and §6m.
    # Order matters for the reasoning trace: §6h reports first when both
    # would fire, since dimension-RHS is the more elementary category
    # error.
    sentinel = instances[0] if instances else None

    obs_6h = next(o for o in obstructions if o.id == "6h")
    if sentinel is not None and obs_6h.predicate(candidate, sentinel):
        obstructions_hit.append("6h")
        reasoning.append(
            f"§6h fires (type-level): {obs_6h.short_description} "
            f"Candidate's RHS is `{candidate.rhs_type.value}`, but d_X is "
            "a weight quantity. Dimension invariants are k-invariants."
        )
        return Classification(
            candidate_id=candidate.id,
            obstructions_hit=tuple(obstructions_hit),
            bravyi_blast_radius=(),
            verdict=Verdict.SHELVED_A_PRIORI,
            reasoning=tuple(reasoning),
        )

    obs_6m = next(o for o in obstructions if o.id == "6m")
    if sentinel is not None and obs_6m.predicate(candidate, sentinel):
        obstructions_hit.append("6m")
        reasoning.append(
            f"§6m fires (structural): {obs_6m.short_description} "
            "An F_2[G]-module-iso-class invariant cannot determine min "
            "Hamming weight, so it cannot tightly lower-bound d_X."
        )
        return Classification(
            candidate_id=candidate.id,
            obstructions_hit=tuple(obstructions_hit),
            bravyi_blast_radius=(),
            verdict=Verdict.SHELVED_A_PRIORI,
            reasoning=tuple(reasoning),
        )

    # Per-instance obstructions (§6i, §6j, §6k, §6l).
    per_instance_obs = [
        o for o in obstructions if o.id not in _STRUCTURAL_OBS_IDS
    ]
    blocked_instances: set[str] = set()
    for inst in instances:
        for obs in per_instance_obs:
            if obs.predicate(candidate, inst):
                if obs.id not in obstructions_hit:
                    obstructions_hit.append(obs.id)
                blast.append(f"{obs.id}@{inst.id}")
                blocked_instances.add(inst.id)
                reasoning.append(
                    f"§{obs.id} fires on {inst.id}: {obs.short_description}"
                )

    if not obstructions_hit:
        reasoning.append("No §6 obstruction triggered. Proceed to Tier 1+.")
        verdict = Verdict.PROCEED
    elif len(blocked_instances) == len(instances) and instances:
        reasoning.append(
            f"Every canonical instance ({len(instances)} total) is blocked "
            "by at least one obstruction. Candidate cannot be tight on any "
            "engineering target — SHELVED-A-PRIORI."
        )
        verdict = Verdict.SHELVED_A_PRIORI
    else:
        survivors = [
            i.id for i in instances if i.id not in blocked_instances
        ]
        reasoning.append(
            f"Candidate is blocked on {len(blocked_instances)} of "
            f"{len(instances)} canonical instances. Survivors: "
            f"{survivors}. Proceed with awareness of the blast radius."
        )
        verdict = Verdict.PROCEED

    return Classification(
        candidate_id=candidate.id,
        obstructions_hit=tuple(obstructions_hit),
        bravyi_blast_radius=tuple(blast),
        verdict=verdict,
        reasoning=tuple(reasoning),
    )


# --- Round-1 reproduction candidates -------------------------------------
#
# These are the round-1 candidates whose verdicts we expect the
# classifier to reproduce. Used by tests/test_obstructions.py and
# importable by future Tier-2 work as historical lineage anchors.


CV1_ORIGINAL_JACOBSON_SUM = Candidate(
    id="Cv1-original-jacobson-sum",
    name="Original Cv1 Jacobson-radical dimension sum",
    family=Family.RADICAL_WEIGHT,
    rhs_type=RHSType.DIMENSION,  # the round-1 footgun: dim, not weight
    bound_formula="d_X ≥ Σ_O |O| · μ_O(A, B)",
    citation="bb_lab Cv1 round 1 (commit 1224c2c); falsified Tier-3 round 1 (commit 509d702)",
)

CV1_W1_REFINED = Candidate(
    id="Cv1-w1-refined",
    name="Cv1 w_1 weight invariant (refined; not itself a bound)",
    family=Family.RADICAL_WEIGHT,
    rhs_type=RHSType.WEIGHT,
    bound_formula="w_1(A, O) := min weight in V_{O,1}(A) (NOT a distance bound)",
    citation="bb_lab Cv1 round 2 (commit 1224c2c); see radical_weight.py",
)

HT_ROOS = Candidate(
    id="HT-Roos-multivariate-cyclic",
    name="Hartmann–Tzeng / Roos multivariate-cyclic distance bound",
    family=Family.CHAR_THEORETIC,
    rhs_type=RHSType.WEIGHT,
    bound_formula="d ≥ HT(A) (per-axis HT bound combined via product)",
    citation=(
        "bb_lab T2R3 (commit a6d48e7); see notes/T2R3.0_literature_check.md. "
        "Camion 1971 / Saints–Heegard 1995 / BBCS 2016 — all assume F[G] "
        "semisimple."
    ),
    requires_semisimple=True,
)

SRB_COVER_GRAPH = Candidate(
    id="SRB-cover-graph",
    name="Symons–Rajput–Browne 2025 cover-graph chain-map bound",
    family=Family.CHAIN_MAP,
    rhs_type=RHSType.WEIGHT,
    bound_formula="d_cover ≥ d_base / h  (rigorous form, gcd(h, char F) = 1)",
    citation=(
        "bb_lab T2R5 (commit fa5ecdd); arXiv:2511.13560. Trivial on gross "
        "(rigorous gives d ≥ 1) because gross is an h=2 cover over F_2."
    ),
    requires_cover_coprime=True,
)

LIN_PRYADKO_STMT_12 = Candidate(
    id="Lin-Pryadko-Stmt-12",
    name="Lin–Pryadko Statement 12 (Tillich–Zémor analog)",
    family=Family.LIFTED_PRODUCT,
    rhs_type=RHSType.WEIGHT,
    bound_formula="d ≥ ⌈min(d_A^⊥, d_B^⊥) / c⌉",
    citation=(
        "arXiv:2306.16400 Statement 12 §IV.F. Provably correct everywhere; "
        "tight on 0.1% of round-1 corpus; bound = 2 on every Bravyi code "
        "(loose by 4–10)."
    ),
)

FAMILY_C_V1_SPECTRAL = Candidate(
    id="family_c_v1_spectral",
    name="Family C v1: Cayley-graph spectral / Sipser-Spielman bound",
    family=Family.COMBINATORIAL,
    rhs_type=RHSType.WEIGHT,
    bound_formula="d ≥ ⌊n · (w − λ_2(M_A or M_B)) / (2w)⌋",
    citation=(
        "Sipser-Spielman 1996 IT / Tanner 1981 spectral bound applied to "
        "BB Cayley graphs; round-2 Family C v1, FALSIFIED-AS-PREDICTOR via "
        "§6l (joint vanishing forces λ_2 = weight, gap = 0 for every k ≥ 2 "
        "BB code). Empirical Pearson(gap, d) = −0.020 across 4,364 rows."
    ),
    uses_cayley_spectral_bound=True,
)


FAMILY_D_V1_KOSZUL_H_2_MIN_WEIGHT = Candidate(
    id="family_d_v1_koszul_h2_min_weight",
    name="Family D v1: minimum Hamming weight in Koszul H_2",
    family=Family.SYZYGY,
    rhs_type=RHSType.WEIGHT,
    bound_formula="d_X ≥ min weight in H_2(K(A, B)) \\ {0}",
    citation=(
        "Round-2 v2 first session (commit 5580064); falsified empirically "
        "(0/5 Bravyi rows satisfy lower bound; 199/200 corpus rows are "
        "strictly UPPER-bounded). The relation d_X ≤ min_wt(H_2) is a "
        "robust upper bound, never a lower bound. See "
        "pipeline/attempts/bb_distance_conjecture_family_d_v1_koszul_h2/result.md "
        "for the §5 mechanism (γ ∈ H_2 ⇒ (γ, 0) ∈ ker H_X) and §6 "
        "generalization to §6m."
    ),
    # The hypothesis was that min_wt(H_2) is determined by H_2's
    # F_2[G]-module-iso-class. The witness in
    # `scripts/family_d_v1_koszul_h2_iso_witness.py` shows this is
    # false (H_0 ≅ H_2 but min_wt differs by 32×), so any version of
    # this candidate that reads min_wt off the module class is blocked
    # by §6m as well as being empirically wrong-signed.
    is_module_natural_invariant=True,
)


FAMILY_D_V1_HILBERT_SERIES_MIN_DEGREE = Candidate(
    id="family_d_v1_hilbert_series_min_degree",
    name=(
        "Family D 4a (handoff): minimum non-vanishing degree of "
        "Hilbert series of syz(A, B)"
    ),
    family=Family.MODULE_THEORETIC,
    rhs_type=RHSType.WEIGHT,  # claimed weight, but RHS factors through
                              # the iso class of syz(A, B), so §6m fires.
    bound_formula=(
        "d_X ≥ min { d ≥ 0 : dim_F_2 syz_d(A, B) > 0 }  in the "
        "augmentation grading of F_2[G]"
    ),
    citation=(
        "HANDOFF_FAMILY_D_MOONSHOT.md §4a — the canonical Family D 4a "
        "candidate (Hilbert series of syz(A, B) under augmentation "
        "grading). Hilbert series coefficients are dim_F_2 of graded "
        "pieces, so the minimum non-vanishing degree is an F_2[G]-"
        "module-iso-class invariant. Falls to §6m structurally."
    ),
    is_module_natural_invariant=True,
)


FAMILY_D_V1_CM_REGULARITY = Candidate(
    id="family_d_v1_castelnuovo_mumford_regularity",
    name="Family D 4b (handoff): Castelnuovo–Mumford regularity of (A, B)",
    family=Family.MODULE_THEORETIC,
    rhs_type=RHSType.WEIGHT,
    bound_formula="d_X ≥ φ(reg((A, B)))  for some monotone φ",
    citation=(
        "HANDOFF_FAMILY_D_MOONSHOT.md §4b — Castelnuovo–Mumford "
        "regularity adapted to F_2[G]. Regularity is defined via "
        "dimensions of Tor groups (Aramova-Herzog; Eisenbud-Goto). "
        "Each Tor_i^{F_2[G]}(F_2, F_2[G]/(A,B)) is an F_2[G]-module-"
        "iso-class invariant, so reg is too. Falls to §6m."
    ),
    is_module_natural_invariant=True,
)
