# bb_lab Round 2 — toward a tight `d_X` bound on gross

Round-2 handoff. Picks up from the round-1 closure documented in
[`HANDOFF.md`](HANDOFF.md) §6h–§6k and
[`pipeline/attempts/bb_distance_conjecture_radical_weight_narrow_tier3/result.md`](../../pipeline/attempts/bb_distance_conjecture_radical_weight_narrow_tier3/result.md).

---

## 1. Strategic goal (unchanged from round 1)

A closed-form lower bound `d_X ≥ f(G, A, B)` on the minimum distance of
BB(G, A, B) codes, provable in Lean against `bbChainComplex`, with `f`
**tight or near-tight on the IBM gross polynomials** `(x³+y+y², y³+x+x²)
on Z₁₂ × Z₆`.

Honest framing: tight on gross is the moonshot. The program produces a
first-class output (an enriched obstruction map) even if no round lands
a tight bound. Lin–Pryadko Statement 12 (the textbook fallback) gives
`d_X ≥ 2` on gross (actual `d = 12`); see
[`notes/T2R2.4_evaluation.md`](notes/T2R2.4_evaluation.md). It is not
the target.

## 2. Round-1 retrospective (what closed and why)

Round 1 ran six conjecture rounds (Cv1 → Cv4, R1 → R5) over ~2 days of
Claude-led work on a corpus of 3,894 labeled BB instances (16,382 total
with `d_ub` from L1 sampling), 8 group structures, n ∈ [18, 108]. The
round-1 [`HANDOFF.md`](HANDOFF.md) §4 table showing "460 / total" is a
stale early-snapshot — the live numbers come from
[`notes/T2R2.4_evaluation.md`](notes/T2R2.4_evaluation.md). All six
rounds shelved. The durable outputs are:

- **One contribution**: the `w_1` weight invariant for `F₂[G]` non-
  semisimple group algebras
  ([`src/bb_lab/radical_weight.py`](src/bb_lab/radical_weight.py)).
  Refines per-orbit dual distance via Jacobson-radical Loewy filtration;
  passes §6h's weight-vs-dimension check; is *not* itself a distance bound.
- **Four structural obstruction theorems** ([`HANDOFF.md`](HANDOFF.md)
  §6h–§6k):
  - §6h — dimension invariants bound `k`, not `d`.
  - §6i — Bravyi engineers degeneracy (`c > 1`); non-degenerate
    hypotheses exclude the engineering target.
  - §6j — character-theoretic bounds require `gcd(|G|, char F) = 1`;
    gross has `2 | |G| = 72`, blocking the whole family.
  - §6k — chain-map / cover-graph bounds require `gcd(h, char F) = 1`;
    gross is an `h = 2` cover over `F₂`, blocking the family.

The §6j and §6k findings are the round-1 deliverable: **whatever makes
gross `d = 12` is not visible in the character decomposition of `F₂[G]`
and is not visible to chain-map transfer in characteristic 2.**

Round-2 architecture is shaped by these findings.

## 3. Cross-cutting architecture (build before Tier 1+)

Four shared pieces, used by every tier:

1. **Obstruction registry** —
   [`src/bb_lab/obstructions.py`](src/bb_lab/obstructions.py).
   §6h–§6k encoded as machine-checkable predicates on a `Candidate`
   record and the canonical Bravyi-instance fingerprints.
   `classify(candidate)` returns `{obstructions_hit, bravyi_blast_radius,
   verdict ∈ {PROCEED, SHELVED-A-PRIORI, NEEDS-NEW-THEORY}}`. New §6
   entries land here when discovered. Three of round 1's four shelved
   rounds would have been blocked by this gate.

2. **Candidate registry** — DuckDB table `bb_candidates` (schema in §12).
   Replaces the prose-in-notes pattern. Columns:
   `candidate_id, family, rhs_type, hypothesis_predicates, bound_formula,
   parent_id, source_paper, generation_method, obstructions_hit,
   corpus_stats_json, adversarial_stats_json, status, falsifier_id`.
   Queryable for "which lineage is alive", "which family hasn't been
   tried", etc.

3. **Parameterized adversarial generator** —
   `src/bb_lab/adversarial.py` (new). Given a candidate's hypothesis
   predicates, auto-generates stress-test instances targeting each
   predicate (multi-prime `G_odd`, rank-1-on-one-prime, c-cliff,
   even-weight near-violators, support-subgroup-edge). Replaces the
   hand-coded `scripts/adv_attack*.py` family.

4. **Family-budgeted generation** — Tier 2 budgets work across five
   categorically distinct families (§7). No family is allowed to
   monopolize.

## 4. Predicate vocabulary and structural axes

A shared, fixed vocabulary describes both **what a candidate's hypothesis
asserts** (the conjunction of predicates the conjecture assumes) and
**along which structural axes Tier 3 should sample to falsify it** (the
dimensions of variation the hypothesis fails to pin down). Round 1's
hand-coded adversarial scripts implicitly used this vocabulary; round 2
makes it explicit and shared across:

- `Candidate.hypothesis_predicates` in the candidate registry
  (JSON-stored, queryable)
- `generate_stress_tests(hypothesis_predicates=...)` in `adversarial.py`
- The §6 obstruction-classifier predicates that fire on family
  classification (`obstructions.py`)

**The mental model: an adversarial search lives *inside* the hypothesis
domain.** A candidate of the form `hypothesis ⟹ bound` is falsified by
an instance satisfying every hypothesis predicate (so the conjecture
applies) yet violating the bound. Hypotheses are assumptions, not
targets; we vary *unpinned* structural axes while *holding pinned axes
fixed* at hypothesis-satisfying values.

### 4.1 Predicates (the assumption vocabulary)

A predicate is a machine-checkable property of a BB-code instance.
A candidate's hypothesis is a conjunction of predicates; an instance
satisfies the hypothesis iff every predicate evaluates to True on it.

**Group-structure predicates:**

| Predicate | Statement |
|---|---|
| `elem_ab_G_odd` | each prime-part of `G_odd` is elementary abelian (each axis's odd-part order is squarefree) |
| `strict_elem_ab_G_odd` | `G_odd ≅ (Z_p)^k` for a single odd prime `p` |
| `single_prime_G_odd` | `G_odd` has exactly one distinct prime factor |
| `multi_prime_G_odd` | `G_odd` has ≥ 2 distinct prime factors |
| `G_odd_all_rank_1` | each prime factor `p` of `G_odd` appears at `p`-rank 1 |
| `G_odd_mixed_rank` | at least one prime factor of `G_odd` appears at `p`-rank ≥ 2 |
| `G_2_trivial` | `G` has odd order (no 2-Sylow); implies `F_2[G]` semisimple |
| `G_2_elem_ab` | 2-Sylow of `G` is `(Z_2)^k` |
| `non_semisimple_F2G` | `2 \| \|G\|` (so `F_2[G]` is not semisimple) |

**Degeneracy / intersection predicates:**

| Predicate | Statement |
|---|---|
| `non_degenerate` | `⟨supp(A)⟩ = ⟨supp(B)⟩ = G` (so `c = 1`) |
| `degenerate` | `c > 1` |
| `c_geq_2`, `c_geq_3` | `c ≥ 2`, `c ≥ 3` (Bravyi-fingerprint is `c ≥ 3`) |
| `c_eq_3_exact` | `c = 3` (matches all 5 Bravyi codes) |

**Polynomial-structure predicates:**

| Predicate | Statement |
|---|---|
| `weight_eq_A(w)` | `\|supp(A)\| = w` |
| `weight_eq_B(w)` | `\|supp(B)\| = w` |
| `odd_weight_A` | `\|supp(A)\|` is odd |
| `odd_weight_B` | `\|supp(B)\|` is odd |
| `joint_vanishing_nonempty` | ∃ orbit `O` where both `A` and `B` vanish on `O` |
| `no_weight_le_2_syzygy_AB` | no `(α, β)` of weight ≤ 2 in `F_2[G]²` with `αA + βB = 0` |

**Cover-structure predicates** (for chain-map family candidates):

| Predicate | Statement |
|---|---|
| `cover_index_eq_h(h)` | the BB code is realized as an `h`-fold cover of a smaller BB |
| `cover_index_coprime_to_char` | `gcd(h, 2) = 1` for the natural cover `h` |

Predicate values may carry parameters (e.g. `weight_eq_A(3)`); parameter-
free forms are common shorthands. The canonical list lives in
`bb_lab/predicates.py` (created alongside `adversarial.py`); each
predicate carries a check function `(G, A, B) -> bool`.

### 4.2 Structural axes (the variation vocabulary)

A structural axis is a property along which BB-code instances can vary
independently. Each axis is **pinned** by a (possibly empty) subset of
predicates and **unpinned** by the rest. Tier-3 adversarial generation
walks values on unpinned axes while keeping pinned axes fixed at
hypothesis-satisfying values.

| Axis | Range | Predicates that pin it |
|---|---|---|
| `prime_structure` | `single` / `multi` | `single_prime_G_odd`, `multi_prime_G_odd` |
| `prime_rank_profile` | `all_rank_1` / `mixed_rank` | `G_odd_all_rank_1`, `G_odd_mixed_rank` |
| `G_odd_elem_ab_class` | `strict` / `loose` / `non` | `elem_ab_G_odd`, `strict_elem_ab_G_odd` |
| `G_2_shape` | `trivial` / `elem_ab` / `non_elem_ab` | `G_2_trivial`, `G_2_elem_ab`, `non_semisimple_F2G` |
| `c_value` | `1, 2, 3, 5, 7, ...` | `non_degenerate`, `c_geq_2`, `c_geq_3`, `c_eq_3_exact` |
| `A_weight` | `3, 4, 5, ...` | `weight_eq_A(w)` |
| `B_weight` | `3, 4, 5, ...` | `weight_eq_B(w)` |
| `A_parity` | `odd / even` | `odd_weight_A` |
| `B_parity` | `odd / even` | `odd_weight_B` |
| `joint_vanishing` | `present / absent` | `joint_vanishing_nonempty` |
| `cover_index` | `1, 2, 3, ...` | `cover_index_eq_h(h)` |

### 4.3 How adversarial generation uses this

```
unpinned_axes(hypothesis_predicates) := ALL_AXES \ pinned_by(hypothesis_predicates)
```

For each unpinned axis, the generator enumerates values from its range.
For each `(axis, value)` pair, it constructs `~budget // |unpinned|`
instances that:

1. **Satisfy every predicate** in `hypothesis_predicates`.
2. **Pin the chosen axis to the chosen value.**
3. Leave other unpinned axes random or in a small enumeration.

Each generated instance carries metadata
`(hypothesis_predicates_satisfied: set, axis_probed: str,
value_probed: Any)`. A falsifier is an instance whose actual `d_X`
(from SAT or L1 sampling for n > ~108) is strictly below the
candidate's bound formula evaluated on `(G, A, B)`.

### 4.4 Round-1 in this vocabulary (worked example)

The R1+R4 conjecture from
[`Cv4_R4_falsified.md`](notes/Cv4_R4_falsified.md) had:

- `hypothesis_predicates = {elem_ab_G_odd, c_geq_3, odd_weight_A, odd_weight_B}`
- `bound = ⌈(1/c) · cross_orbit_min_weight(A, B, G)⌉`

Axes pinned by this hypothesis: `G_odd_elem_ab_class` (= `loose`),
`c_value` (lower-bounded at 3), `A_parity` (= `odd`), `B_parity` (= `odd`).

Axes left unpinned (a partial list): `prime_structure`,
`prime_rank_profile`, `G_2_shape`, `A_weight` (only parity is pinned),
`B_weight`, `joint_vanishing`, `cover_index`.

The Z₃ × Z₁₅ falsifier corresponds to setting
`prime_structure = multi` and `prime_rank_profile = mixed_rank`
(Z₃ × Z₁₅ ≅ Z₃² × Z₅, so 3-rank 2 and 5-rank 1) with
`A_weight = 3, B_weight = 5` (both odd, satisfying the parity
hypothesis). All hypothesis predicates satisfied; bound = 4 but
`d_X = 2`. A parameterized generator that enumerates
`(prime_structure × prime_rank_profile)` values within
hypothesis-satisfying instances would have surfaced this in minutes —
not the ~2 hours `adv_attack3_z3xz7.py` took to write by hand from
a structural-failure analysis.

## 5. Tier 0 — Pre-flight obstruction gate

**Every candidate, before any corpus run or proof attempt**, passes
through `classify(candidate)`. The classifier returns:

```
Classification(
    candidate_id: str,
    obstructions_hit: tuple[str, ...],           # e.g. ("6j", "6k")
    bravyi_blast_radius: tuple[str, ...],        # which Bravyi instances are blocked
    verdict: Verdict,                            # PROCEED | SHELVED-A-PRIORI | NEEDS-NEW-THEORY
    reasoning: tuple[str, ...],
)
```

**Verdict semantics:**

| verdict | meaning | action |
|---|---|---|
| `PROCEED` | no obstruction blocks all Bravyi instances | run Tier 2/3 |
| `SHELVED-A-PRIORI` | §6h category error, OR every Bravyi instance is blocked | do not generate code; archive with citation |
| `NEEDS-NEW-THEORY` | candidate explicitly requires unbuilt math | mark as a research seed; do not pursue formally yet |

**Exit criterion** for Tier 0 (the module, not the gate): each round-1
candidate (`Cv1-original`, `HT-Roos`, `SRB-cover-graph`, `Lin-Pryadko`,
`Cv1-w1-refined`) classifies correctly per the round-1 historical
record. Implemented and tested in
[`tests/test_obstructions.py`](tests/test_obstructions.py).

## 6. Tier 1 — Lab (targeted corpus scale-up)

Round 1's corpus (as of T2R2.4) is **3,894 labeled rows** with `d_exact`
plus **15,922 with `d_ub`** from L1 sampling — 16,382 total across 8
group structures, n ∈ [18, 108], k ∈ [4, 72], d_exact ∈ [2, 8].
Multi-prime `G_odd` is **already present at scale**: `Z3xZ5` (103 rows)
and `Z5xZ6` (2622 rows) together give ~2725 multi-prime `G_odd`
instances — but both groups have **rank-1 on each prime**.

The R1+R4 falsifier on Z_3 × Z_15 required something the corpus does
*not* have: **multi-prime `G_odd` with rank-2 on one prime and rank-1
on another** (Z_3 × Z_15 = Z_3² × Z_5). bb_90_8_10's group is
Z_15 × Z_3 = Z_3² × Z_5 — structurally in the falsifier regime, only
dodging it via specific polynomial choices. Yet **no Z_3 × Z_15-shaped
corpus rows exist**; bb_90 sits as a lone giant of its structural class.

Round 2 expands where round 1 was blind:

| Regime | Round-1 count | Round-2 target | Rationale |
|---|---:|---:|---|
| Multi-prime `G_odd`, mixed-rank (Z_3² × Z_p, Z_3 × Z_p², ...) | ~0 | ≥1000 | R1+R4 failure regime; bb_90's structural class |
| Gross-scale (n ∈ [108, 144]) | small | ≥500 | gross [[144,12,12]] shouldn't be a lone giant of Z₁₂×Z₆ |
| Bravyi-polynomial near-misses on Z₁₂×Z₆ | 0 | ~200 | systematic neighborhood of `(x³+y+y², y³+x+x²)` |
| Non-degenerate (`c = 1`) | ~50% | balanced | §6i regime mapping (currently 1937 non-degenerate of 3894 = 49.7%) |

**Concrete enumeration** (with bitset canonical form from `0fb18e5`).
Mixed-rank multi-prime targets come first — that's the round-1 blind
spot:

```bash
# Multi-prime G_odd with rank-2 on one prime (bb_90's structural class):
uv run bb-lab enumerate --ell 3  --m 15 --weight 3 --only-k-geq 2  # Z_3² × Z_5
uv run bb-lab enumerate --ell 5  --m 15 --weight 3 --only-k-geq 2  # Z_3 × Z_5²
uv run bb-lab enumerate --ell 3  --m 21 --weight 3 --only-k-geq 2  # Z_3² × Z_7
uv run bb-lab enumerate --ell 9  --m 5  --weight 3 --only-k-geq 2  # Z_3² × Z_5 alt
# Gross-scale (extend Z₁₂×Z₆ neighborhood + Z₁₂×Z₁₂):
uv run bb-lab enumerate --ell 12 --m 6  --weight 3 --only-k-geq 2  # gross group
uv run bb-lab enumerate --ell 12 --m 12 --weight 3 --only-k-geq 2  # bb_288 group
# Distance-fill (SAT is fine up to n ≈ 108; L1 sampling beyond):
uv run bb-lab fill-distances --max-n 108 --timeout-per-instance 600
uv run bb-lab fill-distances --max-n 144 --timeout-per-instance 1800
```

For `n > 108` where SAT becomes impractical, L1 sampling
([`src/bb_lab/l1_sampling.py`](src/bb_lab/l1_sampling.py), already
built) gives `d_ub`.

**Exit criterion**: corpus has ≥1000 mixed-rank multi-prime `G_odd`
rows with `d_exact` or `d_ub` recorded, AND ≥3 Bravyi-polynomial
near-misses on Z₁₂×Z₆, AND ≥1 instance per Bravyi structural class
beyond the Bravyi codes themselves.

## 7. Tier 2 — Conjecture mill (5 family slots)

Round 1's Cv1–Cv4 all sat inside §6j's blast radius. Round 2 budgets
generation explicitly across categorically distinct families. Each
family slot ≈ 1–2 days of Tier 2 work; family ordering is by expected
novelty per remaining-after-§6j-§6k math.

### Family A — Radical-aware weight invariants v2

§6k's surviving direction. Goal: a weight invariant on the Jacobson-
radical filtration of `F₂[G]` that **distinguishes R_O-unit-equivalent
polynomials** (the H_UNIT² failure mode). Starting points: Berman–
Charpin–Andriatahiny radical-of-elementary-abelian-p-group framework,
Jitman–Ling 2013 ([`notes/Cv1_literature.md`](notes/Cv1_literature.md)),
and the H_UNIT² failure analysis
([`notes/T3_CV3_H_UNIT2_attempt.md`](notes/T3_CV3_H_UNIT2_attempt.md)).
Highest novelty, hardest; explicit research seed if 2 days yields no
candidate distinguishing `(4,5)` from `(1,11)` on Z₁₂ × Z₁₂.

### Family B — Lifted-product–specific algebraic

Exploit BB's bilinear lifted-product structure beyond LP's generic
quasi-abelian wrapper. Candidates: Panteleev–Kalachev lift-then-product,
Hastings–Haah–O'Donnell quantum Tanner, lifted-product expansion
bounds. Not pure character theory; should partially dodge §6j.

### Family C — Direct combinatorial / qLDPC-expander

Tanner girth, expansion, percolation. Works in any characteristic,
obstruction-free, but historically loose. Expected ceiling on gross
≤ 6. Included as a baseline measurement of how far obstruction-free
bounds can go.

### Family D — Direct F₂[G]-module / syzygy

Don't decompose via characters. Use the F₂[G]-module structure of
`(A, B)` and their second syzygy module directly. Gröbner-style or
Anick-resolution-style techniques. Open whether anything is known for
non-semisimple group algebras.

### Family E — Computational-LP closed-form

Mine recent qLDPC LP/SDP relaxations
([Bravyi–Vargo 2019, Hsieh–Le Gall 2020 §V, Liu et al. 2024](https://arxiv.org/))
for closed-form bounds that don't reduce to Fourier.

**Generation method**: LLM-driven (Claude reads 2–3 source papers per
family) but every proposal passes through Tier 0 *before* any code or
corpus run. Proposals that hit §6j/§6k automatically get reformulated
or shelved.

**Exit criterion** per family: one written candidate descriptor (per
the schema in [`src/bb_lab/obstructions.py`](src/bb_lab/obstructions.py))
plus a Tier-0 classification. PROCEED candidates advance to Tier 3.

## 8. Tier 3 — Skeptic (three batteries)

Every Tier-2 PROCEED candidate runs all three:

1. **Corpus battery** —
   `violation_rate(candidate, corpus)` broken down by
   `(group_struct, c, degeneracy_class, prime-rank profile)`. Round 1
   reported only the headline rate; round 2 demands per-cell.
2. **Parameterized adversarial battery** — auto-generated from the
   candidate's hypothesis predicates. Each predicate gets attacked
   independently. The `Z₃ × Z₁₅` falsifier of R1+R4 would have come
   out of this in minutes.
3. **Bravyi-fingerprint battery** — explicit tests on the 5 published
   Bravyi codes + the ~200 near-misses from Tier 1. Reports
   `{tight, loose-by-1, loose-by-2, …}` buckets.

**Survival criterion for Tier 4**:
- 0 violations across all three batteries, AND
- tight on ≥1 Bravyi code, AND
- no §6 obstruction hit, AND
- executable natural-language proof sketch (each step references
  either an existing `BBChainComplex` lemma, a mathlib lemma, or a
  clearly-formalizable algebraic identity).

A candidate that's loose-by-10 on gross (Lin–Pryadko-style) does not
advance, regardless of corpus performance.

## 9. Tier 4 — Lean (survivor-only)

Unchanged in shape from round 1's plan. The pre-Lean check: the
natural-language sketch must compile in Claude's head — no "and then
by Loewy theory…" handwaves.

Target file: extend
[`QEC/Stabilizer/Framework/Homological/BBChainComplex.lean`](../../QEC/Stabilizer/Framework/Homological/BBChainComplex.lean)
(or a sibling) with the new bound as a `theorem`. The `qec-moonshot`
agent + `lean4:autoprove` + lean-lsp MCP are the right tools at this
stage; Agent C from
[arXiv:2605.22763](https://arxiv.org/abs/2605.22763) is not needed
unless the proof itself becomes the bottleneck (unlikely; one published-
shape proof at a time).

## 10. Phasing and budget

| Phase | Duration | Deliverable | Exit criterion |
|---|---|---|---|
| 0 — Architecture | ~2 days | Obstruction + candidate registries; adversarial generator | Tier-0 tests pass; round-1 candidates reproduced |
| 1 — Corpus scale-up | ~3 days | 5000-instance corpus, multi-prime + gross-scale | ≥1000 multi-prime rows with `d_exact`/`d_ub` |
| 2 — Family bake-off | ~5–8 days | ≥1 candidate per family, classified | ≥1 PROCEED per family OR shelved with reason |
| 3 — Skeptic | continuous | Battery results per PROCEED candidate | Survivor with no obstruction hit and ≥1 Bravyi tight |
| 4 — Lean | ~2–4 weeks | Theorem in `BBChainComplex.lean` (or sibling) | `lake build` green |

Total round-2 through Tier 3: ~10–13 days. Tier 4 only fires if a
real survivor lands.

## 11. Risks and honest framing

- **Family A might be unsolvable in 2 days.** It's open research. If
  2 days of focused effort doesn't yield a candidate distinguishing
  case `(4,5)` from case `(1,11)` on Z₁₂ × Z₁₂, mark as NEEDS-NEW-THEORY
  and shift budget to B–E.
- **Families B–E might all yield loose bounds.** That's still progress
  (richer obstruction map, multiple categorically-distinct lineages
  explored, more §6 entries).
- **The expanded corpus might still be blind.** Round 2's scale-up
  targets the round-1 blind spots, but the next falsifier may live
  in yet another regime. Treat the corpus as living, not final.
- **A tight bound on gross may not exist in closed form.** Gross's
  `d = 12` may be an arithmetic accident of the specific polynomial
  pair with no `f(G, A, B)` of the right shape achieving it. If round
  2 doesn't yield it and the obstruction map narrows, that itself is
  a publishable result (the "every classical analytic distance-bound
  technique cannot be tight on gross" theorem implicit in §6h–§6k
  made explicit and rigorous).

## 12. File map (round-2 additions)

```
experiments/bb_lab/
├── HANDOFF_R2.md                       # this file
├── src/bb_lab/
│   ├── obstructions.py                 # §6h–§6k registry + classify()
│   ├── candidates.py                   # DuckDB candidate registry + state machine
│   ├── predicates.py                   # §4.1 predicate vocabulary + §4.2 axes
│   ├── adversarial.py                  # parameterized stress-test generator
│   └── cli.py                          # `bb-lab classify` subcommand added
└── tests/
    ├── test_obstructions.py            # round-1 candidate reproduction (17 tests)
    ├── test_candidates.py              # registry roundtrip + state machine (29)
    ├── test_predicates.py              # predicate checks + axis pinning (21)
    ├── test_adversarial.py             # stress-test generator + R1+R4 (12)
    └── test_classify_cli.py            # `bb-lab classify` CLI (12)
```

DuckDB schema for `bb_candidates` (in `candidates.py`):

```sql
CREATE TABLE bb_candidates (
    candidate_id TEXT PRIMARY KEY,
    family TEXT NOT NULL,                -- char-theoretic | chain-map | radical-weight | ...
    rhs_type TEXT NOT NULL,              -- weight | dimension | mixed
    hypothesis_predicates JSON,
    bound_formula TEXT,
    parent_id TEXT,                      -- lineage
    source_paper TEXT,
    generation_method TEXT,              -- e.g. "literature-mine:LP23", "evolved-from:Cv1"
    obstructions_hit JSON,
    corpus_stats_json JSON,
    adversarial_stats_json JSON,
    status TEXT NOT NULL,                -- proposed | classified | running | shelved | survived | formalized
    falsifier_id TEXT,                   -- FK to bb_instances on falsification
    created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
);
```

## 13. First-day checklist

1. Read this whole document.
2. Read [`HANDOFF.md`](HANDOFF.md) §6h–§6k carefully — those obstructions
   shape every Tier 2 decision.
3. Verify Tier 0 reproduction:
   ```bash
   cd experiments/bb_lab
   uv sync --extra dev
   uv run pytest tests/test_obstructions.py -q
   ```
   Should classify Cv1-original as SHELVED-A-PRIORI (§6h), HT-Roos and
   SRB-cover-graph as SHELVED on gross (§6j, §6k), and Lin-Pryadko as
   PROCEED.
4. Implement `candidates.py` (DuckDB schema + CRUD).
5. Implement `adversarial.py` (parameterized generator).
6. Start corpus scale-up (§6).
7. Start Family A literature pass.
