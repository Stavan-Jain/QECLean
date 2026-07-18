# bb_lab — Round 2 v2: Family D module/syzygy moonshot
> **[Historical research record — extracted 2026-07-18 from the retired branch
> `claude/priceless-meninsky-3076ce` during branch cleanup; never previously
> merged.]** This document is from the "round-2 / round-2-v2" line (2026-05-27),
> which ran between the round-1 C-series falsification and the A-line
> (`notes/A_HANDOFF.md`, A0–A18) that later proved d(gross) = 12 in Lean by the
> h=2 cover-transfer route. The round-2 line's durable outputs are the §6l–§6n
> obstruction/identity sections in `experiments/bb_lab/HANDOFF.md` (added from
> this same branch), the (4/9)|G| H₂ min-weight identity, and the §14 open
> research questions in
> `pipeline/attempts/bb_distance_conjecture_family_d_v3_h2_minwt_formula/result.md`,
> which the A-line never picked up and which remain open as of this date.
> Section references "§6l/§6m/§6n" here mean the spectral-vacuity /
> module-invariant / (4/9)|G| entries — NOT the unmerged elementary-abelian
> "§6l" that the older HANDOFF_C3/TIER3 docs mention. This is not a live task
> list.


This handoff is for a NEW agent picking up the round-2 v2 program. Read
this whole document, then [`HANDOFF.md`](HANDOFF.md) §6h–§6l (obstructions),
then [`HANDOFF_R2.md`](HANDOFF_R2.md) §6 Family D, then
[`pipeline/attempts/bb_distance_conjecture_round2_obstruction_map/result.md`](../../pipeline/attempts/bb_distance_conjecture_round2_obstruction_map/result.md)
for the full round-2 negative pattern.

---

## 1. Strategic goal (don't drift)

A closed-form, F₂[G]-module-theoretic lower bound

```
    d_X(BB(G, A, B))  ≥  f(A, B, G)
```

with `f` a *structural* quantity — computable from `(A, B)` without
searching for codewords — that is **tight or near-tight on gross**.
The bound should provably hold and ideally be formalizable against
[`QEC/Stabilizer/Framework/Homological/BBChainComplex.lean`](../../QEC/Stabilizer/Framework/Homological/BBChainComplex.lean).

Honest moonshot framing: **failures are first-class outputs**. If
3 sessions of focused work find no bound, that completes the "no
classical analytic technique can be tight on gross" theorem implicit
in §6h–§6l, making it a publishable structural-impossibility result.

---

## 2. What round 2 v1 established (don't repeat these)

| Direction | Verdict | Reference |
|---|---|---|
| Cv* radical-aware refinements (round 1) | All falsified | round-1 result.md files |
| Family A v2 (a_O y'-spread refinement of `w_1`) | FALSIFIED-AS-PREDICTOR (corpus-wide non-discrimination) | `bb_distance_conjecture_family_a_v2_yspread/result.md` |
| Family B (PK / HHO / LZ asymptotic bounds) | NO CLOSED-FORM in published literature | round-2 first-pass §2 |
| Family C v1 (Cayley spectral) | §6l: STRUCTURALLY VACUOUS for k ≥ 2 | HANDOFF.md §6l |
| Family C girth bound (round 1) | Loose by 9 on gross | T2R2.4 |
| Character-theoretic family (any Fourier-via-G_odd) | §6j: blocked when 2 \| \|G\| | HANDOFF.md §6j |
| Chain-map / cover-graph bounds | §6k: blocked when gcd(h, char F) > 1 | HANDOFF.md §6k |
| Dimension-on-RHS candidates | §6h: category error | HANDOFF.md §6h |
| Non-degenerate-only hypotheses | §6i: excludes engineering target | HANDOFF.md §6i |

**Net effect**: characters, chain maps, dimension proxies, and
spectral gaps are all definitively blocked or empirically falsified.
**Family D (module/syzygy / Anick / Koszul / regularity) is the only
remaining major direction.**

---

## 3. The module-theoretic setup

For G abelian, F₂[G] is a commutative ring. The BB code BB(G, A, B)
has a clean module-theoretic description via the **Koszul complex** of
the regular(ish) sequence `(A, B)`:

```
    0  →  F₂[G]  →  F₂[G] ⊕ F₂[G]  →  F₂[G]  →  F₂[G]/(A, B)  →  0
            d_2              d_1
            ↑                ↑
            γ ↦ (Bγ, Aγ)     (α, β) ↦ αA + βB
```

Homology:
- `H_0(K) = F₂[G]/(A, B)` — the quotient ring (k_classical = dim_F₂)
- `H_1(K) = ker(d_1) / image(d_2)` — **the X-logicals**. Exactly the
  syz(A, B) modulo trivial syzygies.
- `H_2(K) = ker(d_2)` — the annihilator of (B, A) ∈ F₂[G]². For
  regular sequences, this is 0; for non-regular, captures relations.

**Key identity** (Bravyi 2024 Lemma 1 / Koszul reformulation):
`d_X = min weight in H_1(K) viewed as F₂-vector space`.

The challenge: find a **structural** lower bound on `min |·|_H over
H_1(K) \ {0}`, computable from (A, B) without explicit minimum-weight
search (which is what SAT does directly).

---

## 4. Concrete candidate directions to attempt

In rough order of perceived tractability. Each is a multi-day effort.

### 4a. Hilbert series of `syz(A, B)` and degree bounds

The syzygy module `syz(A, B) = ker(d_1)` is a finitely generated
F₂[G]-module. Its Hilbert series

```
    H(syz(A, B), t)  =  Σ_d dim_F₂ syz_d(A, B) · t^d
```

(where `syz_d` is the degree-d part under some grading) gives the
dimensions of the degree-graded pieces. If we can find a grading on
F₂[G] under which **Hamming weight is bounded by degree**, then a
lower bound on the minimum nonzero degree of `H(syz(A, B), t)` gives
a lower bound on `min weight in syz(A, B)` — and hence on `d_X`.

**Candidate grading**: the "augmentation grading" — degree of an
element f ∈ F₂[G] = the minimum number of distinct group elements
needed to express f in any basis. This is closely related to Hamming
weight in the standard basis. Need to formalize.

**First moves for the new agent**:
- Implement Hilbert series computation for `syz(A, B)` (via Gröbner
  basis or direct rank computation per degree).
- Compute Hilbert series for gross, bb_72, bb_90, and a sample of
  corpus rows.
- Look for a clean relationship between the minimum non-vanishing
  degree and `d_X`.
- If yes: derive the formal bound. If no: document why the grading
  fails (likely the augmentation degree doesn't lower-bound Hamming
  weight tightly enough).

**Time**: 1-2 sessions to implement; 1-2 sessions to test the
relationship and write up.

### 4b. Castelnuovo-Mumford regularity adapted to F₂[G]

For an ideal I ⊂ F₂[x_1, …, x_n] (polynomial ring), the
Castelnuovo-Mumford regularity reg(I) gives a bound on the maximum
degree of a syzygy in I's minimal free resolution. For F₂[G] =
F₂[x, y]/(x^ℓ - 1, y^m - 1), the polynomial ring quotient changes the
analysis but regularity adaptations exist (Aramova-Herzog,
Eisenbud-Goto, etc.).

If reg((A, B)) ≤ r in some adapted sense, then any minimum-weight
syzygy has weight ≤ 2^r (or similar). The DIRECTION of the bound is
typically "regularity bounds degree of generators" which gives an
UPPER bound on syzygy weight — but we want LOWER bound on d_X.

**The honest read**: regularity is well-suited to upper bounds; the
*reverse* direction (lower bound on syzygy weight) is rarer in the
literature.

**First moves**:
- Confirm whether Aramova-Herzog or related papers give *lower*
  bounds on minimum syzygy degree. If yes, instantiate for F₂[G].
- If no, this direction is probably not productive; document and move
  on to 4c.

**Time**: 1 session for literature; 1-2 for derivation if positive.

### 4c. Anick resolution + minimum-weight differentials

Anick's resolution gives a free resolution of the trivial module F₂
over a quotient algebra F₂[G]/(A, B). The differentials d_n in this
resolution are F₂-linear maps between free F₂[G]-modules; their
matrices have entries in F₂[G].

**Hypothesis**: The minimum Hamming weight of an entry in d_n
(across all n) gives a lower bound on `d_X`. More precisely: the
"resolution depth" at which a minimum-weight element appears.

**Status**: untested. The Anick resolution for finite group algebras
is well-defined but the connection to code distance has not been
explored in the published literature.

**First moves**:
- Read Anick's "On the homology of associative algebras" (1986) and
  any modern computer-algebra implementation.
- Implement Anick resolution for small BB codes (bb_72 first).
- Check whether `min weight in d_n` over n correlates with d_X on
  the corpus.

**Time**: 1 session for theory; 2-3 for implementation; 1 for corpus
test.

### 4d. Koszul non-regularity refinement

For regular sequences `(A, B)`, the Koszul complex K(A, B) has
H_2 = 0. For BB codes, k > 0 means H_1 ≠ 0, which is a non-regularity
*signal* but not the strongest. The dimension and minimum-weight of
H_2 (the second Koszul homology) might bound d_X if non-zero.

**Hypothesis**: `min weight in H_2(K) ≥ τ` implies `d_X ≥ φ(τ)` for
some φ.

**Status**: untested. Connection between H_2 and code distance is not
in the published literature for our setting.

**First moves**:
- Compute H_2 for the Bravyi codes (small dim, tractable).
- Check whether it's nonzero on any of them.
- If so, look for a relationship between min weight in H_2 and d_X.

**Time**: 1 session for compute + check.

### 4e. Brouwer-Zimmermann / probabilistic algorithm distance

The classical Brouwer-Zimmermann algorithm computes minimum distance
of linear codes by enumerating low-weight codewords via random
information set decoding. Its **complexity** depends on the gap
between true d and the code length — *suggesting* that codes with
small d-gap-to-length are computationally easy, large d-gap-to-length
hard. The Brouwer bound gives `d ≥ B-Z budget` for any specific BZ
computation that fails to find a codeword.

For BB codes specifically:
- Implement a B-Z search budgeted at weight w
- If no codeword found at weight ≤ w-1 across N samples, then with
  high probability `d ≥ w`
- This is a PROBABILISTIC bound, not deterministic — a probabilistic
  Family D candidate

**Status**: a known algorithmic technique but not typically presented
as a "structural" bound.

**First moves**:
- Adapt B-Z to BB structure (could use F₂[G]-module decomposition
  for more efficient search than naive F₂^n).
- Run on Bravyi codes; confirm matches known d.
- Document as a Family-D-shaped probabilistic predictor.

**Time**: 1-2 sessions for implementation.

---

## 5. Recommended first session for the new agent

Don't try to attempt all five directions. Pick ONE based on these
criteria:

| Direction | Computational cost | Theoretical risk |
|---|---|---|
| 4a (Hilbert series) | Medium | Medium-low |
| 4b (CM regularity) | Low | High (likely wrong direction) |
| 4c (Anick resolution) | High | Medium |
| 4d (Koszul H_2) | Low | Medium-high (might be trivially zero) |
| 4e (Brouwer-Zimmermann) | Medium | Low (technique exists) |

**Suggested ordering**: 4d → 4a → 4c. 4d is cheap and might rule
itself out quickly; 4a is the most promising structural direction; 4c
is the deepest research investment.

4b (regularity) and 4e (B-Z) are less aligned with the "structural
algebraic" goal — they're either ruled out by direction (b) or
computational rather than analytic (e).

---

## 6. What constitutes success / failure

### Success (any of these):

- A closed-form lower bound `d_X ≥ f(A, B, G)` that gives ≥ 6 on
  gross. (Even loose-by-6 would be the first non-trivial Family-D
  bound; current best is Lin-Pryadko Statement 12 at d ≥ 2.)
- A tight bound on a Bravyi instance (any of bb_72, bb_90, bb_108,
  gross, bb_288). The bound formula must use module-theoretic
  quantities derivable from (A, B), not direct codeword enumeration.
- A Lean proof of an explicit bound (even loose) against
  `bbChainComplex`.

### Productive failure (also valuable):

- A proven §6m obstruction theorem: "Any module-theoretic lower
  bound via [Hilbert series / regularity / Anick / etc.] is
  identically loose on gross because of [structural reason]."
- A new computable feature (analogous to round 1's `w_1` or round 2's
  `a_O_y_spread`) that doesn't bound d but characterizes BB structure.
- A worked-out negative result documenting why the candidate
  direction fails empirically or theoretically. Same shape as
  `pipeline/attempts/bb_distance_conjecture_family_a_v2_yspread/result.md`.

### Inadmissible outputs:

- A bound that holds only for non-degenerate codes (§6i excluded).
- A character-theoretic bound (§6j blocked at Tier 0).
- A chain-map / cover-graph bound (§6k blocked).
- A bound whose RHS is a dimension quantity (§6h category error).
- A spectral-gap-based bound (§6l vacuous for k ≥ 2).

The Tier-0 obstruction gate
([`src/bb_lab/obstructions.py`](src/bb_lab/obstructions.py)) will
auto-reject these via `bb-lab classify`.

---

## 7. Tools and substrate available

### Corpus

`experiments/bb_lab/data/bb_instances.duckdb` (gitignored, 16,704
rows / 4,201 SAT-verified / 13 group structures).

Multi-prime mixed-rank G_odd coverage at 100% SAT for the bb_90
structural class — critical for testing any candidate's
non-semisimple behavior.

If you start from a fresh worktree: copy the DuckDB from
`/Users/stavanjain/Code/QuantumErrorCorrectionLean-fresh/.claude/worktrees/<this-worktree>/experiments/bb_lab/data/bb_instances.duckdb`
or rebuild via the scripts in
[`scripts/`](scripts/).

### Pre-built infrastructure

| Tool | What it does | Where |
|---|---|---|
| `bb_lab.obstructions.classify(candidate)` | Pre-flight §6h–§6l check | `src/bb_lab/obstructions.py` |
| `bb_lab.candidates.CandidateRegistry` | DuckDB candidate state machine | `src/bb_lab/candidates.py` |
| `bb_lab.adversarial.generate_stress_tests` | Parameterized falsifier generator | `src/bb_lab/adversarial.py` |
| `bb_lab.predicates` | 14 named predicate vocabulary | `src/bb_lab/predicates.py` |
| `bb-lab classify` (CLI) | Ad-hoc Tier-0 check | `src/bb_lab/cli.py` |
| `bb_lab.radical_weight.w_mu` | Round-1's radical-aware weight invariant | `src/bb_lab/radical_weight.py` |
| `bb_lab.weight_invariants.tz_lower_bound` | LP Statement 12 reference | `src/bb_lab/weight_invariants.py` |
| `bb_lab.algebraic_features._project_poly_to_R_O` | Orbit projection to local ring | `src/bb_lab/algebraic_features.py` |
| Round-2 v1 examples | Family A v2 + Family C v1 implementations | `scripts/family_*.py` |

### Existing scripts to crib from

- `scripts/family_a_v2_seed_check.py` — orbit-projection + Loewy
  basis change. Reusable for any candidate that needs to operate on
  `a_O` in the Loewy basis.
- `scripts/family_a_v2_corpus_check.py` — corpus iteration template.
  Copy structure for Family D corpus tests.
- `scripts/family_c_spectral_check.py` — Cayley character evaluation.
  Reusable building block.
- `scripts/demo_lp12_eval.py` — full Tier-0 → corpus-eval pipeline
  on a known bound.

### Lean target

If a candidate survives Tier 3, the Lean formalization target is
[`QEC/Stabilizer/Framework/Homological/BBChainComplex.lean`](../../QEC/Stabilizer/Framework/Homological/BBChainComplex.lean).
For Family D specifically, the natural sister-file would be
`QEC/Stabilizer/Framework/Homological/Syzygy.lean` or similar.

---

## 8. Honest expectations

Round 1 ran 6 conjecture rounds across ~3 days; round 2 v1 ran 3
families across ~2 days. **Both ended in negative results** that
sharpen the obstruction map. Round 2 v2 (this moonshot) should be
expected to:

1. Take 3+ sessions of focused work.
2. Most likely end in a §6m obstruction theorem or another clean
   negative.
3. With small probability (~10-20%), produce a real non-trivial
   bound on gross.

The non-trivial-bound probability is small but not zero. Module
theory IS the surviving direction; some structural insight could
plausibly land it. The moonshot framing acknowledges this.

---

## 9. First-day checklist

1. Read this whole document.
2. Read [HANDOFF.md](HANDOFF.md) §6h–§6l (obstructions).
3. Read
   [`pipeline/attempts/bb_distance_conjecture_round2_obstruction_map/result.md`](../../pipeline/attempts/bb_distance_conjecture_round2_obstruction_map/result.md)
   for the round-2 v1 outcomes.
4. Verify infrastructure:
   ```bash
   cd experiments/bb_lab
   uv sync --extra dev
   uv run pytest -q                            # 360 passing
   uv run bb-lab classify --family combinatorial --rhs weight \
       --name "syzygy probe" --uses-spectral   # → SHELVED-A-PRIORI (§6l)
   uv run python scripts/family_a_v2_seed_check.py  # 4 cases match note
   ```
5. Pick a Family D direction from §4. Start with 4d (cheap probe) or
   4a (main candidate).
6. Document in a fresh `pipeline/attempts/bb_distance_conjecture_family_d_<variant>/result.md`
   following the round-1 / round-2-v1 convention (verdict at top,
   evidence, mechanism, scope, recommendations).
7. If a candidate survives Tier-0 and shows promising corpus
   behavior, draft a `HANDOFF_C5.md` (or `Cv5_design.md`) following
   the round-1 design-note convention.

---

## 10. Where to get unstuck

- If 4a (Hilbert series) computation is too expensive: try Macaulay2
  or SageMath for a quick prototype before committing to a Python
  reimplementation.
- If 4c (Anick) literature is unfamiliar: see Anick "On the homology
  of associative algebras" (Trans. AMS 1986) and Cojocaru-Pionkowski
  for a modern algorithmic perspective.
- If progress stalls completely after 1-2 sessions: that's data. Write
  it up as a §6m candidate and re-evaluate. Use the qec-moonshot agent
  to spawn an independent perspective: it can read this handoff and
  attempt a different sub-direction in parallel.

Good luck.
