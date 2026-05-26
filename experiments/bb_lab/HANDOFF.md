# bb_lab Handoff — Tier 1 of 4 toward an *analytic* BB-code distance bound

You are continuing a research-engineering program whose end-goal is a
**closed-form, proof-bearing lower bound on the minimum distance `d` of
bivariate-bicycle (BB) quantum LDPC codes**, of the form
`d ≥ f(G, A, B)` for some function `f` you can write down and prove in
Lean. Read this whole document before touching code.

---

## 1. Strategic goal (don't lose this)

For a BB code `BB(G, A, B)` with `G = ZMod ℓ × ZMod m` and polynomials
`A, B ∈ F₂[G]`:

- **Known**: BB codes admit good `[[n, k, d]]` parameters (gross
  `[[144, 12, 12]]`, the IBM bet). Bravyi et al. (Nature 2024,
  [arXiv:2308.07915](https://arxiv.org/abs/2308.07915)) found their
  distances by *computer search* (MIP). Lean-QEC
  ([arXiv:2605.16523](https://arxiv.org/abs/2605.16523)) verified
  distances of `[[90,8,10]]` and `[[70,6,9]]` via verified SAT+LRAT
  (mechanical, but per-instance, no formula).
- **Status quo**: no analytic lower-bound formula is known. Existing
  algebraic bounds (Camion BCH analog, Lin–Pryadko Statement-12) are
  *provably loose* on engineered BB codes — see
  [`pipeline/attempts/gross/result.md`](../../pipeline/attempts/gross/result.md)
  for the gross moonshot's verified negative result.
- **Target**: a closed-form `d ≥ f(G, A, B)` that:
  1. Holds rigorously (provable in Lean against `BBChainComplex`)
  2. Is **tight or near-tight** on the IBM gross polynomials
     (the loose-by-9 Camion bound and loose-by-9 Tillich–Zémor bound are not the bar)
  3. Has algebraic ingredients (polynomial-ring operations, factor
     structure, character theory) rather than combinatorial-search
     ingredients

You will almost certainly *not* hit this in one session. The program is
designed so that **failed attempts are first-class outputs** — see
[`docs/pipeline.md`](../../docs/pipeline.md) for the
"failures-are-first-class" principle. Document everything.

---

## 2. The 4-tier architecture (be religious about this ordering)

Each tier feeds the next. **Do not skip ahead.**

### Tier 1 — Laboratory (Python, outside Lean)

A queryable corpus of BB instances. Each row carries:
- the canonical `(G, A, B)` representative under
  `G-translation × Aut(G) × block-swap`
- structural features computed cheaply (n, k, kernel dimensions,
  ranks, Tanner girth, support diameters, classical-cyclic-code
  minimum distances of A and B individually)
- exact distance `d_exact` from SAT (for instances where that fits in
  budget) or upper bounds `d_ub` from random sampling (for larger
  instances)
- a deterministic regeneration recipe (CLI command + canonical hash)

Tier 1 exists so that Tier 2 has thousands of (feature → distance)
pairs to fit conjectures against. **Without Tier 1, Tier 2 has no
material to work with.**

### Tier 2 — Conjecture mill (still mostly Python)

For each *candidate* analytic bound `d ≥ f(G, A, B)`:
1. Compute `f` over the Tier 1 corpus
2. Compute `d_actual` (from L2 SAT) and `d_ub` (from L1 sampling)
3. Check: does `f(G, A, B) ≤ d_actual` hold for every row? Where is it
   loose, where tight?
4. Output a structured "conjecture record" with hypothesis, support
   rate, tightness statistics, and the structural pattern (if any)
   distinguishing tight cases from loose ones

The mill produces hypotheses; the corpus is the substrate against
which they're tested. Most conjectures should die at this stage from
a single SQL query against the corpus.

### Tier 3 — Skeptic (independent agent)

Survives-Tier-2 hypothesis → adversarial search for counterexamples in
the BB instance space. Cheap (Python, on the corpus + on synthetic
near-miss perturbations), and orders of magnitude faster than
discovering falsity through a failed Lean proof at line 400.

### Tier 4 — Lean (formal proof)

Only conjectures surviving Tier 3 enter Lean. The existing
`qec-moonshot` agent is the right shape *here*, but starved of inputs
today because Tiers 1–3 are incomplete.

**The Lean target is `QEC/Stabilizer/Framework/Homological/BBChainComplex.lean`'s
`bbChainComplex` instances**, with the new bound stated as a
theorem `d_X ≥ f(G, A, B)` for some structural `f`. Mario Carneiro–
style LRAT checking is *not* the path here — we want an algebraic
proof, not a per-instance certified search.

---

## 3. Where you're starting

- Worktree: `.claude/worktrees/bb-lab-v0/` (this directory's
  grandparent)
- Branch: `bb-lab-v0` off `main` at `a21c0a9`
- Latest commit: `b5de5dd` ("Tier 2 candidate distance bound" — but
  that title was *wrong*; the commit contains a textbook CSS upper
  bound, not a positive bound. See §6 below.)
- Worktree mathlib is symlinked to main's `.lake/packages/` (per
  [`CLAUDE.md`](../../CLAUDE.md) § Worktrees).
- Python project at `experiments/bb_lab/` managed by `uv`. From the
  lab dir: `uv sync --extra dev` then `uv run pytest`.

### Quick-check on arrival

```bash
cd .claude/worktrees/bb-lab-v0/experiments/bb_lab
uv sync --extra dev
uv run pytest                                            # should be 44 passed
uv run bb-lab bravyi-check --quick                       # 3 small Bravyi distances
uv run bb-lab verify-cert certificates/bb_72_12_6.cert.json   # full DRAT verify chain
```

If `pytest` is green and `verify-cert` reports
`d_X(bb_72_12_6) = 6` with `drat-trim verifications PASS 5/5`,
the substrate is healthy.

---

## 4. Tier 1 — what's done

| Sub-phase | Status | Commit | Files |
|---|---|---|---|
| v0 substrate validation | ✅ done | `239070f` | All of `src/bb_lab/{group,poly,checks,linalg,codeparams,sat_distance,lean_bridge,certificate,store,cli}.py`, tests, `instances/bravyi_table.yaml` |
| v0 + DRAT track (b) | ✅ done | `239070f` (and within) | `cadical` CLI subprocess, DRAT proofs verified by `drat-trim` for the 3 small Bravyi instances + gross |
| v1.1 canonical-form deduper | ✅ done | `e6b94df` | `automorphism.py`, `canonical.py` (`canonical_pair`, `is_canonical`) |
| v1.2 enumeration + L0 features | ✅ done | `e6b94df` | `enumerate_bb.py`, CLI `bb-lab enumerate`, DuckDB schema with `rank_HX`, `rank_HZ`, `dim_ker_A`, `dim_ker_B`, `orbit_size` |
| v1.3 combinatorial features | ⚠️ partial | `a9ae42a` | `features.py` with `tanner_girth`, `support_diameter`; CLI `bb-lab fill-features` |
| v1.3 algebraic features | ⚠️ partial | `b5de5dd` | `features.min_weight_in_kernel`; `min_wt_ker_A`, `min_wt_ker_B` columns in DuckDB |
| v2 L1 sampling | ❌ skipped | — | — |
| v2.5 L2 SAT exact distance | ✅ done for small corpus | `43b6a8f` | CLI `bb-lab fill-distances`, 460/460 instances labeled |

**Corpus stats** (regenerable):

| Group | Instances | k≥2 |
|---|---|---|
| Z_3 × Z_3 | 12 | yes |
| Z_3 × Z_4 | 73 | yes |
| Z_3 × Z_5 | 103 | yes |
| Z_3 × Z_6 | 166 | yes |
| Z_4 × Z_5 | 0 | (all k=0 — "4-factor curse") |
| Z_4 × Z_6 | 106 | yes |
| **total** | **460** | |

All 460 have `d_exact` computed. n ranges from 18 to 48.

**Test count**: 44 CI tests in `tests/`, ~45s. Plus 2 heroic SAT tests
(gross [[144,12,12]] confirmed locally, [[288,12,18]] partial:
`d ≥ 14` from a killed SAT run, full d=18 confirmation ETA ~3 days).

---

## 5. Tier 1 — what's missing (THIS IS THE NEXT WORK)

Listed in order of how much each unblocks the strategic goal:

1. **Scale the canonical-form pipeline to (6,6), (9,6), (12,6).**
   - Current bottleneck: `is_canonical` over frozensets is
     ~`O(|G|² · |Aut(G)|)` per pair with high Python overhead.
   - Required: bitset (Python `int`) representation of polynomial
     supports + precomputed permutation tables for each
     `(h, φ, swap) ∈ G × Aut(G) × {0,1}`. Apply via
     `permute(supp_int, σ)`. Roughly 50–100× constant-factor speedup.
   - With that, (6,6) weight-3 (the smallest gross-style scale)
     becomes ~minutes; (12,6) becomes ~hours.
   - **Without this scale**, Tier 2 conjectures will overfit to small-n
     behavior and won't generalize to gross-style codes.
2. **L1 sampling for distance UBs at scale.** When SAT distance is too
   expensive (n ≥ 72), random Pauli sampling gives cheap upper bounds.
   The Stim package is the natural tool; the function signature should
   be `l1_distance_ub(checks: CheckMatrices, n_samples: int = 10**5) -> int`.
3. **Run L2 SAT on the scaled corpus.** Most n ≤ 72 instances fit in a
   minute each via `pysat`. Budget: ~few thousand SAT solves ≈ ~1–2
   days unattended. Use the existing `bb-lab fill-distances` CLI.
4. **Query interface.** A small `bb_lab/corpus.py` exposing helpers
   like `corpus.filter(n_range, k_range, group_struct, d_min, ...)
   -> pandas.DataFrame` so Tier 2 has an ergonomic surface. Maybe a
   Jupyter notebook with canned plots. ~1 hour.
5. **Brouwer–Zimmermann or LP-relaxation min-distance algorithm.**
   Current `min_weight_in_kernel` brute-forces `2^dim_ker - 1` subsets;
   safe up to `dim_ker ≤ 22`. For gross `dim_ker_A = 12` it works; for
   bb_288 `dim_ker_A = 24` it doesn't (16M iterations is fine but
   you'd want to be smarter). Defer until you actually hit it.

---

## 6. Critical lessons learned (don't repeat these)

These are real footguns the previous agent (me) walked into. Read carefully.

### 6a. Check the literature **before** declaring a finding

After commit `b5de5dd`, the previous agent claimed
`d_X ≤ min(d_A^⊥, d_B^⊥)` was a novel result. **It is not** — it's
the standard CSS classical-code upper bound applied to the BB block
structure, derivable in a single line:

> For any nonzero `f ∈ ker(M_B^T)`, the X-error `(f, 0)` lies in
> `ker(H_Z)` because `H_Z (f, 0)^T = M_B^T f + 0 = 0`. So `(f, 0)`
> is at worst a stabilizer; if it's not in `rowspan(H_X)` it's a
> nontrivial X-logical of weight `|f|`. Hence `d_X ≤ |f|` for any
> such `f`, i.e. `d_X ≤ minwt(ker(M_B^T)) = d_B^⊥`. Symmetric for A.

This bound is in Calderbank–Shor / Steane CSS distance theory, and is
referenced (often implicitly) in every BB-code paper since
Kovalev–Pryadko 2013. **Lin–Pryadko 2306.16400 specifically discusses
`d_A^⊥`-style quantities.**

Before committing any "new" bound, run:

```bash
# Check Lin-Pryadko + Bravyi-Cross + recent BB-code surveys
# Especially 2306.16400 §IV–V and 2308.07915 § "Code construction"
# Also Roffe's qLDPC review and any "lifted product" paper
```

If you find your bound there, **document it as a re-derivation,
not a finding**. The corpus + tightness stats may still be novel
empirical observations even when the bound is textbook.

### 6b. Don't skip Tier 1 to do Tier 2

I drifted into Tier 2 conjecture-testing (computing `min_wt_ker` for
the corpus, querying tight-vs-loose) **before finishing Tier 1's
scaling step**. The result: my conjecture only saw n ≤ 48 data, which
was small enough that the Bravyi-tier behavior (gross n=144) wasn't in
distribution. Stay disciplined: finish the substrate first.

### 6c. The 4-factor curse is real

Empirically, weight-3 BB codes over `Z_a × Z_b` where `4` divides
either `a` or `b` give **all k=0 codes** (no logicals). This is why
Bravyi's polynomial-and-group choices avoid `4`-factors. Don't waste
SAT compute enumerating `Z_4 × Z_n` for weight 3 — filter at
`only_k_geq=2` (the default for `bb-lab enumerate`).

### 6d. Two SAT processes can't share a DuckDB

`duckdb.connect()` takes an exclusive file lock. If `fill-distances`
is running, your `bb-lab enumerate` blocks. Read-only access is
allowed: `duckdb.connect(path, read_only=True)`. Use this in any
status-check script.

### 6e. The pysat-CaDiCaL DRAT truncation bug

pysat's bundled CaDiCaL has a stdio buffer that doesn't flush before
`get_proof()` returns; DRAT proofs in the 4–16 KB range get truncated
mid-clause. **Solution already in place**: `bb_lab.sat_distance`
shells out to the bare `cadical` binary (installed via `brew install
cadical`) when `proof_dir` is set. Pysat is still used for the
no-proof fast path. Don't try to "fix" this by going back to pysat
for proofs.

### 6f. The Bravyi-table polynomial format isn't fully standardized

The `'x^3 + y + y^2'` format in
[`pipeline/attempts/gross/state.yaml`](../../pipeline/attempts/gross/state.yaml)
is what `bb_lab.poly.from_string` parses. We extended it in
`43b6a8f` to also accept `*`-separated products (`'x*y^2'`, etc.)
because `Poly.canonical_string` emits them. Implicit products like
`'xy'` (no `*`) are explicitly *rejected*. If you ever add a new
polynomial source, run it through `from_string → canonical_string →
from_string` round-trip first.

### 6g. The `[[288, 12, 18]]` heroic is genuinely days, not hours

The SAT-distance growth factor is `~3.1×` per weight step.
`w=13 UNSAT` took 48 minutes. Extrapolating: `w=17 UNSAT` (the
critical one for d ≥ 18) is ~3 days. **Don't kick off this run unless
you're prepared to leave it.** The smaller Bravyi instances all
finish in seconds–minutes.

### 6h. Dimension counts are not weight invariants

A real footgun this program hit. A Tier-2 conjecture proposed

    d_X(BB(G, A, B)) ≥ Σ_O |O| · μ_O(A, B)

where μ_O is the Jacobson-radical filtration depth at orbit O. The
seed observation was true and sharp: for the gross code,
`dim ker M_A = Σ_O |O| · μ_O(A) = 12`, matching `dim ker M_A` exactly.
Tier 3 then ran this against the corpus and found **407 violations
on 3 894 rows** — and `bb_72_12_6` violates *by itself* (bound = 8,
actual `d = 6`). The conjecture is **falsified**.

**Why it had to fail.** The right-hand side `Σ_O |O| · μ_O(A)` is
literally `dim_{F₂} ker M_A` (this is a theorem, not a hypothesis).
That dimension governs the **size of the X-logical coset space** —
combined with the symmetric quantity for B, it gives Bravyi 2024's
Lemma 1: `k = 2 · dim(ker A ∩ ker B)`. **It is a k-invariant, not a
d-invariant.** The minimum weight of an element in a coset isn't
bounded below by the coset's dimension — a 12-dimensional coset can
contain weight-2 vectors. So the conjecture was using the wrong type
of quantity from the start.

The artifact is preserved at
`pipeline/attempts/bb_distance_conjecture/result.md` as a first-class
negative output, in the spirit of the gross moonshot's negative
result. Tier 3's verdict is explicit: "do not attempt to formalize
this conjecture. The Lean proof would necessarily fail."

**Rule for future Tier-2 candidates.** Before testing any bound, ask:
"is this quantity a weight invariant or a dimension invariant?" Weight
invariants (e.g. classical-cyclic-code minimum distance `d_A^⊥`,
per-orbit dual distances, weight-enumerator coefficients) can bound
`d`. Dimension invariants (`dim ker`, orbit-size sums, rank deficits)
bound `k` or related coset-space sizes, not `d`. The literature uses
both kinds — they look superficially similar — but conflating them
costs weeks. The Lin–Pryadko 2306.16400 Statement 12 lower bound
`d ≥ ⌈d_A^⊥ / c⌉` is the right *shape* for a positive bound (it's a
weight quantity over a weight quantity); the loose-on-gross part is
that `c` is too pessimistic for engineered polynomial pairs.

The Jacobson-radical machinery itself (in `algebraic_features.py` and
`tests/test_jacobson.py`) is **not** wasted — it computes a genuine
algebraic invariant, and the identity `dim ker M_A = Σ_O |O| · μ_O`
remains a useful diagnostic. It's just not the right thing to put on
the right-hand side of a `d ≥ …` inequality.

### 6i. Bravyi engineers degeneracy — the engineering target lives in the regime where simple bounds DON'T apply

A natural rescue of the §6h Jacobson conjecture (Tier 2.5) was to
restrict to **non-degenerate** BB codes: those where `⟨supp(A)⟩ = G`
and `⟨supp(B)⟩ = G` (each support generates the full group). Tier 3
round 2 ran this and found a clean conditional theorem candidate on
the corpus:
- 1 937 non-degenerate rows (49.7% of the labeled corpus)
- Naive 43 violations (2.2%) all of form "`B = unit · A`" or weight-≤2
  syzygies in F₂[G]²
- A tightener "no weight-≤2 syzygy" gives zero violations on 1 796
  rows. Clean.

**But every single Bravyi-table instance is degenerate.** Concretely:

| code | `[G : ⟨supp(A)⟩]` |
|---|---:|
| bb_72_12_6 | 3 |
| bb_90_8_10 | 3 |
| bb_108_8_10 | 3 |
| gross [[144,12,12]] | **3** |
| bb_288_12_18 | 3 |

Gross's `supp(A) = {(3,0), (0,1), (0,2)}` generates a subgroup of
order 24 inside the order-72 group `Z_12 × Z_6`. The factor of 3 is
exactly Lin-Pryadko's `c = |G_a ∩ G_b|`. **Bravyi specifically
engineered the polynomials to live in proper-subgroup supports** —
that's part of what gives the lifted-product wraparound structure
its distance.

Consequence: **the non-degenerate filter excludes the entire
engineering target.** A Lean theorem on the non-degenerate domain
would be clean and provable but say nothing about gross. The Tier 3
round 2 verdict was explicit: "Declare partial progress and shelve.
Do NOT advance to Tier 4."

Rule for future Tier-2 candidates: **the engineering target lives in
the degenerate regime, where `c > 1` and supports generate proper
subgroups.** Any bound that gates on non-degeneracy (`c = 1`) is
useful for understanding BB codes broadly but cannot bound gross.
Bounds that are useful for the engineering target MUST treat the
degeneracy index `c` as a parameter (like Lin-Pryadko Statement 12
does, though loosely). The `bb_lab.degeneracy` module is the
classifier; reach for it as a *feature*, not as a domain restriction.

What survives the round-2 → round-2.5 exhaustion: see
`pipeline/attempts/bb_distance_conjecture_conditional/result.md` for
the clean conditional bound on the non-degenerate subset, and the
section on `bb_lab.degeneracy` API for the support-subgroup classifier.

### 6j. The entire character-theoretic distance-bound family is structurally blind to gross

Tier 2 round 3 (HT/Roos multivariate cyclic, T2R3) and round 4
(Bernal–Bueno-Carreño–Simón 2016 apparent distance, T2R4) both
produced trivial / inapplicable bounds on gross. The Round 4 agent's
literature work pinned down the underlying reason and elevated it
to a much sharper structural claim than §6i.

**The observation, made precise**:

> Every published distance bound for abelian (multivariate cyclic)
> codes derived from the **character-theoretic / Fourier-transform
> decomposition** of `F_q[G]` requires `gcd(|G|, q) = 1` — i.e., that
> `F_q[G]` be semisimple. Gross has `|G| = 72 = 2³·9` over `F_2`,
> so `F_2[G]` is **non-semisimple**. The entire family of approaches
> is structurally impotent on gross.

Verified literature:
- Camion 1971 (multivariate BCH), Sabin–Lomonaco 1992, Saints–Heegard
  1995 (IEEE TIT 41(6)), Bernal–Bueno-Carreño–Simón 2016
  ([arXiv:2402.03938](https://arxiv.org/abs/2402.03938)),
  Bernal–Guerreiro–Simón 2017
  ([arXiv:1704.03761](https://arxiv.org/abs/1704.03761)) — **all
  assume semisimplicity explicitly.** BBCS 2016 §II/§III opening,
  Thm 22, Thm 25 all state this assumption verbatim.
- **Jitman–Ling 2013** ("Abelian Codes in Principal Ideal Group
  Algebras", IEEE TIT) is the load-bearing citation: it proves that
  for non-semisimple `F_q[G]`, distance bounds can only be derived
  from semisimple-quotient bounds, and are **never sharper** than
  what the semisimple quotient yields. They also show abelian codes
  in non-semisimple PIGAs are asymptotically bad.

**Implication for the program**: Gross's d = 12 cannot come from any
character-theoretic argument. The Jacobson radical of `F_2[G]` (the
"non-semisimple part") *contributes to `dim ker M_A`* (§6h's identity
`dim ker M_A = Σ_O |O| · μ_O`) but contributes *nothing* to the
lower-bound side of `d` under any extant character-theoretic
framework. **Whatever makes gross d=12 is not visible in the Fourier
decomposition of `F_2[G]`.**

**Rule for future Tier-2 candidates**: any candidate whose RHS
ultimately decomposes the code via characters / Fourier / orbit
projections is structurally limited by the semisimple quotient. Such
candidates can be tested for completeness, but a-priori their
expected value against gross is bounded above by what BCH / HT /
Roos / BBCS / Camion already give (which is ≤ 8 on gross, see
Round 3). The remaining open directions are:

1. **Homological / chain-complex** bounds (e.g. Pesah–Roffe 2025
   cover-graph chain-map transfer; Hsieh–Le Gall 2020; Kovalev–
   Pryadko 2013). These work on the chain complex of the BB code
   directly, not on the group-algebra decomposition. They are
   *categorically* distinct from the character-theoretic family —
   different toolkit, different obstructions, untouched by §6j.
2. **Radical-aware weight invariants** for `F_2[G]` when `2 | |G|`.
   No literature reference found; would require new theory. A
   weight-invariant filtration on the Jacobson radical of `F_2[G]`
   that bounds `d` from below would dodge §6j by definition.

This is a much stronger pruning than §6i: **the entire algebraic-
coding-theory toolkit for multivariate cyclic codes is blocked from
giving a tight bound on gross**, not just one specific approach.
This is consistent with Otjens 2025's stated open problem and
explains why no closed-form formula has been published despite
extensive interest.

---

## 7. Recommended next moves, prioritized

### Move 1 (engineering, ~half-day): bitset canonical form

`src/bb_lab/canonical.py` currently uses `frozenset[tuple[int, ...]]`
for polynomial supports. Replace with a single `int` per polynomial,
where bit `i` is set iff group element `i` (via `G.index`) is in the
support. Then:

- Precompute, for each `(h, φ, swap) ∈ G × Aut(G) × {0,1}`, a
  permutation `σ: int -> int` mapping group-element indices to
  group-element indices after the transformation.
- `is_canonical(A_bits, B_bits)`: for each `σ`, compute
  `(σ(A_bits), σ(B_bits))` via bit-shuffle; compare against the
  current key. Short-circuit on first smaller key.

Expected speedup: ~50× on (6,6), enabling enumeration in ~minutes.

### Move 2 (engineering, ~hours): scale the corpus

```bash
uv run bb-lab enumerate --ell 5 --m 5 --weight 3 --only-k-geq 2
uv run bb-lab enumerate --ell 5 --m 6 --weight 3 --only-k-geq 2
uv run bb-lab enumerate --ell 6 --m 6 --weight 3 --only-k-geq 2
uv run bb-lab enumerate --ell 9 --m 6 --weight 3 --only-k-geq 2
uv run bb-lab enumerate --ell 12 --m 6 --weight 3 --only-k-geq 2  # gross-group
```

Run these as foreground jobs; expect ~hours for (12, 6). Each adds
hundreds to thousands of canonical instances.

### Move 3 (engineering, ~days unattended): L2 SAT at scale

```bash
uv run bb-lab fill-distances --max-n 72  --timeout-per-instance 300
uv run bb-lab fill-distances --max-n 108 --timeout-per-instance 600
```

Larger instances will hit the timeout. Record their `d_method =
sat-timeout@...` and move on. The successful subset is what Tier 2
gets.

### Move 4 (algorithmic, ~half-day): L1 sampling

Add `bb_lab/l1_sampling.py` with random Pauli sampling against the
BB structure for upper bounds on `d`. Stim is the right backend (it's
already in the BB literature). Backfill `d_ub` on rows where
`d_exact IS NULL`.

### Move 5 (Tier 2 entry — only after 1–4): query interface + first
conjecture mill

Build `bb_lab/corpus.py` with `filter(...)`, `feature_correlation(...)`,
etc. Then a small notebook or script that:
1. Reads the corpus
2. Fits candidate bounds `f(G, A, B)` against `d_exact`
3. Emits a structured "conjecture record" per hypothesis

**Before declaring any conjecture novel**, do the literature check
(§6a). Lin–Pryadko 2306.16400, Kovalev–Pryadko 2013, Hsieh–Le Gall
2020, and Roffe's qLDPC survey are the obvious starting points.

---

## 8. File map (where things live)

### Python (the lab)

```
experiments/bb_lab/
├── pyproject.toml                  # uv-managed, Python 3.11
├── README.md                       # user-facing overview, regenerate
│                                   #   instructions, gate status
├── HANDOFF.md                      # this file
├── .gitignore                      # data/, scratch/, big DRAT bundles
├── src/bb_lab/
│   ├── group.py                    # AbelianGroup(orders); ZmZn(ℓ, m)
│   ├── poly.py                     # F₂-polynomial parse / canonical_string
│   ├── checks.py                   # H_X, H_Z; circulant(poly)
│   ├── codeparams.py               # n, k from check matrices
│   ├── linalg.py                   # F₂ rank, nullspace, quotient complement
│   ├── sat_distance.py             # exact d via pysat (fast) /
│   │                               #   cadical CLI (proof-emitting)
│   ├── certificate.py              # WitnessCertificate (bb-cert/v1):
│   │                               #   witness + DRAT refs + SHA256 hashes
│   ├── lean_bridge.py              # state.yaml ↔ JSON ↔ emitted .lean
│   ├── automorphism.py             # Aut(G) via brute-force gen images
│   ├── canonical.py                # canonical_pair, is_canonical
│   ├── enumerate_bb.py             # weight-bounded canonical enumerator
│   ├── features.py                 # tanner_girth, support_diameter,
│   │                               #   min_weight_in_kernel
│   ├── store.py                    # DuckDB schema; bb_instances table
│   └── cli.py                      # bb-lab {bravyi-check, distance,
│                                   #   lean-{import,emit}, verify-cert,
│                                   #   enumerate, fill-features,
│                                   #   fill-distances}
├── instances/bravyi_table.yaml     # 5 reference BB codes, regression contract
├── certificates/                   # committed witness JSON + bb_72_12_6 DRAT/CNF/LRAT bundle
├── data/bb_instances.duckdb        # gitignored corpus
└── tests/
    ├── test_bravyi_quick.py        # (n, k) over the 5 Bravyi instances
    ├── test_bravyi_sat.py          # SAT d over 3 small + 2 heroic
    ├── test_gross_agreement.py     # Lab H_X/H_Z agree with Lean grossA/B
    ├── test_lean_roundtrip.py      # state.yaml → emitted .lean compiles
    ├── test_drat_emission.py       # cadical CLI emits + drat-trim accepts
    ├── test_verify_cert.py         # committed cert re-verifies end-to-end
    ├── test_canonical.py           # Aut counts, canonical idempotency
    └── test_enumerate.py           # enumeration determinism + no dup
```

### Lean (target & handshake)

```
QEC/Stabilizer/Framework/Homological/
├── BBChainComplex.lean             # bbChainComplex(G, A, B), conv, bbBoundary*
├── Code.lean                       # HomologicalCode abstraction
├── CSS.lean                        # CSS Pauli-encoding of HomologicalCode
├── Distance.lean                   # abstract distance bounds
├── LogicalCorrespondence.lean      # H_1 ↔ logicals
└── ...
```

The Tier-4 deliverable would extend `BBChainComplex.lean` (or a
sibling) with the new bound as a theorem.

### Pipeline integration

```
pipeline/attempts/gross/            # the (closed, negative-result)
                                    #   gross-distance moonshot.
                                    #   READ result.md to understand
                                    #   why algebraic bounds fail on
                                    #   engineered BB polynomials.
```

---

## 9. Conventions

- **Branch**: `bb-lab-v0`. Don't merge to main until the program has
  produced a Tier-4 theorem. Commit liberally on this branch; rebase
  for clarity only at landing time.
- **Commit messages**: `feat(bb_lab): TIERX vY.Z — <short title>` for
  feature commits. `chore(bb_lab): ...` for cleanup. Body should be a
  small honest write-up of what changed and why — see existing
  commits `e6b94df`, `43b6a8f`, `a9ae42a` for examples. Co-author tag
  per [`CLAUDE.md`](../../CLAUDE.md).
- **Tests**: always run `uv run pytest` (from the lab dir) before
  committing. The full suite is ~45s; no excuse.
- **DuckDB locking**: only one writer at a time (see §6d). For
  parallel feature filling, partition by `group_struct` and run
  separately, or just sequence them.
- **Worktree hygiene**: per
  [`CLAUDE.md`](../../CLAUDE.md) § Worktrees, `.lake/packages/` is
  symlinked from main. Don't `rm -rf .lake` without re-symlinking.
- **lean-lsp MCP**: available; use `lean_diagnostic_messages`,
  `lean_goal`, `lean_multi_attempt` for proof iteration. **Don't run
  `lake build` while the MCP is iterating** — they share the
  workspace lock.

---

## 10. What you are *not* doing (defer until later)

- **Tier 2, 3, 4 in this session.** Finish Tier 1 first.
- **F₂[G] units in canonical form.** v1.4 territory; not needed for
  the bound search yet. The current canonical form mods out
  G-translation, Aut(G), block-swap — that's enough for substantial
  Tier 2 work.
- **Non-CSS BB codes.** This program is CSS only. BB codes are
  inherently CSS (the structure forces it).
- **Subsystem codes, Floquet codes, lifted products over non-abelian G.**
  All deferred per the moonshot pipeline's
  [`pipeline/queue.md`](../../pipeline/queue.md).
- **The `[[288, 12, 18]]` heroic SAT proof.** Genuinely takes days;
  not on the critical path.

---

## 11. First-day checklist

1. Read this whole document.
2. Run the §3 quick-check (`uv run pytest`, `bravyi-check`,
   `verify-cert`).
3. Read [`pipeline/attempts/gross/result.md`](../../pipeline/attempts/gross/result.md)
   — the negative-result moonshot whose conclusion this program is
   trying to overturn.
4. Read [`README.md`](README.md) for the lab's public-facing story.
5. Skim [`src/bb_lab/canonical.py`](src/bb_lab/canonical.py) and
   [`src/bb_lab/enumerate_bb.py`](src/bb_lab/enumerate_bb.py) — these
   are the files you'll touch in Move 1.
6. **Do the literature check** for "BB code distance bound", "lifted
   product cyclic distance", "two-block group algebra minimum
   distance". Read Lin–Pryadko 2306.16400 §IV–V at minimum.
7. Then start Move 1.

Good luck.
