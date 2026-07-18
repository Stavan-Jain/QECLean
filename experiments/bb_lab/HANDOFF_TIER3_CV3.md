# bb_lab Handoff TIER3 (for C-v3) — adversarial stress test of the narrowed conjecture
> **[Historical research record — extracted 2026-07-18 from the retired
> orchestration branch `bb-lab-v0` during branch cleanup; never previously
> merged.]** This is an original proposal/handoff document (2026-05-26) for one
> phase of the round-1 C-series (weight-aware Jacobson-radical filtration). The
> executed deliverables have long been on main — `notes/Cv1_*.md`,
> `notes/Cv2_*.md`, `notes/Cv3_*.md`, `notes/T3_CV3_*.md`,
> `notes/Cv4_R4_falsified.md`, and
> `pipeline/attempts/bb_distance_conjecture_radical_weight{,_narrow,_narrow_tier3}/`
> — and cite this document by section throughout; it is extracted to repair
> those references and preserve the proposal-side record (priors, stop
> conditions, alternative formulations). The conjecture line it proposes was
> ultimately **falsified** (C-v2 by corpus/Bravyi sweep; C-v3-as-tight by
> Tier-3 batteries; R1+R4 by the Z₃×Z₁₅ adversary). Note: references here to
> "HANDOFF.md §6l" mean an elementary-abelian-G_odd write-up that was never
> merged; that content lives in
> `pipeline/attempts/bb_distance_conjecture_radical_weight/result.md`, while
> main's actual `HANDOFF.md` §6l (from the later round-2 line) is a different
> obstruction (Cayley-spectral vacuity). Nothing here is a live task.


C-v3 has landed a clean conditional bound candidate. **Your job is to break it.**

The pipeline's design principle: a conjecture that's only been tested
on the corpus it was tuned against is suspect. Tier 3 (Skeptic) is the
gate between an empirically-confirmed conjecture and a formally-proven
theorem. **No conjecture should reach Tier 4 (Lean) without surviving
adversarial out-of-corpus testing.**

Required reading order: `HANDOFF.md` (§§6h–6l) → `HANDOFF_C.md` →
`HANDOFF_C2.md` → `HANDOFF_C3.md` → the C-v3 deliverable
(`pipeline/attempts/bb_distance_conjecture_radical_weight_narrow/result.md`)
→ this document.

---

## 1. The conjecture under attack

From C-v3's surviving verdict:

> **Hypothesis**: `G_odd ≅ (Z_p)^k` for some prime `p` (elementary
> abelian) **AND** `c := [G_a : G_a ∩ G_b] ≥ 3`.
>
> **Conclusion**: `d_X(BB(G, A, B)) ≥ (1/c) · min_O min(w_1(A, O), w_1(B, O))`,
> where `w_1` is C-v1's radical-aware weight invariant.

**Both hypotheses are load-bearing**:
- Elementary-abelian-G_odd alone: vacuous on the corpus (all 7
  corpus groups satisfy it). c=1 violations from C-v2 (97% rate)
  remain in domain.
- c ≥ 3 alone: admits bb_108 (which has c=3 but `G_odd = Z_9 × Z_3`,
  not elementary abelian). bb_108 violates the bound at bound=12,
  d=10.

Only the conjunction is clean on the corpus and on 4 of 5 Bravyi codes.

**Plug-in for gross**: G_odd = Z_3 × Z_3 (p=3, k=2, elementary
abelian ✓); c = 3 (≥ 3 ✓); bound = 36/3 = 12 = actual d. Tight.

---

## 2. The empirical base C-v3 left

C-v3's corpus-sweep findings:

| metric | value |
|---|---|
| in-scope corpus rows (both hypotheses hold) | **74** |
| violations | **0** |
| tightness rate | (TBD — see C-v3 result.md) |

**74 rows is small.** The hypothesis space the conjecture should
apply to is much larger than this:

- **Polynomial weight**: corpus is weight-3 only. Bravyi 2024 Table I
  has weight-4 examples.
- **G_odd primes**: corpus has p = 3 throughout (and p = 5 via
  bb_90's mixed Z_3 × Z_15, but our G_odd-elem-ab definition might
  exclude or include this — confirm with the C-v3 classifier).
- **G_2 size**: corpus has |G_2| ≤ 16 (= |Z_4 × Z_2² × Z_2²| at the
  largest, for Z_6 × Z_6). Gross has |G_2| = 8. Larger G_2 means
  deeper Loewy filtration of F₂[G] — the regime where `w_μ` for
  `μ > 1` might matter.
- **|G| range**: corpus c≥3 subset tops out at |G| = 36 (Z_6 × Z_6
  with G_odd = Z_3 × Z_3, c = 3). Gross has |G| = 72.

**Your job is to fill these gaps adversarially.**

---

## 3. The Tier 3 mindset

You are NOT trying to confirm the conjecture. You are trying to
break it. Specifically:

- **Generate instances the conjecture should apply to** (both
  hypotheses hold) **but might fail on** (out-of-distribution
  relative to corpus).
- **Single counterexample suffices to falsify.** Don't aggregate.
  One violation = the conjecture (in its current form) is false.
  Document the violator concretely; the C-v3 agent will use it
  to propose a third hypothesis clause or shelve.
- **Confirmation is just absence of falsification.** If you run 1000
  out-of-corpus instances and none violate, the conjecture is
  *more credible*, not *proven*. Lean is the proof.
- **Heavy bias toward where violations seem likely.** Don't sample
  uniformly — actively look for "edge cases" the corpus didn't
  cover.

---

## 4. The five test batteries (run all five)

### T3-A. Weight-4 BB codes over Z_6 × Z_6

**Why**: corpus is weight-3 only. Maybe the bound is a weight-3
phenomenon.

**What**:
- Enumerate canonical weight-4 BB pairs over `G = Z_6 × Z_6`
  (`G_odd = Z_3 × Z_3`, elem-ab ✓). C(36, 4) = 58 905 polynomials;
  after canonicalization, expect a few thousand canonical pairs.
- Filter to c ≥ 3 (the conjecture's hypothesis).
- SAT-compute d_exact (n=72, weight-4 → SAT may be slower than
  weight-3; budget ~1 min per instance; use --timeout-per-instance
  in `bb-lab fill-distances`).
- For each labeled in-scope instance: check `d_exact ≥ bb_radical_bound`.
- **Sample size target**: at least 50 in-scope instances, ideally
  200+.

**Existing infrastructure**: `bb-lab enumerate --ell 6 --m 6 --weight 4 --only-k-geq 2`
already works. `fill-distances` already works. The C-v3 agent's
`bb_radical_bound` already works. Just run the pipeline with
weight=4 and apply the in-scope filter.

**Save to**: `notes/T3_CV3_A_weight4.md`.

### T3-B. Other G_odd primes

**Why**: corpus is essentially p=3 only (with possibly p=5 in
bb_90-style mixed-prime cases). The "factor of c" coincidence might
be specific to p=3.

**What**:
- **Z_5 × Z_5 family**: enumerate weight-3 BB pairs over groups
  with `G_odd = Z_5 × Z_5`. Concrete groups to try:
    - `G = Z_5 × Z_5` itself (G_2 trivial; n = 50; the conjecture's
      degenerate-c case if c can be ≥ 3 here)
    - `G = Z_10 × Z_10` (`G_odd = Z_5 × Z_5`, `G_2 = Z_2 × Z_2`;
      n = 200; expensive)
    - `G = Z_5 × Z_5 × Z_2` if you can extend the lab to rank-3
      groups (probably not yet)
- **Z_7 × Z_7 family**: weight-3 over `G = Z_7 × Z_7` (n = 98)
  or `G = Z_14 × Z_14` (n = 392, very expensive).
- **Z_3³ family**: weight-3 over `G = Z_3 × Z_3 × Z_3` if rank-3
  is supported (extend `group.py` if not), or `G = Z_3 × Z_3 × Z_6`
  (n = 108).

**Critical**: many of these will need the lab to be extended (the
existing enumeration is hardcoded for rank-2 groups via `ZmZn(ℓ, m)`).
If extending takes more than a day, **fall back to the simpler tests**:
just do `Z_5 × Z_5` and `Z_7 × Z_7` rank-2 cases.

**Save to**: `notes/T3_CV3_B_primes.md`.

### T3-C. Larger G_2 structure

**Why**: corpus's largest G_2 has order 4 (Z_2 × Z_2 for Z_6 × Z_6).
Gross's G_2 is `Z_4 × Z_2` of order 8. Higher G_2 means deeper
Loewy filtration of F₂[G]. `w_1` at level 1 might miss something
that level `μ > 1` would catch.

**What**:
- **Z_24 × Z_24** (`G_odd = Z_3 × Z_3`, `G_2 = Z_8 × Z_8`, |G_2| = 64).
  n = 1152 — too big to SAT-label exactly. Use L1 sampling for d_ub
  and check `bound ≤ d_ub` as a (weaker) consistency check.
- **Z_12 × Z_12** is bb_288's group; already in the Bravyi-table
  benchmark.
- **Z_24 × Z_12** (`G_odd = Z_3 × Z_3`, `G_2 = Z_8 × Z_4`, |G_2| = 32).
  n = 576 — also big. L1 sampling.
- **Z_12 × Z_6** is gross's group; already in the benchmark.

**Save to**: `notes/T3_CV3_C_g2.md`.

### T3-D. Adversarial polynomial-pair sampling

**Why**: the corpus enumeration uses canonical orbit representatives.
The conjecture might exploit a regularity in the canonical-form
selection. Adversarial = "actively construct (A, B) that should be
worst-case for the conjecture."

**What**:
- Within an in-scope group (e.g., Z_6 × Z_6), construct (A, B) pairs
  by:
  - **Random search with rejection**: sample weight-w (A, B), reject
    unless hypotheses hold and the predicted bound is unusually
    high. Then SAT-label and check.
  - **Simulated annealing / hill-climb**: start at a random in-scope
    (A, B), make small changes (add/remove single monomial), score
    by `(predicted_bound - d_ub)` (where d_ub is from L1 sampling),
    climb to maximize the gap.
  - **Symmetric constructions**: pick `A = α₁ + α₂x + α₃y + α₄xy + …`
    and `B = β₁ + β₂x + β₃y + …` with specific algebraic
    relationships (`B = A^σ` for some automorphism σ; `B = A · u`
    for some unit u; etc.) to see if any natural construction
    breaks the bound.
- Budget: ~500-2000 adversarial samples within the in-scope domain.

**Save to**: `notes/T3_CV3_D_adversarial.md`.

### T3-E. Bravyi paper's other examples

**Why**: we've used the same 5 Bravyi codes as a benchmark
throughout. Bravyi 2024 Table I and the supplementary materials
likely list more codes.

**What**:
- Read Bravyi 2024 (`arXiv:2308.07915`) Tables I, II, supplementary
  S1, etc. Extract any BB codes not in our `instances/bravyi_table.yaml`.
- For each: classify by hypothesis (elem-ab G_odd? c ≥ 3?). For
  those in scope, compute bound, compare to published d.
- Look especially for codes with `G_odd ≠ (Z_3)^k` — those are the
  most informative (testing primes other than 3 in the wild).

**Save to**: `notes/T3_CV3_E_bravyi_extended.md`.

---

## 5. Implementation requirements

You can reuse the existing `bb_lab` infrastructure heavily:

| Need | Existing tool |
|---|---|
| Canonical enumeration | `bb-lab enumerate --ell L --m M --weight W` |
| L2 SAT distance | `bb-lab fill-distances --timeout-per-instance 60` |
| L1 sampling for d_ub | `bb_lab.l1_sampling.l1_distance_ub(...)` |
| `bb_radical_bound(A, B, G)` | `bb_lab.radical_weight` (C-v2) |
| Elem-ab G_odd classifier | `bb_lab.degeneracy.is_g_odd_elementary_abelian` (C-v3) |
| c computation | `bb_lab.radical_weight.joint_support_subgroup_index` (C-v2) |
| Corpus query | `bb_lab.corpus.Corpus(read_only=True)` |

**New code you write** goes under `scripts/tier3_cv3_*.py` and
`notes/T3_CV3_*.md`. **Don't modify** existing modules.

**Adversarial sampler** (T3-D): you'll need to write this from
scratch. ~100 LoC in `scripts/tier3_cv3_d_adversarial_sampler.py`.

**Rank-3 group extension** (T3-B for Z_3³): if you need this,
extend `group.py`'s `AbelianGroup` to handle rank ≥ 3. This may
take more than a day; **document the cost and consider whether
T3-B without it (rank-2 only for new primes) is sufficient**.

---

## 6. Verdict structure

Create `pipeline/attempts/bb_distance_conjecture_radical_weight_narrow_tier3/`
with `state.yaml`, `evidence.md`, `result.md`. The verdicts:

- **survives-tier3-clean** (zero violations across all 5 batteries) →
  hand off to **C-v4 (Lean formal proof)**.
- **survives-tier3-with-refinement-needed** (clean within a sub-domain
  but violations elsewhere) → propose a refined hypothesis (third
  clause) and document. Possibly hand back to C-v3 round 2 with the
  refined hypothesis.
- **falsified** (at least one in-scope counterexample found, no clean
  refinement) → document concretely. The conjecture in its current
  form is dead; the C-v1/C-v2 machinery survives as new mathematics
  with no distance bound.

**Critical**: report the per-battery numbers separately.
Aggregate "0 / N total violations" is less informative than:
- T3-A: 0 / 200 (weight-4 over Z_6 × Z_6)
- T3-B: 5 / 50 (Z_5 × Z_5 has violations!)
- T3-C: 0 / 30 (Z_24 × Z_24 with L1 d_ub)
- T3-D: 12 / 1000 (adversarial found edge cases)
- T3-E: 0 / 8 (Bravyi extended)

That breakdown tells the next agent which sub-domains to refine,
which are clean, and where the structural boundary actually lies.

---

## 7. Hard constraints

- Read-only on `data/bb_instances.duckdb` (corpus). For **new
  instances you generate**, use a separate DB:
  `data/tier3_cv3_outofcorpus.duckdb`. Don't pollute the
  reproducibility of the main corpus.
- **Don't modify** any existing source module (`src/bb_lab/*.py`).
  Extend in new files only.
- **All §6h–§6l rules still apply.** Especially §6l: don't pretend
  the conjecture is general when it's restricted to a specific
  hypothesis. The hypothesis is part of the theorem.
- Tests must pass: `uv run pytest -m 'not slow' -q` from
  `experiments/bb_lab/`. Your new tests add to the count.
- **Don't commit unless explicitly asked.** Pattern-match the C-v1,
  C-v2, C-v3 discipline.

---

## 8. Risks specific to this round

- **Most concerning**: a weight-4 violation in T3-A. The
  conjecture would still survive on weight-3, but the theorem
  statement would need an explicit weight bound. Document
  precisely if found.
- **Most likely**: a Z_5 × Z_5 violation in T3-B. The factor-of-c
  pattern is empirically tested only at p=3. Other primes might
  have different scaling.
- **Edge case**: T3-D adversarial sampling could find violations
  that aren't really structural — e.g., one specific (A, B) where
  the canonical form happens to land badly. Re-verify any
  adversarial-found violation with a fresh SAT computation and
  hand-checking.
- **L1 sampling gives only upper bounds**. If `bound > d_ub`, that's
  a *probable* violation but not certain (d could be ≥ bound and
  d_ub could be a loose sample). For any T3-C "violation" found
  via L1, follow up with L2 SAT to confirm. Budget for this.

---

## 9. First-day checklist

1. Read `HANDOFF.md` end-to-end (especially §6l).
2. Read `HANDOFF_C2.md` and `HANDOFF_C3.md`.
3. Read the C-v3 result:
   `pipeline/attempts/bb_distance_conjecture_radical_weight_narrow/result.md`.
4. Read this document end-to-end.
5. `cd experiments/bb_lab && uv sync --extra dev && uv run pytest -m 'not slow' -q` —
   confirm 256+ passing (C-v2's count) plus whatever C-v3 added.
6. Re-run the C-v3 sweep to verify you reproduce 74 in-scope rows
   with 0 violations. **If you can't reproduce the C-v3 numbers,
   stop and ask** — something's wrong in the pipeline.
7. Start with **T3-A** (weight-4 over Z_6 × Z_6). It's the most
   important single test and uses the most familiar group. If
   weight-4 violates, the conjecture statement needs to add a
   weight bound, which is information you want before running
   T3-B through T3-E.

---

## 10. Expected timeline

- T3-A (weight-4): 1-2 days (mostly compute; SAT-labeling is the
  bottleneck).
- T3-B (other primes): 2-3 days, plus possibly 1-2 days for rank-3
  group extension.
- T3-C (larger G_2): 1-2 days (mostly L1 sampling; L2 follow-up
  on suspected violations).
- T3-D (adversarial): 1-2 days.
- T3-E (Bravyi extended): half-day (mostly literature work).
- Verdict + artifact: half-day.

**Total: ~6-10 days under honest effort.**

Subjective priors before running:
- ~40% survives all 5 batteries cleanly (→ C-v4).
- ~35% survives 4 of 5 with a clean obstruction in the 5th (→ refined
  hypothesis; back to C-v3 round 2).
- ~15% falsifies on T3-A (weight-4) or T3-B (other primes) cleanly
  (→ conjecture statement narrows further).
- ~10% falsifies adversarially with no clean structural distinction
  (→ shelve).

---

## 11. What's after Tier 3

### If survives-clean:
Write `HANDOFF_C4.md` for the Lean formal proof attempt. The C-v4
agent's job: formalize `bb_radical_bound` and the hypothesis
predicate in Lean against `BBChainComplex.lean`, then prove the
distance inequality. The hard pieces are:
- Defining `w_1` in Lean (the existing `Framework/Homological/` has
  the abstract chain complex; you'd extend it).
- Defining `c` (Lin–Pryadko's index) in Lean.
- The actual proof — likely follows a chain-complex / homological
  argument adapting the Lin–Pryadko Statement 12 proof technique
  to the C-v1 radical-aware setting.

### If survives-with-refinement:
Refine the hypothesis. The conjecture statement becomes:
"For BB codes with G_odd elementary abelian AND c ≥ 3 AND [new
condition]: bound holds." Then C-v3 round 2 verifies on the
corpus + this Tier 3's data.

### If falsified:
Document the violator concretely in
`pipeline/attempts/bb_distance_conjecture_radical_weight_narrow_tier3/result.md`.
The C-v1/C-v2 machinery is still a contribution (a new weight
invariant), but the distance-bound goal is unmet. Update HANDOFF
§6m with the new failure mode.

---

## 12. Out-of-scope for Tier 3

- C-v4 (Lean proof).
- Refining the conjecture mid-Tier-3 to dodge a found violation.
  Tier 3's job is *find* violations; refinement is C-v3 round 2's
  job.
- Investigating any G_2 obstruction that doesn't appear in your
  test batteries.
- Generating instances that *don't* satisfy the conjecture's
  hypothesis. The hypothesis is the domain of the claim — only
  in-scope instances are relevant.

---

Good luck. The conjecture is **the strongest result the program
has produced**. Your role is the most thankless in the pipeline
— if it survives, you'll have produced no new code or theorem,
just confidence in someone else's. But if you find a violation,
you've prevented a wrong theorem from being formalized in Lean.

Both outcomes are real contributions. Be the skeptic.
