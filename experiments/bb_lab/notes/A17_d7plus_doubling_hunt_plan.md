# A17 — the d ≥ 7 doubling hunt (plan)

**Status: PLAN (2026-07-06).** Continuation of A14's constructive residue
(§16): "fresh-base enumeration (d ≥ 7, k > 0, outside the Bravyi corpus)
with the battery as front filter, the deficit-wall theory question, and
the consolidation track." Goal: the first BB code with an analytically
certified distance **> 12** via the doubling template — an S4-certified
safe floor ≥ 2·d(base) on a d ≥ 7 base, lifted through the PR #53
parametric `BBCover`/`BBDoubling` layer.

## 0. The reframing finding (2026-07-06 census)

The §16 residue said *fresh-base enumeration*; a census of
`data/bb_instances.duckdb` (16,867 rows) shows the fresh pool **already
sits in the lab's own DB, unscreened**:

- **1,361 SAT-certified d ≥ 7, k > 0 rows** (`d_method = sat`), of which
  the A14 battery ever touched only bb_90/bb_108 (4 axes, §14) and
  bb_288 (§16). The 638-row T1 screen file caps at `d_base = 6`.
  - **d = 12 (8 rows)**: six fresh `bb_neigh_z5z15_*` [[150,8,12]] codes
    on Z₅×Z₁₅ (all A = 1+y+x, varying B) → **d = 24 target at n = 300**,
    beyond the CaDiCaL-UNSAT-tractable regime — doubling would be the
    *only* certification route; plus 2 gross-class Z₁₂×Z₆ rows.
  - **d = 10 (203 rows)**: Z₂₁×Z₃ (84), Z₁₅×Z₆ (86), Z₁₅×Z₃ (15),
    Z₅×Z₁₅ (14), Z₁₅×Z₅ (4) → d = 20 targets. Many are plausibly
    re-decompositions / Frobenius relatives of the bb_90/bb_108 class
    (58-member A5 class) — the deficit wall predicts 18 there — but SF
    is presentation-sensitive, so each stored row is its own cell.
  - **d = 8 (1,150 rows)**: [[60,4,8]] Z₅×Z₆ (936), [[72,4,8]] Z₆×Z₆
    (114), the rest scattered → d = 16 targets. **A single pass already
    beats 12.** This stratum includes the cross-axis rung-2 cells §13
    did *not* sweep (§13 was same-axis only): e.g. pair72 [[72,4,8]]
    doubled along **y** → [[144,4,16]] target. Toric analogy
    (L×L → 2L×L → 2L×2L) predicts cross-axis re-doubling *works*;
    tour-de-gross arithmetic (6→12→18) predicts +6 not ×2 for the
    gross-lineage k=12 cells — the battery decides, cheaply.
- **12,503 enumerated k > 0 rows with `d_exact` NULL** (12,488 on
  Z₉×Z₆, n = 108) — an in-DB frontier before any new `enumerate_bb` run.

So the hunt continues **inside the DB with existing tooling** before any
new enumeration.

## 1. Phase 1 — in-corpus d ≥ 7 battery (1–2 sessions, start here)

New driver `scripts/a17_corpus_battery.py`, generalizing
`a14_d10_battery.py`:

1. Pull all d ≥ 7, k > 0 rows via `bb_lab.corpus.Corpus` (read-only);
   both axes each → ≈ 2,722 (row, axis) cells.
2. Per cell: k-gate (Bezout `1 + x^ℓ ∈ (A,B)`, A12 theorem) → S0 (raw
   seam, free) → S1+ (descent) → S2 (sector); **S4 safe-floor SAT only
   on cheap-tier survivors** (base-side membership-row augmentation,
   ~25 s certify / up to ~70 s deep-refute at n = 288 scale, so n ≤ 180
   bases are cheap).
3. Discipline carried over from A14 §8: screen **stored presentations**
   (no Aut-orbit maximization before screening; only G-translations are
   safe), never read a timeout as a floor, never claim
   necessity-for-doubling (overlap rescues exist).
4. **Persist every S4 refutation witness** (weight + vector) — this is
   the Phase-3 dataset; a silent pass/fail bit wastes the run.
5. Tag rows with `diffset_predicates.is_frobenius_related` against the
   bb_90/bb_108 class for *reporting* (per-code ceilings), not for
   skipping.
6. Priority order inside the run: d = 12 strata first (highest value),
   then d = 10, then d = 8 (highest hit probability); log per-stratum
   power/yield so the sweep is auditable.

**Decision gates.**
- Any S4-certified pass → jump to Phase 4 (certification) immediately.
- Near-miss (deficit ≤ 2) → §15-protocol orbit sweep for that code
  (`a14_bb108_orbit_sweep.py` machinery + §16 lazy k-gate; sampling
  protocol at scale).
- All-fail → the deficit-wall sample grows from ~3 codes to O(10³)
  cells across three distance strata (Phase-3 fuel), and Phase 2 starts.

## 2. Phase 2 — enumeration frontier (background-friendly, compute-bound)

**Battery as front filter — invert the old pipeline.** SAT-distance is
the expensive step; the battery is base-presentation-side and seconds
per cell. So:

1. **In-DB first:** run k-gate + S0/S1+ against a *target* floor
   (≥ 16) over the 12,503 distance-less rows; `fill-distances` (SAT)
   only on battery-passers whose `d_lb`/`min_wt_ker_*` columns permit
   d ≥ 7 — never the reverse order.
2. **Fresh enumeration:** audit `group_struct` coverage, then extend
   `enumerate_bb` (sharded parallel) to uncovered |G| ∈ ~54–150 shapes;
   weight-4 as a stretch (Cv3-A precedent). Every new row: k > 0 gate →
   battery → SAT-d on survivors → DB. Known lesson: structural gates
   over-produce (k = 0 flood) — k-check + SAT validation stay mandatory.
3. DuckDB single-writer discipline (HANDOFF §6d): one writer, readers
   `read_only=True`.

## 3. Phase 3 — deficit-wall theory (parallel thinking track)

Candidate OQ from §16: is `max over presentations of the safe-floor
minimum` pinned to **2d − 2** for non-doubling (code, axis)? Note
2d − 2 = 2(d − 1) — the "weight-(d−1) base object whose double-cover
shadow lands in the safe sector" hypothesis.

1. Decompose the killer witnesses in hand (bb_108 wt-16/18, bb_288
   wt-28–34) **plus every Phase-1 refutation witness** through the
   Prop A14.1 seam-carry formula into base components; look for
   lift-of-(d−1)-object + bounded-correction structure.
2. Deliverable either way: a *necessary* condition for SF ≥ 2d ("SF ≥ 2d
   ⟹ [algebraic condition on (A,B)]") that prunes Phases 1–2, or a
   located crack telling us where passes can live. Connects to the open
   closed-form-S0 residue (§14) and the overlap-rescue model system
   (Z₃×Z₄:y, A11).

## 4. Phase 4 — certification & consolidation (triggered by first hit)

1. **LRAT bridge spike** (scoped: one certificate end-to-end): S4
   safe-floor SAT + base-distance SAT emit DRAT → LRAT, checked
   (cake_lpr or equivalent); store under `certificates/`. Both SAT legs
   of a hit must carry checkable proofs.
2. **Lean instantiation** of the hit through the parametric cover /
   doubling layer, [[72,4,8]] chain as template → `HasCodeDistance` for
   the double; two-tier claim per the Paper-1 positioning (Lean doubling
   theorem + certificate-checked base facts).
3. **A14 Phase 3 Lean** (Prop A14.1(1)–(2) in `BBDoubling.lean`) — now
   cheaper: A13-L2b's exactness core (`BBTransferH1`,
   `push0_surjective`) already landed; land once, consume twice.
4. hit3-y engine re-instantiation stays queued but **subordinate** — a
   d ≥ 14 hit supersedes it as headline; revisit if the hunt closes
   negative.

## 5. Logistics

- Worktree; symlink `.lake/packages` (CLAUDE.md recipe) **and** the
  gitignored corpus DB from the main checkout
  (`experiments/bb_lab/data/bb_instances.duckdb`) — read-only
  connections are concurrency-safe.
- Branch: `claude/a15-corpus-d7-battery`.
- Failures are first-class: log in this note + `research_log.md`.

## 6. Phase 1 log (2026-07-06) — sweep complete; a 21-cell live docket

Driver: `scripts/a17_corpus_battery.py` (tier semantics identical to
`a14_d10_battery.py`; adds corpus-DB targeting, witness persistence,
per-class cheap-weight persistence, x^21-1 idempotent support for the
Z21xZ3 frames, glob-resume + `--shard K/N` parallelism). **Validation
gate GREEN on first run**: all four SS14 verdicts reproduced bit-for-bit
(bb90-x/y cheap-reject at 10, bb108-x K-gate, bb108-y cheap-reject at
18), and both SF-true anchors (pair72-base-x, gross-base-x) came back
**SF-CERTIFIED** by S4 rather than merely unrejected — an independent
re-run of the SAT-vs-Lean cross-check. Data:
`data/a17/corpus_battery*.jsonl` (per-cell records incl. witnesses),
`data/a17/docket_probe.json`, logs `data/a17/run_*.log`.

**Coverage: 2,722/2,722 cells** (16 d=12 + 406 d=10 + 2,300 d=8; the
completeness identity checked after the sharded runs). Ops note: at
`conf_budget=10M` a handful of S4 cells grind for hours; the sweep
protocol that worked is 8-way sharding + a final low-budget
(300k-conflict) pass recording honest INCONCLUSIVE, leaving hard cells
to a dedicated docket pass. Verdicts:

| stratum | cells | K-GATE-FAIL | CHEAP-REJECT | SF-REFUTED | INCONCLUSIVE | SF-CERTIFIED |
|---|---|---|---|---|---|---|
| d=12 (floor 24) | 16 | 1 | 8 | 7 | 0 | 0 |
| d=10 (floor 20) | 406 | 9 | 299 | 95 | **3** | 0 |
| d=8 (floor 16) | 2,300 | 193 | 1,400 | 689 | **18** | 0 |

**Headline 1 — the deficit-2 bucket dominates, and (per the parallel
P3 result) that is the parity-maximal failing value, not a mystery.**
IMPORTANT measurement discipline, from A17-P3 (branch
`claude/charming-euler-ef6879`, `notes/A17_deficit_wall.md`, same
day): recorded reject weights are **first-found witness / descent
weights = upper bounds on d_safe, NOT minima** — the SS15/SS16
"orbit ceiling 18 / 32-34" readings were retracted on exact ladders
(stored bb108-y: d_safe = 14, certified both sides). Read this
histogram accordingly: among 2,497 refuted cells, reached-weight
deficit 2 is the largest bucket, **708 cells (28%)**, vs 636 at 4,
623 at 6, then falling; per stratum 40% (d=12) / 22% (d=10) / 29%
(d=8); across every frame in the pool. P3's L1 (parity theorem: |A|,
|B| odd forces all cycle weights even, so **2d - 2 is the unique
maximal SF-failing value**) explains the bucket's location; its size
says how often refutation lands at the parity boundary. The d=12
instance: six Z5xZ15 [[150,8,12]] cells passed EVERY cheap tier
(cheap minima 24-32, at/above floor 24) and were refuted only by
solver witnesses at 22 (one at 20) — i.e. **d_safe <= 22 = 2d - 2**,
exact minima unmeasured, the same "invisible to raw seams and
descent" shape as bb_288's SS16 killers. The corrected P3 residue
(code invariant: maxSF in {2d} union {even <= 2d - 2}) now has a
2,700-cell upper-bound dataset with per-class weights and witness
supports for calibration.

**Headline 2 — rung-2 confirmations.** The corpus's own gross-class
[[144,12,12]] rows reproduce SS13's same-axis freeze (x-cells
cheap-reject at 12), and the *cross-axis* rung-2 cells — the one
direction SS13 left unswept — die too (one K-GATE-FAIL: a condition-2
death; one cheap-reject at 12). Consistent with tour-de-gross
arithmetic (its r=2 member is [[288,12,18]], not 24).

**Headline 3 — condition-2 deaths are frame-concentrated.** 193 of the
203 K-GATE-FAILs are the single frame (Z5xZ6, axis x) — the x-cover of
that group kills k across essentially its whole d=8 population. (A12's
Bezout criterion `1 + x^l in (A,B)` now has a bulk in-the-wild dataset;
possibly a clean ideal-theoretic reason at (l, m) = (5, 6).)

**Headline 4 — the live docket: 21 INCONCLUSIVE cells, 0 certified,
0 refuted.** Composition:

- **13x Z21xZ3 [[126,8,8]]** (floor 16), 11 on axis x, ALL sharing
  A = y + y^2 + x^3 with three-monomial B's — a single A-family. Cheap
  minima exactly 16 = floor; S4 could not decide <= 15 in 10M conflicts
  (several ground 2-9 ks each).
- **5x Z5xZ15 [[150,8,8]]** (floor 16), cheap minima 18-32.
- **3x Z15xZ6 [[180,4,10]]** (floor 20), cheap minima 28, 48, 50 (!).

**Ladder-from-above probe** (`scripts/a17_docket_probe.py`, 300k
budgets, 17 s total): every above-floor cell has SAT witnesses far
below its cheap minimum — descent tiers are nowhere near truth on
these frames (cmin 50 -> wt-34 witness instantly; cmin 48 -> 32;
cmin 32 -> 24; cmin 22 -> 18; cmin 18 -> 16 = floor exactly). True
minima sit in [floor, floor + ~14], undecided at the floor boundary.

**Parity sharpening (checked, all 21 cells).** Every im d2 generator
of a weight-(3,3) BB code has even weight 6, and weight-parity is
additive over XOR, so each safe coset has constant parity; all docket
seam weights are even. Hence: **refutation requires a witness at
<= floor - 2** (14 resp. 18 — the floor-1 queries were chasing an
impossible odd weight), and **certification = UNSAT at floor - 2 plus
the parity lemma** — the same kernel-clean step the gross Lean proof
already uses (`chainWeight_coset_even`). (This is the docket-level
instance of A17-P3's L1, re-derived here independently — convergent.)
The f2a6f17e1c41ff96:y cell (witness AT floor 16) is one UNSAT-at-14
from SF-CERTIFIED-with-tightness; likewise 38d3c884:x (witness 18)
and the whole Z21xZ3 family. P3's cost calibration tempers
expectations: a base-side coset UNSAT@12 on a 54-cell frame took
~69 min at 20M conflicts; our docket frames have 126-180 cells, which
is exactly why 10M-conflict queries stalled — hence the XOR-solver
spike below, before any CaDiCaL-days.

**Status of the hunt after Phase 1:** no doubling pass yet; the wall
holds everywhere it was decided; but the sweep's residue is a sharp,
small, structured docket — 21 cells, three families, one decisive
query shape (UNSAT at floor - 2 on n = 126-180 frames, the XOR-heavy
regime where CaDiCaL stalls both ways). Next actions, in order:

1. **Docket decision pass.** Export the 21 floor-2 queries to DIMACS;
   spike XOR-aware / stronger solvers (CryptoMiniSat native XOR,
   kissat) before burning CaDiCaL-days; high-budget CaDiCaL overnight
   as fallback. Any UNSAT = **first SF-certification at d >= 7** (a
   [[252,8,16]]-target or [[360,4,20]]-target double), which would be
   the program's first analytic floor > 12.
2. **Wall theory: SS3 is EXECUTED** by the parallel A17-P3 fork
   (parity value theorem + pushforward mechanism + the witness-weight
   retraction; see `notes/A17_deficit_wall.md` on
   `claude/charming-euler-ef6879`). What this sweep adds to it: the
   2,700-cell upper-bound dataset for calibrating the corrected
   residue (max-SF invariant), and the Z21xZ3 docket A-family
   (y + y^2 + x^3) as a concrete hover-at-the-floor population worth
   a K_z / pushforward analysis before any solver-days.
3. Deficit-2 orbit sweeps (SS15 protocol) stay DE-prioritized: the
   wall's cross-family recurrence prices rescue odds low; the docket
   dominates on expected value per CPU-hour.

### 6.1 Docket decision pass (2026-07-06/07) — FOURTEEN SF-CERTIFICATIONS

Driver: `scripts/a17_docket_decide.py`. The decisive query per cell is
`exists coset element of weight <= floor - 2` per G-orbit rep (parity
makes floor-1 vacuous): SAT refutes SF; UNSAT on all reps certifies
`SeamCosetFloor floor`. Backends: **cryptominisat5 with the XOR rows
passed natively as DIMACS x-lines** (no Tseitin), kissat/cadical
binaries on the Tseitin CNF as second opinions. Every SAT model is
re-verified in numpy before being believed; smoke gates (known-refuted
cell -> SAT; pair72-base @6 -> UNSAT) passed on both cms and kissat.

**The XOR-native encoding cracked what pysat-CaDiCaL could not**: the
Z21xZ3 queries that stalled for hours at 10M conflicts decided in
3-20 min each under CMS. Run shape: 6-way shards, 1200 s/query
timeout, ~2 h wall. Results (data/a17/docket_decision.jsonl):

- **SF-CERTIFIED: 14 of 21** — every safe-class coset minimum >= 2d,
  solver-grade, witnessed UNSAT on every G-orbit rep + the parity step:
  - **all 12 Z21xZ3 [[126,8,8]] x-cells** (the complete A-family
    x-slice, A = y + y^2 + x^3) — doubling target [[252,8,16]];
  - **e21c6389f1a88067 on BOTH axes** (y-reps ~15 min each);
  - **f2a6f17e1c41ff96:y [[150,8,8]] (Z5xZ15) — WITH TIGHTNESS**: the
    SS6 probe's weight-16 witness + UNSAT@14 pin its safe minimum at
    exactly 16 = 2d. First certification outside the Z21xZ3 family.
- **Retry pass (7200 s/query, 3 workers) certified 4 more**:
  16884e06:y (both axes now), 38d3c884:x AND :y (third both-axes
  code; its x-side UNSAT took 7489 s — the hardest landed query),
  ac46bbea:y. **Final: 18/21 SF-CERTIFIED, 0 refuted** — every
  floor-16 docket cell certified.
- **UNKNOWN: 3** — the Z15xZ6 [[180,4,10]] floor-20 cells (37a70e02:x,
  5e50a9:x/y) resisted 2h+ per query (n = 180 at bound 18 is a harder
  class). Honest open; candidates for longer budgets, a totalizer
  cardinality encoding, or a bigger machine.

**Both-axes codes (each = two independent certified doubling axes):**
e21c6389 (Z21xZ3), 16884e06 (Z21xZ3), 38d3c884 (Z5xZ15).

**kissat/DRAT spike (proof-grade leg): LANDED.** The tightness cell
f2a6f17e:y re-proved UNSAT@14 by kissat on the Tseitin CNF (2429
vars / 5430 clauses) in 9506 s, emitting a **6.85 GB DRAT proof**
(gzipped to 3.3 GB, `data/a17/kissat_f2a6f17e_y_w14.drat.gz`,
regenerable deterministically). Two fully independent solver routes
now agree on the first certification. Cost ratio kissat:CMS ~ 10:1 —
a full 18-cell DRAT sweep is machine-days; batch it deliberately.
drat-trim verification + LRAT emission NOT yet run: the build was
declined by the session sandbox (external-code rule) and, more
practically, the disk was at 99% (LRAT > DRAT; ~3-7 GiB free). The
proof-check leg needs: user-approved drat-trim (or cake_lpr) install
+ disk headroom.

**These are the program's first safe-floor certifications past d = 6**
— SeamCosetFloor 16 on eighteen (code, axis) cells over fifteen
distinct d = 8 bases. What certification does and does not give: SF is
the template's provability bottleneck (A11: SF-true doublers 111/111;
0/465 sufficiency violations; T2: SF + (M)-half => doubles), but the
unconditional doubling claim per cell still owes the cover-side
confirmation — next: witness-side cover ladders at 16 on the n = 252 /
n = 300 cover targets (cheap), cover UNSAT@14 / Lean packaging after.

**Trust status, stated honestly:** CMS UNSATs ride its Gauss-Jordan
XOR reasoning — sound but proof-less (DRAT is disabled under Gauss).
SAT-side answers are numpy-re-verified; UNSAT-side rests on solver
correctness, same trust tier as the corpus's CaDiCaL d_exact values.
Proof-grade upgrade in flight: kissat DRAT spike on the tightness
cell's Tseitin CNF (first LRAT-bridge artifact if it lands); full
kissat confirmation sweep + cake_lpr checking = the Phase-4 residue.

**Cross-fork ops note:** CMS-with-x-lines re-prices every "CaDiCaL
can't" in the program — A17-P3's "bb_288 exact minima priced out"
(<= 34, unmeasured) and the 5 h bb108-y cover-side UNSAT are worth
re-running under this backend.

### 6.2 Lean packaging of the tightness cell (2026-07-07)

**The f2a6f17e1c41ff96:y pair is Lean-packaged** — the Phase-4 item 2
deliverable, [[72,4,8]] chain as template, Paper-1 two-tier shape.
New: `QEC/Stabilizer/Codes/BivariateBicycle/Z5Z15F2A6/` (Defs,
DeckHomotopy, Witness, Distance) + a parametric extension of
`Framework/Homological/BBDoubling.lean`. Generator:
`scripts/gen_f2a6_z5z30_data.py` (all checks green; data:
`data/a17/f2a6_z5z30_lean_data.json`).

**A template correction forced by d = 8 (the parametric extension).**
The shipped assembly consumed `StrongBaseFloor d` (every nonzero base
cycle ≥ d) — TRUE for gross (d=6) and pair72 (d=4) but **false for
every d ≥ 7 weight-(3,3) base**: generator columns ∂₂δ_g are weight-6
cycles. Fix: the zero rung's descended diagonal chain is automatically
a non-boundary (pullbacks of boundaries are boundaries), so the plain
distance floor suffices. New `LogicalFloor d` Prop + `_of_logicalFloor`
variants (zero rung, sector assembly, chain/Pauli `IsLeast`) — these,
not the strong forms, are what every future A17 instance consumes.
(The single/pair-shape rungs still take the strong floor; generalize
when a d ≥ 7 dangerous sector is first discharged.)

**Two-tier split for this instance:**

- *Kernel-checked (native_decide, unconditional):* the cover bundle
  (proj/deck/section, push_A/push_B for the literal lift); homotopy (R)
  via a genuinely two-sided Bezout witness `P⋆A + Q⋆B = 1 + y^15`
  (|P| = 25, |Q| = 3 — first non-`P = 0` instance; solved + greedy-
  sparsified offline); the tight witness u* (weight-8 base logical) and
  its lift τ(u*) (weight-16 cover logical, dual-flux-witness certified,
  wt-18 witness) — i.e. the witness halves d(base) ≤ 8, d(cover) ≤ 16
  are now kernel facts, upgrading the SS6/ladder SAT witnesses.
- *Certificate-checked hypotheses (named Props on the theorems):*
  `LogicalFloor 8` (corpus CaDiCaL UNSAT@7), `SeamCosetFloor 16` (the
  §6.1 S4 certificate: CMS UNSAT@14 + parity + transport; kissat DRAT),
  `DangerousFloorNZ 16` (**assumption** — the (M)-half; A11 0/465, per-
  instance rung discharge = future work).

Headlines: `cover300_chain_distance_eq_16`,
`cover300_pauli_distance_eq_16` — d(cover) = 16 = 2d conditional on the
three floors; `cover300_exists_weight16_nontrivial_cycle` +
`base150_exists_weight8_nontrivial_cycle` unconditional.

**A pleasing decode:** the ladder's weight-16 cover witness is
deck-invariant on the nose — its 16 cells pair under y ↦ y+15 — so it
IS τ(u*) for a weight-8 base logical u* (extracted by fiber descent +
the lab→repo reflection). The tight-witness leg needed no new search.

**Naming note:** dir is `Z5Z15F2A6` (not `Z5Z15`) because 38d3c884 is a
second certified Z5xZ15 code (both axes) that would collide on a later
packaging.

### 6.3 Dangerous-sector discharge for f2a6f17e:y (2026-07-12) — partial;
### a new stratum found

Goal: turn `DangerousFloorNZ 16` (the (M)-half, so far a bare assumption)
into a proof. Scripts `a17_f2a6_dangerous_{census,rungs,windows,cutoff}.py`,
`a17_f2a6_nearkernel_recon.py`; data `data/a17/f2a6_dangerous_*.json`.

**Small-preimage classification + rung coverage: COMPLETE.** All light
boundaries (0 < |b| ≤ 14) with a support-≤4 preimage: 94 translation
classes, weights {6:1, 10:6, 12:33, 14:54} (no |b| = 8 — which dodges
the pair-rung bound's failure zone). Unlike pair72 (chosen for zero
seam-hostile classes), 60/94 classes have seam-hostile translates,
concentrated at y ∈ {13, 14} (the section-wrap zone). Full dispatch over
all 94 × 75 = 7,050 cells:
- **5,765 single-shape** (some ker-coset preimage seam-good);
- **1,170 pair-shape** (both parts seam-good; |U| bound holds — at
  |b| = 10 it is tight, 15 ≤ 15);
- **115 window cells** (|b| = 14, t = 1, all shape rungs fail): a NEW
  rung closes them — at t = 1 either an off-cell exists (≥ 16 directly)
  or the normalized descent lies in W = supp b ∪ seam(f₀), and "every
  cycle in W is a boundary" is a per-cell finite check. All 115 windows
  (|W| ∈ {14, 16}) PASS, verified two ways (rank identity + 2^|W|
  enumeration, 0 mismatches).

**Lean: the parametric rungs are SHIPPED** (`BBDoubling.lean`):
`dangerous_bound_of_{single,pair}_shape_of_logicalFloor` (the weak-floor
forms every d ≥ 7 instance needs — light residual cycle concluded to be
a *boundary*, not zero) and `dangerous_bound_of_window` (floor-free).
Build green; axiom-clean (standard three).

**The cutoff conjecture is FALSE — a near-kernel stratum exists.** The
completeness certificate ("every light b has a small preimage") came back
SAT in 0 s: there are |b| = 10 boundaries whose minimal preimage weighs
31–33. Structure: balanced simultaneous near-annihilation
(|A⋆f| = |B⋆f| ∈ {5, 6, 7}), far from BOTH single kernels (dist ≥ 31)
— not kernel-plus-perturbation. Sharpened by SAT: μ_Z = 6 globally
(UNSAT at |b| ≤ 4 over ALL preimages, 2 s), and the no-small-preimage
stratum STARTS at |b| = 10 (UNSAT at caps 4/6/8 with min-rep ≥ 5:
2 s / 25 s / 159 s — CaDiCaL scaling is ugly; caps 10–14 and the
min-rep gap [5, 30] are OPEN, CMS-native-XOR re-run recommended).
Consequence: no support-bounded census can complete the classification;
the light-boundary set of a d ≥ 7 base is genuinely two-strata. The
near-kernel stratum is a new research object (connects to the A16
radical-weight machinery and the deficit-wall's cancellation
phenomenology).

**Certificate leg (in flight):** the subsuming cover-side UNSAT@14 for
f2a6f17e:y relaunched solo (`a17_f2a6_cover_unsat_only.py`, CMS, 6 h
budget, log `run_f2a6_cover_unsat_only.log`) — the prior round-2 launch
died with its session, unnoticed (the CPU load mistaken for it was a
parallel fork's T4 w=5 sweep). On UNSAT: d_X(cover) = 16 exact and
`DangerousFloorNZ 16` becomes certificate-checked (still not
kernel-checked — the in-kernel route needs the near-kernel stratum
classified, plus a Lean sweep dispatching the three rungs over the
small-preimage stratum).

**Honest status of (M) for this instance:** assumption → certificate
(pending the CMS run) → kernel (open: near-kernel stratum + the [5, 30]
rep-gap + the ≤4-support Lean sweep, ~75³-scale with translation
reduction).

### 6.4 The near-kernel stratum CLASSIFIED — light boundaries of
### f2a6f17e are 113 classes, rung coverage 100% (2026-07-13)

Scripts `a17_f2a6_{spectral_recon,sigma_structure,athin_lines,light_enum,
full_dispatch,t3_exact}.py`; data `f2a6_light_classes.jsonl` (complete),
`f2a6_full_dispatch.json`.

**The algebraic identity of the stratum (all asserted exactly).** The
pair is secretly σ-correlated: **B = xy⁶·σ(A)** with σ:(x,y)↦(xy⁶,y⁴)
an ORDER-2 group automorphism, and σ(B) = x·A back. Consequences:
(i) light boundaries are pairs of A-images — |b| = |A⋆f| + |A⋆(σf)|
up to monomials — so the classification is about the σ-correlation of
the A-thin sets of the single trinomial 1+x+y; (ii) there is a
weight-preserving block-swapping involution Φ on translation classes of
im ∂₂ (verified), which explains the balanced near-kernel weights and
pairs the unbalanced small classes ((3,9)↔(9,3), (4,6)↔(6,4),
(5,9)↔(9,5)); (iii) Â and B̂ vanish on the SAME GF(16) component
(2-orbit of (1,14)), so ker MA = ker MB = ker ∂₂ and the transfer
T = B̂/Â is total off that component, with small orders {1,3,5,15};
(iv) the 5:1 quotient to Z₅×Z₃ kills σ and degenerates the pair
(B̄ = x̄Ā, a [[30,0]] code) — the stratum's step-3 y-progressions are
its fiber fingerprints. The A-thin layer alone is HUGE (4,375 weight-3
"A-lines" in 59 classes, 228,600 weight-4, ~1.0M weight-5 — matching
the random 4-check-code model): the σ-correlation is the entire filter,
and no support-side description can exist (the §6.3 refutation, now
explained).

**Exhaustive enumeration (solver-grade complete).** All weight-≤14
codewords of the [150,71,6] code im ∂₂, up to translation: SAT with
translation-orbit blocking, final UNSAT (the completeness certificate,
DRAT-able on the blocked CNF) took 9.6 h. **113 classes**: the 94
small-preimage classes of §6.3 reproduced EXACTLY (weights
{6:1, 10:6, 12:33, 14:54}) + **19 near-kernel classes** (1× |b|=10
(5|5), 3× |b|=12 (6|6), 15× |b|=14 (7|7); preimage-coset minima 31–33).
The coset-min spectrum over all 113 is strictly bimodal
{1,2,3} ∪ {31,32,33} — **the [5,30] rep gap is EMPTY, closed as a
byproduct**. Cross-checks: Φ-closure holds (29 Φ-fixed + 42 Φ-pairs,
0 missing partners) — an independent exhaustiveness check.

**Unified rung dispatch: 8,475/8,475 light cells covered, 0 uncovered.**
Priorities S → P (pool-based pieces) → W/W+:

| route | cells | Lean status |
|---|---|---|
| single-shape S | 5,765 | shipped (`_of_logicalFloor`) |
| pair-shape P | 1,170 | shipped (`_of_logicalFloor`) |
| window W (t=1) | 1,205 | shipped (`dangerous_bound_of_window`) |
| gen. window W+ (t=2, exact) | 260 | rung generalization pending |
| gen. window W+ (t=3, exact) | 75 | rung generalization pending |

The near-kernel classes are exactly the shape-rung-hostile ones (heavy
preimages ⟹ no seam-good coset element): |b|=14 ones fall to the
shipped t=1 window; |b|=12 (t=2) need the generalized window (off ≤ 1
⟹ descent in W ∪ {one extra cell}; verified for ALL single-cell
extensions — the exact t=2 condition); the single |b|=10 class (t=3)
verified for ALL ≤2-cell extensions (`a17_f2a6_t3_exact.py`, 447 s —
the exact t=3 condition; every window condition in the dispatch is now
exact, none probe-grade). CORRECTION to §6.3: of its "115 window
cells", 80 were t=1 and 35 were actually |b|=12/t=2 — the old window
check verified those only in the (insufficient) t=1 sense; the new
dispatch verifies the exact t=2 condition and they pass.

**(M) certificate restructured — the cover-side query is no longer
needed.** The 6h CMS cover-UNSAT@14 TIMED OUT (UNKNOWN, honest); but
the discharge now decomposes base-side: [113-class enumeration
completeness, n=75-frame UNSAT, DRAT-able] + [per-cell rung checks,
numerically verified today, kernel-upgradeable] + [Lean rung theorems,
axiom-clean, shipped] ⟹ DangerousFloorNZ 16. Remaining for the full
kernel route: the generalized-window rung in Lean (t ≥ 2 — mechanical
extension of the t=1 proof), the per-class Lean check tables, and the
dispatch sweep; the completeness certificate stays solver-grade (2⁷⁵
statement).

## 7. Success criteria

- **Primary:** one (code, axis) with S4-certified SF ≥ 2·d(base) ≥ 14,
  LRAT-checked, Lean-packaged double.
- **Honorable negative:** corpus d ≥ 7 exhausted with certificates and
  the wall confirmed at 2d − 2 across three distance strata → the
  deficit wall graduates from observation to a well-posed OQ with a
  serious dataset; publishable per the two-sided/A14 precedent.
