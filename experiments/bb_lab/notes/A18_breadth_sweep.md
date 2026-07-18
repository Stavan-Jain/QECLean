# A18 — corpus breadth sweep (2026-07-07)

Goal: widen the `bb_instances.duckdb` corpus across **group-shape
variety** and **slightly-higher-distance codes** while staying
SAT-tractable. Time-boxed session (~5h wall).

## Starting state

16,867 rows, 19 group labels (≈15 isomorphism classes), 100%
weight-3×weight-3, heavily skewed: 12,488 rows are a single
`Z9xZ6` (n=108) block with no `d_exact`. Distance-filled rows: 4,364
(d≤8: 4,153; d=10: 203; d=12: 8). Every group in the corpus had
3 | |G|.

## The μ_e barrenness criterion (new, load-bearing)

For weight-3 × weight-3 BB codes, `k > 0` requires a common character
zero of A and B. A trinomial character value is `1 + u + v` with
`u, v ∈ μ_e` (e = exponent of the odd part of G, or a divisor), so
`k > 0` instances exist iff

    gcd(x^e + 1, (x+1)^e + 1)  over F₂  has degree > 0

for some admissible e. Computed table (deg gcd):

| e | 3 | 5 | 7 | 9 | 11 | 13 | 15 | 17 | 19 | 21 | 23 | 25 | 27 | 33 | 35 | 39 | 45 | 49 | 63 | 77 | 81 |
|---|---|---|---|---|----|----|----|----|----|----|----|----|----|----|----|----|----|----|----|----|----|
| deg | 2 | 0 | 6 | 2 | 0 | 0 | 14 | 0 | 0 | 8 | 0 | 0 | 2 | 2 | 6 | 2 | 14 | 6 | 62 | 6 | 2 |

- **Barren odd parts** (weight-3 k=0 always): exponent ∈ {5, 11, 13,
  17, 19, 23, 25} with no other odd prime — e.g. Z4xZ5, Z5xZ5, Z5xZ8,
  Z4xZ10, Z10xZ10, Z4xZ11 all yield zero codes. Empirically confirmed
  for Z4xZ5 and Z5xZ5 (exhaustive: 0 canonical k≥2 instances).
- **Pure 2-groups are barren** for any odd weight: odd-weight
  polynomials are units in the local ring F₂[G] (confirmed
  exhaustively on Z4xZ4: 0 instances).
- **Maximally rich**: e = 2^d − 1 (3, 7, 15, 63) where μ_e = F_{2^d}^×;
  e = 63 has 62 solutions — Z7xZ9 (cyclic Z63, n=126) is the richest
  new shape, and μ7-parts (Z7, Z49, Z77) are the main richness axis
  beyond the corpus's ubiquitous μ3.
- μ9 ⊋ μ3 and μ27, μ81 add **nothing** beyond μ3 (deg stays 2);
  μ49 adds nothing beyond μ7 (deg stays 6).

## Tier E — exhaustive enumeration (new groups, |G| ≤ 48)

`bb-lab enumerate --workers 8`, canonical (Aut × translation × swap)
dedup, k ≥ 2. New isomorphism classes only (checked against existing
corpus labels; e.g. Z5xZ9 = cyclic Z45 is NOT the corpus's
Z15xZ3 ≅ Z3²×Z5).

Groups: Z3xZ7 (Z21), Z3xZ8 (Z24), Z3xZ9, Z4xZ7 (Z28), Z5xZ7 (Z35),
Z3xZ12 (Z3²×Z4), Z4xZ9 (Z36), Z3xZ13 (Z39), Z6xZ7 (Z42), Z5xZ9 (Z45),
Z4xZ12 (Z4²×Z3). Confirmed-barren probes: Z4xZ4, Z4xZ5, Z5xZ5 (0 rows).

## Tier S — sampled enumeration (hunt zone, n = 112…200)

New script `scripts/a18_sample_enum.py`: uniform random weight-3
pairs, k≥2 filter first, then the same `canonical_bits` walk and
`instance_id` scheme as `bb-lab enumerate`; `code_id` prefix
**`bb_samp_`** marks non-exhaustive provenance. Groups (all new iso
classes; Z12xZ6 = the gross group, previously 18 rows):

Z7xZ9 (n=126), Z12xZ6 (144), Z7xZ8 (112), Z6xZ10 (120), Z5xZ12 (120),
Z7xZ12 (168), Z6xZ14 (168), Z7xZ11 (154), Z8xZ9 (144), Z6xZ13 (156),
Z7xZ7 (98), Z9xZ9 (162).

## Distance filling

- `scripts/a18_fill_ubs.py` — parallel L1-sampling `d_ub`
  (hunt zone first, 60k samples).
- `scripts/a18_sat_fill.py` — SAT exact `d` with per-row watchdog
  timeout + global time box; pass 1 breadth-first over new n≤100 rows,
  pass 2 = hunt (n∈[104,200], `d_ub ≥ 10`, cheapest-first).

## Results

Corpus: **16,867 → 58,021 rows**, **19 → 41 group labels**, exact
distances **4,364 → 13,886** (+9,522 SAT-certified, 0 errors).

- Tier E: 11 new groups exhaustively enumerated (+32,004 rows), the
  largest being Z6xZ7 (12,200 codes) and the costliest Z4xZ12
  (1,472 codes, 115 min — |Aut| = 192 makes canonical dedup ~18×
  pricier per candidate than cyclic shapes; budget by |Aut|·|G|, not
  by pair count).
- Tier S: 12 hunt-zone groups sampled to target (+9,150 rows, 18 min,
  every group hit its quota).
- d histogram of new exact values: d=2: 920, d=4: 3,190, d=6: 3,217,
  d=8: 2,168, **d=10: 483, d=12: 44**.
- **d=12 hosts, both new shapes**: `[[96,4,12]]` on Z4xZ12
  (exhaustive provenance, e.g. A = y + y² + x, B = 1 + x·y² + x·y⁴)
  and `[[98,6,12]]` on Z7xZ7 (sampled; matches the known 2BGA
  [[98,6,12]] parameter point). Corpus d=12 population: 8 → 52.
- Other notable strata: `[[78,4,10]]` on Z3xZ13 (184 d≥10 rows —
  d=10 at 12 fewer qubits than Bravyi's [[90,8,10]]) and
  `[[112,6,10]]` on Z7xZ8 (119 rows).

**Remaining frontier** (deliberately unspent): 40 pass-2 timeouts at
n = 96/112 with d_ub 12–18 (retry at 900–1200 s — cheapest shot at a
first d=14), and the n = 120–168 hunt zone: 7,489 rows with
d_ub ≥ 10, of which 6,450 have d_ub ≥ 14. The legacy Z9xZ6 block
(12,488 rows) stays distance-less by choice — one shape, low
breadth value.

## Operational notes

- Machine was contended: six niced `cryptominisat5` shards (A15 cover
  ladder, another session) at ~98% CPU each until ~11:45.
- **Disk-full incident**: the volume hit 0 bytes free mid-run (killed
  the first Tier-E chain inside Z3xZ12's shard-pickle writes; DuckDB
  unharmed — bulk insert is transactional and happens after
  enumeration). ~90GB of the Data volume is root-only-readable and
  du-invisible (likely `/var/db/diagnostics` unified-log flood from
  days of solver subprocess churn); no local APFS snapshots; no
  passwordless sudo, so it could not be cleaned from this session.
  All later phases run behind a ≥250MB free-space guard.
- **Two unattended-run deaths**, same root cause class: (1) machine
  slept mid-pipeline (fix: wrap the driver in `caffeinate -ims`);
  (2) a side DB + driver scripts staged in `/private/tmp` were lost
  to the 3-day tmp purge / reboot before their merge ran. Rule:
  long-running pipeline state (side DBs, driver scripts, logs)
  goes on durable storage (`data/a18_run/`, gitignored), never
  `/tmp`; and any deferred merge step should be part of the same
  driver script, not a separate manually-triggered action.
- SAT throughput at n ≤ 100 (8 workers, M-series, uncontended):
  ~2.8 solves/s average; the 60 s per-row timeout loses only 0.8%
  of rows. Hunt-zone (n 96–112, d ≈ 10–12) rows average ~90 s each
  at 300 s timeout.
