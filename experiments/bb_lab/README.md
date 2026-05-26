# bb-lab — Bivariate-Bicycle code laboratory

Python substrate for the QEC moonshot pipeline. Computes properties of
bivariate-bicycle (BB) quantum LDPC codes outside Lean, so that conjecture
search can happen before formalization.

## Status

**v0 — substrate validation: PASSING.**

- All 5 published Bravyi-table `(n, k)` values reproduce exactly.
- 4 of 5 Bravyi distances confirmed exact with **drat-trim-verified
  DRAT proofs**:
  - `[[72,12,6]]`     d=6   ← committed proof bundle (~850 KB)
  - `[[90,8,10]]`     d=10  ← regenerable (~90 MB)
  - `[[108,8,10]]`    d=10  ← regenerable (~55 MB)
  - `[[144,12,12]]` gross  d=12  ← regenerable (~525 MB)
- `[[288,12,18]]` heroic SAT runs unattended in the background; growth
  per weight ≈ 3-4×, total ETA on the order of days — not on the CI
  path. (This is the only Bravyi-table instance without a verified
  proof bundle yet.)
- Lean handshake round-trips: `pipeline/attempts/gross/state.yaml →
  descriptor → JSON → emitted .lean → compile under lake env lean`.

**v1-track (b) — DRAT proofs verified end-to-end (working).**

- `cadical` CLI subprocess emits per-UNSAT-weight DRAT proofs reliably
  (the pysat-bundled CaDiCaL has an stdio buffer bug that truncates
  mid-sized proofs; we shell out instead).
- Each proof is independently **VERIFIED by `drat-trim`** in the CI test
  suite. The UNSAT direction of every distance bound is no longer just
  "the solver said so" — it's accepted by a separate verifier.
- Each proof is paired with its DIMACS CNF and SHA256-hashed in the
  certificate JSON — anyone with `cadical` + `drat-trim` can regenerate
  and verify.
- Committed evidence: `certificates/bb_72_12_6/` (5 DRAT/CNF pairs,
  ~850 KB). Larger instances are gitignored but regenerable via
  `bb-lab bravyi-check --emit-proofs`.
- Remaining: a Lean-side LRAT consumer (`drat-trim -L` converts our
  DRAT to LRAT, then a verified LRAT checker in Lean 4 — Mario
  Carneiro's `lrat-check` is the model — would close the loop into
  the kernel).

## Quick start

```bash
cd experiments/bb_lab
uv sync --extra dev
uv run pytest                                # the v0+ CI gate (82 tests, ~40 s; slow tests deselected)
uv run pytest -m slow                        # only the heroic SAT tests (gross ~2 min, bb_288 days)
uv run pytest -o addopts=''                  # everything including slow
uv run bb-lab bravyi-check --quick           # 3 small SAT distances
uv run bb-lab bravyi-check --quick --emit-proofs   # +DRAT proofs
uv run bb-lab bravyi-check --full --emit-proofs    # n=144 (~2 min), n=288 (days)
uv run bb-lab verify-cert certificates/bb_72_12_6.cert.json   # full re-check

# Build drat-trim once (used by the verify-cert test):
( cd /tmp && git clone --depth 1 https://github.com/marijnheule/drat-trim.git \
  && cd drat-trim && cc -O2 -o drat-trim drat-trim.c )
```

## Module layout

| Path | Purpose |
| --- | --- |
| `src/bb_lab/group.py` | Finite abelian group `ZMod ℓ × ZMod m` arithmetic |
| `src/bb_lab/poly.py` | F₂-polynomial parsing (`'x^3 + y + y^2'`) and canonicalization |
| `src/bb_lab/checks.py` | `H_X`, `H_Z` construction. **Single source of truth vs the Lean `conv` definition.** |
| `src/bb_lab/linalg.py` | Dense F₂ rank, nullspace, quotient-complement |
| `src/bb_lab/codeparams.py` | `n`, `k` from check matrices |
| `src/bb_lab/sat_distance.py` | Exact distance via SAT; dual backend (pysat fast / cadical CLI for proofs) |
| `src/bb_lab/certificate.py` | JSON witness + DRAT-reference certificate format `bb-cert/v1` |
| `src/bb_lab/lean_bridge.py` | `state.yaml` ↔ JSON ↔ `BBChainComplex.lean` skeleton |
| `src/bb_lab/store.py` | DuckDB schema (for v1 corpus) |
| `src/bb_lab/cli.py` | `bb-lab` entry points |
| `instances/bravyi_table.yaml` | Regression contract for the five published BB codes |
| `certificates/<code_id>.cert.json` | Per-instance witness + DRAT-hash certificate |
| `certificates/<code_id>/` | DRAT + CNF proof bundle (committed for bb_72_12_6 only) |

## The Lean handshake

The Lab agrees with `QEC/Stabilizer/Framework/Homological/BBChainComplex.lean`
on the convolution convention:

> `conv A f g = ∑_h A(h) · f(g − h)` over F₂[G]

which means the check matrix is `H_X[g, h] = A(g − h)` for the X-block and
`B(g − h)` for the Z-block. **If a future change makes `bb_lab` and the
Lean side disagree on this, `tests/test_gross_agreement.py` is the
canary.**

The full bridge: `pipeline/attempts/<id>/state.yaml` (polynomial strings) →
`bb_lab.lean_bridge.descriptor_from_state_yaml` → JSON
(`schema_version: bb-instance/v1`) → `emit_skeleton` → compilable
Lean file importing `BBChainComplex`. See `tests/test_lean_roundtrip.py`
for the round-trip property test (compiles the emitted file under
`lake env lean`).

## CI gate

```
pytest experiments/bb_lab/tests/
```

passes iff all four suites are green:

1. `test_gross_agreement` — Lab `H_X` for gross matches the Lean truth
   bitwise.
2. `test_bravyi_quick` — `(n, k)` matches the published table for all
   five instances.
3. `test_bravyi_sat` — SAT distance matches `{6, 10, 10}` for the three
   smallest instances.
4. `test_lean_roundtrip` — `gross` state.yaml → Lab → emitted `.lean`
   compiles cleanly under `lake env lean`.
5. `test_drat_emission` — `cadical` CLI subprocess emits well-formed
   DRAT + CNF pairs; certificate JSON records SHA256-stable references;
   **`drat-trim` independently verifies every proof** (skipped if the
   `drat-trim` binary is missing).
6. `test_verify_cert` — the committed `bb_72_12_6.cert.json` re-verifies
   end-to-end: matrix hashes match the rederived (G, A, B), witness
   passes the three-condition logical check, and every committed DRAT
   proof passes `drat-trim`. This is the v1-track (b) soundness gate.

The `bb-lab bravyi-check --full` heroic runs (n=144 and n=288 SAT
distances) are **not in CI**; they're run manually before v0 is declared
fully passing.

## Where (b) is heading

The DRAT proof files are the v1 hand-off. The next step on track (b)
is plumbing a Lean-side LRAT consumer:

- Read `certificates/<code_id>.cert.json` — get `n`, `direction`,
  `witness_support`, `h_check_sha256`, `l_logical_sha256`,
  `unsat_proofs: [{weight_bound, drat_path, cnf_path, sha256s}]`.
- Reconstruct `H_check` and `L_logical` from the same `(G, A, B)` Lean
  already has (`bbChainComplex`). Hashes match → the certificate is
  about *our* code, not someone else's.
- For each `UnsatProofRef`: convert DRAT→LRAT with `drat-trim -L`,
  then run an in-kernel LRAT verifier (Carneiro-style), conclude no
  logical of weight ≤ `weight_bound` exists.
- Combine with the witness model (in the certificate) for the SAT
  direction at weight `distance`. Together: a Lean-checked proof of
  exact distance.

Mario Carneiro's [LRAT-check project](https://github.com/digama0/mm0)
contains a verified LRAT checker for MM0; porting it to Lean 4 is the
remaining significant piece. Once landed, the gross-`[[144,12,12]]`
distance is the first qLDPC distance bound mechanically verified end-to-end
inside Lean — a result Lean-QEC ([arXiv:2605.16523](https://arxiv.org/abs/2605.16523))
explicitly did not reach.
