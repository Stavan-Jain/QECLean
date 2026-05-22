# Pipeline

Working state for the QEC-code formalization pipeline. See `docs/pipeline.md`
for the full architecture.

## Files

- `queue.md` — human-readable top-N priority list with proposed track
  (engineering / moonshot) per candidate. Read this to decide what to work on.
- `attempts/<code-name>/` — one directory per in-flight or completed
  formalization attempt. Contains:
  - `state.yaml` — current status, track, started_at, owner
  - `plan.md` — formalization strategy
  - `informal_spec.md` — plain-English statement of every theorem to prove,
    cross-referenced to the original paper
  - `progress.md` — running log
  - `result.md` — final write-up (success / partial / failed)
- `research_log.md` — index of all moonshot attempts, including failures.
  Failures are first-class outputs and document what didn't work + why.
- `cache/` — pinned eczoo_data snapshot (gitignored; reproducible from
  SHA in `cache/PIN.md`).
