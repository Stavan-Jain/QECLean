# Formalization pipeline (architecture)

A catalog-driven pipeline for prioritizing and formalizing quantum
error-correcting codes in this repo. Source-of-truth: the
[Error Correction Zoo](https://errorcorrectionzoo.org/). Heavy automation
via Claude Code; tight human review at the high-leverage gates.

> **Looking for "how do I use this"?** See `docs/pipeline-usage.md` for
> task-oriented recipes (weekly triage, starting a code, reviewing a
> skeleton, running Stage 4, opening PRs, refreshing the catalog,
> initializing a moonshot). This file is the architectural reference.

## State after Stage-0 bootstrap

| Artifact | Path | Generator | Status |
|---|---|---|---|
| Pinned EC Zoo snapshot | `pipeline/cache/eczoo_data/` (gitignored) | `pipeline/cache/PIN.md` | populated |
| Structured catalog | `catalog/zoo.yaml` (267 codes) | `scripts/ingest_zoo.py` | populated |
| Per-code priority scores | `catalog/scoring.yaml` | `.claude/agents/qec-prioritizer.md` | populated |
| Top-of-queue summary | `pipeline/queue.md` | same agent | populated |
| Active attempts | `pipeline/attempts/` | (one dir per code, hand-spawned) | empty |
| Research log | `pipeline/research_log.md` | manual + agent | empty |

Current snapshot: **267 quantum stabilizer codes scored**, **6 already done**
(Shor9, Steane7, repetition, RSC, toric, Quantum Hamming), **71 engineering
candidates**, **3 moonshot candidates**, **14 deferred**, **173 skipped**.

## Architecture summary

```
                  ┌────────────────────┐
                  │  Error Correction  │
                  │      Zoo data      │   ←  pinned by SHA in PIN.md
                  └─────────┬──────────┘
                            │ scripts/ingest_zoo.py  (Stage 0)
                            ▼
                    catalog/zoo.yaml
                            │ .claude/agents/qec-prioritizer.md  (Stage 0/refresh)
                            ▼
              catalog/scoring.yaml + pipeline/queue.md
                            │ weekly triage (human, 30 min)
                            ▼
                  ┌─────────┴─────────┐
                  ▼                   ▼
          ENGINEERING TRACK    RESEARCH TRACK
            (known proofs)     (novel attempts)
                  │                   │
                  ▼                   ▼
        pipeline/attempts/<name>/   pipeline/attempts/<moonshot>/
                  │                   │
                  ▼                   ▼
              merged into QEC/   research_log entry
                  └───────┬──────────┘
                          ▼
                  update CLAUDE.md
                  + re-run prioritizer
```

Full architectural rationale lives in the conversation that produced this
pipeline; this file is the runbook.

## Refresh procedures

### Refresh the catalog (when eczoo_data updates)

```bash
# 1. Bump the snapshot
cd pipeline/cache
rm -rf eczoo_data
git clone --depth 1 https://github.com/errorcorrectionzoo/eczoo_data.git
cd eczoo_data && git rev-parse HEAD       # update PIN.md with this SHA

# 2. Regenerate the structured catalog
cd ../../..
python3 scripts/ingest_zoo.py
```

### Re-score (after a major repo milestone)

Whenever a new abstraction lands or a new code finishes, reuse and
prerequisite scores shift. Re-run the prioritizer:

```
Tell Claude:  "Re-run the qec-prioritizer agent against the current catalog
and repo state. Update catalog/scoring.yaml and pipeline/queue.md."
```

The agent reads `.claude/agents/qec-prioritizer.md` for its rubric. Tweak
weights in that file (and propagate to the formula in this doc) if the queue
stops matching intuition.

## Scoring rubric — quick reference

Six axes, each 0–10:

| Axis | High score means |
|---|---|
| `reuse` | Directly fits existing `Stabilizer/` + `HomologicalCode` infra |
| `canonicality` | In textbooks, syllabi, foundational |
| `hardware` | Used in real published demos, 2023–2026 |
| `tractability` | Known clean distance proof (homological / algebraic) — *not* SAT-only |
| `prerequisites` | No missing abstractions in this repo (10 = none missing) |
| `effort` | Cheap to formalize (10 = days; 0 = months) |

Composite formula:
```
0.25*reuse + 0.15*canonicality + 0.15*hardware + 0.15*tractability + 0.20*prerequisites + 0.10*effort
```

Tracks:
- **engineering**: composite ≥ 6.0, tractability ≥ 5, prerequisites ≥ 5
- **moonshot**: composite ≥ 5.0, canonicality + hardware ≥ 12, tractability ≤ 4
- **defer**: composite ≥ 5.0 but prerequisites < 5
- **skip**: composite < 4.0

## Weekly triage (you, ~30 min)

1. Open `pipeline/queue.md`.
2. For the top 3–5 engineering candidates and any moonshot candidate, decide
   `GO / DEFER / SKIP`.
3. For each `GO`, create the attempt directory:
   ```bash
   mkdir -p pipeline/attempts/<code-name>
   ```
   and ask Claude to spawn a skeleton-drafter agent (to be defined; see
   below).

## Stage 2 — skeleton drafter (implemented)

Agent: `.claude/agents/qec-skeleton-drafter.md`. Reads a code from the
catalog + scoring, fetches the original paper(s) via WebFetch, and produces
a complete formalization plan + Lean skeleton with structured `sorry`
markers. Does **not** attempt proofs.

### Invocation

Spawn with `subagent_type: "general-purpose"` (the project-scoped agent
definition is loaded by reference) and `isolation: "worktree"`:

```
Agent(
  description: "Skeleton: <code_id>",
  subagent_type: "general-purpose",
  isolation: "worktree",
  prompt: "<read .claude/agents/qec-skeleton-drafter.md; target = <code_id>>"
)
```

### Worktree → main sync

The agent runs in an isolated worktree, so all outputs (including
`pipeline/attempts/<code-name>/`) initially live there. After completion,
**copy the attempt-metadata directory back to main** so it's visible
during weekly triage:

```bash
cp -r .claude/worktrees/<branch>/pipeline/attempts/<code-name> \
      pipeline/attempts/
```

The Lean skeleton file stays in the worktree branch (`worktree-agent-<sha>`)
until Stage 5 merge. The `state.yaml` records the worktree branch name.

### What Stage 2 produces

For target `<code-name>`, each pass yields:

```
pipeline/attempts/<code-name>/
  state.yaml          # status, worktree branch, parameters
  informal_spec.md    # plain-English statement of every theorem (review target)
  plan.md             # proof strategy + dependency graph
  reuse_audit.md      # what existing repo APIs apply
  gap_audit.md        # missing abstractions in repo + mathlib

<worktree>/QEC/Stabilizer/Codes/<CodeName>.lean   # parses with sorry-markers
```

## Stage 3 — spec review (human)

For each `state: skeleton-review` attempt: open
`pipeline/attempts/<code-name>/informal_spec.md` and cross-check it against
the original paper. Approve, request changes, or reject. **The highest
value 15 minutes of human time** — catches wrong theorem statements before
proof effort is spent.

## Stage 4 — formalization loop (not yet implemented)

Subsequent stage, to be implemented once 2–3 Stage-3 reviews have settled
the skeleton patterns:

- Leverages existing `lean4:autoprove`, `lean4:sorry-filler-deep`,
  `lean4:proof-repair`, `lean4:proof-golfer` skills.
- Closes structured `TODO(<code-id>-T<n>)` sorries in the worktree branch.

## Moonshot track (implemented)

Agent: `.claude/agents/qec-moonshot.md`. Targets codes with no known
clean distance proof (`gross`, `honeycomb_floquet`, `kitaev_honeycomb`).

### Differences from engineering track

| Aspect | Engineering | Moonshot |
|---|---|---|
| Proof method | Known | To be discovered |
| Success criterion | All sorries closed | Tight bound OR documented obstacle |
| Number of attempts | 1 skeleton, 1 fill | Multiple approaches per moonshot |
| Per-approach budget | 8h | 12h (then re-evaluate) |
| Total budget | 8h | 80h across all approaches before forced re-evaluation |
| Refactoring `Core/`/`Homological/` | Forbidden | Allowed |
| Failure write-up | BLOCKED markers | Full `final_writeup.md` per approach |
| `research_log.md` entry | No | Always, regardless of outcome |
| Publishability | Internal artifact | Possible (success) or partial (negative result) |
| Sessions | Single-shot | Multi-session (resume via re-invocation) |

### Invocation

Stage-2' (hypothesis setup): first invocation creates `hypothesis.md`,
`budget.yaml`, `success_criterion.md`, `partial_value.md`, then **stops
and waits for human review** before any approach execution.

Stage-4' (approach execution): after hypothesis approval, the agent
iterates through the planned approaches with their per-approach budgets.

Stage-write-up: aggregates all approaches into `result.md`, appends to
`pipeline/research_log.md`, optionally seeds a paper draft.

### What a moonshot produces

```
pipeline/attempts/<moonshot>/
  state.yaml                    # track: moonshot
  hypothesis.md                 # reviewed in Stage 3'
  budget.yaml                   # per-approach + total caps
  success_criterion.md          # tight vs partial vs negative bars
  partial_value.md              # what's worth keeping even if main goal fails
  approaches/
    <approach-1>/
      plan.md
      attempt.lean              # in worktree
      daily_log.md
      obstacle_diary.md
      final_writeup.md          # mandatory
    <approach-2>/
      ...
  result.md                     # aggregated across all approaches
  research_log_entry.md         # one-paragraph for public log
  paper_draft_seed.md           # if a publishable result emerged
```

### Current moonshot candidates

Per `pipeline/queue.md`:
1. **`gross`** ([[144,12,12]] BB code) — most concrete starting point.
   Camion's multivariate BCH bound on abelian quantum codes is the
   strongest first-approach candidate; lifted-product bounds and
   polynomial-ideal Gröbner structure are alternative angles. See
   `.claude/agents/qec-moonshot.md` § "Specific guidance" for detailed
   approach-by-approach analysis.
2. **`honeycomb_floquet`** — gated on building a dynamic-code framework
   first. Defer.
3. **`kitaev_honeycomb`** — gated on subsystem-code framework. Defer.

## References

- [Error Correction Zoo](https://errorcorrectionzoo.org/)
- Source data repository: <https://github.com/errorcorrectionzoo/eczoo_data>
- Current pinned SHA: see `pipeline/cache/PIN.md`
