# Pipeline usage — operator's manual

This is the task-oriented companion to `docs/pipeline.md` (which is the
architectural overview). When you want to **do** something with the
pipeline, this is the file.

## Quick reference

| Stage | Who | Cadence | Wall-clock | Recipe |
|---|---|---|---|---|
| **1. Weekly triage** | You | Weekly | ~30 min | [#weekly-triage](#recipe-weekly-triage) |
| **2. Skeleton draft** | Claude (agent) | Per code | 5–20 min | [#start-engineering](#recipe-start-an-engineering-track-formalization) |
| **3. Spec review** | You | Per code | ~15 min | [#stage-3-review](#recipe-review-a-skeleton-stage-3) |
| **4. Formalization** | Claude (agent) | Per code | 1–8 h | [#stage-4](#recipe-run-stage-4-on-an-approved-skeleton) |
| **5. PR review + merge** | You | Per code | varies | [#stage-5-pr](#recipe-review-and-merge-a-pr-ready-formalization) |
| **6. Reflection** | Claude | Post-merge | ~5 min | [#stage-6](#recipe-post-merge-reflection) |
| **Catalog refresh** | You + Claude | When EC Zoo updates | ~30 min | [#refresh-catalog](#recipe-refresh-the-catalog) |
| **Re-scoring** | Claude (agent) | Monthly / per milestone | ~15 min | [#rescoring](#recipe-re-score-the-queue) |
| **Moonshot init** | Claude (agent) | Per moonshot | 30–90 min | [#moonshot-init](#recipe-initialize-a-moonshot) |
| **Moonshot approve + run** | You + Claude | Per approach | 12 h per approach | [#moonshot-run](#recipe-approve-and-run-a-moonshot) |
| **Moonshot write-up** | Claude | Per moonshot | ~30 min | [#moonshot-writeup](#recipe-write-up-a-finished-moonshot) |

The pipeline is designed so that **your total weekly bandwidth is ~3–5
hours**. Most of that is the weekly triage, Stage-3 spec reviews, and
Stage-5 PR reviews. Claude does the rest, including overnight.

## Pre-flight checks

Before doing anything else in a session, run:

```bash
cd /Users/stavanjain/Code/QuantumErrorCorrectionLean-fresh
git status                                 # nothing critical uncommitted?
ls catalog/ pipeline/                      # catalog + scoring present?
ls pipeline/attempts/ 2>/dev/null          # what's in flight?
git -C pipeline/cache/eczoo_data rev-parse HEAD 2>/dev/null  # snapshot pinned?
```

If anything looks off, jump to [#troubleshooting](#troubleshooting).

---

## Recipe: weekly triage

**Trigger:** Monday morning, or whenever you have 30 min and want to
queue work for the week.

**Prerequisites:**
- `catalog/scoring.yaml` exists (run the prioritizer first if not — see
  [#rescoring](#recipe-re-score-the-queue)).
- No more than 1–2 attempts already `formalization` status (don't overload
  yourself).

**Steps:**

1. **Open `pipeline/queue.md`.** Read the "Engineering track (top 20)" table
   and the "Moonshot track" table.

2. **For each candidate at the top of the queue you haven't already
   decided on**, mentally label it as one of:
   - `GO` — start a Stage-2 skeleton this session
   - `DEFER` — important but not now (track infra dependency)
   - `SKIP` — not worth pursuing
   - `MOONSHOT` — research track (different recipe — see
     [#moonshot-init](#recipe-initialize-a-moonshot))

3. **For each `GO`:** kick off [#start-engineering](#recipe-start-an-engineering-track-formalization)
   for that code. You can have multiple skeletons in flight simultaneously
   — they're in separate worktrees.

4. **Skim "Deferred" section** — if any deferred candidate's infra blocker
   has been resolved since the last triage, promote it to engineering and
   re-run [#rescoring](#recipe-re-score-the-queue).

5. **Check `pipeline/attempts/`** for any directory whose `state.yaml`
   shows `skeleton-review`. Each of those needs a Stage-3 review — jump to
   [#stage-3-review](#recipe-review-a-skeleton-stage-3).

6. **Check for any `pr-ready` directory** — each gets a Stage-5 PR.

**Expected outcome:** 1–3 new skeletons started, 0–2 Stage-3 reviews done,
0–2 PRs reviewed.

**Triage budget:** ~30 minutes. If you spend longer, you're probably
deliberating too long on `SKIP` candidates — when in doubt, defer.

---

## Recipe: start an engineering-track formalization

**Trigger:** You marked a candidate `GO` in triage.

**Prerequisites:**
- Target's `code_id` is in `catalog/scoring.yaml` with
  `proposed_track: engineering` and `status: not_started`.
- `pipeline/attempts/<code_id>/` does not already exist (would mean an
  attempt is already in flight — investigate first).

**Steps:**

1. **Spawn the skeleton-drafter agent** via the Agent tool:

   ```
   Agent({
     description: "Skeleton: <code_id>",
     subagent_type: "general-purpose",
     isolation: "worktree",
     prompt: "You are the QEC skeleton drafter. Operating spec in
              .claude/agents/qec-skeleton-drafter.md. Target: <code_id>.

              Mathlib symlink: [ ! -L .lake/packages ] && \
                diff lake-manifest.json ../../../lake-manifest.json && {
                  rm -rf .lake/packages
                  ln -s ../../../../.lake/packages .lake/packages
                }

              Catalog/scoring inputs at the absolute paths under the main
              repo. Reference template: QEC/Stabilizer/Codes/_TEMPLATE.lean.

              Produce: pipeline/attempts/<code_id>/{state.yaml,
              informal_spec.md, plan.md, reuse_audit.md, gap_audit.md}
              + QEC/Stabilizer/Codes/<CodeName>.lean that parses with sorries."
   })
   ```

   No `run_in_background: true` — skeleton drafting is fast (5–20 min) so
   foreground is fine. You'll get the worktree path in the agent's result.

2. **Sync the attempt-metadata back to main.** After the agent finishes:

   ```bash
   cp -r .claude/worktrees/<agent-branch>/pipeline/attempts/<code_id> \
         pipeline/attempts/
   ```

   The Lean skeleton stays in the worktree until Stage 5.

3. **Verify the skeleton parses:** the agent should have already done this,
   but spot-check:

   ```bash
   cd .claude/worktrees/<agent-branch>
   lake build QEC.Stabilizer.Codes.<CodeName>
   ```

   Should report "declaration uses sorry" warnings only — no errors.

4. **Update queue tracker.** The new attempt should appear in
   `pipeline/attempts/<code_id>/` with `state.yaml.status: skeleton-review`.

**Expected outcome:** A new worktree with a parsing Lean skeleton, plus
five metadata files in `pipeline/attempts/<code_id>/`. Status:
`skeleton-review`. Ready for Stage 3.

**What to do if it fails:**
- *Agent crashes mid-drafting:* check the agent's last output. If the
  Lean file isn't parsing, the agent should have flagged it — investigate
  the parse error directly. If everything else is complete, you can hand-
  patch the Lean file or re-spawn.
- *EC Zoo data missing:* run [#refresh-catalog](#recipe-refresh-the-catalog).
- *Worktree symlink broken:* see [#troubleshooting](#troubleshooting).

---

## Recipe: review a skeleton (Stage 3)

**Trigger:** A `pipeline/attempts/<code_id>/state.yaml` shows status
`skeleton-review`. This is **the highest-value 15 minutes** in the
pipeline — catching wrong theorem statements here saves weeks of wasted
proof effort downstream.

**Prerequisites:** The Stage-2 skeleton drafter has finished.

**Steps:**

1. **Open `pipeline/attempts/<code_id>/informal_spec.md`.** This is the
   primary review target.

2. **For each theorem statement (T1, T2, …, T_n) in the spec:**
   - Cross-check against the original paper (linked in the spec's
     "Originally introduced in" section). For canonical codes, check
     against the EC Zoo entry too.
   - Specifically verify:
     - **Parameters** (`n`, `k`, `d`) match the literature
     - **Stabilizer generators** match the paper (paste the paper's
       generator list next to the spec's and compare)
     - **Logical operators** match the paper's codeword convention
       (different papers sometimes use different conjugate bases; pick
       one and verify the spec is self-consistent)
     - **Distance claim** matches the paper

3. **Open `pipeline/attempts/<code_id>/plan.md`.** Verify the proof
   strategy seems reasonable. Look at the per-theorem dependency graph —
   does it suggest the proof should close cleanly?

4. **Skim `gap_audit.md`.** Are there flagged repo gaps that would block
   Stage 4? If yes, decide:
   - Block this attempt and unblock the gap first (separate engineering
     effort).
   - Accept BLOCKED markers for theorems that hit the gap, and proceed
     with whatever else can close.

5. **Decide and act:**
   - **APPROVE:** edit `state.yaml` to set `status: formalization` (or
     leave as `skeleton-review` — Stage 4 will transition it). Jump to
     [#stage-4](#recipe-run-stage-4-on-an-approved-skeleton).
   - **REQUEST_CHANGES:** add a `review_notes.md` to the attempt directory
     listing your concerns; spawn the skeleton-drafter again with the
     notes as input. Loops back to Stage 2.
   - **REJECT:** edit `state.yaml.status` to `rejected`, add `result.md`
     explaining why. The attempt is closed.

**Expected outcome:** A clear approve/reject decision in ~15 minutes.

**What to look for that suggests REJECT:**
- The agent couldn't find the original paper and the spec is based on EC
  Zoo description alone. (Risk: paper might disagree.)
- Logical-operator commutation table doesn't check (e.g., `X̄_1` and
  `Z̄_1` are claimed to anticommute but their symplectic inner product
  computes to 0).
- The proposed proof method requires infrastructure not in the gap_audit.

---

## Recipe: run Stage 4 on an approved skeleton

**Trigger:** A skeleton has been approved in Stage 3.

**Prerequisites:**
- `pipeline/attempts/<code_id>/state.yaml` has `status: skeleton-review`
  or `formalization`.
- The worktree from Stage 2 still exists.

**Steps:**

1. **Identify the worktree path.** From `state.yaml`, read
   `worktree_branch`. The path is typically
   `.claude/worktrees/<agent-...>/`. If you can't find it, see
   [#troubleshooting](#troubleshooting) → worktree lost.

2. **Spawn the formalization-runner agent.** Run in background since
   Stage 4 can take 1–8 hours:

   ```
   Agent({
     description: "Stage 4: <code_id>",
     subagent_type: "general-purpose",
     run_in_background: true,
     prompt: "You are the QEC formalization runner. Operating spec in
              .claude/agents/qec-formalization-runner.md. Target: <code_id>.

              Work inside the worktree at .claude/worktrees/<branch>/.
              Verify mathlib symlink. Commit Stage-2 skeleton as baseline
              before starting.

              Budget: 8h wall-clock. Per-sorry: 15min autoprove +
              25min sorry-filler-deep. Commit every 3 sorries.

              When done, write pipeline/attempts/<code_id>/result.md
              and print one-line summary."
   })
   ```

3. **Continue with other work** — the agent runs autonomously. You'll be
   notified when it completes.

4. **On completion notification:** the agent surfaces `result.md` and
   one of two end states:
   - `status: pr-ready` — all sorries closed; jump to
     [#stage-5-pr](#recipe-review-and-merge-a-pr-ready-formalization).
   - `status: formalization-blocked` — some sorries remain as
     `BLOCKED(...)`. Read `result.md`'s "Blocked sorries" section. Options:
     a. Accept the partial result and PR what's closed (write a follow-up
        attempt for the blocked sorries).
     b. Investigate the blocker yourself (often a missing repo helper).
     c. Re-spawn with hints in the prompt.

**Expected outcome:** Either a fully-closed Lean file ready for PR, or a
partially-closed file with structured BLOCKED markers + a detailed
`result.md`.

**What to do if it fails:**
- *Agent looped past budget:* the agent should have stopped on its own.
  Read `progress.md` to see where it got stuck.
- *Lake build broken:* the agent shouldn't merge state that breaks the
  build. If it did, spawn `lean4:proof-repair` on the worktree.
- *Cascading mathlib version issue:* see [#troubleshooting](#troubleshooting).

---

## Recipe: review and merge a `pr-ready` formalization

**Trigger:** A Stage-4 attempt has finished with `status: pr-ready`.

**Prerequisites:**
- All sorries closed (or zero BLOCKED).
- `lake build` clean in the worktree.

**Steps:**

1. **Read `pipeline/attempts/<code_id>/result.md`** end-to-end.
   Especially the "Patterns discovered" section — these may need to land
   in `CLAUDE.md`.

2. **Review the Lean file directly** in the worktree:

   ```bash
   cd .claude/worktrees/<branch>
   git log --oneline main..HEAD                  # commit history
   git diff main -- QEC/Stabilizer/Codes/<CodeName>.lean | less
   ```

   Look for:
   - Theorem statements match `informal_spec.md`
   - No `set_option linter.* false` suppressions
   - All linters clean (the worktree's `lake build` output should confirm)
   - No surprising changes to other files (the agent should have only
     touched `Codes/<CodeName>.lean` and the umbrella)

3. **Open the PR:**

   ```bash
   cd .claude/worktrees/<branch>
   git push -u origin <branch-name>

   gh pr create \
     --title "feat(<code-shortname>): formalize [[n,k,d]] <code-name>" \
     --body "$(cat <<'EOF'
   ## Summary
   <1-3 bullets from result.md>

   ## Code
   - New file: \`QEC/Stabilizer/Codes/<CodeName>.lean\` (<LoC> lines, N theorems)
   - Updated: \`QEC/Stabilizer/Codes.lean\` umbrella
   - Pipeline state: \`pipeline/attempts/<code_id>/\`

   ## Test plan
   - [ ] \`lake build QEC.Stabilizer.Codes.<CodeName>\` clean
   - [ ] No new linter warnings
   - [ ] Theorem statements match \`informal_spec.md\`

   See \`pipeline/attempts/<code_id>/result.md\` for full details.

   🤖 Pipeline: Stage 4 — qec-formalization-runner
   EOF
   )"
   ```

4. **Review on GitHub** as you would any PR.

5. **Merge** when satisfied. After merge, jump to
   [#stage-6](#recipe-post-merge-reflection).

**Expected outcome:** Merged PR adding the new code.

**What to do if it fails:**
- *PR build breaks on CI:* CI may run with a different mathlib cache than
  your local repo. Pull main into the branch and retry.
- *Reviewer (you) wants changes:* push to the same branch; the agent
  doesn't have to be re-spawned for small edits.

---

## Recipe: post-merge reflection (Stage 6)

**Trigger:** A PR just merged.

**Steps:**

1. **Promote patterns from `result.md`'s "Patterns discovered" section.**
   Use the tiered destination rule — most patterns are NOT CLAUDE.md
   material:

   - **`docs/lean-patterns.md`** (default destination): patterns
     specific to a code shape (CSS distance, non-CSS distance,
     parametric family, mechanical fixes). The vast majority of
     promoted patterns end up here.
   - **`docs/mathlib-version-quirks.md`**: mathlib API drift you worked
     around during the formalization (deprecations, renames, signature
     changes). Date the entry.
   - **`CLAUDE.md`** (highest bar): only patterns that either generalize
     across ≥ 2 different code shapes OR are pure codebase-wide
     policy/style. If you're tempted to add to CLAUDE.md, ask whether
     `lean-patterns.md` would be the better home — usually yes.
   - **Stay in `result.md`** (no promotion): one-off observations,
     patterns that haven't recurred yet, or notes too narrow to
     generalize.

   The rationale: CLAUDE.md is pulled by every agent on every
   invocation. Each line costs tokens forever. Keep it small and
   high-signal; let `docs/*.md` carry the long tail.

2. **Update `pipeline/attempts/<code_id>/state.yaml`** to `status: done`.
   Add `merged_at` and `merged_pr` fields.

3. **Re-run the prioritizer** if the merge added a new abstraction that
   shifts `reuse` scores — see [#rescoring](#recipe-re-score-the-queue).
   Typically only needed every 3–5 merges, not after every one.

4. **(Optional)** Delete the worktree:

   ```bash
   git worktree remove .claude/worktrees/<branch>
   git branch -d <branch-name>   # or -D if not merged
   ```

   Or leave it — the disk space is small and an in-place worktree is
   sometimes useful for follow-ups.

5. **(Periodic) Audit CLAUDE.md size.** Every ~5 merges, or when
   CLAUDE.md crosses ~500 lines, scan for entries that haven't been
   referenced in subsequent `result.md` files and consider moving them
   to `lean-patterns.md` or pruning. The point of the split is to keep
   CLAUDE.md sustainably small.

**Expected outcome:** Repo state updated; new patterns landed in the
appropriate tier; CLAUDE.md stayed small.

---

## Recipe: refresh the catalog

**Trigger:** EC Zoo has updated and you want to pick up new entries; or
you're suspicious that the catalog has gotten stale.

**Cadence:** Maybe quarterly. The catalog doesn't change that often.

**Steps:**

```bash
# 1. Bump the snapshot
cd pipeline/cache
rm -rf eczoo_data
git clone --depth 1 https://github.com/errorcorrectionzoo/eczoo_data.git
cd eczoo_data && git rev-parse HEAD              # note the new SHA

# 2. Update PIN.md
cd ../../..
# Edit pipeline/cache/PIN.md to record the new SHA + date

# 3. Regenerate the structured catalog
python3 scripts/ingest_zoo.py

# 4. Spot-check: any new entries we care about?
diff <(yq -r '.[].code_id' catalog/zoo.yaml | sort) \
     <(git -C pipeline/cache/eczoo_data show HEAD -- 'codes/quantum/*' | head)
```

After the ingest, re-score — see [#rescoring](#recipe-re-score-the-queue).

**Expected outcome:** Updated `catalog/zoo.yaml`, new PIN, queue ready for
re-scoring.

---

## Recipe: re-score the queue

**Trigger:**
- Catalog was just refreshed
- A major milestone landed (new abstraction, new code merged)
- You suspect the priority order has drifted from intuition
- You changed scoring weights in `.claude/agents/qec-prioritizer.md`

**Steps:**

1. **Spawn the prioritizer agent:**

   ```
   Agent({
     description: "Re-score QEC catalog",
     subagent_type: "general-purpose",
     prompt: "You are the QEC prioritizer. Operating spec in
              .claude/agents/qec-prioritizer.md. Re-score every entry in
              catalog/zoo.yaml against current repo state.

              Update catalog/scoring.yaml and pipeline/queue.md.
              Print one-line summary."
   })
   ```

2. **Apply manual audit corrections.** The prioritizer doesn't perfectly
   match parametric-family instances to existing formalizations. After
   it finishes, audit:

   ```bash
   python3 scripts/patch_scoring.py    # applies any pending corrections
   ```

   If new corrections are needed (e.g., a new parametric family was
   formalized this milestone), edit `scripts/patch_scoring.py` to add
   them.

3. **Skim the new `pipeline/queue.md`.** Does the top-5 match your taste?
   If not, edit the weights in `.claude/agents/qec-prioritizer.md` and
   re-run.

**Expected outcome:** Fresh `scoring.yaml` and `queue.md` reflecting
current repo state and any new catalog entries.

---

## Recipe: initialize a moonshot

**Trigger:** A moonshot-track candidate (per `pipeline/queue.md`) is the
right thing to work on; you want to scope its hypothesis before
committing approach-execution budget.

**Prerequisites:**
- Target has `proposed_track: moonshot` in `catalog/scoring.yaml`.
- `pipeline/attempts/<moonshot_name>/` does not exist.

**Steps:**

1. **Spawn the moonshot agent** for hypothesis setup only:

   ```
   Agent({
     description: "Moonshot <name>: hypothesis",
     subagent_type: "general-purpose",
     isolation: "worktree",
     run_in_background: true,
     prompt: "You are the QEC Moonshot Runner. Operating spec in
              .claude/agents/qec-moonshot.md. Target: <moonshot_name>.

              CRITICAL: this is a hypothesis-setup-only invocation.
              Do NOT start any approach execution. Stop after drafting
              hypothesis.md, budget.yaml, success_criterion.md,
              partial_value.md, literature_notes.md. Wait for human
              review (Stage 3') before proceeding.

              Mathlib symlink setup as usual.

              Literature dive: spend ~45 minutes on the prior art relevant
              to this moonshot. Key papers should be enumerated in the
              agent's spec under 'Specific guidance' for this target."
   })
   ```

2. **Continue with other work** — agent runs autonomously (30–90 min
   typically).

3. **On completion notification:** read the artifacts in
   `pipeline/attempts/<moonshot_name>/`. The hypothesis is the gate —
   jump to
   [#moonshot-run](#recipe-approve-and-run-a-moonshot).

**Expected outcome:** Five markdown files in
`pipeline/attempts/<moonshot_name>/` describing what would be attempted,
budget, success criteria, partial value, and the literature scan.

---

## Recipe: approve and run a moonshot

**Trigger:** A moonshot's hypothesis-setup phase finished. Status is
`hypothesis-pending`.

**Prerequisites:** Hypothesis is reviewable.

**Steps:**

1. **Read `pipeline/attempts/<moonshot>/hypothesis.md` carefully.** This
   is the analog of the Stage-3 spec review but for a research target.
   Focus on:
   - Is the stated approach concrete enough that I'd recognize success
     if I saw it?
   - Are the approaches genuinely distinct (not just relabeled
     variations)?
   - Does the partial-value section describe outcomes I'd actually want?
   - Are the budget caps reasonable for the difficulty level?

2. **Decide:**
   - **APPROVE_ALL:** edit `state.yaml.status` to `hypothesis-approved`.
   - **APPROVE_FIRST_ONLY:** narrow the approach list in `hypothesis.md`
     to just the first approach; agent will revisit between approaches.
   - **REFINE:** add a `review_notes.md`, re-spawn the moonshot agent
     for another hypothesis-setup pass.
   - **REJECT:** archive the attempt (`state.yaml.status: rejected`,
     write a brief `result.md`).

3. **For APPROVE_*:** spawn the moonshot agent for execution:

   ```
   Agent({
     description: "Moonshot <name>: approach <K>",
     subagent_type: "general-purpose",
     run_in_background: true,
     prompt: "You are the QEC Moonshot Runner. Operating spec in
              .claude/agents/qec-moonshot.md. Target: <moonshot_name>.
              Phase: stage-4-research.

              The hypothesis has been approved
              (state.yaml.status: hypothesis-approved). Begin executing
              the approaches in pipeline/attempts/<name>/hypothesis.md
              in order. Per-approach budget per budget.yaml.

              Work inside the existing worktree where the hypothesis
              was drafted. Continue committing on the same branch.

              After each approach, write final_writeup.md regardless
              of outcome. After all approaches (or success / budget),
              write result.md."
   })
   ```

4. **Continue with other work.** Approach execution is long (hours per
   approach, days for a full moonshot). You'll be notified on each
   substantive completion.

5. **Between approaches:** the agent may pause for human input if the
   `spec_doubt_threshold` from `budget.yaml` triggers (two consecutive
   approaches fail the same way). Surface this for re-evaluation rather
   than continuing.

**Expected outcome:** Eventually a `result.md` documenting whether the
moonshot succeeded, partially succeeded, or failed, plus per-approach
write-ups in `approaches/`.

---

## Recipe: write up a finished moonshot

**Trigger:** A moonshot completes (`success-tight`, `success-partial`, or
`negative-result`).

**Steps:**

1. **Read `pipeline/attempts/<moonshot>/result.md`** end-to-end.

2. **Append to `pipeline/research_log.md`** with the one-paragraph entry
   from `research_log_entry.md`. Format:

   ```
   - 2026-MM-DD — <moonshot> — <status> —
     <one-line summary>. [details](attempts/<moonshot>/result.md)
   ```

3. **If `success-tight` or `success-partial`:** open a PR like an
   engineering attempt — see [#stage-5-pr](#recipe-review-and-merge-a-pr-ready-formalization).
   The PR should reference both `result.md` and any new abstractions
   added in `Core/` or `Homological/`.

4. **If `negative-result`:** the result is still valuable, but no PR is
   needed — the research_log entry suffices. Optionally write a short
   technical note in `docs/` if the negative result has broader
   implications.

5. **If `paper_draft_seed.md` exists:** decide whether to develop it into
   a workshop / journal submission. This is your call as research lead.

6. **Update CLAUDE.md** with any new idioms or patterns discovered.

**Expected outcome:** Research log updated; if applicable, PR open with
new repo additions.

---

## Troubleshooting

### Worktree symlink to `.lake/packages` is broken

```bash
cd .claude/worktrees/<branch>
diff lake-manifest.json ../../../lake-manifest.json   # must succeed
rm -rf .lake/packages
ln -s ../../../../.lake/packages .lake/packages
ls -la .lake/packages       # confirm symlink
lake build <one-small-module>   # smoke test
```

If `diff` fails (worktree has a different mathlib pin), do **not**
symlink — that would silently mix mathlib versions. Either:
- Reset the worktree's mathlib pin to match main:
  `git checkout main -- lake-manifest.json lakefile.toml lean-toolchain`
- Or run `lake exe cache get` (requires user approval per CLAUDE.md).

### Worktree lost (deleted or unfindable)

If a worktree was deleted but its branch still exists:
```bash
git worktree list                          # check known worktrees
git branch -a | grep <agent-id>            # find the branch
git worktree add .claude/worktrees/<new-name> <branch>
```

If the branch was also deleted: the work is lost. Re-spawn the relevant
Stage-2 or Stage-4 agent.

### LSP / `lake build` hangs

```bash
bash scripts/prune-stale-ileans.sh
```

If still hanging, no other `lake` process should be running. Check:
```bash
ps aux | grep lake
```

### Agent loops past budget

The agent should have explicit stop criteria. If it didn't honor them,
edit its operating spec in `.claude/agents/<agent-name>.md` to add a
firmer cap. Then surface the looping incident — it's a bug in the agent
prompt.

### Catalog parse failure

```bash
python3 scripts/ingest_zoo.py    # re-run; will report parse failures
```

If specific YAMLs fail, inspect them directly — they may be temporarily
malformed in the EC Zoo snapshot.

### Prioritizer's queue doesn't match intuition

The weights in `.claude/agents/qec-prioritizer.md` may need tuning.
Tweak them and re-run [#rescoring](#recipe-re-score-the-queue). If
specific entries are mis-classified by parametric-family overlap, add a
correction to `scripts/patch_scoring.py`.

### Stage-4 agent says "no progress" repeatedly

Three causes, in order of likelihood:
1. **Spec is wrong** (logical-operator basis doesn't match the paper).
   Re-do Stage 3 review.
2. **Mathlib gap** that's harder than the agent's budget. Mark BLOCKED
   and surface for separate engineering effort.
3. **Agent prompt is missing tactical hints.** Check the `plan.md`'s
   per-theorem strategy — sometimes augmenting the prompt with explicit
   lemma names unblocks.

### Moonshot agent declares partial success without compiling Lean

Per the moonshot agent spec: "Lean compilation is evidence; 'I think
this works' is not." If `result.md` claims success without commits
showing the compiling proof, treat as `negative-result` until verified.

---

## See also

- `docs/pipeline.md` — architectural overview, scoring rubric, stage
  diagrams
- `CLAUDE.md` — project-wide naming/tactic/linter conventions
- `.claude/agents/qec-prioritizer.md` — Stage-0 scoring agent
- `.claude/agents/qec-skeleton-drafter.md` — Stage-2 agent
- `.claude/agents/qec-formalization-runner.md` — Stage-4 agent
- `.claude/agents/qec-moonshot.md` — research-track agent
- `QEC/Stabilizer/Codes/_TEMPLATE.lean` — canonical CSS code structure
