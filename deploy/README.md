# Hosted tutorial environments

Two ways for QCE26 attendees to run QECLean without installing anything.
Both build the `QECTutorial` target rather than the default one — see
[`QECTutorial.lean`](../QECTutorial.lean) for why (short version: the
bivariate-bicycle safe-floor leaves peak around 3.75 GB each under
`native_decide`, and CI only survives them by adding 12 GB of swap).

| | Codespaces | lean4web |
|---|---|---|
| Attendee needs | a GitHub account | nothing |
| Startup | seconds with a prebuild, ~15–40 min without | instant |
| Editor | full VS Code + InfoView | single-file web editor |
| Runs on | GitHub's machines, billed to each attendee | one box you rent |
| Fails if | GitHub logins are slow on conference wifi | the box is undersized |

Recommendation: Codespaces as the primary path, lean4web as the walk-up
fallback for anyone without a GitHub account.

---

## Route A — GitHub Codespaces

Everything needed is in [`.devcontainer/`](../.devcontainer). Attendees open:

```
https://codespaces.new/Stavan-Jain/QECLean
```

`setup.sh` installs the pinned toolchain, runs `lake exe cache get` for
mathlib's prebuilt oleans, and builds `QECTutorial`.

### Turn on prebuilds before the tutorial

This is the difference between attendees waiting ~15–40 minutes and being
ready in seconds, and it is the single most important thing to do in advance.
Prebuilds are configured in the GitHub UI, not in a file:

**Settings → Codespaces → Set up prebuild**, with:
- Branch: `main`
- Configuration file: `.devcontainer/devcontainer.json`
- Trigger: *On push* (or a schedule if pushes are frequent)
- Region: whichever is nearest Toronto — `East US` is the usual pick
- Machine type: 4-core, matching `hostRequirements`

Prebuild storage bills to the repo owner. Delete the prebuild after the
conference.

### Cost

Compute bills to each attendee's own account, not yours — GitHub's free tier
covers 60 core-hours/month, so a 4-core Codespace for a half-day session is
comfortably inside it for most people. Confirm current quotas before the
session; GitHub has changed them before.

---

## Route B — self-hosted lean4web

[`install.sh`](lean4web/install.sh) provisions a fresh **Ubuntu 22.04** box
(the only OS lean4web claims to support):

```bash
DOMAIN=lean.example.org ./install.sh
```

It installs Node, elan, and bubblewrap; clones lean4web; clones QECLean into
`Projects/QEC` (the folder name must be exactly `QEC`, since lean4web requires
the folder and its root `.lean` file to match); copies in
[`leanweb-config.json`](lean4web/leanweb-config.json) and
[`leanweb-build.sh`](lean4web/leanweb-build.sh); and runs `npm run build`.

Then:

```bash
cd ~/lean4web && npx pm2 start ecosystem.config.cjs
```

Attendees land straight on QECLean, since `leanweb-config.json` sets
`"default": true`. It is also reachable explicitly at `#project=QEC`.

### Sizing — measure this, do not trust the table

Each concurrent user gets their own Lean server process, and a mathlib-scale
project is not cheap per session. **These are estimates, not measurements:**

| Concurrent users | Rough RAM | Notes |
|---|---|---|
| ~10 | 16 GB | comfortable |
| ~25 | 32 GB | realistic for a half-day tutorial |
| ~50 | 64 GB+ | ask whether Codespaces is the better answer |

Disk: budget 25–30 GB for mathlib's oleans plus the toolchain.

Get a real number before committing to a box — open the editor, type an
`example`, and watch one session:

```bash
ps -o rss=,comm= -C lean | sort -rn | head
```

Multiply the steady-state RSS by your expected concurrency and add headroom.
lean4web's own README notes that larger projects are considered out of scope,
so treat a full room as something to load-test, not assume.

### Before the day

- Rehearse a cold start on the real box, not just locally.
- Load-test with more concurrent sessions than you expect attendees.
- Have the Codespaces link ready as a fallback if the box struggles.
- lean4web runs Lean under bubblewrap by default. Do not set `NO_BWRAP=true`
  on a public instance — that runs attendee-supplied code uncontained.
- Depending on where the box lives, GDPR may require you to fill in
  `serverCountry` and `contactDetails` in `client/config/config.tsx`.

### Teardown

The instance is only needed for the session. Snapshot or destroy the box
afterwards rather than leaving an unattended public Lean server running.
