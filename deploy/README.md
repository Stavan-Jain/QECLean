# Hosted environments

Two ways to run QECLean without installing anything locally.

Both build [`QECLight`](../QECLight.lean) rather than the default target: the
bivariate-bicycle safe-floor leaves peak around 3.75 GB each under
`native_decide`, and CI only survives them by adding 12 GB of swap. Neither a
4-core container nor a shared server can. Everything else in the library is
available.

| | Codespaces | lean4web |
|---|---|---|
| User needs | a GitHub account | nothing |
| Startup | seconds with a prebuild, ~15–40 min without | instant |
| Editor | full VS Code + InfoView | single-file web editor |
| Runs on | GitHub's machines, billed per user | a box you run |
| Good for | anyone wanting to develop against the library | a link people can click |

---

## Codespaces

Everything needed is in [`.devcontainer/`](../.devcontainer):

```
https://codespaces.new/Stavan-Jain/QECLean
```

`setup.sh` installs the pinned toolchain, runs `lake exe cache get` for
mathlib's prebuilt oleans, and builds `QECLight`. The container opens on
[`Playground.lean`](../Playground.lean).

### Prebuilds

Without a prebuild, the first open costs the full `lake exe cache get` plus the
`QECLight` build — on the order of 15–40 minutes. With one, it is seconds.
Prebuilds are configured in the GitHub UI, not in a file:

**Settings → Codespaces → Set up prebuild**, with branch `main`, configuration
`.devcontainer/devcontainer.json`, trigger *on push*, and a 4-core machine
matching `hostRequirements`. Prebuild storage bills to the repo owner.

Worth turning on before pointing a group of people at the link, and turning
off again afterwards.

---

## Self-hosted lean4web

[`lean4web/install.sh`](lean4web/install.sh) provisions a **Ubuntu 22.04** box
(the only OS lean4web claims to support):

```bash
DOMAIN=lean.example.org ./install.sh
```

It installs Node, elan, and bubblewrap; clones lean4web; clones QECLean into
`Projects/QEC` (the folder name must be exactly `QEC` — lean4web requires the
folder name and its root `.lean` file to match); copies in
[`leanweb-config.json`](lean4web/leanweb-config.json) and
[`leanweb-build.sh`](lean4web/leanweb-build.sh); and runs `npm run build`.

Then:

```bash
cd ~/lean4web && npx pm2 start ecosystem.config.cjs
```

Visitors land on QECLean, since `leanweb-config.json` sets `"default": true`.
It is also reachable explicitly at `#project=QEC`.

### Sizing — measure this, do not trust the table

Each concurrent user gets their own Lean server process, and a mathlib-scale
project is not cheap per session. **These are estimates, not measurements:**

| Concurrent users | Rough RAM | Notes |
|---|---|---|
| ~10 | 16 GB | comfortable |
| ~25 | 32 GB | plausible for a class or workshop |
| ~50 | 64 GB+ | consider pointing people at Codespaces instead |

Disk: budget 25–30 GB for mathlib's oleans plus the toolchain.

Get a real number before committing to a box — open the editor, type an
`example`, and watch one session:

```bash
ps -o rss=,comm= -C lean | sort -rn | head
```

Multiply steady-state RSS by expected concurrency and add headroom. lean4web's
own README notes that larger projects are considered out of scope, so treat
high concurrency as something to load-test rather than assume.

### Operating notes

- lean4web runs Lean under bubblewrap by default. Do not set `NO_BWRAP=true`
  on a public instance — that runs visitor-supplied code uncontained.
- Depending on where the box lives, GDPR may require filling in
  `serverCountry` and `contactDetails` in `client/config/config.tsx`.
- Rehearse a cold start on the real box before relying on it for an event.
- If the instance is only needed for a fixed window, snapshot or destroy the
  box afterwards rather than leaving an unattended public Lean server running.
