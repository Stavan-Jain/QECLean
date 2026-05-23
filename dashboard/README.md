# QEC pipeline dashboard

Static HTML dashboard for the formalization pipeline. Reads
`catalog/zoo.yaml`, `catalog/scoring.yaml`, `pipeline/attempts/*/`, and
`pipeline/research_log.md` from the repo root; writes to `dashboard/dist/`.

## Build

```bash
pip3 install --user --break-system-packages -r dashboard/requirements.txt
python3 dashboard/build.py
```

## View locally

```bash
python3 -m http.server 8765 --directory dashboard/dist
# open http://localhost:8765
```

## Pages

- `/` — overview: counts, in-flight, queue head, recent commits
- `/queue/` — all 267 codes, client-side sort/filter
- `/code/<slug>/` — per-code detail; renders `result.md`, `informal_spec.md`,
  etc., as tabs when an attempt directory exists
- `/research/` — moonshot-focused; per-moonshot approach tables

## Layout

```
dashboard/
├── build.py            # generator
├── requirements.txt    # PyYAML, Jinja2, markdown-it-py, mdit-py-plugins
├── templates/          # Jinja2 templates (base, overview, queue, code, research)
├── static/             # style.css, queue.js
└── dist/               # generated HTML (gitignored)
```

## Deploying to GitHub Pages

[`.github/workflows/dashboard.yml`](../.github/workflows/dashboard.yml)
rebuilds and deploys on every push to `main` that touches `dashboard/`,
`catalog/`, or `pipeline/`. The workflow uses
`actions/upload-pages-artifact` + `actions/deploy-pages`.

**One-time setup in the repo settings**: Settings → Pages → Build and
deployment → Source: **GitHub Actions**. After the first successful run,
the live URL appears as the `deploy` job's environment URL.

## Schema dependencies

The build script reads but does not modify upstream YAML. New fields
in `scoring.yaml` entries are fine — they just won't show up until
templated. The build fails loudly if `catalog/scoring.yaml` is missing
or unparseable.
