#!/usr/bin/env python3
"""Static dashboard generator for the QEC formalization pipeline.

Reads catalog/zoo.yaml, catalog/scoring.yaml, pipeline/attempts/*/, and
pipeline/research_log.md from the repo root, renders four page types
(overview, queue, per-code detail, research log) into dashboard/dist/.

Run: python3 dashboard/build.py
"""
from __future__ import annotations

import json
import re
import shutil
import subprocess
import sys
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any

import yaml
from jinja2 import Environment, FileSystemLoader, select_autoescape
from markdown_it import MarkdownIt
from mdit_py_plugins.tasklists import tasklists_plugin


REPO_ROOT = Path(__file__).resolve().parent.parent
DASHBOARD_DIR = REPO_ROOT / "dashboard"
TEMPLATES_DIR = DASHBOARD_DIR / "templates"
STATIC_DIR = DASHBOARD_DIR / "static"
DIST_DIR = DASHBOARD_DIR / "dist"

CATALOG_PATH = REPO_ROOT / "catalog" / "zoo.yaml"
SCORING_PATH = REPO_ROOT / "catalog" / "scoring.yaml"
ATTEMPTS_DIR = REPO_ROOT / "pipeline" / "attempts"
RESEARCH_LOG_PATH = REPO_ROOT / "pipeline" / "research_log.md"
QUEUE_MD_PATH = REPO_ROOT / "pipeline" / "queue.md"

GITHUB_REPO = "Stavan-Jain/QECLean"

# Manually curated map of done codes → their primary Lean file(s) in the
# repo. Used to render reliable source links on the /done/ page. Some
# rationales contain wildcards/braces (toric, repetition, RSC) that don't
# parse as clean URLs, so we maintain this list by hand.
DONE_LEAN_PATHS: dict[str, list[str]] = {
    "stab_4_2_2":         ["QEC/Stabilizer/Codes/Small/FourQubit_4_2_2.lean"],
    "stab_5_1_3":         ["QEC/Stabilizer/Codes/Small/FiveQubit_5_1_3.lean"],
    "shor_nine":          ["QEC/Stabilizer/Codes/Small/Shor9.lean"],
    "steane":             ["QEC/Stabilizer/Codes/Small/Steane7.lean"],
    "quantum_hamming":    ["QEC/Stabilizer/Codes/Small/QuantumHamming.lean"],
    "stab_15_7_3":        ["QEC/Stabilizer/Codes/Small/QuantumHamming.lean"],
    "quantum_repetition": [
        "QEC/Stabilizer/Codes/Repetition/Three.lean",
        "QEC/Stabilizer/Codes/Repetition/N.lean",
    ],
    "toric":              ["QEC/Stabilizer/Codes/Toric/"],
    "rotated_surface":    ["QEC/Stabilizer/Codes/RotatedSurface/"],
    "surface-17":         ["QEC/Stabilizer/Codes/RotatedSurface/N.lean"],
    "qubit_stabilizer":   ["QEC/Stabilizer/Core/"],
}


# ---------------------------------------------------------------------------
# Data loading
# ---------------------------------------------------------------------------

@dataclass
class Attempt:
    code_id: str
    state: dict[str, Any]
    files: dict[str, str] = field(default_factory=dict)  # filename -> raw markdown
    approaches: list[dict[str, Any]] = field(default_factory=list)

    @property
    def status(self) -> str:
        return str(self.state.get("status", "unknown"))

    @property
    def track(self) -> str:
        return str(self.state.get("track", "engineering"))

    @property
    def covering_file(self) -> str | None:
        return self.state.get("covering_lean_file")

    @property
    def sorries_summary(self) -> str | None:
        closed = self.state.get("sorries_closed")
        total = self.state.get("sorries_total") or self.state.get("sorries_closed", 0) + self.state.get("sorries_blocked", 0)
        if closed is None:
            return None
        if total and total > 0:
            return f"{closed} / {total}"
        return str(closed)


@dataclass
class CodeEntry:
    code_id: str
    name: str
    short_name: str
    parameters: dict[str, Any]
    family_chain: list[str]
    introduced_refs: list[str]
    description_snippet: str
    has_hardware_demo: bool
    realizations_count: int
    citation_count: int
    eczoo_link: str | None

    # From scoring
    status: str
    axes: dict[str, int]
    composite: float
    proposed_track: str
    rationale: str
    blockers: list[str]
    estimated_loc: int | None

    # From attempts/
    attempt: Attempt | None = None


def load_catalog() -> list[dict[str, Any]]:
    with open(CATALOG_PATH) as f:
        return yaml.safe_load(f)


def load_scoring() -> dict[str, Any]:
    with open(SCORING_PATH) as f:
        return yaml.safe_load(f)


def load_attempts() -> dict[str, Attempt]:
    attempts: dict[str, Attempt] = {}
    if not ATTEMPTS_DIR.exists():
        return attempts
    for attempt_dir in sorted(ATTEMPTS_DIR.iterdir()):
        if not attempt_dir.is_dir():
            continue
        state_path = attempt_dir / "state.yaml"
        if not state_path.exists():
            continue
        with open(state_path) as f:
            state = yaml.safe_load(f) or {}
        code_id = state.get("code_id", attempt_dir.name)
        attempt = Attempt(code_id=code_id, state=state)
        for md_name in ("informal_spec.md", "plan.md", "result.md",
                        "hypothesis.md", "literature_notes.md",
                        "success_criterion.md", "partial_value.md",
                        "reuse_audit.md", "gap_audit.md", "progress.md"):
            p = attempt_dir / md_name
            if p.exists():
                attempt.files[md_name] = p.read_text()
        approaches_dir = attempt_dir / "approaches"
        if approaches_dir.exists():
            for approach_dir in sorted(approaches_dir.iterdir()):
                if not approach_dir.is_dir():
                    continue
                approach: dict[str, Any] = {"name": approach_dir.name, "files": {}}
                for md in approach_dir.glob("*.md"):
                    approach["files"][md.name] = md.read_text()
                attempt.approaches.append(approach)
        attempts[code_id] = attempt
    return attempts


def merge_entries(catalog: list[dict[str, Any]],
                  scoring: dict[str, Any],
                  attempts: dict[str, Attempt]) -> list[CodeEntry]:
    catalog_by_id = {c["code_id"]: c for c in catalog}
    entries: list[CodeEntry] = []
    for score in scoring["entries"]:
        cid = score["code_id"]
        cat = catalog_by_id.get(cid, {})
        family_chain = cat.get("family_chain") or []
        eczoo_link = None
        if cid and not cid.startswith("stab_") and not cid.startswith("css_"):
            eczoo_link = f"https://errorcorrectionzoo.org/c/{cid}"
        entries.append(CodeEntry(
            code_id=cid,
            name=strip_math_delims(score.get("name", cat.get("name", cid))),
            short_name=cat.get("short_name", "") or "",
            parameters=cat.get("parameters", {}) or {},
            family_chain=family_chain,
            introduced_refs=cat.get("introduced_refs", []) or [],
            description_snippet=strip_math_delims(cat.get("description_snippet", "") or ""),
            has_hardware_demo=bool(cat.get("has_hardware_demo")),
            realizations_count=cat.get("realizations_count", 0) or 0,
            citation_count=cat.get("citation_count", 0) or 0,
            eczoo_link=eczoo_link,
            status=score.get("status", "not_started"),
            axes=score.get("axes", {}),
            composite=float(score.get("composite", 0.0)),
            proposed_track=score.get("proposed_track", "skip"),
            rationale=strip_math_delims(score.get("rationale", "") or ""),
            blockers=score.get("blockers", []) or [],
            estimated_loc=score.get("estimated_loc"),
            attempt=attempts.get(cid),
        ))
    return entries


def recent_commits(n: int = 8) -> list[dict[str, str]]:
    paths = ["pipeline/", "catalog/", "QEC/Stabilizer/Codes/", "QEC/Stabilizer/Homological/"]
    try:
        out = subprocess.check_output(
            ["git", "log", f"-{n}", "--pretty=format:%h%x09%ad%x09%s",
             "--date=short", "--"] + paths,
            cwd=REPO_ROOT,
            stderr=subprocess.DEVNULL,
        ).decode()
    except subprocess.CalledProcessError:
        return []
    commits = []
    for line in out.strip().splitlines():
        parts = line.split("\t", 2)
        if len(parts) != 3:
            continue
        sha, date, subject = parts
        commits.append({
            "sha": sha,
            "date": date,
            "subject": subject,
            "url": f"https://github.com/{GITHUB_REPO}/commit/{sha}",
        })
    return commits


# ---------------------------------------------------------------------------
# Markdown rendering
# ---------------------------------------------------------------------------

MATH_INLINE_RE = re.compile(r"\\\(([^)]*?)\\\)")
MATH_BLOCK_RE = re.compile(r"\\\[([^\]]*?)\\\]")


def preprocess_math(text: str) -> str:
    """Convert \\([[n,k,d]]\\) to inline code so it survives markdown unchanged."""
    text = MATH_INLINE_RE.sub(lambda m: f"`{m.group(1)}`", text)
    text = MATH_BLOCK_RE.sub(lambda m: f"`{m.group(1)}`", text)
    return text


def strip_math_delims(text: str) -> str:
    """Remove \\(...\\) and \\[...\\] delimiters from plain-text fields (names, rationales).

    Used for fields rendered directly in templates without markdown processing.
    """
    if not text:
        return text
    text = MATH_INLINE_RE.sub(lambda m: m.group(1), text)
    text = MATH_BLOCK_RE.sub(lambda m: m.group(1), text)
    return text


RATIONALE_PREFIX_RE = re.compile(
    r"^(Audit override:\s*|Already formalized:\s*)", re.IGNORECASE,
)


def done_summary(rationale: str, max_len: int = 220) -> str:
    """Extract a short summary from a done-code's rationale.

    Strips the "Audit override:" / "Already formalized:" prefix and any
    "Previous rationale: ..." trailer, then truncates to max_len.
    """
    if not rationale:
        return ""
    text = RATIONALE_PREFIX_RE.sub("", rationale.strip())
    # Some rationales have a "Previous rationale:" trailer — drop it.
    idx = text.find("Previous rationale:")
    if idx != -1:
        text = text[:idx].rstrip().rstrip(".")
    text = " ".join(text.split())  # collapse newlines/whitespace
    if len(text) > max_len:
        text = text[: max_len - 1].rstrip() + "…"
    return text


def basename(path: str) -> str:
    """Filename portion of a path, or the path itself if it ends with /."""
    if path.endswith("/"):
        return path
    return path.rsplit("/", 1)[-1]


def render_md(text: str | None) -> str:
    if not text:
        return ""
    md = MarkdownIt("commonmark", {"breaks": False, "linkify": True, "html": False})
    md.enable(["table", "strikethrough"])
    md = md.use(tasklists_plugin)
    return md.render(preprocess_math(text))


# ---------------------------------------------------------------------------
# Page rendering
# ---------------------------------------------------------------------------

AXIS_ORDER = ["reuse", "canonicality", "hardware", "tractability", "prerequisites", "effort"]
AXIS_LABELS = {
    "reuse": "Reuse",
    "canonicality": "Canon",
    "hardware": "Hardware",
    "tractability": "Tract",
    "prerequisites": "Prereq",
    "effort": "Effort",
}
AXIS_WEIGHTS = {
    "reuse": 0.25,
    "canonicality": 0.15,
    "hardware": 0.15,
    "tractability": 0.15,
    "prerequisites": 0.20,
    "effort": 0.10,
}


def format_parameters(p: dict[str, Any]) -> str:
    if not p:
        return ""
    n, k, d = p.get("n"), p.get("k"), p.get("d")
    if n and k is not None and d:
        return f"[[{n},{k},{d}]]"
    if n and k is not None:
        return f"[[{n},{k}]]"
    return ""


def code_slug(code_id: str) -> str:
    return re.sub(r"[^a-z0-9_-]", "-", code_id.lower())


def write(path: Path, content: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content)


def build():
    print(f"[build] repo root: {REPO_ROOT}")
    print(f"[build] loading catalog ({CATALOG_PATH.relative_to(REPO_ROOT)})")
    catalog = load_catalog()
    print(f"[build]   {len(catalog)} catalog entries")

    print(f"[build] loading scoring ({SCORING_PATH.relative_to(REPO_ROOT)})")
    scoring = load_scoring()
    print(f"[build]   {len(scoring['entries'])} scoring entries")

    print(f"[build] loading attempts ({ATTEMPTS_DIR.relative_to(REPO_ROOT)})")
    attempts = load_attempts()
    print(f"[build]   {len(attempts)} attempts: {list(attempts)}")

    entries = merge_entries(catalog, scoring, attempts)
    entries.sort(key=lambda e: -e.composite)

    # Reset dist
    if DIST_DIR.exists():
        shutil.rmtree(DIST_DIR)
    DIST_DIR.mkdir(parents=True)

    # Copy static
    static_dst = DIST_DIR / "static"
    if STATIC_DIR.exists():
        shutil.copytree(STATIC_DIR, static_dst)

    env = Environment(
        loader=FileSystemLoader(TEMPLATES_DIR),
        autoescape=select_autoescape(["html"]),
    )
    env.globals["axis_order"] = AXIS_ORDER
    env.globals["axis_labels"] = AXIS_LABELS
    env.globals["axis_weights"] = AXIS_WEIGHTS
    env.globals["github_repo"] = GITHUB_REPO
    env.filters["render_md"] = render_md
    env.filters["format_parameters"] = format_parameters
    env.filters["code_slug"] = code_slug
    env.filters["done_summary"] = done_summary
    env.filters["basename"] = basename
    env.globals["done_lean_paths"] = DONE_LEAN_PATHS

    by_track: dict[str, list[CodeEntry]] = {"engineering": [], "moonshot": [], "defer": [], "skip": []}
    for e in entries:
        by_track.setdefault(e.proposed_track, []).append(e)
    done = [e for e in entries if e.status == "done"]
    in_flight = [e for e in entries if e.status == "in_flight"]
    not_started = [e for e in entries if e.status == "not_started"]

    # --- Overview ---
    print("[build] rendering overview")
    overview_tmpl = env.get_template("overview.html")
    queue_head_engineering = [e for e in by_track["engineering"] if e.status != "done"][:8]
    queue_head_moonshot = [e for e in by_track["moonshot"]]
    write(DIST_DIR / "index.html", overview_tmpl.render(
        title="QEC formalization pipeline",
        active="overview",
        root_prefix="",
        total=len(entries),
        done=done,
        in_flight=in_flight,
        not_started=not_started,
        by_track=by_track,
        queue_head_engineering=queue_head_engineering,
        queue_head_moonshot=queue_head_moonshot,
        recent_commits=recent_commits(8),
        scoring_metadata=scoring.get("metadata", {}),
    ))

    # --- Queue ---
    print("[build] rendering queue")
    queue_tmpl = env.get_template("queue.html")
    queue_json = [
        {
            "code_id": e.code_id,
            "name": e.name,
            "params": format_parameters(e.parameters),
            "track": e.proposed_track,
            "status": e.status,
            "composite": e.composite,
            "axes": {a: e.axes.get(a) for a in AXIS_ORDER},
            "rationale": e.rationale,
            "slug": code_slug(e.code_id),
            "has_attempt": e.attempt is not None,
        }
        for e in entries
    ]
    write(DIST_DIR / "queue" / "index.html", queue_tmpl.render(
        title="Queue",
        active="queue",
        root_prefix="../",
        entries=entries,
        queue_json=json.dumps(queue_json),
    ))

    # --- Done ---
    print("[build] rendering done")
    done_tmpl = env.get_template("done.html")
    # Split done into concrete (has parameters.n) and parametric/abstract; within each
    # group, sort by n ascending (concrete) or alphabetically (parametric).
    done_concrete = sorted(
        [e for e in done if e.parameters.get("n")],
        key=lambda e: (e.parameters.get("n"), e.parameters.get("k", 0), e.code_id),
    )
    done_parametric = sorted(
        [e for e in done if not e.parameters.get("n")],
        key=lambda e: e.code_id,
    )
    write(DIST_DIR / "done" / "index.html", done_tmpl.render(
        title="Done",
        active="done",
        root_prefix="../",
        done_concrete=done_concrete,
        done_parametric=done_parametric,
    ))

    # --- Research log ---
    print("[build] rendering research")
    research_tmpl = env.get_template("research.html")
    moonshots = [e for e in entries if e.proposed_track == "moonshot"]
    research_log_md = RESEARCH_LOG_PATH.read_text() if RESEARCH_LOG_PATH.exists() else ""
    write(DIST_DIR / "research" / "index.html", research_tmpl.render(
        title="Research log",
        active="research",
        root_prefix="../",
        moonshots=moonshots,
        research_log_md=research_log_md,
    ))

    # --- Code detail pages ---
    print(f"[build] rendering {len(entries)} code detail pages")
    code_tmpl = env.get_template("code.html")
    for e in entries:
        slug = code_slug(e.code_id)
        write(DIST_DIR / "code" / slug / "index.html", code_tmpl.render(
            title=e.name,
            active="queue",
            root_prefix="../../",
            code=e,
            params=format_parameters(e.parameters),
        ))

    print(f"[build] done. {sum(1 for _ in DIST_DIR.rglob('*.html'))} HTML files in {DIST_DIR.relative_to(REPO_ROOT)}/")


if __name__ == "__main__":
    try:
        build()
    except Exception as exc:
        print(f"[build] FAILED: {exc}", file=sys.stderr)
        raise
