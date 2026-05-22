#!/usr/bin/env python3
"""
Ingest the Error Correction Zoo data snapshot into a structured catalog
(``catalog/zoo.yaml``) used by the formalization-pipeline prioritizer.

Source: ``pipeline/cache/eczoo_data/`` (pinned SHA in ``pipeline/cache/PIN.md``).

Scope: qubit stabilizer, subsystem, small-distance, and dynamic codes. We
deliberately skip qudit/oscillator/fermion families for now since the repo's
current abstractions target qubits.

Output schema per entry:

    code_id              str   — eczoo unique id
    short_name           str
    name                 str   — raw LaTeX-formatted display name
    family               str   — path-derived bucket (e.g. "stabilizer/css")
    family_chain         list  — full path components below codes/quantum/
    physical             str
    logical              str
    parameters           dict  — n/k/d extracted from name when possible
    protection_text      str
    introduced_refs      list  — extracted \\cite{...} keys from `introduced`
    realizations_count   int   — proxy for hardware-demo signal
    has_hardware_demo    bool
    parents              list  — code_ids
    cousins              list  — code_ids
    description_snippet  str   — first ~200 chars, LaTeX preserved
    citation_count       int   — count of \\cite{...} in description (rough proxy)
    source_path          str   — relative to repo root
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

import yaml


REPO_ROOT = Path(__file__).resolve().parent.parent
ECZOO = REPO_ROOT / "pipeline" / "cache" / "eczoo_data"
QUANTUM_ROOT = ECZOO / "codes" / "quantum"
OUTPUT = REPO_ROOT / "catalog" / "zoo.yaml"

# Filter: only ingest these path prefixes (relative to codes/quantum/).
SCOPE_PREFIXES = (
    "qubits/stabilizer",
    "qubits/small_distance",
    "qubits/subsystem",
    "qubits/dynamic",
)

# Skip "family" YAMLs that share a name with a sibling directory — those define
# the family taxonomy; we only want the concrete leaf-code entries.
def is_family_doc(path: Path) -> bool:
    """True if this .yml has a sibling directory of the same stem (= family doc)."""
    sibling_dir = path.with_suffix("")
    return sibling_dir.is_dir()


def in_scope(path: Path) -> bool:
    rel = path.relative_to(QUANTUM_ROOT).as_posix()
    return any(rel.startswith(p) for p in SCOPE_PREFIXES)


def family_from_path(path: Path) -> tuple[str, list[str]]:
    """Map ``codes/quantum/qubits/stabilizer/css/steane.yml`` to
    family='stabilizer/css' (depth-2 below qubits/) and the full chain."""
    rel = path.relative_to(QUANTUM_ROOT).with_suffix("")
    parts = list(rel.parts)
    # Drop the leading "qubits/" since everything we ingest is qubit-physical.
    if parts and parts[0] == "qubits":
        parts = parts[1:]
    # Drop the trailing leaf if it's the code_id itself.
    chain = parts[:-1] if len(parts) > 1 else parts
    family = "/".join(chain) if chain else "(root)"
    return family, parts


# Regex to extract [[n,k,d]] from the name field.  Allows optional brackets
# and dollar signs; accepts integer parameters; ignores LaTeX escape backslashes.
_NKD_RE = re.compile(r"\[\[\s*(\d+)\s*,\s*(\d+)\s*,\s*(\d+)\s*\]\]")
_NK_RE = re.compile(r"\[\[\s*(\d+)\s*,\s*(\d+)\s*\]\]")


def extract_parameters(name: str) -> dict:
    """Best-effort [[n,k,d]] extraction from the code's display name."""
    if not name:
        return {}
    m = _NKD_RE.search(name)
    if m:
        return {"n": int(m.group(1)), "k": int(m.group(2)), "d": int(m.group(3))}
    m = _NK_RE.search(name)
    if m:
        return {"n": int(m.group(1)), "k": int(m.group(2))}
    return {}


_CITE_RE = re.compile(r"\\cite\{([^}]+)\}")


def extract_refs(field: str | None) -> list[str]:
    """Pull \\cite{...} keys out of a LaTeX field. Splits comma-separated
    multi-key citations into individual references."""
    if not field:
        return []
    keys: list[str] = []
    for m in _CITE_RE.finditer(field):
        for k in m.group(1).split(","):
            k = k.strip()
            if k:
                keys.append(k)
    return keys


def count_citations(field: str | None) -> int:
    """Proxy for how heavily-referenced an entry is."""
    return len(_CITE_RE.findall(field or ""))


def description_snippet(desc: str | None, limit: int = 240) -> str:
    if not desc:
        return ""
    snippet = " ".join(desc.split())
    return snippet[:limit] + ("…" if len(snippet) > limit else "")


def normalize_relations(raw) -> list[str]:
    """Extract code_ids from a `relations.parents` or `.cousins` list."""
    if not raw:
        return []
    out: list[str] = []
    for entry in raw:
        if isinstance(entry, dict) and "code_id" in entry:
            out.append(entry["code_id"])
        elif isinstance(entry, str):
            out.append(entry)
    return out


def realizations_count(raw) -> int:
    if not raw:
        return 0
    if isinstance(raw, list):
        return len(raw)
    return 1


def process_one(path: Path) -> dict | None:
    try:
        with open(path, "r", encoding="utf-8") as f:
            data = yaml.safe_load(f)
    except yaml.YAMLError as exc:
        print(f"warning: failed to parse {path}: {exc}", file=sys.stderr)
        return None
    if not isinstance(data, dict) or "code_id" not in data:
        return None

    family, chain = family_from_path(path)
    name = data.get("name", "")
    relations = data.get("relations", {}) or {}

    return {
        "code_id": data["code_id"],
        "short_name": data.get("short_name", ""),
        "name": name,
        "family": family,
        "family_chain": chain,
        "physical": data.get("physical", ""),
        "logical": data.get("logical", ""),
        "parameters": extract_parameters(name),
        "protection_text": (data.get("protection") or "").strip(),
        "introduced_refs": extract_refs(data.get("introduced")),
        "realizations_count": realizations_count(data.get("realizations")),
        "has_hardware_demo": bool(data.get("realizations")),
        "parents": normalize_relations(relations.get("parents")),
        "cousins": normalize_relations(relations.get("cousins")),
        "description_snippet": description_snippet(data.get("description")),
        "citation_count": count_citations(data.get("description")),
        "source_path": str(path.relative_to(REPO_ROOT)),
    }


def main() -> int:
    if not QUANTUM_ROOT.is_dir():
        print(
            f"error: missing snapshot at {QUANTUM_ROOT}\n"
            "run the clone step in pipeline/cache/PIN.md first",
            file=sys.stderr,
        )
        return 1

    candidates: list[Path] = []
    for path in QUANTUM_ROOT.rglob("*.yml"):
        if not in_scope(path):
            continue
        if is_family_doc(path):
            continue
        candidates.append(path)
    candidates.sort()

    entries: list[dict] = []
    skipped = 0
    for path in candidates:
        entry = process_one(path)
        if entry is None:
            skipped += 1
            continue
        entries.append(entry)

    entries.sort(key=lambda e: e["code_id"])

    OUTPUT.parent.mkdir(parents=True, exist_ok=True)
    with open(OUTPUT, "w", encoding="utf-8") as f:
        f.write(
            "# Generated by scripts/ingest_zoo.py from the pinned eczoo_data\n"
            "# snapshot (see pipeline/cache/PIN.md).  Do not edit by hand —\n"
            "# regenerate to refresh.\n\n"
        )
        yaml.safe_dump(entries, f, sort_keys=False, allow_unicode=True, width=120)

    print(
        f"ingested {len(entries)} entries → {OUTPUT.relative_to(REPO_ROOT)}\n"
        f"  skipped: {skipped} (failed parse or missing code_id)\n"
        f"  scope: {', '.join(SCOPE_PREFIXES)}"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
