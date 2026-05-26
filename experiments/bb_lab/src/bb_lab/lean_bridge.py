"""Lab ↔ Lean handshake for BB codes.

Three flows, all file-mediated (no live process):

1. **`state.yaml` → JSON descriptor**: `descriptor_from_state_yaml`
   reads a `pipeline/attempts/<id>/state.yaml` row and produces the
   canonical JSON descriptor (schema `bb-instance/v1`).

2. **Lean `def` block → JSON descriptor**: `descriptor_from_lean_defs`
   parses the de-facto `def grossA : GrossGroup → ZMod 2 | (i,j) => 1 | _ => 0`
   pattern used in
   `pipeline/attempts/gross/approaches/*/attempt.lean`. Regex-based,
   tolerates whitespace, refuses anything outside this exact shape.

3. **JSON descriptor → `.lean` skeleton**: `emit_skeleton` writes a
   Stage-2-style Lean file that imports
   `QEC.Stabilizer.Framework.Homological` and instantiates
   `bbChainComplex`. The emitted file is auto-generated and meant to be
   re-emitted, not hand-edited.

Naming convention: `code_id 'foo_bar' → grossA-style identifiers
`fooBar` (camelCase), `FooBar` (PascalCase), with the polynomial
suffixes `A` / `B`. Identifiers must be Lean-safe — the helper
`to_lean_identifier` enforces this and raises if the conversion
collapses to something illegal (e.g. starting with a digit).
"""

from __future__ import annotations

import json
import re
from dataclasses import asdict, dataclass, field
from pathlib import Path
from typing import Any

import yaml

from .group import AbelianGroup, ZmZn
from .poly import Poly


SCHEMA_VERSION = "bb-instance/v1"


@dataclass(frozen=True, slots=True)
class BBDescriptor:
    """Canonical JSON-friendly representation of a BB code instance."""

    code_id: str
    schema_version: str
    group_orders: tuple[int, ...]
    A_support: tuple[tuple[int, ...], ...]
    B_support: tuple[tuple[int, ...], ...]
    A_string: str
    B_string: str
    n: int
    metadata: dict[str, Any] = field(default_factory=dict)

    def to_json(self) -> str:
        d = asdict(self)
        # JSON-friendly tuples → lists
        d["group_orders"] = list(self.group_orders)
        d["A_support"] = [list(t) for t in self.A_support]
        d["B_support"] = [list(t) for t in self.B_support]
        return json.dumps(d, indent=2, sort_keys=True)

    @classmethod
    def from_json(cls, text: str) -> "BBDescriptor":
        d = json.loads(text)
        return cls(
            code_id=d["code_id"],
            schema_version=d["schema_version"],
            group_orders=tuple(d["group_orders"]),
            A_support=tuple(tuple(t) for t in d["A_support"]),
            B_support=tuple(tuple(t) for t in d["B_support"]),
            A_string=d["A_string"],
            B_string=d["B_string"],
            n=int(d["n"]),
            metadata=d.get("metadata", {}),
        )

    def group(self) -> AbelianGroup:
        return AbelianGroup(self.group_orders)

    def poly_A(self) -> Poly:
        return Poly.from_support(self.A_support, self.group())

    def poly_B(self) -> Poly:
        return Poly.from_support(self.B_support, self.group())


# ---------------------------------------------------------------------------
# state.yaml → descriptor

# state.yaml format uses a string like 'Z_12 x Z_6' for the group.
_GROUP_RE = re.compile(r"Z_(\d+)\s*[x×]\s*Z_(\d+)", re.IGNORECASE)


def descriptor_from_state_yaml(
    state_yaml_path: str | Path,
    *,
    code_id: str | None = None,
) -> BBDescriptor:
    """Read a `pipeline/attempts/<id>/state.yaml` and return the descriptor."""
    path = Path(state_yaml_path)
    data = yaml.safe_load(path.read_text())
    if code_id is None:
        code_id = data["code_id"]
    group_str = data["group"]
    m = _GROUP_RE.search(group_str)
    if not m:
        raise ValueError(
            f"state.yaml group field {group_str!r} does not match the "
            f"Z_<ell> x Z_<m> convention; v0 only supports ZMod ℓ × ZMod m"
        )
    ell, m_ord = int(m.group(1)), int(m.group(2))
    G = ZmZn(ell, m_ord)
    A_str = data["polynomials"]["A"]
    B_str = data["polynomials"]["B"]
    A = Poly.from_string(A_str, G)
    B = Poly.from_string(B_str, G)
    return BBDescriptor(
        code_id=code_id,
        schema_version=SCHEMA_VERSION,
        group_orders=G.orders,
        A_support=tuple(sorted(A.support)),
        B_support=tuple(sorted(B.support)),
        A_string=A_str,
        B_string=B_str,
        n=2 * G.cardinality,
        metadata={
            "source": "state_yaml",
            "source_path": str(path.relative_to(path.parent.parent.parent.parent))
                if path.is_absolute() and len(path.parts) >= 4
                else str(path),
            "display_name": data.get("display_name", ""),
        },
    )


# ---------------------------------------------------------------------------
# Lean `def` block → descriptor

_LEAN_DEF_RE = re.compile(
    r"def\s+(?P<name>\w+)\s*:\s*(?P<grp>\w+)\s*→\s*ZMod\s+2",
)
_LEAN_PATTERN_RE = re.compile(
    r"\|\s*\(\s*(?P<i>\d+)\s*,\s*(?P<j>\d+)\s*\)\s*=>\s*1",
)
_LEAN_GROUP_ABBREV_RE = re.compile(
    r"abbrev\s+(?P<grp>\w+)\s*:\s*Type\s*:=\s*ZMod\s+(?P<ell>\d+)\s*×\s*ZMod\s+(?P<m>\d+)",
)


def descriptor_from_lean_defs(
    lean_source: str, *, code_id: str
) -> BBDescriptor:
    """Parse a Lean source containing `abbrev <Grp> := ZMod ℓ × ZMod m` and
    two `def <name>A`/`def <name>B : <Grp> → ZMod 2` blocks.

    Only the strict gross-style pattern is supported. Raises on
    anything else.
    """
    g_match = _LEAN_GROUP_ABBREV_RE.search(lean_source)
    if not g_match:
        raise ValueError(
            "Lean source has no `abbrev <Name> : Type := ZMod ℓ × ZMod m` line"
        )
    ell = int(g_match.group("ell"))
    m_ord = int(g_match.group("m"))
    G = ZmZn(ell, m_ord)

    defs: dict[str, list[tuple[int, int]]] = {}
    for def_match in _LEAN_DEF_RE.finditer(lean_source):
        name = def_match.group("name")
        body_start = def_match.end()
        # Scan forward until the next `def`/`theorem`/`end`/blank-non-bullet
        # line. Cheap stop: take everything until 'def ', 'theorem ',
        # 'noncomputable', 'end', or end-of-file.
        rest = lean_source[body_start:]
        stop = re.search(
            r"(?m)^(?:def\s|theorem\s|lemma\s|noncomputable\s|@\[|end\s)",
            rest,
        )
        body = rest[: stop.start()] if stop else rest
        supp = [
            (int(m.group("i")), int(m.group("j")))
            for m in _LEAN_PATTERN_RE.finditer(body)
        ]
        defs[name] = supp

    if len(defs) < 2:
        raise ValueError(
            f"expected exactly 2 polynomial defs (A and B), found "
            f"{list(defs.keys())}"
        )
    # Convention: identifiers ending in 'A' / 'B' are the polynomials.
    A_name = next((n for n in defs if n.endswith("A")), None)
    B_name = next((n for n in defs if n.endswith("B")), None)
    if A_name is None or B_name is None:
        raise ValueError(
            f"could not identify A/B polynomials; "
            f"defs were {list(defs.keys())}"
        )
    A = Poly.from_support(defs[A_name], G)
    B = Poly.from_support(defs[B_name], G)
    return BBDescriptor(
        code_id=code_id,
        schema_version=SCHEMA_VERSION,
        group_orders=G.orders,
        A_support=tuple(sorted(A.support)),
        B_support=tuple(sorted(B.support)),
        A_string=A.canonical_string(),
        B_string=B.canonical_string(),
        n=2 * G.cardinality,
        metadata={"source": "lean_defs"},
    )


# ---------------------------------------------------------------------------
# Identifier conversion

_VALID_LEAN_IDENT = re.compile(r"\A[A-Za-z][A-Za-z0-9]*\Z")


def to_lean_identifier(code_id: str) -> tuple[str, str]:
    """Return ``(camelCase, PascalCase)`` Lean identifiers for `code_id`.

    Accepts snake_case (`bb_72_12_6`) and camel/PascalCase; raises if the
    result wouldn't be a legal Lean identifier (e.g. starts with a digit
    or is empty).
    """
    parts = [p for p in re.split(r"[_\-]+", code_id) if p]
    if not parts:
        raise ValueError(f"empty code_id after splitting: {code_id!r}")
    camel = parts[0][0].lower() + parts[0][1:] + "".join(
        p.capitalize() for p in parts[1:]
    )
    pascal = "".join(p.capitalize() for p in parts)
    if not _VALID_LEAN_IDENT.match(camel) or not _VALID_LEAN_IDENT.match(pascal):
        raise ValueError(
            f"code_id {code_id!r} does not produce a legal Lean identifier "
            f"(got camel={camel!r}, pascal={pascal!r})"
        )
    return camel, pascal


# ---------------------------------------------------------------------------
# JSON descriptor → .lean skeleton

_SKELETON_TEMPLATE = '''\
/-
# {pascal_name} — Bivariate-bicycle code skeleton.

**Auto-generated by `bb_lab.lean_bridge.emit_skeleton`.**
Do not edit by hand — re-emit from the descriptor.

  schema:    {schema_version}
  code_id:   {code_id}
  group:     ZMod {ell} × ZMod {m}
  A:         {A_string}
  B:         {B_string}
  qubits:    n = {n}

The chain-complex law `∂₁ ∘ ∂₂ = 0` is automatic from
`Quantum.Stabilizer.Homological.BB.bbBoundary_comp`.
-/

import QEC.Stabilizer.Framework.Homological

namespace Quantum
namespace Stabilizer
namespace Homological

open scoped BigOperators

namespace BB
namespace {pascal_name}

/-- The group `G = ZMod {ell} × ZMod {m}` for `{code_id}`. -/
abbrev {pascal_name}Group : Type := ZMod {ell} × ZMod {m}

/-- Polynomial `A = {A_string}`, as an indicator function. -/
def {camel_name}A : {pascal_name}Group → ZMod 2
{A_arms}  | _ => 0

/-- Polynomial `B = {B_string}`, as an indicator function. -/
def {camel_name}B : {pascal_name}Group → ZMod 2
{B_arms}  | _ => 0

/-- `{code_id}` as a `HomologicalCode`. -/
noncomputable def {camel_name}HomologicalCode : HomologicalCode :=
  bbChainComplex (G := {pascal_name}Group) {camel_name}A {camel_name}B

/-- `{code_id}` has `{n}` physical qubits. -/
@[simp] lemma {camel_name}HomologicalCode_numQubits :
    {camel_name}HomologicalCode.numQubits = {n} := by
  change bbNumQubits {pascal_name}Group = {n}
  unfold bbNumQubits
  decide

end {pascal_name}
end BB

end Homological
end Stabilizer
end Quantum
'''


def _arms_for(support: tuple[tuple[int, ...], ...]) -> str:
    lines = []
    for g in support:
        if len(g) != 2:
            raise ValueError(
                f"emit_skeleton currently supports only rank-2 groups; "
                f"got element {g}"
            )
        lines.append(f"  | ({g[0]}, {g[1]}) => 1")
    return "\n".join(lines) + ("\n" if lines else "")


def emit_skeleton(descriptor: BBDescriptor, out_path: str | Path) -> Path:
    """Write a Lean skeleton file at `out_path`. Returns the path written."""
    if len(descriptor.group_orders) != 2:
        raise ValueError(
            f"emit_skeleton only supports rank-2 groups; got "
            f"orders {descriptor.group_orders}"
        )
    camel, pascal = to_lean_identifier(descriptor.code_id)
    text = _SKELETON_TEMPLATE.format(
        code_id=descriptor.code_id,
        schema_version=descriptor.schema_version,
        ell=descriptor.group_orders[0],
        m=descriptor.group_orders[1],
        A_string=descriptor.A_string,
        B_string=descriptor.B_string,
        n=descriptor.n,
        camel_name=camel,
        pascal_name=pascal,
        A_arms=_arms_for(descriptor.A_support),
        B_arms=_arms_for(descriptor.B_support),
    )
    p = Path(out_path)
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text(text)
    return p
