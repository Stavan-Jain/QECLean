# Informal spec: Ganti-Onunkwo-Young `[[6r, 2r, 2]]` code family

## Summary

The **Ganti-Onunkwo-Young (GOY) code family**, introduced in
[Ganti-Onunkwo-Young 2013, `arxiv:1309.1674`], is a parametric family of
`[[6r, 2r, 2]]` CSS quantum error-detecting codes. It was designed for
practical scalable adiabatic quantum computation: all logical operators
have weight 2, the connectivity graph is planar with fixed degree, and it
supports a universal set of weight-2 logical interactions. The defining
structural feature is that **all but two stabilizer generators are
weight-2 (two-body)**, with the remaining two stabilizers having weight
`4r` each (the "all-X" and "all-Z" type stabilizers covering most qubits).

For `r = 1` this is the **C_6 code** — equivalent (as a code subspace) to
Knill's `[[6, 2, 2]]` code formalized at
`QEC/Stabilizer/Codes/Small/SixQubit_6_2_2.lean`, but with a **different
stabilizer presentation** (2 weight-2 + 2 weight-4 generators here vs. 4
weight-4 generators in Knill's presentation). See § "Relation to
SixQubit_6_2_2.lean" below.

**Paper-extraction status.** The construction below is extracted **directly
from the paper** — specifically from Eq. (3) (stabilizer generators), Eq.
(4) (single-body logical operators), and the distance argument in §III.
Citations in each theorem statement use the form
`[GOY §III, Eq. M]`. The PDF text was retrievable; no reconstruction was
necessary.

## Parameters

- Physical qubits: **n = 6r**
- Logical qubits: **k = 2r**
- Distance: **d = 2** (detects a single error; cannot correct)
- Family: **CSS** (separable into X-only and Z-only generators)
- Parameter constraint: **`r ≥ 1`** (`Fact (1 ≤ r)`)
  - `r = 0` would give a trivial `[[0, 0, 2]]` code with zero qubits, which
    we exclude.
  - Paper uses parameter `k` for the family index (so paper's "k" = our `r`);
    we use `r` in Lean to avoid colliding with the project-wide use of `k`
    for logical-qubit count.
- Originally introduced in: [Ganti-Onunkwo-Young 2013, `arxiv:1309.1674`].
- EC Zoo entry: <https://errorcorrectionzoo.org/c/goy>.

## Qubit indexing

The paper labels each of the `6r` physical qubits by a pair `(i, c)` where
`i ∈ {1, ..., 2r}` and `c ∈ {x, 0, z}`. Each "logical row" `i` consists of
three physical qubits: `(i, x)`, `(i, 0)`, `(i, z)`. See
[GOY Fig. 2 §III, p.3].

**Our Lean indexing (0-based row-major).** For `i : Fin (2r)`:

```
qubit_x i := 3 * i.val      ∈ Fin (6r)    -- maps paper (i+1, x) to row i
qubit_0 i := 3 * i.val + 1  ∈ Fin (6r)    -- maps paper (i+1, 0) to row i
qubit_z i := 3 * i.val + 2  ∈ Fin (6r)    -- maps paper (i+1, z) to row i
```

So physical qubit indices `{3i, 3i+1, 3i+2}` carry the x-, 0-, z-roles of
logical row `i`. Each `Fin (6r)` index lies in exactly one row (`i = q.val / 3`)
and exactly one role (`q.val mod 3 ∈ {0, 1, 2}`).

**Why this indexing.** Row-major puts the (i,x), (i,0), (i,z) triples
contiguously, which makes the `qubit_x` / `qubit_0` / `qubit_z` accessors
straightforward `omega`-discharged `Fin` constructions, and makes the
weight-2 X-link / Z-link stabilizer supports adjacent triples in `Fin (6r)`.

## Stabilizer generators

Per [GOY Eq. (3), §III, p.3], the stabilizer group has **4r generators**:

```
S = ⟨ {X(i,x) X(i+1,x)}_{i=1}^{2r-1},   ⊗_{i=1}^{2r} X(i,0) X(i,z),
      {Z(i,z) Z(i+1,z)}_{i=1}^{2r-1},   ⊗_{i=1}^{2r} Z(i,x) Z(i,0) ⟩
```

In our Lean notation (0-based, `i : Fin (2r - 1)` or `Fin (2r)` as appropriate):

| Generator       | Type | Weight | Support                                            | Count          |
|-----------------|------|--------|----------------------------------------------------|----------------|
| `XLink i`       | X    | 2      | {qubit_x i, qubit_x (i+1)} = {3i, 3(i+1)}          | `2r − 1` of them |
| `XBig`          | X    | `4r`   | { qubit_0 j, qubit_z j : j ∈ Fin (2r) } = {3j+1, 3j+2 : j} | 1            |
| `ZLink i`       | Z    | 2      | {qubit_z i, qubit_z (i+1)} = {3i+2, 3(i+1)+2}      | `2r − 1` of them |
| `ZBig`          | Z    | `4r`   | { qubit_x j, qubit_0 j : j ∈ Fin (2r) } = {3j, 3j+1 : j}   | 1            |

Total: `(2r − 1) + 1 + (2r − 1) + 1 = 4r` generators. ✓
And `n − k = 6r − 2r = 4r`. ✓

**Why the family requires `2r` (even) many logical qubits.** Per [GOY §III,
p.3]: *"Note that it is the requirement that the two many-body stabilizer
generators commute that forces the total number of logical qubits in the
code to be even."* Specifically, `XBig` and `ZBig` overlap at `{qubit_0 j :
j ∈ Fin (2r)}` (every (i,0) qubit), giving anticommutation count `2r`,
which must be even. The paper's `k` (our `r`) is unconstrained in
parity, but `2k` (our `2r`) being even is the key.

## Logical operators

Per [GOY Eq. (4), §III, p.3], the single-body logical operators are:

```
X̄_i = X(i,x) X(i,0)
Z̄_i = Z(i,0) Z(i,z)
```

In our Lean (for `i : Fin (2r)`):

```
logicalX i := X at qubits {qubit_x i, qubit_0 i} = {3i, 3i+1}     (weight 2)
logicalZ i := Z at qubits {qubit_0 i, qubit_z i} = {3i+1, 3i+2}   (weight 2)
```

**These are the natural single-body logicals — both have weight exactly 2**,
which is the property that motivated the paper's construction. Per [GOY
§III, p.3, after Eq. (5)]: *"all single body interactions are limited to
the three qubits comprising the logical qubit, while all couplings involve
only the (i, 0) qubits."*

### Two-body logical operators (from [GOY Eq. (5)])

The paper also provides simplified two-body logicals via stabilizer-group
equivalence, exploiting that `X(i,x) X(j,x)` is in the stabilizer:

```
X̄_i X̄_j = X(i,0) X(j,0)
Z̄_i Z̄_j = Z(i,0) Z(j,0)
```

We **do not formalize the two-body forms** — they are derived consequences,
not needed for the `StabilizerCode` packaging. We use only Eq. (4) above for
the logical-operator definitions in our `LogicalQubitOps` family.

## Codespace

The code subspace is the simultaneous +1 eigenspace of all `4r` stabilizer
generators. We do not characterize it as an explicit basis — instead, its
dimension `2^(2r)` follows abstractly from `generators_independent` plus
the standard `2^(n−k)`-index theorem for an independent stabilizer
generator set on `n` qubits.

## By-hand verification of the (anti)commutation table

For Pauli operators `P = ⟨0, p⟩` and `Q = ⟨0, q⟩` with phase 0, the "number
of qubits where they anticommute" is the cardinality of `{i | (p i, q i) ∈
{(X,Z), (Z,X), (X,Y), (Y,X), (Y,Z), (Z,Y)}}`. They commute iff this
cardinality is even.

### Stabilizer commutation table

| Pair                          | Anticomm support                          | Size | Even? | Result   |
|-------------------------------|-------------------------------------------|------|-------|----------|
| `XLink i · XLink j`           | ∅ (both X-type)                          | 0    | ✓     | commute  |
| `XLink i · XBig`              | ∅ (XLink at {3i, 3(i+1)}, XBig at {0-,z-qubits}; disjoint roles, both X) | 0 | ✓ | commute |
| `ZLink i · ZLink j`           | ∅ (both Z-type)                          | 0    | ✓     | commute  |
| `ZLink i · ZBig`              | ∅ (similar; both Z-type)                  | 0    | ✓     | commute  |
| `XLink i · ZLink j`           | depends on overlap of {3i, 3(i+1)} (x-qubits) and {3j+2, 3(j+1)+2} (z-qubits) — disjoint qubit types ⇒ ∅ | 0 | ✓ | commute |
| `XLink i · ZBig`              | overlap of {3i, 3(i+1)} (x-qubits) with ZBig support {x,0-qubits across rows} — at qubits 3i and 3(i+1), both X(XLink) vs Z(ZBig) anticomm | 2 | ✓ | commute |
| `XBig · ZLink j`              | overlap of {0,z-qubits} (XBig) with {3j+2, 3(j+1)+2} (ZLink z-qubits) — at 3j+2 and 3(j+1)+2 both X(XBig) vs Z(ZLink) anticomm | 2 | ✓ | commute |
| `XBig · ZBig`                 | overlap of XBig {0,z}-roles with ZBig {x,0}-roles = {0}-role qubits = {3j+1 : j} | `2r` | ✓ | commute |

All stabilizer pairs commute. ✓

### Logical–stabilizer commutation table (for each `i : Fin (2r)`)

`logicalX i` has support `{3i, 3i+1}` (x- and 0-qubits of row i).
`logicalZ i` has support `{3i+1, 3i+2}` (0- and z-qubits of row i).

| Pair                          | Anticomm support             | Size | Even? | Result   |
|-------------------------------|------------------------------|------|-------|----------|
| `logicalX i · XLink j`        | ∅ (both X-type)             | 0    | ✓     | commute  |
| `logicalX i · XBig`           | ∅ (both X-type)             | 0    | ✓     | commute  |
| `logicalX i · ZLink j`        | Overlap = {3i, 3i+1} ∩ {3j+2, 3(j+1)+2}. Both elements of logicalX support are x- or 0-qubits (mod-3 in {0,1}); both elements of ZLink support are z-qubits (mod-3 = 2). Disjoint. | 0 | ✓ | commute |
| `logicalX i · ZBig`           | Overlap of {3i, 3i+1} with ZBig support {x-, 0-qubits} = {3i, 3i+1} ∩ {x-,0-qubits} = {3i, 3i+1} | 2 | ✓ | commute |
| `logicalZ i · XLink j`        | Overlap = {3i+1, 3i+2} ∩ {3j, 3(j+1)}. logicalZ has 0- and z-qubits (mod-3 ∈ {1,2}); XLink has only x-qubits (mod-3 = 0). Disjoint. | 0 | ✓ | commute |
| `logicalZ i · XBig`           | Overlap of {3i+1, 3i+2} with XBig support {0-, z-qubits} = {3i+1, 3i+2} | 2 | ✓ | commute |
| `logicalZ i · ZLink j`        | ∅ (both Z-type)             | 0    | ✓     | commute  |
| `logicalZ i · ZBig`           | ∅ (both Z-type)             | 0    | ✓     | commute  |

All logical-stabilizer pairs commute. ✓ (so logicals are in the centralizer)

### Logical pairwise (anti)commutation table

| Pair                           | Anticomm support                                | Size | Even? | Result      |
|--------------------------------|-------------------------------------------------|------|-------|-------------|
| `logicalX i · logicalX j`      | ∅ (both X-type)                                | 0    | ✓     | commute     |
| `logicalZ i · logicalZ j`      | ∅ (both Z-type)                                | 0    | ✓     | commute     |
| `logicalX i · logicalZ i`      | {3i+1} (qubit (i,0): X vs Z anticomm; qubit 3i: X vs I commute; qubit 3i+2: I vs Z commute) | 1    | ✗     | **anticommute** |
| `logicalX i · logicalZ j` (i≠j)| Both qubits of logicalX are in row i; both qubits of logicalZ are in row j. Distinct rows ⇒ disjoint. | 0 | ✓ | commute |

The **diagonal anticommutation count is 1** (the (i,0) qubit, where logicalX
has X and logicalZ has Z), giving the required ⊥ relation. ✓

### Why the diagonal anticommutation gives the canonical k=2r structure

For each pair of logical-qubit indices `(i, j) ∈ Fin (2r) × Fin (2r)`:

- `i = j`: `X̄_i ⊥ Z̄_i` (anticommute at qubit (i,0), the shared anchor).
- `i ≠ j`: `X̄_i Z̄_j = Z̄_j X̄_i` (disjoint row supports).
- All X̄·X̄ pairs commute (X-type).
- All Z̄·Z̄ pairs commute (Z-type).

This is exactly the canonical `LogicalQubitOps` table for a CSS code with
`k = 2r` independent logical qubits. ✓

## Distance proof

Per [GOY §III, p.3 final paragraph]: *"all single-physical-qubit Pauli
errors anticommute with at least one of the stabilizer generators, and are
therefore detectable by the code."*

This translates directly into `hasCodeDistance_two_of_anticommute_witness`
(PR #34, in `Framework/Core/CSS/CSSDistance.lean`):

1. Every weight-1 single-qubit Pauli anticommutes with **some** stabilizer
   generator ⇒ no weight-1 element is in the centralizer ⇒ d ≥ 2.
2. `logicalX 0` is a nontrivial weight-2 element of the centralizer ⇒ d ≤ 2.

So d = 2. ✓

### Weight-1 anti-witness function (per-qubit by role)

For `i : Fin (6r)` and `P ∈ {X, Y, Z}`, we exhibit a stabilizer generator
that anticommutes with `weightOneAt i P`. The witness depends on the role
of `i` (which is determined by `i.val mod 3`):

**Case `P ∈ {X, Y}`** (X or Y at qubit `i`, anticommutes with Z at `i`):

- If `i.val mod 3 = 0` (i.e., `i` is an x-qubit, `i = qubit_x j` for some `j`):
  Use `ZBig` (which has Z at all x- and 0-qubits, including this x-qubit).
- If `i.val mod 3 = 1` (i.e., `i` is a 0-qubit, `i = qubit_0 j`):
  Use `ZBig` (covers 0-qubits).
- If `i.val mod 3 = 2` (i.e., `i` is a z-qubit, `i = qubit_z j`):
  Use **some** `ZLink ℓ` that covers `i` — specifically `ZLink (j - 1)` if
  `j ≥ 1` else `ZLink 0` (covers qubits 0 and 1, including `j = 0`). The
  Z-link chain at z-qubits is `ZLink 0` covers {z-qubit 0, z-qubit 1},
  `ZLink 1` covers {z-qubit 1, z-qubit 2}, …, `ZLink (2r-2)` covers
  {z-qubit (2r-2), z-qubit (2r-1)}. So every z-qubit is covered by **at
  least one** ZLink — `ZLink 0` covers z-qubits 0 and 1; in general, for
  `j ∈ {1, ..., 2r-1}` the row `j`'s z-qubit is covered by `ZLink (j-1)`.

  **Subtlety**: when `r = 1`, 2r = 2, so the only `ZLink` is `ZLink 0`
  which covers z-qubits {0, 1} — both. For `r ≥ 2`, every z-qubit is
  in some `ZLink`'s support, by induction on `2r ≥ 2`.

**Case `P = Z`** (Z at qubit `i`, anticommutes with X at `i`):

- If `i.val mod 3 = 0` (x-qubit): Use some `XLink ℓ` covering `i`. Same
  Z-link/X-link symmetry: `XLink 0` covers x-qubits {0, 1}, …, `XLink (2r-2)`
  covers {2r-2, 2r-1}.
- If `i.val mod 3 = 1` (0-qubit): Use `XBig` (which has X at 0- and z-qubits).
- If `i.val mod 3 = 2` (z-qubit): Use `XBig` (covers z-qubits).

**Structural summary**: 6 cases (3 role-positions × 2 Pauli-classes); 4 of
them use the "big" stabilizers (`XBig`/`ZBig`) trivially; the remaining 2
(`x-qubit, Z-error`) and (`z-qubit, X-or-Y-error`) need to dispatch over
which `XLink`/`ZLink` covers the qubit.

For the **link dispatch**: each row `j ∈ Fin (2r)` has its x-qubit covered by:
- `XLink (j-1)` if `j ≥ 1` (X at x-qubit (j-1) and x-qubit j)
- `XLink j`     if `j ≤ 2r-2` (X at x-qubit j and x-qubit (j+1))

So row `0`'s x-qubit is covered by `XLink 0` only (no XLink (−1)); row
`2r-1`'s x-qubit is covered by `XLink (2r-2)` only. All interior rows are
covered by two XLinks; we canonically pick `XLink j` when `j < 2r-1` and
`XLink (2r-2)` for the last row. (Symmetric for z-qubits with ZLinks.)

## Theorems to formalize

The skeleton's theorem set follows `_TEMPLATE.lean`'s §1–§14 layout,
parametrized over `r` with `[Fact (1 ≤ r)]`.

### Index helpers

(`@[inline] private def`s)

- `qubit_x r i : Fin (6 * r)` for `i : Fin (2 * r)` — returns `⟨3 * i.val, ...⟩`
- `qubit_0 r i : Fin (6 * r)` for `i : Fin (2 * r)` — returns `⟨3 * i.val + 1, ...⟩`
- `qubit_z r i : Fin (6 * r)` for `i : Fin (2 * r)` — returns `⟨3 * i.val + 2, ...⟩`
- `linkIdx r i : Fin (2 * r)` for `i : Fin (2 * r - 1)` — embeds link index into qubit-row index (= `i.val`)
- `linkIdxSucc r i : Fin (2 * r)` for `i : Fin (2 * r - 1)` — embeds successor link index (= `i.val + 1`)

### T1: Z-type predicate for `ZLink` generators

For each `i : Fin (2r - 1)`, `IsZTypeElement (ZLink i)` (Z at two
specific qubits, I elsewhere).
[Source: derived from Eq. (3).]

### T2: Z-type predicate for `ZBig`

`IsZTypeElement ZBig` (Z at all x- and 0-qubits — i.e., role ∈ {0, 1};
I at z-qubits — role = 2). [Source: derived from Eq. (3).]

### T3: X-type predicate for `XLink` generators

For each `i : Fin (2r - 1)`, `IsXTypeElement (XLink i)`. Mirror of T1.

### T4: X-type predicate for `XBig`

`IsXTypeElement XBig` (X at all 0- and z-qubits). Mirror of T2.

### T5: Z-generators are all Z-type

`∀ g ∈ ZGenerators r, IsZTypeElement g`. Combines T1 + T2.

### T6: X-generators are all X-type

`∀ g ∈ XGenerators r, IsXTypeElement g`. Combines T3 + T4.

### T7: Cross-commutation (every Z-gen commutes with every X-gen)

`∀ z ∈ ZGenerators r, ∀ x ∈ XGenerators r, z * x = x * z`.

Four sub-cases (parametric over `i, j` link indices):

- T7a: `ZLink i · XLink j`: disjoint supports (z-qubits vs x-qubits, distinct mod-3 roles) ⇒ commute via `pauli_comm_componentwise` or empty-filter.
- T7b: `ZLink i · XBig`: overlap = {qubit_z i, qubit_z (i+1)} (both Z(ZLink) vs X(XBig), anticomm), count 2, even ⇒ commute.
- T7c: `ZBig · XLink j`: overlap = {qubit_x j, qubit_x (j+1)} (both Z(ZBig) vs X(XLink), anticomm), count 2, even ⇒ commute.
- T7d: `ZBig · XBig`: overlap = {qubit_0 j : j ∈ Fin (2r)} = 2r elements (Z(ZBig) vs X(XBig) at every 0-qubit), count 2r, even ⇒ commute.

[Source: the structural argument behind GOY §III, p.3 paragraph after Eq.
(3); paper does not spell out the filter cardinalities explicitly but
states the commutation requirement.]

### T8: All-pair commutation

`∀ g ∈ generators r, ∀ h ∈ generators r, g * h = h * g`. Standard
4-way `rcases` over Z-vs-X partition + CSS commutation lemmas + T7.

### T9: `−I` not in stabilizer subgroup

Standard CSS argument via `CSS.negIdentity_not_mem_closure_union` consuming
T5, T6, T7.

### T10: Generator list & set equality

`generatorsList r` is the explicit `List` form (Z-generators first, then
X-generators). `listToSet (generatorsList r) = generators r`.

### T11: Phase-zero generators

`AllPhaseZero (generatorsList r)`. All `4r` generators have phase 0 by
construction.

### T12: Generator independence (the hardest parametric proof)

`rowsLinearIndependent (generatorsList r)`. The `4r × 12r` check matrix
has the block-triangular structure of a chain code: see plan.md § T12 for
the detailed strategy. We expect ~50-80 LoC for this proof.

### T13: Bundled `StabilizerGroup (6 * r)`

Standard `mkStabilizerFromGenerators` packaging.

### T14: `stabilizerGroup_toSubgroup_eq`

Bridge between `stabilizerGroup.toSubgroup` and `Subgroup.closure generators`.

### T15: Logical X anticommutes Logical Z (diagonal)

For each `i : Fin (2r)`, `Anticommute (logicalX i) (logicalZ i)`. The
anticomm support is exactly `{qubit_0 i}` (cardinality 1, odd). Parametric
filter-equality argument.

### T16: Logical operators commute pairwise (off-diagonal)

- T16a: `logicalX i · logicalX j = logicalX j · logicalX i` (always — both X-type).
- T16b: `logicalZ i · logicalZ j = logicalZ j · logicalZ i` (always — both Z-type).
- T16c: For `i ≠ j`: `logicalX i · logicalZ j = logicalZ j · logicalX i`. Disjoint row supports.

### T17: Logical X in centralizer

`∀ i : Fin (2r), logicalX i ∈ centralizer (stabilizerGroup r)`.

Reduces to per-generator commutation:

- vs. `XLink j`: both X-type, trivial.
- vs. `XBig`: both X-type, trivial.
- vs. `ZLink j`: disjoint support (logicalX is on x- and 0-qubits, ZLink is on
  z-qubits) ⇒ commute.
- vs. `ZBig`: overlap = {qubit_x i, qubit_0 i} (count 2, even) ⇒ commute.

### T18: Logical Z in centralizer

`∀ i : Fin (2r), logicalZ i ∈ centralizer (stabilizerGroup r)`.

Symmetric to T17:

- vs. `ZLink j`: both Z-type, trivial.
- vs. `ZBig`: both Z-type, trivial.
- vs. `XLink j`: disjoint support (logicalZ on 0- and z-qubits, XLink on
  x-qubits) ⇒ commute.
- vs. `XBig`: overlap = {qubit_0 i, qubit_z i} (count 2, even) ⇒ commute.

### T19: `StabilizerCode (6 * r) (2 * r)` packaging

Bundle T10-T18 plus the `Fin (2r)`-indexed logical-cross-commute. The
`logical_commute_cross` field uses the parametric structural pattern from
`Iceberg/N.lean` (cannot `fin_cases ℓ` over `Fin (2r)` symbolically).

### T20: `stabilizerCode_toSubgroup_eq`

Bridge for the distance proof. Standard.

### T21: Weight-1 anticommute witness (the parametric distance step)

```
∀ i : Fin (6r), ∀ P : PauliOperator, P ≠ I →
  ∃ g ∈ generators r, Anticommute (weightOneAt i P) g
```

Strategy: trichotomy on `i.val mod 3` (qubit role), then dispatch over
`P ∈ {X, Y, Z}`:

- `(role 0 = x-qubit, P ∈ {X, Y})`: witness `ZBig` (Z at every x-qubit).
- `(role 0 = x-qubit, P = Z)`: witness `XLink (some index covering this qubit)`.
- `(role 1 = 0-qubit, P ∈ {X, Y})`: witness `ZBig`.
- `(role 1 = 0-qubit, P = Z)`: witness `XBig`.
- `(role 2 = z-qubit, P ∈ {X, Y})`: witness `ZLink (some index covering this qubit)`.
- `(role 2 = z-qubit, P = Z)`: witness `XBig`.

[Source: GOY §III, p.3 final paragraph — *"all single-physical-qubit Pauli
errors anticommute with at least one of the stabilizer generators."* The
mod-3 role decomposition is forced by the qubit indexing.]

### T22: `code_has_distance_two : HasCodeDistance stabilizerCode 2`

One-liner via `hasCodeDistance_two_of_anticommute_witness` (PR #34),
consuming T20 + T21 plus an explicit weight-2 witness (`logicalX 0`).

### T23: `StabilizerCodeWithDistance (6 * r) (2 * r) 2` packaging

Trivial wrapper from T19 + T22.

## Edge cases / convention notes

1. **`r = 0` excluded.** Without `[Fact (1 ≤ r)]`, `n = 0` and `k = 0`,
   giving a trivial empty code. We exclude via `[Fact (1 ≤ r)]`.

2. **`2 * r - 1` requires `r ≥ 1`.** Both `2r - 1` and `Fin (2r - 1)` use
   `Nat.sub`, which is well-defined for `r ≥ 1`. The link generators
   `XLink i, ZLink i` are indexed by `i : Fin (2r - 1)`, and at `r = 1`
   there is exactly one of each.

3. **0-based qubit indexing throughout.** Paper uses 1-based `i ∈ {1, ..., 2r}`;
   we use 0-based `i : Fin (2r)`. The translation is `paper(i) = lean(i-1)`.

4. **Phase conventions.** All generators and logical operators have
   `phasePower = 0`. No logical Y is defined (optional per `_TEMPLATE.lean §10`).

5. **`linkIdxSucc` requires `i.val + 1 < 2r`**, which is exactly the
   `Fin (2r - 1)` bound (since `i.val < 2r - 1` gives `i.val + 1 ≤ 2r - 1 < 2r`).
   When `r = 1` and `i.val ∈ Fin (2r - 1) = Fin 1`, only `i.val = 0` and
   `i.val + 1 = 1 < 2`. ✓

6. **Distance proof method: `hasCodeDistance_two_of_anticommute_witness`
   (PR #34).** This is the canonical closer; see plan.md § T22.

7. **Cross-check at r=1 (the key sanity check before Stage 4).**
   See § "Relation to SixQubit_6_2_2.lean" below.

## Relation to `Codes/Small/SixQubit_6_2_2.lean`

At `r = 1`, this parametric family gives `[[6, 2, 2]]`, which is the same
**physical code subspace** as `SixQubit_6_2_2.lean` (Knill's C_6
presentation) — but the **stabilizer generator set is different**.

### GOY presentation at `r = 1` (this file)

n = 6 qubits, indexed as:
```
0 = (0,x)  1 = (0,0)  2 = (0,z)
3 = (1,x)  4 = (1,0)  5 = (1,z)
```

Generators (4 total: 2 weight-2 + 2 weight-4):

```
XLink 0 = X _ _ X _ _      (X at qubits 0, 3)              weight 2
XBig    = _ X X _ X X      (X at qubits 1, 2, 4, 5)        weight 4
ZLink 0 = _ _ Z _ _ Z      (Z at qubits 2, 5)              weight 2
ZBig    = Z Z _ Z Z _      (Z at qubits 0, 1, 3, 4)        weight 4
```

Logical operators (`Fin 2` logicals):

```
logicalX 0 = X X _ _ _ _   (X at qubits 0, 1)             weight 2
logicalX 1 = _ _ _ X X _   (X at qubits 3, 4)             weight 2
logicalZ 0 = _ Z Z _ _ _   (Z at qubits 1, 2)             weight 2
logicalZ 1 = _ _ _ _ Z Z   (Z at qubits 4, 5)             weight 2
```

### Knill C_6 presentation (existing `SixQubit_6_2_2.lean`)

Generators (4 total: all weight 4):

```
S_Z1 = Z Z Z Z _ _         (Z at qubits 0, 1, 2, 3)        weight 4
S_Z2 = Z Z _ _ Z Z         (Z at qubits 0, 1, 4, 5)        weight 4
S_X1 = X X X X _ _         (X at qubits 0, 1, 2, 3)        weight 4
S_X2 = X X _ _ X X         (X at qubits 0, 1, 4, 5)        weight 4
```

Logical operators (also `Fin 2` logicals):

```
logicalX_1 = _ _ X X _ _   (X at qubits 2, 3)              weight 2
logicalX_2 = _ X _ X X _   (X at qubits 1, 3, 4)           weight 3
logicalZ_1 = Z _ _ Z Z _   (Z at qubits 0, 3, 4)           weight 3
logicalZ_2 = _ _ _ _ Z Z   (Z at qubits 4, 5)              weight 2
```

### Are the two codes the same?

**Yes**, in the sense of describing the same code subspace (the EC Zoo
entry explicitly states GOY at `r = 1` is the C_6 code). The two
**stabilizer groups** generate the same subgroup of the Pauli group on 6
qubits — the GOY stabilizers can be expressed as products of Knill's
stabilizers and vice versa:

- `S_Z1 = Z Z Z Z _ _` = `ZBig · ZLink 0`? Let's check:
  - `ZBig = Z Z _ Z Z _` at qubits {0,1,3,4}
  - `ZLink 0 = _ _ Z _ _ Z` at qubits {2,5}
  - Product = `Z Z Z Z Z Z` — **all-Z on 6 qubits**, not `S_Z1`!

So the equality of subgroups is **not as immediate as a product of two
elements**. We need:

- The GOY stabilizers `{XLink 0, XBig, ZLink 0, ZBig}` and the Knill
  stabilizers `{S_Z1, S_Z2, S_X1, S_X2}` generate **the same 16-element
  subgroup of `Pauli^⊗6`**. This is true (per EC Zoo) but is NOT
  formalized in this PR — it would require either a Clifford-equivalence
  argument or an explicit subgroup-equality proof. We **do not prove
  this equivalence**; the two formalizations coexist as separate Lean
  objects (mirroring `Iceberg/N.lean` ↔ `FourQubit_4_2_2.lean`).

### Cross-check: GOY r=1 commutation table consistency

At r=1, we manually verify (already done above in this document):

- All 4 stabilizers pairwise commute. ✓
- All 4 logicals × 4 stabilizers commute (16 pairs). ✓
- `logicalX 0 ⊥ logicalZ 0` and `logicalX 1 ⊥ logicalZ 1`. ✓
- `logicalX 0 · logicalZ 1` and `logicalX 1 · logicalZ 0` commute (disjoint
  row supports). ✓
- All X̄·X̄ and Z̄·Z̄ commute. ✓
- Every weight-1 single-qubit Pauli anticommutes with some stabilizer (6
  qubits × 3 Paulis = 18 cases). ✓ (by trichotomy + GOY witness rules above)
- `logicalX 0` has weight 2 (X at qubits 0 and 1). ✓

**Verdict**: the GOY presentation at r=1 is internally consistent and
correctly captures a `[[6, 2, 2]]` code. The codespace-level equivalence
to Knill's C_6 is asserted (per EC Zoo) but not formally bridged.

### What this comparison rules out

If the GOY r=1 commutation table failed any of the above checks, our spec
would be wrong (paper extraction error). Since every check passes by
direct mod-3 case analysis, the spec is sound.

## Source-availability note

The construction was extracted directly from
[arxiv:1309.1674](https://arxiv.org/abs/1309.1674), specifically:

- **Eq. (3)** (page 3): explicit stabilizer construction.
- **Eq. (4)** (page 3): single-body logical operators.
- **§III, p.3 final paragraph**: distance argument (every weight-1 Pauli
  anticommutes with some stabilizer).
- **Fig. 2** (page 3): visual layout of the linear arrangement (rows of
  three qubits each, with link-stabilizers connecting adjacent rows).

The paper does NOT explicitly verify the r=1 = C_6 equivalence — that's
asserted by the EC Zoo entry. Our formalization respects this: we treat
the GOY family and Knill's C_6 as separate Lean objects.

The only **convention choice** we make is:

- 0-based vs. 1-based qubit indexing (we use 0-based, paper uses 1-based;
  isomorphic up to relabeling).
- Row-major qubit indexing within `Fin (6r)` (we put (i,x), (i,0), (i,z)
  at positions 3i, 3i+1, 3i+2; paper's Fig. 2 puts them in column-major
  order x → 0 → z, but the rows are independent so this is also
  isomorphic).

These conventions are documented at the top of `N.lean`.
