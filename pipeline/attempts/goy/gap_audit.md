# Gap audit: Ganti-Onunkwo-Young `[[6r, 2r, 2]]`

## Repo gaps (this code surfaces / requires new abstractions)

### Gap 1: Variable-weight stabilizers in a single CSS family — the **first instance**

**Status: NOT a missing API gap, but a NEW PATTERN in the repo.**

GOY is the first parametric CSS code in the repo with stabilizers of **two
distinct weights** (weight-2 link generators + weight-4r big generators).
All prior parametric formalizations (iceberg, toric, rotated surface,
repetition) have uniform-weight stabilizers per family.

**Consequence for the formalization**:
- The cross-commute proofs split into 4 cases (T7a-d), each with a
  different overlap-cardinality pattern.
- The all-pair commute lemma `T8` dispatches over a 4-way `rcases`
  instead of 2-way (`Z-generator vs X-generator`, plus the further split
  on `link vs big` within each).
- The `generators_commute` proof is roughly 2x the size of iceberg's.

**Resolution**: not blocking — just longer. Mitigation: keep the 4
sub-commute lemmas as `private lemma`s so the dispatch in T7 is mechanical.

### Gap 2: Mod-3 trichotomy on qubit roles — the **first occurrence**

**Status: NEW PATTERN, would be worth promoting to `Geometry/` after this lands.**

GOY's row-major qubit indexing means `q.val mod 3` decomposes `Fin (6r)`
into the three qubit-roles (x, 0, z). This decomposition appears in:
- `qubit_x` injectivity proofs.
- T2, T4 (`ZBig`, `XBig` are Z/X-type).
- T7b, T7c, T7d (cross-commute filter cardinalities).
- T17, T18 (logicals in centralizer).
- T21 (weight-1 anti-witness — the trichotomy dispatch).

**Possible follow-up PR**: extract a `Geometry/ThreeQubitRow.lean` with
helpers like `qubit_role_of`, `coveringLink`, etc. Not blocking — for now,
the helpers live inside `GOY/N.lean`.

### Gap 3: Parametric "all-X commutes with all-Z when intersection size is 2r" lemma

**Status: missing, will prove inline (same call as iceberg's Gap 1).**

The iceberg formalization noted (`iceberg/gap_audit.md:7-26`) that
`SymplecticInner.lean` has only the `allX_allZ_anticommute (n : ℕ) (hn : Odd n)`
direction, not the dual "Even count ⇒ commute". GOY needs the latter for
T7d (ZBig vs XBig at 2r anticommutation positions).

**Resolution**: prove inline in T7d using `pauli_comm_even_anticommutes` +
`Finset.card_image_of_injective` + `Even (2 * r)`. Same approach iceberg
took. ~30 LoC inline.

### Gap 4: `Fin (2 * r - 1) ↪ Fin (2 * r)` coercion (link → row)

**Status: no clean reusable helper; explicit construction needed.**

The lifts `linkIdx : Fin (2 * r - 1) → Fin (2 * r)` (= `i.val`) and
`linkIdxSucc : Fin (2 * r - 1) → Fin (2 * r)` (= `i.val + 1`) are needed
in every link generator's definition and every link-related commutation
proof.

**Decision**: use `@[inline] private def`s in the GOY file, same as
iceberg's `logIdx` helper. The bound proofs `omega`-discharge from
`i.isLt` + `Fact.out`.

**Possible follow-up**: if a third parametric family needs similar
"link/edge → vertex" lifts (toric does, but uses a different abstraction),
promote to `Geometry/`.

### Gap 5: `coveringXLink`, `coveringZLink` — row-to-covering-link functions

**Status: GOY-specific, no analog elsewhere.**

T21 (weight-1 anti-witness) needs: "for every row `j : Fin (2 * r)`, there
exists an `XLink ℓ` whose support includes `qubit_x j`." The natural
function is:

```lean
private def coveringXLink (r : ℕ) [Fact (1 ≤ r)] (j : Fin (2 * r)) :
    Fin (2 * r - 1) :=
  if h : j.val < 2 * r - 1 then
    ⟨j.val, h⟩
  else
    ⟨2 * r - 2, by have := Fact.out (p := (1 ≤ r)); omega⟩
```

When `j.val < 2r - 1`: `XLink j` covers `{qubit_x j, qubit_x (j+1)}` — includes `qubit_x j`. ✓
When `j.val = 2r - 1`: `XLink (2r - 2)` covers `{qubit_x (2r-2), qubit_x (2r-1)}` — includes `qubit_x j`. ✓

(Symmetric for `coveringZLink`.)

**Risk**: this `if-then-else` introduces a case split in every use of
`coveringXLink`. Each downstream proof must handle both branches.
**Mitigation**: define a covering-statement lemma `coveringXLink_supports_qubit_x`
that returns the anticomm witness directly, with the case split absorbed
inside its proof.

**Possible follow-up**: if a future parametric code needs similar covering
maps, promote.

### Gap 6: `coveringXLink` may need to bridge boundary rows differently

**Status: minor design choice, not a structural gap.**

At `r = 1`: `2r - 1 = 1`, so only one link (`XLink 0`). Both rows 0 and 1
are covered by `XLink 0`. The `if h` branch fires only when `j = 0`; for
`j = 1` we need the `else` branch picking `XLink 0` (since `2r - 2 = 0`).
So the `else` branch is `XLink 0` at r=1. Consistent.

At `r = 2`: `2r - 1 = 3`, so links are `XLink 0, 1, 2`. Rows 0, 1, 2, 3.
- Row 0: `XLink 0` (j.val = 0 < 3). ✓
- Row 1: `XLink 1` (j.val = 1 < 3). ✓
- Row 2: `XLink 2` (j.val = 2 < 3). ✓
- Row 3: `XLink 2` (j.val = 3, not < 3 — else branch picks 2r-2 = 2). ✓

So the construction is correct. Edge cases discharged.

### Gap 7: Parametric `weight_logicalX` (and `weight_logicalZ`) helpers

**Status: probably missing.**

T22 needs `weight (logicalX r 0) = 2`. Iceberg's analog
(`Iceberg/N.lean:725-744`) computes this directly via support cardinality.
We adapt the same pattern, with the support being `{qubit_x 0, qubit_0 0}
= {0, 1}` instead of iceberg's `{logIdx i, xAnchor m}`.

**Resolution**: inline calculation, ~15 LoC.

### Gap 8: 4-way generator dispatch in centralizer proofs (T17, T18)

**Status: no abstraction, just longer dispatches than iceberg's 2-way.**

Iceberg's T13 (`logicalX_mem_centralizer`) dispatches over 2 generators
(`S_Z m` and `S_X m`). GOY's T17 needs to dispatch over **4 generator
types** (ZLink, ZBig, XLink, XBig), with the ZLink and XLink cases each
being a `∀ j : Fin (2r-1)`. This requires:

```lean
rcases hs with hgZ | hgX
· rcases hgZ with hgZLink | hgZBig
  · obtain ⟨ℓ, rfl⟩ := hgZLink  -- ZLink ℓ
    exact (logicalX_commutes_ZLink r i ℓ).symm
  · rcases (by simpa [ZBigGenerators] using hgZBig) with rfl
    exact (logicalX_commutes_ZBig r i).symm
· rcases hgX with hgXLink | hgXBig
  · obtain ⟨ℓ, rfl⟩ := hgXLink
    exact (logicalX_commutes_XLink r i ℓ).symm
  · rcases (by simpa [XBigGenerators] using hgXBig) with rfl
    exact (logicalX_commutes_XBig r i).symm
```

**Resolution**: standard mechanical dispatch. ~40 LoC per centralizer
theorem (T17, T18). Total ~80 LoC vs. iceberg's ~30 LoC for both.

### Gap 9: Generator independence proof at parametric `4r × 12r` scale (T12)

**Status: HARDEST piece. NEW PATTERN.**

The check matrix has block-diagonal structure (X-side and Z-side are
independent), and within each block we need to prove a `2r × 6r` matrix is
linearly independent. The structure is:

```
[Z-block of M_Z, 2r rows × 6r columns]
ZLink 0:  ones at z-qubit-cols {3, 5}                       [z-qubit cols are 2, 5, 8, ..., 6r-1]
ZLink 1:  ones at z-qubit-cols {5, 8}
...
ZLink (2r-2): ones at z-qubit-cols {6r-4, 6r-1}
ZBig:     ones at all x- and 0-qubit-cols
```

This is a **chain incidence matrix** (the ZLinks form a path on z-qubits)
plus one extra row in a different block (the ZBig in the x- and 0-block).

**Strategy** (parametric chain-independence cascade):
1. Specialize the `∑ a_i (ZLink i) + b * ZBig = 0` equation at any
   x-qubit column: only `ZBig` has a 1, so `b = 0`.
2. Specialize at z-qubit 0: only `ZLink 0` has a 1, so `a_0 = 0`.
3. Specialize at z-qubit 1: only `ZLink 0` and `ZLink 1` have 1's. Since
   `a_0 = 0`, this gives `a_1 = 0`.
4. ...cascade by induction...
5. Specialize at z-qubit `i`: gives `a_{i-1} + a_i = 0`, so `a_i = 0`.

**Risk**: this requires a Nat-induction on `i.val` for `i ∈ Fin (2r-1)`.
Standard pattern but verbose. Estimated ~80-100 LoC.

**Mitigation if this is too long**: defer T12 as a sorry blocked on
`chain_independence_n` helper (to add to `BinarySymplectic/`). The
remaining theorems can still close in Stage 4.

### Gap 10: Multi-Z mixed-trichotomy weight-1 anti-witness (NEW PATTERN)

**Status: extension of the C_6 multi-Z trichotomy pattern from
`docs/lean-patterns.md`.**

C_6's weight-1 anti-witness uses a trichotomy `{0,1} | {2,3} | {4,5}` to
pick which Z-stabilizer covers the qubit. GOY's trichotomy is on
`i.val mod 3`:
- `mod = 0` (x-qubits): `ZBig` for X/Y errors; some `XLink` for Z errors.
- `mod = 1` (0-qubits): `ZBig` for X/Y; `XBig` for Z.
- `mod = 2` (z-qubits): some `ZLink` for X/Y; `XBig` for Z.

Two of the six (mod, Pauli) cases involve **finding a covering link** (a
`ZLink` or `XLink` whose support includes the qubit). This is a new
combinatorial step relative to C_6 and iceberg. **The `coveringXLink` /
`coveringZLink` helpers handle this**.

**Resolution**: ~150 LoC across helper definitions, anticomm-for-cover
lemmas, and the trichotomy dispatch.

## Mathlib gaps (lemmas not in mathlib v4.30)

**None expected.** The parametric proofs use:

- `Finset.univ.filter`, `Finset.card`, `Finset.card_singleton`,
  `Finset.card_empty`, `Finset.card_insert_of_notMem`,
  `Finset.card_image_of_injective`, `Finset.image` — all standard.
- `Even`, `Nat.even_two_mul`, `even_two` — standard.
- `Fin.val_eq_val`, `Fin.ext`, `Fin.castLE` — standard.
- `Nat.sub` arithmetic via `omega` — standard.
- `Nat.div_lt_iff_lt_mul`, `Nat.mod_lt` — standard, used at T21 for
  decomposing `i.val` as `3 * (i.val / 3) + i.val % 3`.

No new mathlib lemma is required.

## Likely "BLOCKED(<reason>)" sorries

**At most one anticipated**: T12 (generator independence) if the chain
induction proves intractable inline. The proof is ~80-100 LoC of careful
Nat-induction on `Fin (2r-1)` cascading per-column constraints. If a
project helper `chainIndependence_n` is added, T12 becomes a one-liner;
without one, the proof is mechanical but long.

**Decision**: attempt T12 inline. If after ~3 hours of Stage-4 work it
isn't closed, defer as a `BLOCKED(chain-independence-n-helper)` sorry and
land the rest of the file.

All other theorems should close with current infrastructure + the
inline-proven parametric lemmas in the GOY file. The other risks are
about LoC budget and proof-engineering effort, not about missing
abstractions.

## Anticipated structural challenges from the task spec

The task spec listed four anticipated trouble spots:

### Challenge 1: Variable-weight stabilizers

**Confirmed.** 4 generator types (2 link types + 2 big types), giving
4 distinct cross-commute filter cardinalities. See § Gap 1.

**Mitigation**: 4 private sub-lemmas (T7a, T7b, T7c, T7d), with explicit
filter equalities. ~50 LoC each = 200 LoC for T7 total.

### Challenge 2: k = 2r logicals parametrically

**Confirmed.** `Fin (2r)` cannot be `fin_cases`'d when `r` is symbolic.

**Mitigation**: use Iceberg's structural-refine pattern (T15 in
`Iceberg/N.lean:628-633`): state T16a, T16b "for all i, j" (no `hij`
hypothesis), T16c "for i ≠ j", and combine via `refine ⟨_, _, _, _⟩`.

### Challenge 3: Weight-1 anti-witness function

**Confirmed.** GOY's stabilizer supports cover qubits via a 3-way pattern:

- **Big stabilizers**: `ZBig` covers all x- and 0-qubits; `XBig` covers all
  0- and z-qubits. Together they cover every qubit except for the cases
  where the qubit has the "wrong" Pauli.
- **Link stabilizers**: `ZLink` and `XLink` cover z- and x-qubits
  respectively, but each link covers only 2 qubits.

So the witness depends on both the qubit role (mod 3) and the Pauli (X/Y vs
Z). 6 sub-cases. 2 of those need a link-covering function (see Gap 5).

**Mitigation**: define `coveringXLink`, `coveringZLink` with `if-then-else`
on row index, plus 4 helper lemmas
`weightOneAt_*_anticomm_*Link`/`*Big`. Trichotomy + match-on-Pauli at the
top-level. ~150 LoC.

### Challenge 4: r=1 specialization consistency

**Verified by hand** in `informal_spec.md` § "Cross-check: GOY r=1
commutation table consistency". Every commutation pair, every weight-1
case, and every weight-2 logical witness checks out at r=1.

**The GOY r=1 stabilizer group is NOT identical (set-equal) to the Knill
C_6 stabilizer group**, but they generate the same Pauli-group-closure
(both stabilize the same `2^2`-dimensional codespace). We do NOT prove
this equivalence at the formal-Lean level; the two formalizations coexist
as separate Lean objects (mirroring `RepetitionCode3.lean` ↔
`RepetitionCodeN.lean` and `FourQubit_4_2_2.lean` ↔ `Iceberg/N.lean`).

## Architectural / future-cleanup notes

1. **Promote `Geometry/ThreeQubitRow.lean`** in a follow-up PR if a second
   3-qubits-per-row code appears (the "morphed simplex codes" in the
   catalog have similar structure).

2. **Promote `coveringLink` to `Geometry/PathCovering.lean`** if a second
   parametric chain-graph code (e.g., a 1D color code) appears.

3. **Promote `allX_allZ_commute_of_even_count`** to `SymplecticInner.lean`
   in a cleanup PR (per iceberg's Gap 1 mirror). After this PR lands,
   that helper would shorten 3 lemmas in `goy/N.lean` (T7d, T17 vs ZBig, T18 vs XBig).

4. **Promote the mod-3 trichotomy weight-1 anti-witness** to
   `docs/lean-patterns.md` after Stage 4. The current `lean-patterns.md`
   has the multi-Z **disjoint** pattern (CSS_4_1_2) and the multi-Z
   **overlapping** pattern (C_6 trichotomy). GOY adds a **mod-N partition
   pattern**, where the qubits' roles decompose cleanly via modular
   arithmetic.

5. **Document the "parametric `Fin (2 * r - 1)` indexing"** in the
   `Iceberg/N.lean`-style note on parametric `Fin` proofs (the patterns
   page already has it under "Parametric code families").

6. **`weight_logicalX r 0` / `weight_logicalZ r 0`** could be unified into
   a single "weight of two-set Pauli" helper if a third parametric
   weight-2 code appears.
