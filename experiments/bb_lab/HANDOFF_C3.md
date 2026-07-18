# bb_lab Handoff C-v3 — narrow to elementary-abelian G_odd
> **[Historical research record — extracted 2026-07-18 from the retired
> orchestration branch `bb-lab-v0` during branch cleanup; never previously
> merged.]** This is an original proposal/handoff document (2026-05-26) for one
> phase of the round-1 C-series (weight-aware Jacobson-radical filtration). The
> executed deliverables have long been on main — `notes/Cv1_*.md`,
> `notes/Cv2_*.md`, `notes/Cv3_*.md`, `notes/T3_CV3_*.md`,
> `notes/Cv4_R4_falsified.md`, and
> `pipeline/attempts/bb_distance_conjecture_radical_weight{,_narrow,_narrow_tier3}/`
> — and cite this document by section throughout; it is extracted to repair
> those references and preserve the proposal-side record (priors, stop
> conditions, alternative formulations). The conjecture line it proposes was
> ultimately **falsified** (C-v2 by corpus/Bravyi sweep; C-v3-as-tight by
> Tier-3 batteries; R1+R4 by the Z₃×Z₁₅ adversary). Note: references here to
> "HANDOFF.md §6l" mean an elementary-abelian-G_odd write-up that was never
> merged; that content lives in
> `pipeline/attempts/bb_distance_conjecture_radical_weight/result.md`, while
> main's actual `HANDOFF.md` §6l (from the later round-2 line) is a different
> obstruction (Cayley-spectral vacuity). Nothing here is a live task.


C-v2 produced the **sharpest structural diagnostic** in the entire
program. The primary conjecture was falsified universally (85.2%
corpus violations), **but the violations are confined to a
structurally identifiable subset**, and the conjecture survives
cleanly on the complement — which includes gross. Your job is to
test the *narrowed* form on its proper domain and, if it survives,
hand off to C-v4 (formal proof).

Required reading order: `HANDOFF.md` (§§6h–6l) → `HANDOFF_C.md`
→ `HANDOFF_C2.md` → the C-v2 deliverable notes (`Cv1_*.md`,
`Cv2_*.md`) → this document.

---

## 1. What C-v2 found

The primary conjecture was

  `d_X ≥ (1/c) · min_O min(w_1(A, O), w_1(B, O))`

where `c = [G_a : G_a ∩ G_b]` is the Lin-Pryadko index.

**Corpus sweep**:

| metric | value |
|---|---|
| rows tested | 3 894 |
| violations | 3 319 (85.2%) |
| **violations at c=1** | **3 148 / 3 245 (97%)** |
| **violations at c≥3** | **0 / 74 (0%)** |
| tight | 213 |

**Bravyi table**:

| code | G | G_odd | d | bound | verdict |
|---|---|---|---|---|---|
| bb_72_12_6   | Z_6 × Z_6   | **Z_3 × Z_3** | 6  | 6  | tight |
| bb_90_8_10   | Z_15 × Z_3  | **Z_3 × Z_3 × Z_5** (= Z_3 × Z_15) | 10 | 10 | tight |
| bb_108_8_10  | Z_9 × Z_6   | **Z_9 × Z_3**       | 10 | 12 | **VIOLATES** |
| gross        | Z_12 × Z_6  | **Z_3 × Z_3**       | 12 | 12 | tight |
| bb_288_12_18 | Z_12 × Z_12 | **Z_3 × Z_3**       | 18 | 18 | tight |

**The distinguisher**: bb_108's `G_odd = Z_9 × Z_3` is **cyclic
prime-power**. The other 4 Bravyi codes' `G_odd` are
**elementary abelian** (in fact `Z_3 × Z_3` for three of them; for
bb_90, `Z_3 × Z_15`, which has elementary-abelian 3-part).

The factor-of-3 between `w_1 = 36` and `d = 12` is a coincidence
of the elementary-abelian structure, **not** a general theorem.

See `HANDOFF.md §6l` for the canonical write-up.

---

## 2. The narrowed conjecture (your falsification target)

For a BB code `BB(G, A, B)`:

> **If `G_odd` is elementary abelian** — that is, `G_odd ≅ (Z_p)^k`
> for some prime `p` and some `k ≥ 1` — then
>
> `d_X(BB(G, A, B)) ≥ (1/c) · min_O min(w_1(A, O), w_1(B, O))`,
>
> where `c = [G_a : G_a ∩ G_b]` and `w_1` is C-v1's invariant.

**Plug-in for gross**: `G_odd = Z_3 × Z_3` is elementary abelian
(p=3, k=2). Conjecture applies, predicts `d ≥ 12`. ✓

**Why this might be true**:
- Elementary abelian `G_odd` means F₂[G_odd] has a particularly
  clean Wedderburn decomposition into copies of `F_{2^d}` for
  small d (`d` divides `2^k − 1`).
- The Jacobson-radical structure of F₂[G] is dictated by the
  2-Sylow part `G_2`. For elementary abelian `G_odd`, the
  isotypical components of F₂[G] each have **uniform structure
  across all primitive idempotents** — which is why `w_1 = 36`
  is the same on every vanishing orbit for gross.
- The factor of `c` then emerges from the support-subgroup
  structure (Lin–Pryadko's framework, applied to the
  isotypical components instead of the whole code).

**Why it might fail on the elementary-abelian subset**: the
clean structure above is "necessary but maybe not sufficient" —
there could be elementary-abelian-G_odd BB codes in the corpus
where the conjecture still doesn't hold, distinguished by a
finer feature (e.g., the structure of `G_2`, or some specific
relation between `supp(A)` and `supp(B)`). The corpus sweep tells
you.

---

## 3. Your specific tasks

### T C-v3.1 — Implement the elementary-abelian-G_odd classifier

Add to `src/bb_lab/degeneracy.py` (extending the existing module,
not modifying it destructively):

- `g_odd_decomposition(G: AbelianGroup) -> tuple[int, ...]`:
  returns the orders of the cyclic factors of `G_odd` (the
  max-odd-order quotient). For G = Z_12 × Z_6, `G_odd = Z_3 × Z_3`,
  returns `(3, 3)`. For G = Z_9 × Z_6, `G_odd = Z_9 × Z_3`,
  returns `(9, 3)`.
- `is_g_odd_elementary_abelian(G: AbelianGroup) -> bool`:
  returns True iff `G_odd` is elementary abelian. `g_odd_decomposition`
  returns `(p, p, ..., p)` for some prime `p` — i.e., all factors
  equal and prime.
- `g_odd_elementary_prime(G: AbelianGroup) -> int | None`:
  returns `p` if `G_odd ≅ (Z_p)^k`, else None.

Add tests in `tests/test_degeneracy.py`:
- `Z_12 × Z_6` → G_odd `(3, 3)` → elementary abelian, p=3.
- `Z_9 × Z_6` → G_odd `(9, 3)` → NOT elementary abelian.
- `Z_6 × Z_6` → G_odd `(3, 3)` → elementary abelian, p=3.
- `Z_15 × Z_3` → G_odd `(3, 15)` — careful: 15 = 3·5, so primary
  decomposition gives `Z_3 × Z_3 × Z_5`. Decision: define
  "elementary abelian" as "all primary parts are elementary abelian
  in their respective primes" OR "exactly one prime divides
  G_odd." Pick the version consistent with the C-v2 finding (bb_90
  was tight) — most likely the second: G_odd is `(Z_p)^k` for
  *one* prime `p`. Document which.

### T C-v3.2 — Restricted corpus sweep

Write `scripts/cv3_restricted_sweep.py`:

1. Read corpus via `Corpus(read_only=True)`.
2. Filter to rows where `is_g_odd_elementary_abelian(G)` is True.
   Report the count.
3. For each such row, compute `bb_radical_bound(A, B, G)` (from
   C-v2 in `radical_weight.py`).
4. Count violations. **Zero violations is the bar.**
5. Per-(G_odd-prime, k) breakdown of tightness rate.

Save to `notes/Cv3_restricted_sweep.md`.

### T C-v3.3 — Bravyi-table verification

Re-run on all 5 Bravyi instances:

| code | G_odd | elementary abelian? | conjecture applies? | bound | actual d | verdict |

Expected from C-v2: bb_72_12_6, bb_90_8_10, gross, bb_288_12_18
satisfy the hypothesis and are tight. bb_108_8_10 doesn't satisfy
the hypothesis (so doesn't disprove anything). Confirm.

### T C-v3.4 — Z_4 × Z_6 anomaly investigation

C-v2 flagged this subset as showing 65% tightness despite NOT
having elementary-abelian G_odd (G_odd = Z_3 there, rank 1).

Question to answer: is this a genuinely separate domain (a
*second* clean conditional theorem with a different hypothesis)?
Possible explanations:
- "rank-1 G_odd" is its own clean class with a different bound
  shape.
- The c definition collapses here in an interesting way.
- It's actually consistent with the elementary-abelian
  hypothesis (Z_3 IS technically elementary abelian, just k=1).

If the third option: **the elementary-abelian hypothesis includes
rank-1 G_odd**, and the conjecture should be tested on Z_4 × Z_6
under the same statement. If it survives, the domain widens.

Save to `notes/Cv3_z4xz6_anomaly.md`.

### T C-v3.5 — Tightness characterization on the restricted domain

If C-v3.2 shows zero violations, characterize *where the bound is
tight vs. loose* within the elementary-abelian-G_odd subset.
Decision-tree classifier on the survivors, as in T2.1.

The tight cases are the natural domain for **C-v4** (formal proof):
restrict the theorem to (elementary-abelian-G_odd ∧ structural-feature-X),
prove it, and you have a Lean theorem covering gross.

Save to `notes/Cv3_tightness.md`.

### T C-v3.6 — Verdict + pipeline artifact

Create `pipeline/attempts/bb_distance_conjecture_radical_weight_narrow/`
with `state.yaml`, `hypothesis.md`, `evidence.md`, `result.md`.

Possible verdicts:

- **survives-tight-on-gross-and-clean** (zero corpus violations,
  bound matches all 4 Bravyi codes in the hypothesis domain, gross
  bound = 12). → **C-v4 handoff** for formal proof.
- **survives-tight-on-gross-but-with-residuals** (gross is tight,
  but some other elementary-abelian-G_odd corpus rows violate or
  are extremely loose). Document the residuals; characterize the
  refined condition; iterate.
- **survives-but-loose-on-gross** (no violations, but gross bound
  < 12). Document; investigate alternatives in HANDOFF_C2 §5
  again within the restricted domain.
- **falsified-on-restricted-domain** (some elementary-abelian-G_odd
  corpus row violates). Document the violator concretely. The
  bb_108-style obstruction reappears in a different form;
  document as §6m and shelve unless a further refinement is
  obvious.

---

## 4. The Z_4 × Z_6 anomaly is the most strategically interesting outcome

If the Z_4 × Z_6 65%-tightness pattern turns out to be *the same
conjecture* (because Z_3 is technically elementary abelian with
k=1), then C-v3's restricted domain is much wider than just
gross-style codes. That would be a significantly more general
result.

Conversely, if Z_4 × Z_6 is a *separate* phenomenon (a different
clean conditional bound with a different hypothesis), the program
has produced **two** new bounds in this round — a significant
acceleration.

Run T C-v3.4 early, before T C-v3.5, to know which world you're
in.

---

## 5. Hard constraints

- Read-only on `data/bb_instances.duckdb`.
- **Don't modify** `src/bb_lab/radical_weight.py`, `algebraic_features.py`,
  `ht_roos.py`, `homological_bounds.py`, `weight_invariants.py`,
  `features.py`, `canonical.py`, `enumerate_bb.py`, `cli.py`,
  `corpus.py`. Extend `degeneracy.py` only by adding new functions
  (don't modify existing ones).
- **§6h–§6l still apply.** Especially §6l: don't pretend the
  bound is general when it's restricted to a specific G_odd
  structure. The hypothesis is part of the theorem, not
  decoration.
- Tests must pass: `uv run pytest -m 'not slow' -q` from
  `experiments/bb_lab/`. The C-v2 deliverable brought the count to
  256; your additions should grow it.
- **Don't commit unless explicitly asked.** Matches HANDOFF_C and
  HANDOFF_C2 discipline.

---

## 6. Risks

- **Violations may reappear within the restricted domain.** The
  elementary-abelian-G_odd hypothesis is necessary (per C-v2 data),
  but might not be sufficient. The corpus has lots of
  elementary-abelian-G_odd rows with c=1; the C-v2 result showed
  c=1 rows violate at 97% rate. The narrowing to elementary
  abelian *and* c≥3 might be needed, or some finer feature.
- **The Z_4 × Z_6 anomaly might collapse the entire framing.**
  If Z_4 × Z_6's 65% tightness is just elementary-abelian-G_odd
  with k=1, then the simpler "G_odd ≅ (Z_p)^k for any k ≥ 1"
  hypothesis works and is much cleaner. But the prior round's
  data needs to be re-evaluated through this lens — possibly
  changing C-v2's reported violation counts.
- **The C-v1 invariance restriction (no F₂[G]-unit invariance)**
  carries through. If the C-v4 proof needs full equivalence-class
  reasoning, the proof's setting will need to drop F₂[G]-unit
  invariance from BB equivalence — making the theorem statement
  slightly less standard. Document this carefully.
- **bb_90_8_10's `G_odd = Z_3 × Z_15`** has both a Z_3 and a Z_5
  factor — two primes. Verify your `is_g_odd_elementary_abelian`
  definition correctly handles this case (one prime per factor,
  but multiple primes overall). The C-v2 data says bb_90 was
  tight; if your classifier excludes it, your classifier is wrong.

---

## 7. First-day checklist

1. Read `HANDOFF.md` end-to-end, especially §6l.
2. Read `HANDOFF_C.md` and `HANDOFF_C2.md`.
3. Read C-v1 and C-v2 deliverable notes:
   `notes/Cv{1,2}_*.md` and
   `pipeline/attempts/bb_distance_conjecture_radical_weight/result.md`.
4. Read this document end-to-end.
5. `cd experiments/bb_lab && uv sync --extra dev && uv run pytest -m 'not slow' -q`
   — confirm 256+ passing.
6. Reproduce the C-v2 bb_108 violation: compute `bb_radical_bound`
   on bb_108_8_10's polynomials and verify you get bound = 12
   with d_published = 10.
7. Implement T C-v3.1 (the classifier).
8. Verify it on all 5 Bravyi codes — exactly bb_108 should fail
   the hypothesis.
9. Then T C-v3.2 (the restricted sweep).

---

## 8. Expected timeline + variance

- **First survivable result**: 1–2 days. The classifier is small;
  the sweep is fast.
- **First falsification (if it happens within the restricted
  domain)**: also 1–2 days.
- **C-v3.4 Z_4 × Z_6 investigation**: 1 day.
- **C-v3.6 verdict + artifact**: half day after the data is in.

Total: **3–6 days under honest effort.**

Subjective priors:
- ~55% the narrowed conjecture survives the corpus cleanly.
- ~30% it survives with a small residual that needs further
  tightening.
- ~10% it falsifies (would mean even within the restricted
  domain, c-divided bounds don't hold).
- ~5% the Z_4 × Z_6 anomaly forces a major reframing.

If the narrowed conjecture survives, **this is the strongest bound
result the program will have produced**. It covers gross with a
tight prediction (d ≥ 12), uses a novel weight invariant (w_1
from C-v1), and is conditional on a structurally clean hypothesis
(elementary abelian G_odd) that 4 of 5 Bravyi instances satisfy.

---

## 9. Pointer to C-v4

If C-v3 lands a clean conditional theorem:

`HANDOFF_C4.md` would attempt the formal Lean proof against
`Framework/Homological/BBChainComplex.lean`. The theorem statement
would look approximately:

```lean
theorem bb_distance_lower_bound_elementary_abelian
    {G : Type} [hG : Fintype G] [AddCommGroup G]
    (A B : G → ZMod 2)
    (h_ea : IsElementaryAbelianGOdd G)
    : (bbChainComplex A B).distance ≥
        bbRadicalBound G A B := by
  sorry
```

The hard parts:
- `bbRadicalBound` (the C-v2 formula combining `w_1` and `c`)
  needs to be defined in Lean.
- The Jacobson radical of F₂[G] for general abelian G — not in
  mathlib for the non-semisimple case in a usable form.
- The actual distance inequality — the proof should follow from
  the Lin-Pryadko Statement 12 proof technique applied to the
  refined `w_1` quantity, but verifying this carefully is the
  research content.

That's all out-of-scope for C-v3. Focus on the empirical
falsification + tightness characterization within the restricted
domain.

---

## 10. Out of scope for C-v3

- C-v4 (formal Lean proof).
- Anything modifying the existing `bb_radical_bound` implementation
  in `radical_weight.py`. If it has a bug, document, don't fix.
- Re-doing the C-v1 / C-v2 work.
- Investigating bb_108 in detail — it's outside the conjecture's
  domain by hypothesis. Note its presence and move on.

Good luck. C-v2 left an exceptionally clean structural pin-point;
C-v3 has the highest expected value of any handoff in the C-series.
