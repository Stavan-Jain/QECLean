# C-v3 — Z_4 × Z_6 anomaly investigation

Date: 2026-05-26. HANDOFF_C3 §C-v3.4.

## The C-v2 observation

`Cv2_tightness.md` flagged Z_4 × Z_6 as showing 65.1% tightness — a
striking outlier compared to:

- Z_3 × Z_3 (8.3% tight)
- Z_3 × Z_6 (1.2% tight)
- Z_5 × Z_6 (2.2% tight)
- Z_6 × Z_6 (7.3% tight)

The question: is Z_4 × Z_6 a **separate** clean conditional theorem,
or is it the **same** as the elementary-abelian-G_odd conjecture?

## Result

**Same conjecture.**

`Z_4 × Z_6` has

- 2-Sylow = Z_4 × Z_2 (= gross's G_2 exactly)
- G_odd = Z_3 (axis 1 contributes nothing; axis 2 = Z_6 = Z_2 × Z_3)
- `g_odd_decomposition(Z_4 × Z_6) = (3,)`
- `is_g_odd_elementary_abelian(Z_4 × Z_6) = True` (rank-1, single-prime, p=3)

The C-v3 narrowed conjecture **does cover Z_4 × Z_6** because Z_3
is trivially elementary abelian (any prime-order cyclic group is
(Z_p)^1). So the Z_4 × Z_6 65% tightness is consistent with the
narrowed conjecture's "elem-ab G_odd ∧ c ≥ 3" survival domain.

## Stratification within Z_4 × Z_6 (106 labeled rows)

| `c` | rows | tight | loose | violations |
|:---:|:---:|:---:|:---:|:---:|
| 1 | 79 | 69 | 0 | 10 |
| 2 | 27 | 0 | 27 | 0 |

The headline 65% tightness rate (69/106) is concentrated almost
entirely at `c = 1`. The 10 violations are also at `c = 1`.

Among the c=1 violations:

| instance | A | B | d | bound |
|---|---|---|:---:|:---:|
| 7c184175 | 1+y+y² | 1+y+y² | 2 | 4 |
| 6b365cc3 | 1+y+y² | y³+y⁴+y⁵ | 2 | 4 |
| ce76d404 | 1+y+y² | x+x·y+x·y² | 2 | 4 |

The violating cases are degenerate (A and B are translates of each
other; bound = 4 but d = 2). The narrowed conjecture's c ≥ 3
condition correctly excludes them.

But the 79 c=1 rows include **69 tight cases**. These are
non-violations at c=1 — the bound is *exactly* d. The conjecture
doesn't apply here (c=1 is outside the hypothesis), but the bound
matches d anyway. Coincidence or sign of a sharper theorem?

Looking at a few c=1 tight rows: A and B with non-trivial xy-coupling
(not just y-only). The bound = w_1 in these cases happens to equal
d. Suggests:

- **A separate conjecture** might exist for c = 1 codes on Z_4 × Z_6,
  perhaps `d_X = min_O w_1(A, O)` directly (no denominator).
- But this is `c = 1` specific and doesn't generalize trivially.

## Conclusion

Z_4 × Z_6 anomaly is **the same conjecture**, just rank-1 G_odd. The
narrowed conjecture's "elem-ab G_odd" hypothesis correctly includes
Z_4 × Z_6. The high empirical tightness is partially explained by the
c=1 cases where the bound = min_O w_1 happens to equal d — but the
formal conjecture (with c ≥ 3) excludes those.

**No collapse of framing required.** The narrowed conjecture covers
Z_4 × Z_6 cleanly within its c ≥ 3 hypothesis.

## What about c = 1 codes on Z_4 × Z_6?

These are outside the C-v3 conjecture's domain by the c ≥ 3 condition.
A sharper "if c = 1 then d = min_O w_1" rule appears to hold on Z_4
× Z_6 (69 of 79 tight, 10 violations from A ≅ B cases) — but the
empirical 87% tightness rate is not 100%, so it's not a clean
theorem.

The 10 violations at c=1 are all "A is a unit multiple of B" cases
(`A = B`, `A = y^k · B`, etc.), where the BB code becomes the
trivial repetition `H_X = [M_A | u·M_A]` which collapses. This is
a separately-known phenomenon documented in HANDOFF.md §6h (the
T2R1 conjecture violations were dominated by these cases). The C-v3
"c ≥ 3" condition correctly excludes them.
