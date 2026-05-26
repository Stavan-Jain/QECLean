# Result — Tier-2 Round 4 verdict on the BBCS-2016 apparent-distance candidate

**Verdict: SHELVED — PAPER DOES NOT HELP.**

This maps to the explicit `shelved-paper-doesnt-help` branch of the
T2R4 verdict tree:

> *"If the paper turns out to NOT handle non-semisimple F₂[G] (which
> would re-instate the Round 3 obstruction), document this and stop.
> The shelved verdict is the correct output. Don't force the
> implementation."*

The Bernal–Bueno-Carreño–Simón 2016 framework explicitly assumes
F_q[G] semisimple (`gcd(|G|, q) = 1`). Four of the five Bravyi BB
instances — including the engineering target, gross — have F_2[G]
non-semisimple. The Round 3 obstruction (HANDOFF §6i: non-semisimple
F_2[G] + non-cyclic G_odd, compounding) is **not lifted** by this
candidate.

No code was written. The literature lookup (T2R4.0) is the round's
sole deliverable.

---

## Final report (per T2R4 spec)

### 1. Literature verdict

Does BBCS 2016 handle:

| Property | Verdict | Citation |
|---|:---:|---|
| (a) Non-cyclic G | **YES** | BBCS 2016, hypermatrix construction in Section II (multivariate q-orbits modulo `(r_1, …, r_s)`); Example 23 of the paper computes `mad` on a `Z_3 × Z_3 × Z_5` hypermatrix. |
| (b) Non-semisimple F₂[G] | **NO** | BBCS 2016, page 2 Section II ("We deal with abelian codes in the semisimple case … gcd(r_k, q) = 1"); reiterated Section III, Theorem 22, Theorem 25; identical assumption in the 2017 companion BGS paper, page 3. |
| (c) Degenerate supports | partially | Framework operates on the abelian code's defining set, which is the same in F_q[G] as in F_q[⟨supp⟩]; doesn't help BB-code distance because BB couples A and B over G, not over ⟨supp(A)⟩ ∩ ⟨supp(B)⟩. |

**(b) is the show-stopper.** Per the spec: stop here, report
`shelved-paper-doesnt-help`.

Companion check: Jitman-Ling 2013 explicitly addresses non-semisimple
PIGAs and shows (i) any distance bound there is derived from the
semisimple-quotient bound and (ii) abelian codes in non-semisimple
PIGAs are asymptotically bad. So this is a structural feature of
the entire character-theoretic / Fourier-transform line, not a gap
in any one paper.

### 2. Apparent distance on individual Bravyi polynomials

**Not computed** (no implementation written; the spec branch is
"stop"). For context, here is the prediction of what BBCS *would*
return, on the regime where it applies:

| code | F_2[G] semisimple? | BBCS apparent_distance(A) |
|---|:---:|:---|
| grossA (in F_2[Z_12 × Z_6]) | NO | undefined (out of scope) |
| grossB | NO | undefined |
| bb_72A | NO | undefined |
| bb_72B | NO | undefined |
| bb_90A (in F_2[Z_15 × Z_3]) | yes | computable; would be ≥ Round 3's HT bound (1) |
| bb_90B | yes | computable |
| bb_108A | NO | undefined |
| bb_108B | NO | undefined |
| bb_288A | NO | undefined |
| bb_288B | NO | undefined |

Bb_90 is the single Bravyi instance where BBCS is in scope. If
implemented, it might produce a sharper-than-HT lower bound for
bb_90's `d_A^⊥` and `d_B^⊥`. But bb_90 is not the engineering
target.

### 3. Structural condition `S`

**Not formulated** for this round. Reusable framework from Round 3
(`bb_ht_condition`) gates on F_2[G] semisimplicity at the very
first check; for the four out-of-scope Bravyi instances, the
condition returns "G_not_semisimple" and the bound chain
short-circuits to the trivial value 1. BBCS would not alter this
gating — the gate is structurally identical to BBCS's own scope
restriction.

Candidate `S` formulations from the hypothesis doc (none
implemented):

1. **Descriptive (checkable on labeled corpus)**: `d_X(BB(A, B)) =
   min(d_A^⊥, d_B^⊥)`.
2. **Predictive algebraic**: `gcd(A, B) = 1` in `F_2[G]` (Pesah-style).
3. **Predictive BBCS-internal**: the BBCS witness `χ_β` for A is not
   in the joint defining set of `(A, B)` over `2|G|` coordinates.

None of these were evaluated because the underlying bound
`bb_apparent_bound` is not well-defined on the non-semisimple
Bravyi instances.

### 4. Corpus sweep

**Not run** (no implementation). Prediction based on the same
F_2[G]-semisimple gate Round 3 used:

| group | total rows | F_2[G] semisimple? | BBCS in scope? |
|---|---:|:---:|:---:|
| Z3xZ3 | 12 | yes (\|G\|=9 odd) | yes |
| Z3xZ4 | 73 | no (\|G\|=12) | no |
| Z3xZ5 | 103 | yes (\|G\|=15 odd) | yes |
| Z3xZ6 | 166 | no (\|G\|=18) | no |
| Z4xZ6 | 106 | no (\|G\|=24) | no |
| Z5xZ6 | 2622 | no (\|G\|=30) | no |
| Z6xZ6 | 812 | no (\|G\|=36) | no |
| **TOTAL** | **3894** | — | **115 in scope** |

BBCS would be applicable to 115/3894 = 3.0% of corpus rows. Of
these, Round 3's HT bound already fires nontrivially on the Z_3 × Z_5
subset (13/13 tight, all `d=2` rows). The remaining 12 Z_3 × Z_3
rows include `bb_72_12_6`'s sub-code structure but not the full
[[72,12,6]] code itself. BBCS would at most produce sharper numbers
on the same 115 rows.

### 5. Bravyi table

| code | S? | bb_apparent_bound | actual d | verdict |
|---|:---:|:---:|---:|---|
| bb_72_12_6 | n/a (F_2[G] non-ss) | undefined | 6 | **out of scope** |
| bb_90_8_10 | not computed | undefined (could be > 1) | 10 | in scope but not target |
| bb_108_8_10 | n/a | undefined | 10 | **out of scope** |
| gross [[144,12,12]] | **n/a** | **undefined** | **12** | **out of scope (engineering target)** |
| bb_288_12_18 | n/a | undefined | 18 | **out of scope** |

The "in scope" instance (bb_90) is irrelevant to the program's goal
of bounding gross.

### 6. Verdict + recommendation

**Verdict**: `shelved-paper-doesnt-help`. The BBCS framework's
explicit assumption of F_q[G] semisimple (gcd(|G|, q) = 1) places
the engineering target (gross, F_2[Z_12 × Z_6], |G|=72 even) outside
the framework's scope. The Round 3 obstruction is not lifted.

**Recommendation** (do NOT advance to Tier 3 / Tier 4):

1. **Stop the BBCS branch.** This is the spec's explicit
   instruction for this verdict; honoring it preserves program
   discipline. A forced implementation against the paper's stated
   assumption would be dishonest.

2. **Strengthen the Round-3 compounding-obstructions lesson.**
   HANDOFF §6i originally identified three obstructions
   simultaneously active on Bravyi instances. Round 3 confirmed
   obstructions (1) [F_2[G] non-semisimple] + (2) [G_odd non-cyclic]
   block classical HT. Round 4 now confirms BBCS lifts (2) but not
   (1), so the entire character-theoretic / Fourier-transform line
   (Camion 1971 → Sabin-Lomonaco 1992 → Saints-Heegard 1995 → BBCS
   2016 → BGS 2017) is silent on the engineering target. Recommend
   adding a paragraph to HANDOFF §6i to record this stronger
   conclusion: **future Tier-2 candidates must explicitly address
   the radical of F_2[G], not just the non-cyclic-G_odd part.**

3. **Future Tier-2 directions to consider (next round, not this
   round):**

   - **Cover-graph chain-map transfer bounds**: Pesah et al. 2025
     (lifted-product / cover-graph framework). If gross is a cover
     of a smaller base BB code with known distance, structural
     theorems may transfer the distance. This is *not* algebraic
     — it operates on the underlying Tanner graph and dodges the
     semisimplicity question entirely.

   - **Homological-product surgery bounds**: Hsieh-Le Gall 2020
     (arXiv:2008.09495) and Kovalev-Pryadko 2013 (arXiv:1206.6536).
     These bound `d_X` in terms of the homology of the C-block / B-block
     2-complex coupled through the boundary maps. The algebra is
     different (chain-complex / Künneth-style), no reliance on
     `F_q[G]` semisimplicity.

   - **Radical-aware weight invariant**: a "depth-weighted apparent
     distance" that operates on the Jacobson filtration of `F_2[G]`.
     No reference found in the literature surveyed; if such a thing
     exists it would be a literature gap to identify, not a
     plug-and-play candidate. Speculative.

   - **Lifted-product structural theorems**: the Lin-Pryadko (2306.16400)
     Statement 12 lower bound `d ≥ ⌈d_A^⊥ / c⌉` (where `c = [G : ⟨supp(A)⟩]`
     is the degeneracy index) is correct-shape per HANDOFF §6h and
     does fire on gross (c = 3, d_A^⊥ = 12 → bound 4, loose vs.
     actual 12). A *tightening* of the c-factor for Bravyi-style
     supports is an open direction with no obvious starting paper.

4. **What survives this round for future Tier-2 work:**

   - The literature triangulation (T2R4.0) now firmly establishes
     that the multivariate-abelian-code distance-bound literature
     does *not* contain a tool for gross. This rules out a class
     of candidates and is a first-class negative result.

   - The crisp diagnostic: any candidate for the engineering target
     must explicitly handle the radical of F_2[G] for `2 | |G|`,
     OR be structural/non-algebraic (cover-graph or homological).
     This is now a documented filter on future Tier-2 candidates.

## Headline numbers (literature-only)

* BBCS paper: 14 pages, located, downloaded, read in full.
* F_q[G] semisimplicity assumption: stated 4 separate places in the
  2016 paper (page 2 §II opening, page 3 §III opening, Theorem 22
  hypothesis, Theorem 25 hypothesis); identical assumption in the
  2017 BGS companion paper.
* Bravyi instances in scope: **1/5** (bb_90 only).
* Engineering target (gross) in scope: **NO**.
* Implementation: **none written** (per spec branch
  "shelved-paper-doesnt-help").
* Test count: **195 passed / 2 skipped** (unchanged from Round 3
  baseline; no new tests added).

## Implementation status

No new source code, scripts, or tests. Sole artifacts:

* `experiments/bb_lab/notes/T2R4.0_literature.md` — detailed
  literature triage with verbatim quotes, property checklist,
  references with DOIs / arXiv IDs, companion-literature analysis
  (Jitman-Ling 2013, Camion 1971, Roth-Seroussi 1986).
* `pipeline/attempts/bb_distance_conjecture_bbcs/{state.yaml,
  hypothesis.md, evidence.md, result.md}` — this attempt.

All `src/bb_lab/*.py` files untouched (per T2R4 hard constraints).
All `scripts/tier2_*.py` and `scripts/tier3_*.py` untouched.
`uv run pytest -m "not slow" -q` returns 195 passed, 2 skipped,
3 deselected, identical to Round 3's baseline.
