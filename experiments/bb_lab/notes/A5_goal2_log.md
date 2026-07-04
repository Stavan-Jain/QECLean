# A5 — goal 2: analytic distance bounds for a CLASS of BB codes

Track log for the goal-2 program (A_HANDOFF §1 goal 2; seeded from
A4 §7 "Generalization" and Entry 28 §Next). Numbered entries, A3-log
conventions. **Log-choice decision (recorded per the session brief):**
goal 2 gets its own log file rather than continuing
`A3_track1p1_log.md` — the A3 log is the gross-instance story arc
(Entries 1–28, closed); goal 2 is corpus-wide and reads better
self-contained. Cross-pointer added to `A_HANDOFF.md` §8.

Standing constraint (A_HANDOFF §1): fully analytic only. Every number
computed by the `a5_*` scripts — including every `d_exact` consumed
from `data/bb_instances.duckdb` — is **discovery/validation only**,
never load-bearing. The database is the round-2-era enumeration; per
the known over-claim history its rows were spot-checked before use
(Entry 1 §0).

---

## Entry 1 (2026-06-12) — the instance-hypothesis checker and the corpus sweeps

### 0. Database spot-check (owed before leaning on it)

`data/bb_instances.duckdb` copied READ-ONLY from the main repo
(16,867 instances; 4,364 with SAT-exact d; 812 Z6xZ6 + 68 Z15xZ3 with
exact d — counts match the brief). Spot-checks against our own
substrate:

* (n, k) recomputed for 3 random rows across Z6xZ6 / Z15xZ3 / Z3xZ4 —
  all match.
* SAT distance recomputed end-to-end for 2 rows
  ((3,4)-instance d=2; (6,6)-instance d=4), both directions
  (d_X = d_Z = d_db). Match.

Verdict: trustworthy as discovery data.

### 1. The checker

`scripts/a5_instance_hypotheses.py` (+ `tests/test_a5_instance_hypotheses.py`,
6 tests). For an instance (Z_ℓ×Z_m, A, B) it computes:

* **CRT frame**: per-axis 2-part × odd part; frame shape ∈
  {semisimple, Z2, Z2xZ2, deeper}. The A4 §3 engine needs Z2xZ2.
* **Component table**: for every Frobenius orbit j of the odd character
  group, the value vector V_j(f)[s] = ψ_j(f_s) ∈ F_{2^r} over the
  2-part layers s — this IS the coefficient vector of f̂_j ∈ K[G₂] —
  and its classification: unit (augmentation ≠ 0) / engine_radical
  (Z₂² only: one zero + three pairwise-distinct nonzero values — the
  §3 engine's co-point rigidity input) / radical_other / zero.
* **Hypothesis (i)**: all components of Â, B̂ ∈ {unit, engine_radical}.
* **Hypothesis (ii)**: dA, dB multiplicity-free; dA ∩ dB = ∅;
  coordinate-disjointness per axis.
* **Hypothesis (iii)**: projection pattern (monomial in one axis,
  full-weight in the other, mirrored) — the gross §4.4 shape.
* **Goal-2 labeling data** (§10.1 m-analogue, Z₂² frames): kill
  vectors κ of the radical components, slot-bijection flags.
* **Layer dictionary d_H** (d₃ analogue) for the odd part: min weight
  of nonzero f with Fourier support ⊆ W, for W = single-orbit (±
  trivial) classes. DISCOVERY ONLY (enumeration), dim-capped.

**Validation: on the base code the checker reproduces the A4 §3/§10.1
data exactly** — the five-orbit unit/radical table, B̂ = ωu+v ↦
vec (ω², ω, 1, 0), κ(B̂) = m, κ(Â₃) = m′, κ(Â₄) = ω²m = m′², and the
dictionary rows 9/6/3. Frozen as the test contract.

### 2. Tier a — the five Bravyi instances

| code | frame | (i) | (ii) | (iii) | notes |
|---|---|---|---|---|---|
| bb_72 (base) | Z2xZ2 | PASS | PASS | PASS | the A4 §3 table verbatim |
| bb_90 | semisimple | FAIL | PASS | PASS | no radical at all; Â, B̂ have ZERO components |
| bb_108 | Z2 | FAIL | PASS | PASS | radicals are c·(1+s): 2 layers, no co-point engine |
| gross | deeper (Z4×Z2) | FAIL | PASS | PASS | radical depth 4 — as §7 predicted |
| bb_288 | deeper (Z4×Z4) | FAIL | PASS | PASS | same |

All five pass (ii)+(iii) — the family-defining structure; the
discriminator is the frame/(i). The (i)-FAILs are *frame* failures,
each with its own replacement mechanism (Entries 2–3).

### 3. Tier b1 — Z6xZ6 sweep (812 instances, exact d)

Artifacts: `data/a5/z6z6_sweep.jsonl` (gitignored, reproducible via
`--db-sweep Z6xZ6`).

* **The DB stores one canonical representative per Aut(G)-orbit, and
  the canonicalization does NOT preserve (ii)-coordinate-disjointness
  or (iii)** — those are presentation properties. (i), mult-freeness,
  and dA ∩ dB = ∅ are Aut-invariant. The literal base instance is not
  a DB row; its orbit representative is.
* Aut-invariant cross-tab:
  * (i) PASS: 126/812; d ∈ {2:13, 4:19, 6:76, 8:18} — (i) alone does
    not give d ≥ 6.
  * **(i) ∧ mult-free ∧ disjoint: 25/812, d ∈ {6:16, 8:9} — ZERO
    exceptions to d ≥ 6.** This is the empirical shape of the class
    theorem.
  * The 69 near-misses ((i) ∧ mult-free ∧ d ≥ 6 but excluded) all
    fail on dA ∩ dB ≠ ∅ alone.
* **Engine validation at scale**: (i) PASS ⟹ min(min_wt_ker_A,
  min_wt_ker_B) ∈ {6, 18} — never < 6, 126/126. (i) FAIL admits 4
  (253 rows). The §4.1 one-sided floor is exactly what (i) buys.
* **Aut-orbit refinement**: searching all 288·2 presentations
  (GL₂(Z₆) × A↔B swap) of the 25 class members for a full
  (ii)+(iii) pass: **exactly the six k=12, d=6 instances (the
  base-code family) pass, each with 96 presentations** (stabilizer of
  order 6); the other 19 (k=8 d=6, k=4 d=8) have NO passing
  presentation. The Theorem-A grid as written runs verbatim on the
  six; the 19 need presentation-free replacements for the
  (1,3)/(2,2) kills (Entry 3).

### 4. Tier b2 — Z15xZ3 probe (68 instances; where the CRT frame breaks)

* All 68: frame = semisimple ⟹ (i) FAILS STRUCTURALLY: with no
  radical, k > 0 forces zero components of Â, B̂ (in Z₂²-frame codes
  k comes from radical components instead). The §3 engine, the layer
  parity argument, and the §4.1 "≥ 3 layers × even" chain are all
  gone — this is the precise break the probe was sent to find.
* **The semisimple replacement floor**: Ann(A) = I(V_A) (the ideal of
  the vanishing-orbit set), so μ(Ann A) = d_H(V_A) — an exact
  identity, validated 7/7 against the DB's min_wt_ker_A (typical
  bb_90-family value: d_H = 10; the one dim-30 vanishing set is
  un-enumerable and NULL on both sides).
* Cross-tab: mult-free ∧ disjoint: 29/68, d ∈ {6:6, 8:9, 10:14} —
  **zero exceptions to d ≥ 6 here too.** Combined with Z6xZ6: the
  candidate class "floor-bearing frame + mult-free + disjoint" has
  54 members across two groups, 0 counterexamples.
* The d=2 rows (5 of them) all fail mult-free/disjoint — correctly
  excluded.

### Next

→ Entry 2: template run on bb_108 (the Z2-frame engine).
→ Entry 3: gap analysis for the single class theorem.

---

## Entry 2 (2026-06-12) — Theorem-A template run on bb_108: d ≥ 6, μ(Ann) = 12

Target: bb_108 = (Z₉×Z₆, A = x³+y+y², B = y³+x+x²) — same polynomials
as gross, [[108,8,10]] published. Confirmation script:
`scripts/a5_bb108_smallcycles.py` (W1–W7, all PASS).

**Theorem A′ (bb_108 small cycles).** The instance has no nonzero
X-type or Z-type 1-cycle of weight ≤ 5. In particular d(bb_108) ≥ 6,
and μ(Ann A) = μ(Ann B) = 12 (attained).

Frame: layers L = Z₂ (y mod 2), odd part H = Z₉×Z₃ (x, y mod 3),
|H| = 27. Radical orbit sets (checker, W1): W_A = {(0,1),(3,1),(3,2)},
W_B = {(3,0),(3,1),(3,2)}, every radical component of the rigid form
c·(1+s); no zero components; units elsewhere.

### 2.1 The Z₂-engine (replaces A4 §3's co-point engine)

In K[Z₂] (u = 1+s, u² = 0): Ann(c·u) = K·u. So for z ∈ Ann(A),
componentwise: unit orbits force both layer values to 0; radical
orbits force the two layer values EQUAL. Then w := z_e + z_s has all
components zero (equal values cancel), so by semisimple Fourier
inversion on F₂[H]: z_e = z_s =: w₀ and V_j(w₀) = 0 off W_A. Hence

    Ann(A) = (1+s) ⊗ I(W_A),   |z| = 2|w₀|,  w₀ ∈ I(W_A).

(Confirmed W2: dim Ann = 6 = Σ orbit sizes; every annihilator element
(0,3)-periodic.)

### 2.2 The pullback dictionary (reuses the gross d₃!)

Every character in W_A ∪ W_B has order 3, so factors through
Q = Z₃² = H/K (K = 3Z₉ ≅ Z₃ in the x-axis). Therefore
I(W) = {3-fold pullbacks π*h : h ∈ F₂[Q], ĥ ⊆ W̄}, |π*h| = 3|h|, and
under the relabeling (3,b) ↦ (1,b), (0,1) ↦ (0,1):

    W̄_A = {ψ₁, ψ₃, ψ₄},   W̄_B = {ψ₂, ψ₃, ψ₄}

— exactly the gross base's radical sets (same polynomials, same odd
collapse). The A4 §3 dictionary row d₃(3 nontrivial orbits, no
trivial) = 2 applies verbatim (achiever: a δ-pair along ker ψ₂ resp.
ker ψ₁), so

    μ(Ann A) = 2 · 3 · d₃((3,F)) = 12,   μ(Ann B) = 12,

both attained (z = (1+s)·π*(δ-pair)). One-sided splits (k,0)/(0,k)
are dead for ALL k ≤ 11, not just ≤ 5. (Confirmed W2: μ = 12 exact,
both sides.)

### 2.3 The case grid (weights ≤ 5)

(PAR): |A| = |B| = 3 odd ⟹ |u_L| ≡ |σ| ≡ |u_R| (mod 2) (augmentation
hom — generic). Kills (1,2),(2,1),(2,3),(3,2),(1,4),(4,1).

(1,1): A·g = B·r ⟹ dA = dB; but dA ∩ dB = ∅ (W3/W4; in fact
x-coordinate-disjoint: dA_x ⊆ {0,3,6}, dB_x ⊆ {1,2,7,8}). Dead.

(1,3): mult-free dB ⟹ |B·z| = 9−2p+4T; = 3 forces (p,T) = (3,0),
i.e. z a dB-triangle. Census (W5): two classes up to translation —
{0,(1,0),(2,3)} (the three overlaps coincide: T = 1, image weight 7 ✗)
and {0,(1,0),(8,3)} (image weight 3 but CONSTANT-y = {(1,0),(3,0),(8,0)}-
shaped, while A·g has y-coordinates {g_y, g_y+1, g_y+2} pairwise
distinct ✗). Dead — gross's §4.3 kill verbatim.

(3,1): dA-triangle census (W5): three classes; one has image weight
7 ✗; **two have weight-3 images that are NOT constant-x** —
the gross §4.3 mirror kill does NOT transfer. They die anyway, by the
principled comparison "A·z must be a translate of B":

* {0,(0,1),(3,5)}: A·z = {(0,1),(0,3),(6,5)} — only 2 distinct
  x-coordinates; B-translates have 3. ✗
* {0,(3,4),(6,2)}: A·z = {(0,1),(3,5),(6,3)} — 3 distinct
  y-coordinates; B-translates have y-multiplicity profile {2,1}. ✗

Surveyable, but a different reason than gross — first concrete datum
that the (1,3)/(3,1) kills are census-dependent (Entry 3).

(2,2): the π_x/π_y bookkeeping runs as in gross §4.4 with the Z₉
weight tables replacing the Z₆ ones: π_y(A) = 1+y+y², π_x(A) = x³,
π_y(B) = y³, π_x(B) = 1+x+x² (gross pattern, W1/checker).
|σ| = 4 branch: |π_y| matching forces ℓ-y-gap ±1 / r-y-gap 3;
|π_x| matching ((1+x+x²)(1+x^g) over Z₉ has weight 2 only at
g ∈ {1,8}, else 4 or 6; x³(1+x^g) has weight 2 ∀g ≠ 0) plus the
final translate comparison kills all four surviving gap combos
(x-multiplicity profiles {2,1,1}-vs-{1,1,1} mismatches). |σ| = 6
branch: y-gap case split (0, ±1, ±2, 3) dies on |π_y|/|π_x| weight
mismatches alone — e.g. ℓ-y-gap 0 forces r-x-gap ∉ dB ∪ {1,8} whence
right |π_x| ∈ {4,6} vs left 2. Dead. (Confirmed exhaustively, W6:
no (2,2) cycle at all.)

All splits dead ⟹ no nonzero Z-cycle of weight ≤ 5. X-side: the
inversion duality Φ(w_L, w_R) = (ι(w_R), ι(w_L)) is generic BB
(ι(B)·ι(u_R) = ι(A)·ι(u_L) follows by applying ι to the Z-cycle
condition), weight-preserving — so no small X-cycles either.
(Both kernels independently confirmed UNSAT at w ≤ 5, W7.) **∎**

### 2.4 The Theorem-B transfer (stated, as owed by the brief)

A4 §5's Theorem B consumed only (a) the free-Z₂ block form of the
cover boundary and (b) "no nonzero base cycle of weight < c". Both
are available with base = bb_108, c = 6. Hence:

**Corollary (covers of bb_108).** Any free-Z₂ double cover of bb_108
with the same polynomials — (Z₁₈×Z₆, A, B) in the x-direction or
(Z₉×Z₁₂, A, B) in the y-direction, both n = 216 — has no nonzero
cycle of weight < 6; in particular d ≥ 6. (Sheet-projection p:
|v| ≥ |p(v)| if p(v) ≠ 0; else v diagonal, |v| = 2|v₀| ≥ 12.)

Neither cover is in the DB (no exact-d Z18xZ6/Z9xZ12 rows) — the
corollary is a prediction, validation welcome next session.

### 2.5 bb_90 (the stress test) — status

Frame semisimple: the engine is replaced by the exact identity
μ(Ann) = d_H(V) (Entry 1 §4; bb_90's own floors are 10/10 by the
checker's dictionary — comfortably ≥ 6). (PAR) ✓, dA ∩ dB = ∅ ✓,
A·g has 3 distinct y's ✓ (mod 3!), B·r 3 distinct x's ✓. What is NOT
yet done: its (1,3)/(3,1) triangle censuses and (2,2) tables over
Z₁₅×Z₃. No structural obstruction visible — a bb_90 run is mechanical
next-session work with the same script skeleton. NOT claimed today.

### Next

* bb_90 template run (the semisimple variant — would make the grid
  3-for-3 across frame shapes).
* Add the (iv)/(v) finite-table verdicts to the checker (Entry 3) and
  sweep the 54-member empirical class for full-grid passes.
* Push bb_108 past 6: the dangerous/safe sector machinery on its
  covers (the (M)-analogue) — the gross Entries 16–28 playbook.

---

## Entry 3 (2026-06-12) — gap analysis: what blocks a single class theorem

The question (stretch goal): which Theorem-A steps resist the
hypothesis-generic form "every BB code satisfying (i)–(iii) has
d ≥ 6"?

### 3.1 What IS generic (no obstruction)

* **(PAR)** — |A|, |B| odd. Augmentation hom; group-free.
* **(1,1) kill** — needs only dA ∩ dB = ∅ (nonempty by mult-free).
* **|B·z| = 9 − 2p + 4T inclusion–exclusion** — needs only
  multiplicity-free dB (pairwise translate overlaps ≤ 1). Forces the
  triangle census shape of (1,3)/(3,1) generically.
* **The X–Z inversion duality** — generic BB; one side suffices.
* **The Theorem-B transfer** — generic over free-Z₂ covers of any
  instance with a small-cycle bound.

### 3.2 What fragments by FRAME (hypothesis (i) is three hypotheses)

The one-sided floor mechanism depends on the 2-part of G:

| 2-part | engine | floor | status |
|---|---|---|---|
| Z₂×Z₂ | §3 co-point rigidity | "≥ 3 layers × even" ⟹ ≥ 6 | A4, hand-proven |
| Z₂ | Ann = (1+s)⊗I(W) | 2·d_H(W) | Entry 2, hand-proven |
| trivial | Ann = I(V) (semisimple) | d_H(V) | exact identity, Entry 1 §4 |
| Z₄×…, deeper | none developed | — | open (radical depth ≥ 4; A4 §7 flagged the grid blow-up — gross itself sits here) |

So "(i)" in a class theorem must be read as "the frame is
floor-bearing and the floor ≥ 6", with the floor computed by the
frame-appropriate engine + the odd-part dictionary d_H. The
dictionary is group-dependent with no closed form, but each needed
row is a hand-provable lemma (A4's d₃; Entry 2's pullback trick
reduced bb_108's rows to d₃ verbatim — covers whose radical orbits
factor through a common quotient inherit the quotient's dictionary).

### 3.3 What is census-dependent: the (1,3)/(3,1) kills

Gross killed its surviving triangle class by constant-y/constant-x
images. bb_108's (1,3) side died the same way, but its (3,1) side
needed coordinate-MULTIPLICITY-PROFILE mismatches (Entry 2.3) — the
kill *reason* varies per instance even when the kill *shape* (a
finite census of triangle classes, each compared against translates
of the partner polynomial) is uniform. The honest generic hypothesis
is finite-verification:

> **(iv)** for every dB-triangle class T with |B·T| = 3: B·T is not a
> translate of A; mirror for dA-triangles vs B.

Checkable by hand per instance (the censuses here had 2–3 classes);
analytic in the A_HANDOFF §1 sense; presentation-free. The price: it
is a verification schema, not a structural condition — there is no
visible closed-form condition on (G, A, B) implying it.

### 3.4 What is least generic: the (2,2) bookkeeping

The §4.4 grid is uniform in SHAPE (π_x/π_y matching, |σ| ∈ {4,6}
split, final translate comparison) but consumes per-instance weight
tables of (π(P))(1+t^g) — Z₆ tables for gross, Z₉ tables for bb_108 —
and, on Z6×Z6, the projection pattern itself is only available in
SOME presentation of SOME instances (Entry 1 §3: 6 of 25). Generic
form, again finite-verification:

> **(v)** the (2,2) translate-match table is empty: for all
> δ_L, δ_R ≠ 0 and all t: A·{0,δ_L} ≠ B·{t, t+δ_R}.

Exhaustive over |G|²·|G| triples (script: W6), hand-surveyable
through the projection bookkeeping when (iii) holds in some
presentation.

### 3.5 The Aut-orbit obstruction (empirical, the sharpest datum)

On Z6×Z6 the empirical class {(i) ∧ mult-free ∧ disjoint} has 25
members, all d ≥ 6 — but only the 6 base-family members admit ANY
presentation where (iii) holds; the other 19 satisfy the d ≥ 6
conclusion without the coordinate machinery being available in any
coordinates. Conclusion: **the coordinate-projection route cannot be
the proof mechanism for the full class** — (iv)/(v) (or something
better) must replace it, or the class theorem covers only the
base-family orbit.

### 3.6 Proposed class-theorem shape (the deliverable)

**Conjecture (class small-cycle theorem).** Let (G = Z_ℓ×Z_m, A, B)
be a BB instance with |A| = |B| = 3, satisfying:
  (a) frame floor-bearing (2-part ∈ {1, Z₂, Z₂²}) with one-sided
      floor ≥ 6 (§3.2);
  (b) dA, dB multiplicity-free and dA ∩ dB = ∅;
  (c) the (1,3)/(3,1) censuses kill (iv);
  (d) the (2,2) table is empty (v).
Then the instance has no nonzero 1-cycle of weight ≤ 5, hence
d ≥ 6 — and every free-Z₂ cover has d ≥ 6.

Every hypothesis is analytically checkable; (a)+(b) are structural,
(c)+(d) finite and surveyable. The proof is the A4 §4 grid with the
frame-appropriate engine — gross and bb_108 are its first two
instantiations (Z₂² and Z₂ frames); bb_90 would complete the
semisimple column. Empirical support: 54 class-candidate members
across Z6xZ6 + Z15xZ3 ((a) checked at the (i)-level proxy), zero
d < 6 exceptions; censuses (c)/(d) not yet swept (next session).

### 3.7 What this does NOT give

* No route past d ≥ 6 at the class level: gross's 12 needed the cover
  dichotomy + (M)/(M-im) — instance-specific machinery (the §10–§12
  slot frame is "instance-generic" in m/offsets/dictionary, per
  Entry 28, but discharging its hypotheses per instance is a project,
  not a check).
* Nothing for deeper 2-parts (gross, bb_288 as BASE instances) — the
  missing engine is the single biggest structural gap.
* No closed-form characterization of (c)/(d) — candidate next
  analytic target: prove (iv)/(v) follow from (b) + coordinate
  conditions in SOME presentation, or find a counterexample instance
  where a census match actually occurs (none seen yet).

---

## Entry 4 (2026-06-12) — bb_90: the semisimple template run; d ≥ 6, μ(Ann) = 10

Target: bb_90 = (Z₁₅×Z₃, A = x⁹+y+y², B = 1+x²+x⁷) — [[90,8,10]],
the SEMISIMPLE frame (the Entry-1 stress test). Confirmation:
`scripts/a5_bb90_smallcycles.py`, W1–W7 all PASS (first run).

**Theorem A″ (bb_90 small cycles).** The instance has no nonzero
X-type or Z-type 1-cycle of weight ≤ 5. In particular d(bb_90) ≥ 6,
and μ(Ann A) = μ(Ann B) = 10 (attained).

The expected stress test turned out to be the EASIEST of the three
frames — every kill is projection arithmetic, no censuses needed:

### 4.1 The semisimple engine and the third pullback

Ann(A) = I(V_A) exactly (no radical), V_A = {(0,1),(5,1),(5,2)},
V_B = {(5,0),(5,1),(5,2)} — and every vanishing character has order
3, factoring through Q = Z₃² via (x mod 3, y), kernel K = 3Z₁₅ ≅ Z₅.
So I(V) = {5-fold pullbacks π*h, ĥ ⊆ V̄}, |π*h| = 5|h|, with

    V̄_A = {ψ₁, ψ₃, ψ₄},   V̄_B = {ψ₂, ψ₃, ψ₄}

— the gross base's radical sets a THIRD time (after gross itself and
bb_108's 3-fold pullback). μ(Ann) = 5·d₃((3,F)) = 5·2 = 10, attained.
One-sided splits dead for all k ≤ 9.

### 4.2 The grid (everything dies on π_y / π_x weights)

Structural facts: dB ⊂ {y = 0} (B is a polynomial in x alone);
dA ⊂ {y ∈ {1,2}}; hence dA ∩ dB = ∅ for free, and:

* **(1,1)**: dead (disjoint difference sets, as always).
* **(1,3)**: mult-free dB ⟹ z is a dB-triangle ⟹ z constant-y
  (dB lives in one y-row!) ⟹ π_y(B·z) = y^c·ε(...) has weight ≤ 1,
  but π_y(A·g) = (1+y+y²)y^{g_y} = 1+y+y² has weight 3. Dead — no
  per-class analysis at all.
* **(3,1)**: census-free. In F₂[Z₃] the all-ones element absorbs:
  (1+y+y²)·v = ε(v)·(1+y+y²). |z| = 3 odd ⟹ π_y(A·z) = 1+y+y²
  (weight 3); π_y(B·r) = y^{r_y} (weight 1, π_y(B) = 1). Dead.
* **(2,2)**: π_y(σ_L) = (1+y+y²)π_y(u_L) = 0 ALWAYS (|u_L| = 2
  even); so π_y(u_R) = 0, forcing the r-pair y-gap to 0, whence
  r-diff = (g, 0) with g ≠ 0. Then π_x: left x⁹(1+x^{g_ℓ}) has
  weight ∈ {0,2}; right (1+x²+x⁷)(1+x^g) has weight ∈ {4,6} for all
  g ≠ 0 (mult-free dB ⟹ translate overlap ≤ 1 ⟹ weight ≥ 6−2 = 4;
  W6 table: exactly {4,6}). Weight mismatch — dead. (σ = 0 is
  excluded: it would put both u-sides in weight-2 annihilators,
  μ = 10.)

(PAR) kills the mixed-parity splits as always. All splits dead. ∎
(W7: SAT-UNSAT w ≤ 5, both kernels, confirmation.)

### 4.3 Theorem-B transfer

Any free-Z₂ double cover of bb_90 with the same polynomials —
(Z₃₀×Z₃, A, B) or (Z₁₅×Z₆, A, B), both n = 180 — has no nonzero
cycle of weight < 6; in particular d ≥ 6.

### 4.4 The grid is now 3-for-3 across frame shapes

| frame | instance | floor | floor mechanism | published d |
|---|---|---|---|---|
| Z₂×Z₂ | bb_72 (base) | 6 | §3 co-point engine + d₃ | 6 (tight!) |
| Z₂ | bb_108 | 6 | (1+s)⊗I + 3-fold pullback to d₃, μ = 12 | 10 |
| semisimple | bb_90 | 6 | I(V) + 5-fold pullback to d₃, μ = 10 | 10 |

All three floors share the SAME radical/vanishing orbit set
{ψ₁,ψ₃,ψ₄} (resp. {ψ₂,ψ₃,ψ₄}) — the gross base's Z₃² layer
structure — so the d₃ analysis applies across the family. **[Correction,
Entry 7 skeptic pass:** the original phrasing here, "all three floors
trace to the row d₃((3,F)) = 2", is overstated. It holds for the two
PULLBACK frames — bb_108: 6 = 2·3·d₃((3,F)) with the Z₂ layer factor 2
and the 3-fold pullback; bb_90: 10 = 5·d₃((3,F)) — but NOT for the
Z₂² base itself, whose one-sided floor 6 comes from the §3 layer engine
("≥ 3 nonzero layers, each even ⟹ ≥ 6", i.e. the d₃({1}) = 6 single-
orbit row), with no pullback (κ = 1, which would give d₃((3,F)) = 2,
not 6). The literally-shared object is the orbit SET, not one floor
formula.**] This is the concrete content of "the Entry-28 frame is
instance-generic" at the small-cycle level.

### Next

* Entry 5: the (iv)/(v) census sweep over the empirical class.

---

## Entry 5 (2026-06-12) — the census sweep: (iv)/(v) NEVER fail on the class

> **⚠ SUPERSEDED IN PART (Entries 6–7).** The "58/58 ⟹ (iv)/(v) are
> theorems of (a)+(b)" inference below is **WRONG**: the 58/58 holds
> only because every DB-stored member happens to carry the
> mirrored-projection pattern (iii). Broadening the sweep to other
> groups (Entry 6, verified Entry 7) found the **Z3×Z5 family: 6
> members with (a)+(b) but d = 4**. The corrected hypothesis adds
> (iii); see Entry 6 for the counterexamples and Entry 7 for the
> independent verification. The raw 58/58 numbers below are correct;
> the conjecture they were taken to support is not.

`scripts/a5_class_census_sweep.py` sweeps the Entry-3 hypotheses
(iv) (triangle censuses kill) and (v) ((2,2) table empty) over the
full empirical class — membership: floor-bearing frame
(Z₂×Z₂ with (i), or semisimple) ∧ mult-free ∧ dA ∩ dB = ∅, over all
exact-d Z6xZ6 + Z15xZ3 rows. Artifact: `data/a5/class_census.jsonl`.

**Corrigendum to Entry 1 §4:** the "29 members" figure on Z15xZ3 was
read off the cross-tab cell that also requires
coordinate-disjointness; plain {mult-free ∧ disjoint} has **33**
members there. The class is 25 + 33 = **58 members**, d ∈
{6: 24, 8: 19, 10: 15} — still zero d < 6 exceptions.

**Result: 58/58 pass the FULL grid (a)–(d).**

* (iv) passes 58/58 — no weight-3 triangle image is ever a translate
  of the partner polynomial. Census sizes are tiny (1–3 weight-3
  classes per side, hand-surveyable in every case).
* (v) passes 58/58 — the (2,2) translate-match table is empty for
  every member.
* Floors: all 25 Z6xZ6 members carry the Z₂²-engine (analytic ≥ 6);
  all 33 Z15xZ3 members have floors (10,10) and are
  pullback-friendly (every vanishing character of order 3) — the
  Entry-4 analytic route applies verbatim to each.

### Epistemic grade (stated carefully, per A_HANDOFF §1)

For the three template instances (bb_72 by A4, bb_108 by Entry 2,
bb_90 by Entry 4) the small-cycle theorem is fully analytic. For the
other 55 class members, what exists today is: (a)+(b) analytic,
(iv)/(v) MACHINE-verified. The (iv) censuses are small enough to
hand-survey per instance; the (v) check as run is a |G|³ enumeration
— NOT surveyable directly; the surveyable route is the per-instance
projection bookkeeping (gross §4.4 / Entry 2.3 / Entry 4.2 style),
demonstrated 3-for-3 but not yet written for the other 55. So the
honest statement is:

> the class theorem's hypotheses hold machine-verified on all 58
> members, its proof mechanism is hand-proven for all three frame
> shapes that occur, and zero counterexamples exist in the corpus —
> but "every member has an analytic d ≥ 6" awaits either 55 short
> per-instance write-ups or (better) the uniform lemma below.

### The sharpened analytic target

(iv)/(v) never failing is strong evidence they are THEOREMS of
(a)+(b), not independent hypotheses. Two concrete conjectures, in
decreasing strength:

* **(C-v)** mult-free + dA ∩ dB = ∅ + floor ≥ 6 ⟹ the (2,2) table
  is empty. (The bb_90 proof pattern suggests the mechanism: σ = 0
  is excluded by the floor, and σ ≠ 0 forces projection-weight
  mismatches; the missing piece is a presentation-free version of
  the weight bookkeeping.)
* **(C-iv)** same hypotheses ⟹ no weight-3 triangle image is a
  translate of the partner. (All observed kills: the image either
  repeats a coordinate value the partner takes distinctly, or
  vice versa — a difference-set-vs-support incidence statement.)

Proving these would upgrade all 58 (and every future class member)
to analytic in one stroke — the actual class theorem. That is the
ranked next step for this track.

### Next

1. Attack (C-v)/(C-iv) — the uniform kills (the class theorem
   proper).
2. The owed skeptic pass over Entries 2/4 (Entry-15/27 style).
3. Past d ≥ 6: the (M)-analogue on the bb_108/bb_90 covers (their
   true d is 10; the dangerous-sector factor-2 machinery is the
   gross playbook).

---

## Entry 6 (2026-06-13) — (C-iv)/(C-v) as stated are FALSE; the fix is (iii)

Attacked (C-iv)/(C-v) via the CRT component picture. The honest
verdict: **both conjectures as literally stated in Entry 5 (mult-free
+ dA∩dB=∅ + floor ≥ 6 ⟹ kill) are FALSE.** They omit a load-bearing
hypothesis — the mirrored-projection pattern (iii) — and the corpus
58/58 pass only because every DB-stored member carries (iii).

All numbers below are discovery/validation (A_HANDOFF §1); the
falsifying counterexamples are exhibits, the corrected statement is a
strengthened conjecture, and the located gap is presentation-bound.

### 6.1 Floor ≥ 6 must mean "Ann ≠ 0 with μ(Ann) ≥ 6" (a clarification)

First subtlety: literal "floor ≥ 6" is satisfied **vacuously** when
Ann(A) = 0 (no annihilator), which is the k = 0 case (A invertible in
F₂[G]). Z₅×Z₅ has 2160 mult-free+disjoint pairs with a (2,2) match,
all with Ann(A) = Ann(B) = 0 (k = 0, not codes). These are correctly
excluded by reading the floor hypothesis as "Ann(A), Ann(B) ≠ 0 and
μ ≥ 6". Even with that reading, the conjecture still fails (§6.2).

Also discovered: for mult-free weight-3 A, μ(Ann A) is NOT always
≥ 6 when nonzero — **Z₇×Z₃ and Z₁₄×Z₃ have mult-free A with
μ(Ann A) = 4** (the Z_ℓ-axis-confined sets a + (1+x^d+x^{2d})). So
"floor ≥ 6" is a genuine, non-vacuous, non-redundant condition. Good:
it makes (C-v) substantive, not a tautology.

### 6.2 The counterexamples (floor ≥ 6, mult-free, disjoint, (v) FAILS)

Exhaustive sweep over weight-3 (A, B) with mult-free dA, dB and
dA ∩ dB = ∅, cross-classified by (μ(Ann A), μ(Ann B)):

* **Z₁₅×Z₃**: 144 (2,2)-matches with **both floors = 8 ≥ 6**.
  Exhibit: A = {0, x, x⁴}, B = {0, x², x⁸} (both **monomials in the
  Z₁₅ axis**, y ≡ 0); match A·{0,x³} = x·B·{0,x⁶}, image
  {1, x, x³, x⁷}. k = 24 (a degenerate stacked code).
* **Z₉×Z₅**: 144 matches, **both floors = 24**; A, B confined to the
  Z₉ axis (x ≡ 0 mod the y-pattern), k = 8.
* (C-iv) mirror: 36/324/1872/1764 floor-≥6 (iv)-failures on
  Z₇×Z₃ / Z₉×Z₃ / Z₁₅×Z₃ / Z₉×Z₅.

So d ≥ 6's would-be class theorem is **not implied** by (a)+(b) alone.

### 6.3 The discriminator IS hypothesis (iii): mirrored projections

Comparing the counterexamples to a genuine member (bb_90) under the
ring homs π_x (collapse y) and π_y (collapse x):

| code | π_x(A) wt | π_y(A) wt | π_x(B) wt | π_y(B) wt | orient |
|---|---|---|---|---|---|
| bb_90 (member) | 1 | 3 | 3 | 1 | **mirrored** |
| Z₁₅×Z₃ ce | 1 | 3 | 1 | 3 | same |
| Z₉×Z₅ ce | 3 | 1 | 3 | 1 | same |

The members are **mirrored** (one polynomial monomial-in-x and the
other monomial-in-y — exactly (iii) / gross §4.4); the counterexamples
have **A, B with the same orientation**. Re-running the full sweep:

> **floor ≥ 6 + (iii) mirrored ⟹ ZERO (v)-failures and ZERO
> (iv)-failures** across Z₇×Z₃, Z₉×Z₃, Z₁₅×Z₃, Z₉×Z₅, Z₁₅×Z₅
> (28080 + 9216 + 3456 + 432 + 251280 mirror members checked; the
> 144+144 same-orientation failures are exactly the non-mirror cases).

**Corrected conjectures.** (C-iv′)/(C-v′): mult-free + dA∩dB=∅ +
[Ann ≠ 0, μ ≥ 6] + **(iii) mirrored-projection** ⟹ the (iv)/(v)
kills. These match the corpus (all 58 members have (iii)) and are the
honest class-theorem hypotheses — i.e. (iii) is NOT a presentation
artifact to be eliminated (the Entry-3.5/3.6 hope) but a TRUE
load-bearing structural hypothesis. The Entry-3.5 Aut-orbit
observation (only the 6 base-family members have (iii) in some
presentation on Z6×Z6) is the warning sign read correctly: the other
19 satisfy d ≥ 6 for reasons OUTSIDE the (iii)-route, so the class
theorem as provable by this mechanism covers only the (iii)-carrying
members.

### 6.4 The mechanism (semisimple), and the precise remaining gap

CRT/character route for the mirror case. Apply π_y (a ring hom, =
restriction to the trivial-on-x character block). For (iii): π_y(A) is
a full weight-3 polynomial a(y) ∈ F₂[Z_m], π_y(B) = monomial y^β. A
size-4 (2,2)-match A·(1+x^{δ_L}) = x^t B·(1+x^{δ_R}) projects to

    a(y)·(1+y^{δ_L,y}) = y^{t_y+β}·(1+y^{δ_R,y}),

RHS weight ∈ {0, 2}. **Weight lemma (proven, probe18):** for weight-3
a, |a·(1+y^δ)| ≤ 2 ⟺ supp(a) is a 3-term AP with common difference δ
(then weight exactly 2); otherwise ≥ 4. So the y-projection forces
either δ_L,y = 0 or supp(π_y A) a 3-AP. **[Correction, Entry 7: this
lemma is FALSE on even-period axes. The correct form has a second
branch — |a·(1+y^δ)| ≤ 2 ⟺ (3-AP with difference δ) OR (2δ ≡ 0 and
supp(a) contains a δ-orbit pair {p, p+δ}). The order-2 branch is LIVE
on bb_108's Z₆ y-axis; the templates dodge it by accident. Verified
0/29510. Any uniform class-theorem proof must use the corrected
form.]**

**The residue (the gap).** In EVERY mirror member, π_y(A) IS a 3-AP
(bb_90: π_y A = 1+y+y² = AP{0,1,2}) — 100% of 28080+... members. So
the y-projection alone never closes; it narrows to the AP common
difference. The mirror x-projection then narrows the x-gaps the same
way. But **both projections passing is NOT sufficient**: on Z₉×Z₃ /
Z₁₅×Z₃ there are 19008 / 67392 (δ_L, δ_R) pairs passing BOTH
projection tests while the full (v) still holds. The final kill is the
**translate-comparison of the actual 4-sets** (gross §4.4's
"x-multiplicity profile {2,1,1} vs {1,1,1}" / Entry 2.3's
"3 distinct y-coords vs profile {2,1}"). This residue is:
real, finite per instance, and the SAME presentation-bound step
flagged in Entry 3.4 — it has a uniform SHAPE (compare multiplicity
profiles of A·{0,δ_L} vs the partner translate) but no
presentation-free closed form yet. **That residue is the precise
remaining gap; it is exactly the part hand-done for the 3 template
instances and not yet for the other 55.**

### 6.5 Status

* (C-iv)/(C-v) as stated: **FALSE** (counterexamples §6.2). Not a
  theorem of (a)+(b).
* (C-iv′)/(C-v′) with (iii) added: **0 corpus counterexamples**,
  matches all 58 members; the right statement.
* Proof of (C-v′): the two-projection reduction is rigorous and
  presentation-free (the weight lemma is proven); the **multiplicity-
  profile residue** after both projections match is the open uniform
  lemma. Most likely break point of any "projections suffice" claim:
  the 3-AP residue branch, where members live and the residue is
  forced.
* Net for the track: the class theorem covers the (iii)-mirror
  members (which is all 58, and the gross/bb_90/bb_108 family) once
  the profile-residue lemma is written; it does NOT cover the
  non-mirror 19 of Entry 3.5 — those need a different argument or are
  outside this theorem.

### Next (revised)

1. The multiplicity-profile residue lemma (§6.4) — the one open
   uniform step; write it presentation-free or accept it as the
   per-instance finite check (then the theorem is (a)+(b)+(iii) ⟹
   d ≥ 6, with a surveyable residue per member).
2. Re-state the Entry-3.6 conjecture with (iii) as hypothesis (e);
   drop the Entry-3.5 hope that (iii) is eliminable.
3. (unchanged) skeptic pass over Entries 2/4; the cover (M)-analogue.

---

## Entry 7 (2026-06-13) — verification pass over the workflow outputs

**Provenance.** Entries 6 and the §6.x analysis, plus the corpus
counterexample hunt and the skeptic re-derivations, were produced by a
26-agent multi-agent workflow ("De-risk + verify + attack the BB
goal-2 class theorem", run 2026-06-13). Entry 6 is **machine-authored**
(the character-Fourier proof-panel agent). This entry is the
human-in-the-loop verification of the load-bearing claims, in the
Entry-15/27 skeptic tradition — nothing from the workflow is taken on
faith. Three of the workflow's own claims were checked and one of its
"corrections" was itself rejected (§7.3).

### 7.1 The refutation is REAL — verified independently, two ways

The core claim "(C-iv)/(C-v) as stated are false" is **confirmed**. I
verified the decisive Z3×Z5 family **before the workflow finished**,
from the live hunt scratch files, end to end:

* Canonical exhibit `262f0556…`: A = x + y² + y³, B = x² + y + y⁴
  over Z₃×Z₅. **Independent SAT: d_X = d_Z = 4** (matches the DB).
* mult-free dA, dB ✓; dA ∩ dB = ∅ ✓; one-sided floor
  μ(Ann A) = μ(Ann B) = **8 ≥ 6** (computed directly from the
  circulant kernel, not via d_H).
* Explicit witness from the substrate H_X (convention-correct): a
  weight-4 **(3,1)** Z-logical, u_L = {(0,2),(0,3),(1,0)} a
  dA-triangle whose A-image equals B·{(0,0)} — i.e. a triangle image
  that IS a translate of the partner. A textbook (C-iv) failure.

So the conclusion stands on the six Z3×Z5 stored rows, which I
verified, **independently of** the proof panel's messier fresh
witnesses (one of which — the synthesis flagged — was not even
mult-free, so not a real member; the refutation does NOT depend on
it).

### 7.2 (iii) is exactly the discriminator — confirmed

All six Z3×Z5 violators have **(iii) = False** (projection pattern
"other": both A and B monomial in the SAME axis, π_x both singletons).
Both templates have **(iii) = True** (mirrored/gross pattern). So the
Entry-6 correction "add (iii) mirrored-projection" is the right fix,
and Entry 6's §6.3 framing is sound.

### 7.3 Corrections to the workflow's own output

* **Entry 6 §6.4 weight lemma is BUGGY** (caught by the
  character-Fourier refute agent, verified here). "|a·(1+y^δ)| ≤ 2 ⟺
  3-AP with difference δ" is false on even-period axes: S = {0,1,3} in
  Z₆ with δ = 3 gives weight 2 without being a 3-AP, because 2δ ≡ 0
  and {0,3} is a δ-orbit pair. Corrected form (the second branch added
  inline at §6.4): **(3-AP, diff δ) OR (2δ ≡ 0 and supp ⊇ a δ-orbit
  pair)** — exhaustively verified **0/29510** violations over Z_n,
  n = 4..16. This branch is **live on bb_108's Z₆ y-axis**; the three
  templates dodge it by accident (bb_90's axis is the odd Z₃;
  bb_108's π_y A = 1+y+y² has no 3-orbit pair), so the template kills
  in Entries 2/4 are unaffected — but **any uniform class-theorem
  proof must use the corrected lemma**. This is the sharpest technical
  finding of the run.
* **Entry 4 §4.4 "all three floors trace to d₃((3,F)) = 2" was
  overstated** — corrected inline. True for the two pullback frames;
  the Z₂² base floor 6 comes from the layer engine (d₃({1}) = 6), not
  κ·d₃((3,F)). Shared object is the orbit set, not one formula.
* **Entry 6 §6.1 spot-check**: the substantive claim "floor ≥ 6 is
  non-vacuous — mult-free weight-3 A can have μ(Ann A) = 4" is
  **confirmed on Z₇×Z₃** (e.g. A = {0,1,3} on the x-axis, 6 such sets,
  μ = 4, dim 9). The Z₁₄×Z₃ half of that claim did NOT reproduce in my
  search (likely the dim-16 enumeration cap) — treat as unverified.
* **REJECTED skeptic "correction":** the bb_108 skeptic agent claimed
  Entry 2 §2.3's triangle-class counts are wrong ("3 → 4 up to
  transl+neg"). My re-derivation gives **2 translation-classes for
  (1,3) and 3 for (3,1)** — exactly what Entry 2 states. The agent
  used an inconsistent canonicalization; **Entry 2 is correct, no
  change made.** (Recorded as a reminder that agent "corrections" get
  re-derived too.)

### 7.4 Skeptic verdict on the standing theorems (accepted)

The three template results — d(gross) (A4), d(bb_108) ≥ 6 (Entry 2),
d(bb_90) ≥ 6 (Entry 4) — **survive** independent re-derivation
(scb = true, SAT-independent = true for each). The flagged gaps are
all non-load-bearing prose (the §4.4 overstatement above; the §4.1
"Ann = I(V)" notation being an F₂-semisimple-annihilator shorthand,
not a literal complex-Fourier-support statement; the Theorem-B
transfers inherited-as-generic rather than re-derived entrywise).
None touches a d ≥ 6 conclusion. The analytic core is intact.

### 7.5 Net state of the track

* **(C-iv)/(C-v) as stated [(a)+(b) only]: dead.** Z3×Z5 d = 4 family,
  verified.
* **(C-iv′)/(C-v′) [+ (iii) mirrored]: the live conjecture**, zero
  counterexamples across every sweep; the honest class-theorem
  hypothesis set.
* **The single open uniform step**: the multiplicity-profile residue
  lemma (§6.4) — now with the corrected even-period weight lemma as
  its first ingredient. Either prove it presentation-free, or accept
  it as a per-instance finite surveyable check, yielding
  **"(a)+(b)+(iii) ⟹ d ≥ 6, with a 2-step surveyable residue per
  member"** — which already covers all 58 corpus members and the full
  gross/bb_90/bb_108 family.
* The six Z3×Z5 d = 4 rows are the canonical **non-mirror exclusions**;
  any future sweep that re-admits them has dropped (iii).

### Next (consolidated)

1. The multiplicity-profile residue lemma, using the corrected
   even-period weight lemma (§6.4 + §7.3) — the one open uniform step.
2. The cover (M)-analogue to push the template family past 6 (true
   d = 10 for bb_90/bb_108) — the gross Entries 16–28 playbook.
3. Housekeeping: fold (iii) into the Entry-3.6 conjecture as a
   load-bearing hypothesis (Entry 6 did this; it is now the headline).
