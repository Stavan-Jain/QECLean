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

All three floors trace to the SAME dictionary row d₃((3,F)) = 2 —
the gross base's Z₃² layer dictionary is doing all the one-sided
work across the family. This is the concrete content of "the
Entry-28 frame is instance-generic" at the small-cycle level.

### Next

* Entry 5: the (iv)/(v) census sweep over the empirical class.

---

## Entry 5 (2026-06-12) — the census sweep: (iv)/(v) NEVER fail on the class

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
  of the partner polynomial. Census sizes are tiny: exactly 1
  weight-3 class per side on the Z6xZ6 members, 2 per side on the
  Z15xZ3 members — hand-surveyable in every case.
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
