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

---

## Entry 8 (2026-07-06) — A15 execution session 1: field-genericity
## PROVEN-SWEPT + the residue lemma re-shaped (difference multisets)

First execution session of the A15 plan
(`A15_base_floor_class_plan.md`): the §1.3 verification sweep and the
T1.1 falsify-first hunt, both landed. All numbers
discovery/validation (A_HANDOFF §1). Scripts:
`a15_field_generic_engine_check.py`, `a15_t11_residue_hunt.py`.

### 8.1 The Z₂²-engine support dichotomy is FIELD-GENERIC (verified)

Sweep E1/E2/E2′ over K = F₄, F₈, F₁₆, F₆₄ (exhaustive at each field
for E2/E2′; E1 exhaustive at F₄, sampled 400×400 above):

* **E1.** For D = aU + bV + cUV ∈ K[Z₂²], (a,b) ≠ 0: D² = 0 and
  x·D = 0 ⟺ x₀ = 0 ∧ x₁b + x₂a = 0, i.e. Ann(D) = span_K{aU+bV, UV}
  = (D), dim 2 — at every field. PASS.
* **E2.** Every nonzero α·D + β·UV has ≥ 3 nonzero slot coordinates
  ⟺ **{0, a, b, a+b} pairwise distinct** (⟺ a ≠ 0, b ≠ 0, a ≠ b);
  c is irrelevant (it absorbs into β). When distinctness fails the
  minimum support is exactly 2 (floor degrades to ≥ 4-with-parity,
  not 6). PASS, all fields.
* **E2′.** The distinctness condition ⟺ **D's four slot values are
  pairwise distinct** — the *widened engine predicate*. The checker's
  `ENGINE_RADICAL` ("one zero + three distinct") is the special case
  c ∈ {0, a, b, a+b}; the zero-count requirement is NOT load-bearing.
  PASS, all fields (262,080 triples at F₆₄).

**Instance consequence (E3).** Control bb_72: all radical components
pass the widened predicate; exact w2/w4/w6 kernel exhaustion (+PAR)
reproduces μ(Ann A) = μ(Ann B) = 6; 500-sample layer structure clean.
**Target Z₆×Z₁₄ [[168,12,6]]** (A = 1+y+x³y³, B = 1+x+x²y⁷, the A8
base; components F₂·F₄·F₈²·F₆₄²): **all radical components pass the
widened predicate** — the engine's one-sided floor applies verbatim
OFF the Z₃² odd part. Exact exhaustion: μ(Ann B) = 6 (w6 witness, no
w2/w4), μ(Ann A) ≥ 8 (consistent with A8's reported 12); 0 layer-
structure violations in 500 samples per side.

**Corrections this licenses**: the §3.2 frame table's Z₂² row and the
extensibility doc §4(a) framing "co-point dichotomy = |F₄ˣ| = 3"
conflate SUPPORT rigidity (field-generic, floor-bearing) with VALUE
rigidity (F₄-only, classification-bearing). Hypothesis (a)'s engine
column widens to Z₂²-frames with ANY odd part, via the widened
predicate.

### 8.1b The hand proof (short; the sweep above is confirmation)

**Lemma (field-generic engine).** Let K be any field of
characteristic 2, R = K[Z₂²] = K[U,V]/(U², V²) with U = 1+s_x,
V = 1+s_y, and D = aU + bV + cUV with (a,b) ≠ (0,0). Then:

1. *(products)* For x = x₀ + x₁U + x₂V + x₃UV:
   x·D = x₀·D + (x₁b + x₂a)·UV, using U² = V² = 0 and U·UV = V·UV
   = 0. In particular D² = 0 (char-2 squaring kills cross terms; U²,
   V², (UV)² all vanish) and D·UV = 0.
2. *(annihilator)* D and UV are linearly independent ((a,b) ≠ 0
   gives D a nonzero U- or V-coefficient; UV has none), so by (1)
   x·D = 0 ⟺ x₀ = 0 and x₁b + x₂a = 0 ⟺ x ∈ K·(aU+bV) ⊕ K·UV
   (parametrize (x₁, x₂) = t·(a, b): x₁b + x₂a = 2tab = 0, and
   conversely if a ≠ 0 set t = x₁/a). Also by (1),
   D·R = K·D + K·UV = K·(aU+bV) ⊕ K·UV, so **Ann(D) = (D)**,
   K-dimension 2.
3. *(support dichotomy)* In the slot (group-element) basis
   (1, s_x, s_y, s_xs_y): U = (1,1,0,0), V = (1,0,1,0),
   UV = (1,1,1,1). A nonzero ideal element z = α(aU+bV) + β′·UV has
   slot vector (α(a+b)+β′, αa+β′, αb+β′, β′). If α = 0: all four
   slots equal β′ ≠ 0 (full support). If α ≠ 0: the slots are
   α·{a+b, a, b, 0} + β′, so a slot vanishes exactly when β′/α hits
   the corresponding member of {a+b, a, b, 0}. Hence
   * {0, a, b, a+b} pairwise distinct (⟺ a, b ≠ 0, a ≠ b) ⟹ at most
     one zero slot: **every nonzero z ∈ (D) has ≥ 3 nonzero slots**;
   * otherwise choosing β′/α = the repeated value gives exactly two
     zero slots: the dichotomy fails at support 2.
   The slot values of D itself are c + {a+b, a, b, 0}, so the
   distinctness condition ⟺ **D's four slot values are pairwise
   distinct** (E2′). ∎

**Corollary (one-sided floor, widened hypothesis).** Let
G = Z_ℓ × Z_m have 2-part Z₂², A ∈ F₂[G] with |A| odd, and suppose
every CRT component Â_j is a unit or a radical D_j whose (a_j, b_j)
satisfy the distinctness condition (no zero components). Then
μ(Ann A) ≥ 6. *Proof.* For 0 ≠ z ∈ Ann(A): some ẑ_j ≠ 0 (CRT
injectivity); j is not a unit component (units force ẑ_j = 0); at
radical j, ẑ_j ∈ Ann(D_j) = (D_j) by (2), so it has ≥ 3 nonzero
slots by (3), i.e. z has ≥ 3 nonzero layers (V_j(z)[s] ≠ 0 needs
z_s ≠ 0). |A| odd makes Â₀ a unit (augmentation 1), so ẑ₀ = 0: every
layer weight |z_s| is even, and nonzero layers weigh ≥ 2. Total
≥ 3·2 = 6. ∎ (A4 §4.1 verbatim; only the hypothesis is widened — no
|F₄ˣ| = 3 input anywhere.)

### 8.2 T1.1 hunt, frame 1 (Z₉×Z₆ — first LIVE even-axis frame)

Self-test: bb_108's stored presentation passes all gates + (iv)+(v)
(Entry-2 consistency). Enumeration: 1431 weight-3 translation
classes/side → mirrored+mult-free → floor/Ann gates (exact w2/w4
kernel exhaustion + PAR — no engine reasoning load-bearing) → 192
mono-x × 282 mono-y polys → **44,064 members** with disjoint diff
sets. Run 1 (first 20,000 members): **0 (iv) violations, 0 (v)
violations**. [Full-frame + Z₆×Z₁₀/Z₁₅×Z₆/Z₆×Z₁₄ runs: §8.4.]

**Pipeline telemetry (the load-bearing discovery).** Classifying the
(2,2) table of 120 members through the E6.4 pipeline:

| stage | kill | rows |
|---|---|---|
| s1 | y-projection weight | 232,200 |
| s2 | x-projection weight | 94,760 |
| s3 | size mismatch | 4,368 |
| s3 residue | profile x / y / both | 640 / 856 / 160 |
| s3 residue | **profile "neither"** | **4,096** |

The projections are far LEAKIER here than on the three template
instances (~48 residue rows/member vs ~1), and **71% of the residue
is profile-resistant**: σ_L ≠ t·σ_R for every t, yet the x- AND
y-multiplicity profiles agree. ⟹ **the multiplicity-profile residue
lemma (E6.4's sketch) is the WRONG SHAPE for the class** — it closes
the three templates by luck of their tables, not by mechanism.
(Contrast: the (iv) triangle kills are 100% profile-separable —
63,030 records, zero "neither" — so (iv)'s uniform lemma CAN stay
profile-based.)

### 8.3 The residue lemma re-shaped: DIFFERENCE-MULTISET incidence

For a size-6 (disjoint-union) row, translation-invariance gives the
exact multiset identity

    d(σ_L) = 2·dA ⊎ (dA ∪ {0} + δ_L) ⊎ (dA ∪ {0} − δ_L),

so a match σ_L = t·σ_R forces d(σ_L) = d(σ_R) as multisets, and
counting any d ∈ dA (multiplicity ≥ 2 on the left; dA ∩ dB = ∅ kills
the 2·dB contribution on the right; the two shifted sets contribute
≤ 1 each) forces the **incidence system**

    d + δ_R ∈ dB ∪ {0}  AND  d − δ_R ∈ dB ∪ {0}   for EVERY d ∈ dA,
    (mirror: e ± δ_L ∈ dA ∪ {0} for every e ∈ dB)

— 12+12 Sidon-type incidences. **Probe (40 Z₉×Z₆ members + 25
Z₆×Z₁₀ members, scratchpad `a15_diffmultiset_probe.py`, now baked
into the hunt script): the difference multiset separates 1580/1580
profile-resistant rows, and the incidence criterion alone kills
1512/1512 size-6 rows.** Zero resistant rows.

Re-shaped T1 target (replaces the profile lemma):

> **(C-res) residue lemma, difference-multiset form.** Under
> (b) D1 ∧ D2 [+ (iii), + floor]: no (δ_L, δ_R) satisfies the
> incidence system; hence no size-6 (2,2) match. Size-4 rows
> (δ_L ∈ dA: one internal overlap) need the corrected multiset
> formula — 68/68 probed rows are also dm-separated.

This is FRAME-AGNOSTIC (no coordinate projections at all — they
survive only as cheap pre-filters) and lives in the same D1/D2
difference-set language as the extensibility-doc §6 two-sided half —
the two-sided theory and the (v)-kill now share one vocabulary. The
proof obligation is a finite incidence analysis of (dA, dB, δ);
plausible uniform route: |dA| = 6 elements each needing BOTH signs to
land in the 7-element dB ∪ {0} forces |(dA + δ_R) ∩ (dB ∪ {0})| = 6
— a near-translation of difference sets, which (iii)'s coordinate
separation should refute outright (x(dA) concentrated on ≤ 2 values
vs x(dB) spread, gross-style). To be drafted as the Entry-9 lemma.
**[Superseded by Entry 9: the ⊎(dA∪{0}±δ) shorthand under-counts —
the ±δ atoms carry multiplicity 3 (6 at 2-torsion) — and the probe's
incidence criterion was only approximately necessary. Entry 9 gives
the exact accounting and the resulting three-branch kill; the 100%
dm-separation figures above are unaffected (they compared true
multisets).]**

### 8.4 Frame completions

| frame | members checked | (iv) fails | (v) fails |
|---|---|---|---|
| Z₉×Z₆ (Z₂ frame, even y) | **44,064 / 44,064 (full)** | 0 | 0 |
| Z₆×Z₁₀ (Z₂² frame, both even, odd part Z₃×Z₅) | **7,776 / 7,776 (full)** | 0 | 0 |
| Z₁₅×Z₆ (Z₂ frame, even y) | 20,000 / 248,904 (cap) | 0 | 0 |
| Z₆×Z₁₄ (Z₂² frame, odd part Z₃×Z₇) | 20,000 / 49,788 (cap) | 0 | 0 |

**Grand total: 91,840 members, zero (iv)/(v) violations, zero
`DM-RESISTANT` alarms** (grep-confirmed on both logs) —
(C-iv′)/(C-v′) survives its first live even-axis frames with the
orbit-pair branch exercised, and the difference multiset separated
every profile-resistant row everywhere one arose (Z₉×Z₆: 4,392 rows
over 150 classified members; Z₁₅×Z₆: 2,796 over 80; **Z₆×Z₁₀ and
Z₆×Z₁₄: zero profile-resistant rows at all** — the projections are
tight on those frames). Per-row invariant telemetry retained
(`data/a15/t11_*.jsonl` + logs). Perf note for reruns: verdict_v is
~0.9 s/member at |G| = 90 (the right-image dictionary is |G|²);
vectorize before scaling past the 20k caps; the uncapped Z₁₅×Z₆
tail (228,904 members) is queued for a vectorized pass.

### Next

1. Draft **(C-res)** (§8.3) as the uniform (v)-kill; prove the
   size-4 variant's multiset formula; keep the profile lemma for
   (iv) only.
2. Finish the frame battery; add a DM-RESISTANT alarm key (done —
   any future row the difference multiset fails to separate prints
   `s3-residue-DM-RESISTANT`).
3. T3a.1: write the hand proof of E1/E2/E2′ (short; the sweep is
   confirmation) and re-scope the checker's `engine_radical`.

---

## Entry 9 (2026-07-06) — (C-res) proven-in-structure: the exact
## multiset accounting and the three-branch (v)-kill

Continuation of Entry 8 (§8.3's re-shaping), same session. The (v)
obligation — no (2,2) translate match A·{0,δ_L} = t + B·{0,δ_R} — is
now killed by a three-branch argument whose first two branches are
proven lemmas and whose third is reduced to a tiny pinned census,
machine-cleared corpus-wide. Verification script (each check = one
proof step): `a15_e9_residue_lemma_checks.py` (V1–V6). Standing
hypotheses: |A| = |B| = 3, D1 (Sidon), D2 (dA ∩ dB = ∅), no-period
(the w2 gate), (iii) mirrored shapes, floor-bearing frame — of which
the (v)-kill consumes only D1, D2, no-period, (iii), and 4 ∤ ℓ ∧
4 ∤ m; the μ ≥ 6 floor is NOT used here.

### 9.0 Correction to §8.3's shorthand

The formula "d(σ_L) = 2·dA ⊎ (dA∪{0} ± δ_L)" under-counts: the ±δ_L
atoms carry multiplicity 3 each (they merge to one atom of
multiplicity 6 when 2δ_L = 0), and the probe's incidence criterion
was approximately-necessary only. Exact accounting below; the §8.3
dm-separation figures compared true multisets and stand.

### 9.1 The exact identities (V1: 2,500 formula checks, both frames)

Size 6 (δ_L ∉ dA; σ_L = A ⊔ (A + δ_L)):

    d(σ_L) = 2·dA ⊎ (dA + δ_L) ⊎ (dA − δ_L) ⊎ {δ_L}³ ⊎ {−δ_L}³.

Size 4 (δ := δ_L ∈ dA; by D1 the ordered pair a_i − a_j = δ is
unique; a_k the third element; e := a_j − a_k):
σ_L = {a_j, a_k, a_j + 2δ, a_k + δ} and

    d(σ_L) = ±{δ, 2δ, e, e − δ, e + δ, e + 2δ}.

Size 2 is vacuous: it needs δ_L ∈ dA with 2δ_L = 0, but a 2-torsion
difference has multiplicity 2 in the ordered-difference multiset,
violating D1. (Mirror statements for σ_R with dB, δ_R, f.)

### 9.2 Branch 1 — the atom dichotomy (proven)

**Lemma A.** If σ_L = t + σ_R (sizes 6), then
δ_L = ±δ_R, or (δ_L ∈ dB and δ_R ∈ dA).

*Proof.* d(σ) is translation-invariant, so the multisets agree. By
§9.1, mult_{d(σ_L)}(δ_L) = 3 + [2δ_L ∈ dA] + 3·[2δ_L = 0] ≥ 3, while
mult_{d(σ_R)}(δ_L) = 2·[δ_L ∈ dB] + [δ_L−δ_R ∈ dB] + [δ_L+δ_R ∈ dB]
+ 3·[δ_L = δ_R] + 3·[δ_L = −δ_R]. If δ_L ≠ ±δ_R and δ_L ∉ dB this is
≤ 2 < 3. The mirror count at δ_R forces δ_R ∈ dA likewise. ∎

(V2: asserted on every size-6 row of both frames — 1.77M rows on
Z₉×Z₆ [800-member slice], 21.8M on Z₆×Z₁₀ [all 7,776 members]; the
atom step alone kills 94.7% / 95.5% of rows.)

### 9.3 Branch 2a — δ_L = ±δ_R =: δ (proven under (iii), 4 ∤ ℓ)

WLOG δ_L = δ_R = δ (σ_R(−δ) is a translate of σ_R(δ)); δ ∉ dA ∪ dB.

**Lemma B (translate rigidity).** A size-6 match with δ_L = ±δ_R
forces dB = dA + δ = dA − δ.

*Proof.* Count d(·) over d ∈ dA: mult_L(d) = 2 + [d−δ ∈ dA] +
[d+δ ∈ dA] ≥ 2 (atoms don't contribute: ±δ ∉ dA). On the right,
mult_R(d) = [d−δ ∈ dB] + [d+δ ∈ dB] ≤ 2 (D2 kills 2·dB; d ≠ ±δ).
Summing over the six d and comparing forces per-element equality
at 2: d ± δ ∈ dB for every d ∈ dA, i.e. dA + δ ⊆ dB ⊇ dA − δ; sizes
(6 = 6) give equality. ∎

**Lemma C (shift lemma; V4, exhaustive ℓ ≤ 24).** For 4 ∤ ℓ, the
x-coordinate difference multiset {±p, ±q, ±(p+q)} of a 3-subset of
Z_ℓ (p, q, p+q ≠ 0 — the (iii) B-shapes guarantee this) is never a
shift of an A-shape x-profile — {0², u², (−u)²} (u ≠ 0; = {0², u⁴}
at 2u = 0) or {0⁶}. At 4 | ℓ the exceptions are exactly the APs with
an order-4 common difference.

*Proof sketch (hand, verified by V4).* Shifts preserve the
multiplicity pattern. A symmetric multiset {±p, ±q, ±r} with r = p+q
and all nonzero has pattern (3 values × mult 2) only if its value
set is negation-closed, which forces either three distinct nonzero
2-torsion values (impossible in a cyclic group) or a pair {w, −w}
plus a 2-torsion value, which solves to an order-4 element (4 | ℓ);
the patterns (2,4) and (6) solve only degenerately. The A-shapes
have patterns (2,2,2), (2,4) (2-torsion u), or (6). ∎

**Theorem D (2a kill).** Under D1, D2, (iii), no-period, and
4 ∤ ℓ ∧ 4 ∤ m: no size-6 match has δ_L = ±δ_R. *Proof.* Lemma B
gives dB = dA + δ, so x(dB) = x(dA) + δ_x as multisets; Lemma C
forbids it (dA carries an A-shape x-profile by (iii); dB carries a
3-subset difference multiset in x with nonzero entries). ∎

Two notes. (1) The dm invariant ALONE cannot close 2a: if
dB = dA + δ did hold, the two §9.1 multisets would coincide
identically — Lemma C (hence (iii) + the frame) is load-bearing,
and this branch is where DM-resistant rows would have lived. (2)
Corpus-wide the rigidity premise never holds anyway: V3 finds
0/44,064 (Z₉×Z₆) and 0/7,776 (Z₆×Z₁₀) members with dB in dA's
translate class.

### 9.4 Branch 2b (S2) — δ_L ∈ dB ∧ δ_R ∈ dA: pinned census (reduced)

For S2 rows, the proven projection-weight machinery (the corrected
even-period lemma, E7.3) pins hard:

* B2-shape (axis-confined B) dies at once: δ_L ∈ dB gives δ_Ly = 0,
  so |π_y σ_L| = 0, while δ_R ∈ dA has δ_Ry ≠ 0 ((iii) forbids the
  spike sharing a y with the pair), so |π_y σ_R| = 2. ✗
* B1-shape survivors must have: δ_Ly = ±h (dB's slant y-gap) with
  |a(y)(1+y^{δ_Ly})| = 2 (a is a 3-AP of difference δ_Ly, or the
  orbit-pair branch), and δ_Rx = ±u (dA's slant x-gap) with
  |b(x)(1+x^{δ_Rx})| = 2 (mirror). In the 3-AP sub-branch, x(dB) =
  {±u², ±2u} regardless of the spike's AP position, and the dA-slice
  count of Lemma B's type then bounds the compatible x-fibers at
  exactly 6, forcing y-alignments (δ_Ry ∈ {±w} ∩ {±s, ±s′}) that
  make a(y) an AP for a second difference — i.e. a(y) a coset of an
  order-3 subgroup — the residual census shape.

Numbers: Z₉×Z₆ (800-member slice): 28,800 S2 rows → **160 S2-hard**
(0.2/member; all in the 3AP/3AP sub-branch, e.g. A =
{(0,0),(0,1),(1,2)}, B = {(0,0),(1,0),(2,5)}, δ_L = (1,5) ∈ dB,
δ_R = (1,1) ∈ dA) → **0 DM-equal**. Z₆×Z₁₀ (all members): 279,936
S2 rows → **0 S2-hard** — the pinning annihilates the branch there.
Status: per-member surveyable census (≤ a few rows), machine-cleared
everywhere; the uniform finish (the order-3-coset case analysis) is
the remaining crumb.

### 9.5 Size 4 — the coupled system (generic derivation + clearance)

For a size-4 match (δ := δ_L ∈ dA, δ′ := δ_R ∈ dB), §9.1 gives
d(σ_L) ⊇ dA = {±δ, ±e, ±(e+δ)} and six values outside dA (D2 keeps
dB off them), so generically the match forces the **coupled system**

    dA = {±2δ′, ±(f−δ′), ±(f+2δ′)}   and
    dB = {±2δ, ±(e−δ), ±(e+2δ)},

a doubling-incidence structure (2δ ∈ dB for δ ∈ dA — the
`is_frobenius_related` gate's kin). V6, all size-4 rows: Z₉×Z₆
108,000 rows (3,000 members) and Z₆×Z₁₀ 279,936 rows (all members):
**0 rows satisfy even one leg of the system; 0 DM-equal**.
Coincidence sub-branches (e.g. 2δ ∈ dA) are folded into the direct
dm check. Uniform infeasibility proof of the system = second
remaining crumb (torsion equations; expect (iii) + 4∤ℓ to close it
by the Lemma-C method).

### 9.6 Status of (C-v′) after this entry

The (v)-kill = Lemma A (proven) + Theorem D (proven, hypotheses D1 ∧
D2 ∧ (iii) ∧ no-period ∧ 4∤ℓ ∧ 4∤m) + S2 census (pinned by proven
lemmas; empty or ≤O(1) rows/member, machine-cleared on 51,840+
members) + size-4 system (necessary condition proven generically;
machine-cleared). What remains of Entry 6's single amorphous
"multiplicity-profile residue": two structured crumbs — the S2
order-3-coset case analysis and the size-4 system's infeasibility.
The (iv) obligation stays profile-based (Entry 8.2: 100%
profile-separable). Certifier consequence (T1.2): the per-member (v)
obligation is now [translate-class compare: one canonicalization] +
[S2-hard census: ≤ few rows] + [size-4 dm rows: ≤ 36] — all
surveyable, replacing the |G|³ table.

### Next

1. Entry 10: the two crumbs — S2's order-3-coset analysis; size-4
   system infeasibility under (iii) + 4∤ℓ (Lemma-C-style torsion
   arithmetic).
2. Wire the three-branch kill into the recipe-certifier (T1.2) and
   re-run the 58-member corpus + the hunt frames through it.
3. Queued falsify-first: the off-(iii) rigidity hunt (∃δ:
   dB = dA + δ with D1∧D2) on 4|ℓ frames — explicit (2,2)-match
   codes would witness (iii)/frame-necessity for branch 2a.

---

## Entry 10 (2026-07-06) — the two crumbs closed: S2's D2-funnel and
## the size-4 family collapse

Same-day continuation of Entry 9. Both residual crumbs of the
(v)-kill are now resolved — S2 by a fully-proven funnel into a D2
contradiction, size-4 by an exact rigidity lemma + a matching
dichotomy that collapses every branch into finite torsion families,
each dead against D2 / D1 / a counting bound / hypothesis (a) — with
one honestly-flagged polish item. Verification:
`a15_e10_size4_s2_kills.py` (W1–W5b). Machine numbers below are
from Z₉×Z₆ (1,200-member slice) + Z₆×Z₁₀ (full) + the fixed ambient
censuses.

### 10.1 Theorem G — the S2 kill (branch 2b closed)

Under D1 ∧ D2 ∧ (iii) ∧ no-period ∧ 4∤ℓ ∧ 4∤m, no size-6 match has
δ_L ∈ dB ∧ δ_R ∈ dA. With Entry 9's Lemma A and Theorem D this
closes size 6: **no size-6 (2,2) match exists at all.**

*Proof sketch (funnel).* The Σ-count over dA (Entry 9's method, with
the S2 atom terms: Σ_R picks up +6 from δ_R ∈ dA) forces
|dA ∩ (dB+δ_R)| + |dA ∩ (dB−δ_R)| ≥ 6. The pinning (Entry 9 §9.4)
gives b(x) = AP(δ_Rx) with δ_Rx = ±u, so x(dB) = {±u², ±2u}
(any spike position), and the x-fiber caps bound the two
intersections by 3+3 (generic u) — equality forces every
x-compatible element to land in dA, pinning the y-data:
{δ_Ry, δ_Ry ∓ h} = {±w}, hence h = ±2w and {s, s′} = {w, 2w} (up to
mirror), i.e. a(y) = AP(w). The pinning also says a(y) = AP(±h) =
AP(2w); a 3-set that is an AP for both w and 2w forces 3w = 0
(difference-multiset comparison; the 5w = 0 option fails
multiplicities). With 3w = 0, dA's slant set becomes all four
(±u, ±w) — and dB always carries a slant with x-part ±u and y-part
±h = ∓w, which therefore lies in dA: **dA ∩ dB ≠ ∅, contradicting
D2**. Sub-branches: 3u = 0 (x(dB) = {±u³}) reruns the count with
per-fiber caps 2 and lands in the same clash via h ∈ {±w, ±2w};
b-side orbit-pair dies by the fiber count (≤ 4 < 6); a-side
orbit-pair forces 4w = 0 ⟹ 2w = 0, excluded because D1 forbids
2-torsion differences ((0,w) would be one). ∎

Machine (W3): all pinned S2-hard rows are AP/AP (160 on Z₉×Z₆, 0 on
Z₆×Z₁₀; 0 orbit-pair rows either side), and **0 rows satisfy the
forced-condition set** [a = AP(w) ∧ (h = ±2w ∨ (3u = 0 ∧ h = ±w))] —
the funnel's terminal configuration never coexists with the D2 gate,
as the proof demands.

### 10.2 Size 4 — exact rigidity, the dichotomy, the family collapse

**Lemma E (exact rigidity; upgrades E9.5's "generic").** A size-4
match forces dA = {±2δ′, ±(f−δ′), ±(f+2δ′)} and
dB = {±2δ, ±(e−δ), ±(e+2δ)}, all six values distinct on each side.
*Proof:* Σ-count over dA: the ±{δ, e, e+δ} multiset hits each dA
element exactly once (D1), the right side reaches 6 only if every
one of its six non-dB values lands in dA, and per-element equality
at 1 makes the cover exact; symmetrically over dB. ∎ (W1: the
Σ-formula asserted on all 86,400 sampled size-4 rows; joint
rigidity holds 0 times on gate-passing members.)

**Lemma F (matching dichotomy).** σ_L = t + σ_R makes σ_L's pair
decomposition (gaps {δ, 2δ}) and σ_R's ({δ′, 2δ′}) two matchings of
ONE 4-set, so one of:
- *aligned* (same matching, gap-aligned): δ = ±δ′ — **D2-dead**;
- *crossed* (same matching, gaps swapped): δ = ±2δ′ ∧ 2δ = ∓δ′ ⟹
  3δ′ = 0 (then 2δ′ = −δ′ gives δ = ±δ′ — **D2-dead**) or 5δ′ = 0 —
  the **pentagonal family**;
- *M₂* ({±e, ±(e+δ)} = {±δ′, ±2δ′}): e or e+δ ∈ ±dB — **D2-dead**;
- *M₃* ({±(δ−e), ±(e+2δ)} = {±δ′, ±2δ′}): the **triangular
  families**, resolved by the closure constraint (dB must itself be
  a 3-set difference set): every sign-assignment forces one of
  3δ = 0-with-3τ = 0 (T₃-confined: |dA ⊎ dB| = 12 > 8 = |Z₃² ∖ 0| —
  **counting-dead**), τ = 3δ with 9δ = 0 (dB acquires 2δ twice —
  **D1-dead**), or 5δ = 0 / 15-torsion **cyclic-confined families**.

**Lemma H (the pentagonal kill).** The crossed-5-torsion analysis
confines all data to the (5,5)-torsion subgroup T₅ ≅ Z₅² (both
coordinates of δ′, e, f are 5-torsion by the (iii)-profile order
argument), so dA ⊂ T₅ and A lies in a single T₅-coset. In char 2
there are **no vanishing weight-3 sums of 5th roots of unity**
((1+ζ)⁵ = ζ + ζ⁴ ≠ 1 for ζ ∈ μ₅ ∖ {1}), so every CRT component of Â
is a unit and Ann(A) = 0 — **hypothesis (a) is violated**. ∎
(W4: the branch is genuinely live at the difference-set level — 960
D1∧D2 σ-shape matches on Z₅², all realizable; W4b: all 276 weight-3
polys on Z₅² have all-unit components — the kill is real and
needed, not vacuous.)

**The confined families vs the gates (machine-exhaustive).** The
15-torsion/cyclic-confined families are also live at the
difference-set level: W5 finds 4,560 D1∧D2 σ-shape matches across
the family ambients — all at 5 | n, i.e. every live confined family
is 5-torsion-flavored, and these are exactly Entry 6's non-mirror
exclusion zone seen structurally (the diagnosed hits are
axis-confined, same-orientation pairs with Ann = 0). **W5b realizes
every hit on the 2-D ambient list (Z_n×Z₃ n ≤ 30, Z_n×Z₅ n ≤ 20,
Z₅²) — 19,120 realized matches — and 0 satisfy
(iii)-mirrored ∧ Ann ≠ 0 ∧ no-w2/w4.** Polish item (flagged): the
by-hand (iii)∧(a)-incompatibility for arbitrary embeddings of the
confined families (diagonal cyclic subgroups of large frames) — the
coordinate-split analysis per family; all axis-aligned and
small-mixed embeddings are covered by the census, and the 91,840-
member frame battery plus W2's zero-precondition-rows corroborate.

### 10.3 Status: the (v)-obligation is now a theorem-with-one-polish-item

    (v) size 6 = Lemma A + Theorem D + Theorem G      [proven]
    (v) size 4 = Lemmas E, F, H + family collapse     [proven; general-
                 embedding polish item, census-exhausted]
    (v) size 2 = vacuous under D1                     [proven]

Hypotheses consumed: D1, D2, (iii), no-period, Ann ≠ 0, 4∤ℓ ∧ 4∤m —
**still no use of the full μ ≥ 6 floor.** Remaining for the class
theorem (C-iv′)/(C-v′): the (iv) uniform lemma (Entry 8.2: 100%
profile-separable — expected to yield to the same multiset toolkit),
the size-4 polish item, and the certifier wiring (T1.2).

### 10.4 Frame battery addendum

Z₅×Z₅ has **zero class members** (144 mirrored candidates, all fail
the floor/Ann gate — Entry 6 §6.1's "Z₅² matches are all k = 0"
reappearing as the pentagonal kill). Pickup (run complete): Z₅×Z₁₀
also has **zero class members**, and Z₁₅×Z₅ — the 25 | |G| frame
where the pentagonal branch is torsion-permitted — is clean at
**20,000 members, 0 (iv)/(v) violations** (916 profile-resistant
rows over 60 classified members, all dm-separated, zero
DM-RESISTANT), exactly as Lemma H predicts. Battery grand total:
**111,840 members across 8 frames, zero violations.**

### Next

1. Entry 11: the (iv) uniform lemma via the same difference-multiset
   toolkit (triangle-image d(σ) identities); then (C-iv′)/(C-v′) is
   a THEOREM modulo the size-4 polish item.
2. T1.2 certifier: per-member (v) is now zero-cost (all uniform);
   per-member (iv) = the small census until Entry 11 lands.
3. Polish: the general-embedding (iii)∧(a) argument; fold Theorem
   G/Lemmas E–H into a consolidated A16 class-theorem write-up.

---

## Entry 11 (2026-07-06) — the (iv) kill: triangle images are
## Frobenius squares; the class small-cycle theorem assembles

Same-day continuation. The (iv) obligation ((1,3)/(3,1) censuses)
turns out to be governed by two char-2 polynomial identities, making
its uniform kill THREE LINES — and with it, (C-iv′)/(C-v′) assembles
into a theorem modulo explicitly-bounded polish items. Verification:
`a15_e11_iv_kill.py` (X1–X3) + the coincidence classifier.

### 11.1 Lemma I (chirality structure of the triangle census)

In char 2: **B·B = B²** (the Frobenius square — squared supports,
3 distinct cells since D1 forbids 2-torsion differences) and
**B·(−B) = {0} ∪ dB** (weight 7 under D1). Consequently the
dB-triangles {0, a, b} (a, b, b−a ∈ dB) generically form exactly two
translate classes, and their weight-3 images are pinned:

* reflection class T ~ B_i − B: image ({0} ∪ dB) + c, weight 7 —
  never produces a (1,3) candidate;
* same-chirality class T ~ B − B_i: image **B² + c**, weight 3.

(X1: 24,000/24,000 image identities verified on the Z₉×Z₆ and
Z₆×Z₁₀ batteries; A4 §4.3's T₊/T₋ = exactly these two classes, and
its "constant-y image y³(1+x²+x⁴)" = 2B + (0,3) verbatim.)

### 11.2 Theorem J (the generic (iv) kill = Frobenius exclusion)

**Under D1 ∧ (iii) alone** (no frame condition): no weight-3
same-chirality image is a translate of A, in either direction.

*Proof.* A match forces dA = d(B²) = 2·dB. dB (B1-shape) contains
(p, 0) with 2p ≠ 0 (D1), so 2·dB contains the nonzero y = 0 element
(2p, 0); but dA under (iii) has y-parts {±w, ±s, ±s′}, all nonzero.
Mirror: dB = 2·dA would need the x = 0 element (0, 2w) ∈ dB —
impossible for B1 (all x-parts nonzero) and for B2 (forces 2w = 0,
D1-dead). ∎

This resolves the extensibility-§6 obstruction arc FOR THE CLASS:
the Frobenius square A ~ B² (including the Z₈²-spread variants that
defeated D3) is exactly the generic (iv) failure mode, and
(iii) + D1 exclude it outright — the `is_frobenius_related` gate is
subsumed by the mirrored-projection hypothesis on class members.

### 11.3 Lemma K (coincidence classes)

Extra triangle classes require extra additive relations in dB, and
the battery classification is exact: **every occurring coincidence
class (4,082/4,082 across both frames) is an order-3-coset triangle**
T = ⟨v⟩ + c for v ∈ dB of order 3 (2v = −v ∈ dB is free by
symmetry — bb_108's third (3,1) class, (6,4) = 2·(3,2) with
3·(3,2) = 0, is this). Its image is the odd-multiplicity coset
s + ⟨v⟩ (the dB-pair's cosets cancel) — an order-3 AP-line; A ~ an
AP-line would put multiplicity 2 in dA at the common difference:
**D1 kills in one line.** The non-occurring genuine-doubling family
(v, 2v ∈ dB with 3v ≠ 0 ⟹ dB = ±{p, 2p, 3p}, image an AP-line with
dA-confinement ±{p, 4p, 5p}) dies by the (iii)-clash: the confined
dA needs an x = 0 representative pattern that forces p's x-part to
0, contradicting B's own (iii)-shape (with a 2-torsion-u sub-case in
the Entry-10 torsion apparatus). Polish item: complete the
relation-type table (q = −3p, 3p + 2q = 0, … patterns) — none occur
in the battery, and all inhabit the same bounded apparatus.

### 11.4 The class small-cycle theorem (v1)

Assembling Entries 8–11:

> **Theorem (class small cycles, v1).** Let (Z_ℓ × Z_m, A, B) with
> |A| = |B| = 3 satisfy: D1 (Sidon difference sets), D2
> (dA ∩ dB = ∅), (iii) (mirrored projections), no-period,
> Ann(A), Ann(B) ≠ 0, and a floor-bearing frame (2-part ∈ {1, Z₂,
> Z₂²} with one-sided floor ≥ 6; 4 ∤ ℓ, 4 ∤ m). Then the code has no
> nonzero 1-cycle of weight ≤ 5; in particular d ≥ 6, μ_Z, μ_X ≥ 6,
> and every free-Z₂ cover has d ≥ 6 (Theorem-B transfer).
>
> *Proof map.* PAR kills mixed-parity splits (|A|, |B| odd). One-
> sided splits: the widened engine floor (Entry 8.1b — field-generic;
> Z₂/semisimple frames by the A5 E2/E4 mechanisms). (1,1): D2.
> (1,3)/(3,1): Lemma I + Theorem J + Lemma K (Entry 11). (2,2):
> Lemma A + Theorem D + Theorem G (size 6; Entries 9–10) and Lemmas
> E/F/H + the family collapse (size 4; Entry 10); size 2 vacuous.
>
> *Modulo* three explicitly-bounded polish items, none of which
> occurs on any of the 91,840+ battery members or the 58-member
> corpus: (P1) the size-4 general-embedding (iii)∧(a) argument
> (census-exhausted on all 2-D family ambients); (P2) Lemma K's
> 2-torsion-u sub-case; (P3) the coincidence relation-type table.

Notable hypothesis accounting: the full μ ≥ 6 floor is consumed
ONLY by the one-sided splits; the entire two-sided analysis needs
just D1 ∧ D2 ∧ (iii) ∧ no-period ∧ Ann ≠ 0 ∧ 4∤ℓ∧4∤m. And the
certifier consequence (T1.2) is now maximal: **every per-member
obligation is uniform** — no censuses, no residue tables; the
certificate is the gate-check itself (O(|G|²) decidable, all
surveyable per instance).

### Next

1. A16: consolidated class-theorem write-up (the Entry 8–11 lemmas
   as one document, with the three polish items discharged — P2/P3
   are small torsion tables, P1 is the coordinate-split analysis).
2. T1.2: wire the theorem into `a5_recipe_certify.py`; re-run the
   58-member corpus + battery as certificates; update the
   extensibility doc §6 (Frobenius arc: closed for the class) and
   the A15 plan (T1 = effectively closed).
3. Then T2 (the Lean base-floor layer) — the theorem's obligations
   are now all decidable-by-construction, which is exactly what the
   `BBSmallCycleData` bundle wants.

---

## Entry 12 (2026-07-07) — T1.2: the certifier lands; Z₆×Z₁₄ becomes
## the fourth analytic instance

`scripts/a15_class_certify.py` wires Entry 11.4 into a per-instance
certificate: gates W3/D1/D2/(iii)/FRM/ANN + the frame-appropriate
analytic floor route (widened engine / Z₂ pullback / semisimple d_H)
+ the exact w2/w4 kernel exhaustion, emitting CERTIFIED (theorem
citation + cover transfer) or REJECTED (first failed gate, no
verdict implied). Every obligation is uniform — the Entry-5-era
per-member censuses are gone. `--verify` runs the direct (iv)/(v)
checks as machine confirmation (A_HANDOFF §1 grade).

Self-test battery (8/8 as predicted): bb_72, bb_108, bb_90 CERTIFIED
(three frame shapes, three floor routes); **Z₆×Z₁₄ [[168,12,6]]
(A = 1+y+x³y³, B = 1+x+x²y⁷) CERTIFIED with the widened-engine
route — the fourth analytic instance and the FIRST off the Z₃² odd
part (components F₂·F₄·F₈²·F₆₄²), subsuming T3a.3's planned
per-instance grid**; its two n = 336 free-Z₂ covers inherit d ≥ 6
(and are SAT-known d = 12 doubles — the natural next engine
targets). gross-as-base and bb_288-base REJECTED at FRM (the Z₄
wall, as designed); the Entry-6 Z₃×Z₅ falsifier and the Z₇²
Frobenius square REJECTED at (iii).

Doc updates: extensibility §6 update block (the class theorem closes
the obstruction arc for mirrored members; engine not frame-locked;
Frobenius subsumed; difference multiset = the stable invariant);
A15 plan header (T1 closed-mod-polish).

### Next (unchanged from Entry 11 + re-ranked)

1. A16 consolidation (discharge P1–P3, one document for Entries
   8–12).
2. T2: the Lean `BBSmallCycleData` layer — all obligations now
   decidable-by-construction; pilot bb_108/bb_90/z6z14.
3. T4 (w = 5 sweep) / T3c (Z₄ pilot) per the plan ranking.
