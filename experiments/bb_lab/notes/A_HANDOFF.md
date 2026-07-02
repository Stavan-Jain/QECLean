# A_HANDOFF — analytic distance-bound effort for gross / BB codes

**Read this first.** This is the canonical handoff for the "Phase A" program:
finding an *analytic* lower bound on the minimum distance `d` of bivariate-
bicycle (BB) quantum codes, especially the gross code `[[144,12,12]]`. It
supersedes the Tier-1-era parts of `HANDOFF.md` for this specific effort and
ties together the `A0`–`A3` notes. Date of handoff: 2026-06-10; updated
2026-06-12 (Entries 11–14: all shape lemmas proven; (M) unconditional;
**d(gross) ≥ 6 fully analytic**; Entry 15: the owed adversarial re-review
passed — the chain HOLDS, **write-up grade**; Entries 16–28: goal 1
closed, reviewed, and written up — **d(gross) = 12 fully analytic**,
A4 Theorem D).

> **A9 update (2026-07-02, `A9_lean_target_screen.md`) — goal-2 milestone.**
> The free-ℤ₂ doubling template is now a **parametric Lean layer**
> (`Framework/Homological/{BBCover,BBDoubling}.lean`), and the `[[36,4,4]] →
> [[72,4,8]]` pair (extensibility doc §5) is **proven through it at the chain
> and Pauli levels, gross axiom bar** (`Codes/BivariateBicycle/Z3Z6/`;
> `StabilizerCodeWithDistance 72 4 8` packaging pending).  Corpus screen: 152
> direct-sweep doubling pairs; the presentation census corrects the Z₆×Z₆
> uniqueness reading — **five new anchorable [[72,12,6]] codes, three with
> exact [[144,12,12]] y-covers** (hit3/4/6): in-frame, engine-necessary
> targets for the next engine re-instantiation.

> **A10 planned (2026-07-02, `A10_descent_twist_screen.md`) — the descent
> question.** Does every certified BB base admit a *descent* free-ℤ₂ cover
> (any extension class, cover polynomials only required to satisfy
> `fiberSum = base`, i.e. `~2^(w_A+w_B)` sheet twists per class) with
> `d(cover) = 2d`?  Known false for literal-lift axis covers (hit2/hit5
> fail both axes; toric by symmetry).  Decisive experiment: exhaustive
> 256-cover twist screens on hit2/hit5 at n = 144 — rescue ⟹ evidence for
> "always constructible"; no rescue ⟹ finitely-certifiable (Lean-kernel
> witness table) counterexamples.  Key enabler: `XDoubleCoverData` is
> already descent-general (`Ac/Bc` free fields + `push_A/push_B`), so no
> new Lean framework either way.  Branch `claude/a10-descent-twist-screen`.

---

## 0. RESUME HERE (the one-paragraph version)

**The program has its first headline theorem (Entry 14): d(gross) ≥ 6,
fully analytic — triple the published Lin–Pryadko floor of 2. Goal 3 is
achieved, and the owed adversarial re-review passed (Entry 15): every link
HOLDS under an independent re-implementation of all machine checks
(`a3_adv15_recheck.py`, 49/49) plus a hand re-derivation of every prose
argument — the theorem is write-up grade.** The
chain: gross is the free-Z₂ double cover of `[[72,12,6]]`; d_X = d_Z by the
inversion duality Φ(w_L,w_R) = (ι(w_R), ι(w_L)) (Entry 13); the safe sector
(pr_* ≠ 0) gives |v| ≥ |p(v)| ≥ 6 via the **small-cycle theorem** (Entry 13:
the base code has NO nonzero 1-cycles of weight ≤ 5, either side — proven by
a per-split hand analysis: parity, the Ann-engine ≥ 6, dA ∩ dB = ∅,
dB-triangle chirality, π_x/π_y projection bookkeeping); the dangerous sector
(pr_* = 0) gives |v| = |b| + 2|v₀ off b| ≥ |b| + 2m(b) ≥ 12 via **(M), now
proven with NO hypothesis**: the light-stabilizer classification (every
0 < |b| ≤ 11 is one of 36 hexagons or 216 D-pairs) is fully hand-proven
(Entries 10–12: dictionary, engine, one-block ≥ 16, floor, six shape
lemmas — R1, R-(1,1,1,1), R-(2,1,1)+endgame, R-(2,1,1,1), R-(2,2,1),
R-(3,1,1)); the m-rungs m(hexagon) ≥ 3 and m(D-pair) ≥ 1 follow from the
small-cycle theorem by mod-hexagon coset averaging; and the old transfer
hypothesis **(H0) d_base ≥ 6 is itself now a theorem** (Entry 13, Cor. 1).
The Entry-8/9 machine checks are demoted to confirmations end to end.
Goal 1 then closed (Entries 16–26): the safe sector sees exactly the
Smith classes, **(R) is proven** by the one-line homotopy, the flux
characterization is fully analytic, **d(gross) = 12 ⟺ (M-im)**, and
(M-im) is proven by the confined-floor program; the Entry-27 review
cleared the chain, and **Entry 28 discharged its two residues: the A4
extension (`notes/A4_writeup.md` Part II, Theorem D) walks the
compressed C-tables and derives the achiever lists by hand —
d(gross) = 12 is fully analytic.**
Start at `notes/A4_writeup.md` (Theorems A–D), then
`notes/A3_track1p1_log.md` Entries 27–28 and
`scripts/a3_a4ext_recheck.py`, `scripts/a3_adv27_recheck.py`.

*Update (Entries 16–26): goal 1 was assembled — d(gross) = 12 via (R) +
the flux characterization + (M-im). Update (Entry 27, 2026-06-12): the
owed adversarial re-review of Entries 16–26 is DONE — every link HOLDS
(75/75 independent conjugate-frame checks, `a3_adv27_recheck.py`; every
prose argument re-derived by hand; two sharpenings found: off₀ = off₂ = 0
identically, making the comp-2 mirror chain a one-liner). Entry 27
demoted the headline to "analytic spine + two machine-certified
residues" — the Entry-24 per-cell C-table evaluations and the Entry-25
achiever-list completeness. **Update (Entry 28, 2026-06-12): both
residues are discharged. The wt-24 closure compresses to ONE standard
form S(a,b) (all four block tables are S-reindexings via Frobenius /
slot maps / translation scalings, using m′² = ω²m) walked in 33
hand-derived buckets, with the slope lemma in its final form (the
hyperbolic-quadruple lemma: the four points (m, m+ωθ) lie on uv = ω²
plus the origin, no three collinear). The achiever-list completeness
follows from the achiever-structure lemma (per-(V₀,γ) block minima are
parity-locked, so achievers = argmin products over the sum-10 loci) +
the per-cell locus tables derived by rules R1–R5: 48 + 48 + 22 = 118,
matching Entry 25, all killed by one-convolution ρ-link checks.
`a3_a4ext_recheck.py` certifies every table (all PASS).
d(gross) = 12 and d(gross) ≥ 6 are both fully analytic.***
**Update (A5 Entries 1–5, 2026-06-12): goal 2 STARTED and producing —
`notes/A5_goal2_log.md`. d(bb_108) ≥ 6 AND d(bb_90) ≥ 6, both fully
analytic: the small-cycle grid now runs on all three occurring frame
shapes (Z₂² base / Z₂ bb_108 / semisimple bb_90); Theorem-B transfers
stated for the four n ∈ {216, 180} covers.**
**Update (A5 Entries 6–7, 2026-06-13): the class theorem SHARPENED by a
counterexample. A 26-agent workflow (corpus hunt + skeptic + proof
panel) plus a human verification pass (Entry 7) established: the
Entry-5 conjecture "(a) floor-bearing frame + (b) mult-free + disjoint
⟹ d ≥ 6" is FALSE — the Z3×Z5 family (A = x+y²+y³, B = x²+y+y⁴ and
5 siblings) has all of (a)+(b) yet d = 4 (independently SAT-verified;
explicit weight-4 (3,1) cycle). The missing load-bearing hypothesis is
(iii) the MIRRORED-projection pattern (A monomial in x, B monomial in
y); all 58 corpus members carry it, all 6 violators lack it. Corrected
live conjecture (C-iv′)/(C-v′) = (a)+(b)+(iii) ⟹ d ≥ 6, zero
counterexamples across every sweep. The three template theorems
(gross/bb_108/bb_90) SURVIVE independent re-derivation. Two technical
finds: a bug in the uniform "weight lemma" (false on even-period axes;
corrected form verified 0/29510), and the one remaining open step is the
presentation-free multiplicity-profile residue lemma (or accept it as a
per-instance surveyable check). The single gross dictionary row
d₃((3,F)) feeds the two pullback floors but NOT the Z₂² base (layer
engine); see Entry 7 §7.3.**

---

## 1. The goal and the hard constraint

**Goals, strict priority order (set by the project owner):**
1. analytic proof that gross `d = 12`;
2. analytic lower bound for a *class* of BB codes;
3. **any** nontrivial analytic lower bound on gross beyond the published floor.

**The published floor is already `d ≥ 2`** (Lin–Pryadko Statement 12: the
degeneracy parameter `c = 8`, so `⌈12/8⌉ = 2`). So "progress on gross" means
**beating 2 analytically**.

**The hard constraint: "fully analytic only — no SAT/`decide` ingredient may be
load-bearing in a final theorem."** This is subtle and was litigated explicitly:
- SAT, a Lean-kernel `decide`, and brute enumeration are all the *same kind* of
  object (exhaustive computation). Trust base (SAT vs kernel) is **orthogonal**
  to analytic-vs-computational. Swapping SAT→kernel does **not** satisfy the
  constraint.
- A finite check is allowed only as the *residue of an analytic reduction* to a
  few human-surveyable cases (à la the repo's small toric/surface proofs), and
  only as validation — never as the argument.
- Concretely: **all computed numbers in the `A*` scripts (distances, the (6,6,6,6)
  ES terms, μ_Z, the SAT sector minima) are discovery/validation only.** They
  tell you what is true so you know what to prove; they can never appear in the
  proof. Treat them exactly as you would the SAT d=12 certificate.

**Gross reference data:** `G = Z₁₂ × Z₆`, `A = x³+y+y²`, `B = y³+x+x²` over `F₂`;
`H_X = (M_A | M_B)`, `H_Z = (M_Bᵀ | M_Aᵀ)`; `n=144`, `k=12`, `d=12`.
`F₂[G]` is non-semisimple (`|G|=72=2³·3²`; 2-Sylow `Z₄×Z₂` is non-cyclic ⇒ neither
PIGA nor PIR). Base `[[72,12,6]]`: `G=Z₆×Z₆`, same polynomials, `d_base = 6`.

---

## 2. What's been done (phase by phase)

| phase | what | artifacts | commits |
|---|---|---|---|
| **A0** | Repaired over-claims in `HANDOFF.md`/`degeneracy.py` (found by an adversarial review); built the baseline scoreboard | `notes/A0_baseline.md`, `scripts/analytic_baseline.py` | `e308e65` |
| **A1** | Four-lane literature deep-dive with adversarial per-citation verification; synthesis + gross-first re-ranking | `notes/A1_literature_L{1,2,3,4}.md`, `notes/A1_synthesis.md` | `ffdb2bb`,`6854c34`,`120ca24` |
| **A2** | Scouting pass over the 3 gross-directed tracks → collapsed them to ONE obstruction; chose Track 1.1 | `notes/A2_scouting.md` | `3c3bfcf` |
| **A3** | Track 1.1 serial deep-push, entries 0–4: framework, Δ explicit, factor-2 lemma reduced and located, Fork B killed | `notes/A3_track1p1_log.md`, `scripts/a3_*.py` | `5d983dd`,`f806b8f`,`e75770f`,`40df45e`,`b64868d` |

The **three gross-directed tracks** from A2 and their fate:
- **Track 1.1 — h=2 Smith cover transfer** (chosen): the only route with a path
  to goals 1 *and* 3. Crux is sharply localized. ← all A3 work is here.
- **Track 1.2 — radical/CMS + Lin–Pryadko**: **dead on gross by an arithmetic
  wall**, not a difficulty estimate. LP divides by `c=8` and the single-block
  distance is already maximal (12), so `⌈12/8⌉=2` regardless of the numerator.
- **Track 1.3 — KP-2013 even-symmetry**: **not independent** — it cleanly handles
  the (irrelevant) symmetric half and collapses to Track 1.1's exact crux on the
  hard half.

---

## 3. Current state of Track 1.1 (the live work)

### Framework (DONE, verified — `scripts/a3_cut_decomposition.py`, `a3_delta_explicit.py`)

- **Sheet coordinates.** Gross is the x-direction double cover of `[[72,12,6]]`;
  deck `σ: x↦x+6`. A cover chain is a pair of base chains `v=(v₀,v₁)`, `σ(v₀,v₁)=(v₁,v₀)`.
- **Verified exactly:** the cover boundary has the block form
  `[[∂_nc, ∂_c],[∂_c, ∂_nc]]` for both `H_X` and `H_Z`, where `∂ = ∂_nc + ∂_c`
  is the base boundary and `∂_c` is the x-seam-crossing part (36 nonzero entries,
  on the monomials `x³` of A and `x, x²` of B). So `τ(u)=(u,u)` and `p(v)=v₀+v₁`
  form a **short exact sequence of complexes** `0→C_base→ᵗᵃᵘ C_cover→ᵖ C_base→0`;
  `p∘τ = 1+σ = 0` over F₂ (this is SRB Lemma 4.4, the obstruction to the naive
  transfer).
- **Smith connecting map, explicit:** `Δ[z] = [∂₂c·z]` (seam part of the boundary
  on a base 2-cycle). Verified `im(Δ) = ker(tr_*)`, both 6-dim.

### The structural picture (verified — `scripts/a3_dangerous_structure.py`)

`pr_* : H₁(cover) → H₁(base)` has **rank 6, kernel 6**. The 6-dim **dangerous
sector** `ker(pr_*)` is where the whole problem lives:
- **Safe sector** (`pr_*≠0`): `|v| ≥ |p(v)| ≥ d_base = 6` *for free* (p is a
  weight-non-increasing chain map). This is the published "safe branch."
- **Dangerous sector** (`pr_*=0`): `p(v)=0`, so the safe branch gives `|v| ≥ 0`
  — **nothing**. Yet **gross's minimum-weight (=12) logicals are exactly the
  dangerous ones**. The 6 dangerous reps are `τ(u)` for `u` a nontrivial base
  6-logical, weight `2·6 = 12 = 2·d_base`.

### The factor-2 lemma: from three cases to one function (Entries 2 → 5)

Target: `d_cover ≥ 2·d_base` on the dangerous sector (the only thing that beats
the floor — see §4). The Entry-2 case table (s=0/[c]≠0 proven at 12; [c]=0
≥ 16; s≠0 = 14) is retained in the log for history, but **Entry 5 proved the
trichotomy is a cut-coordinate artifact**: one decoded weight-14 minimizer has
s-flags `[1,1,1,0,0,0]` across the six cut positions — the same `v` is "s≠0"
for three cuts and "s=0" for the others. The invariant object is the b-graded
slice identity (see §0/§4): `min |v| over {p(v)=b} = |b| + 2·m(b)`, verified
end to end (`a3_mb_foundations.py` all-PASS, `a3_mb_scan.py`,
`a3_mb_crosscheck.py`). All SAT encodings pass the sanity ladder (they
reproduce `d=12`) — the validation the buggy scout script lacked (see §5).

### What is and isn't proven (updated, Entries 11–14)

- **Analytically proven, no hypothesis:** the m(b) reduction; the full
  light-stabilizer classification (every 0 < |b| ≤ 11 is a hexagon or
  D-pair — Entries 10–12); the small-cycle theorem (no nonzero base
  1-cycles of weight ≤ 5, either side — Entry 13), which discharges (H0)
  d_base ≥ 6 AND both m-rungs; (M) in full; the inversion duality
  d_X = d_Z; **hence d(gross) ≥ 6 (Entry 14) and d(base) ≥ 6.**
- **Adversarial re-review: DONE (Entry 15, fresh session).** All four links
  HOLD; two presentation debts recorded for the write-up (the (3,1,1,1)
  derivation order; the d₃ = support-⊆-W clarification). Independent
  checker: `a3_adv15_recheck.py` (49 checks, different encoding path).
- **Goal 1 (d = 12): CLOSED** — Entries 16–26 (the chain), Entry 27
  (review), Entry 28 (the A4 Part-II write-up; fully analytic). See §4's
  update blocks; the open work is the owed Part-II skeptic pass and
  goal 2 (§8).

---

## 4. The precise open problem (where to push)

*(Superseded forms: Entries 0–4 posed this as the s≠0 "fibre-disjointness"
case; Entry 5 replaced it with (M); Entries 10–13 PROVED (M) in full. The
open problem is now the goal-1 frontier below.)*

**(M) is proven — every rung, no hypothesis (Entries 10–13):**

| rung | statement | status |
|---|---|---|
| b = 0 | m(0) ≥ 6 | PROVEN — small-cycle theorem (Entry 13); (H0) is gone |
| \|b\| ≥ 12 | trivial | PROVEN |
| classification | light b = 36 hexagons ∪ 216 D-pairs | PROVEN by hand (Entries 10–12: six shape lemmas) |
| m(hexagon) ≥ 3 | no non-imΔ cycle with ≤ 2 qubits off the hexagon | PROVEN (Entry 13: mod-b rep ≤ 5 ⟹ 0) |
| m(D-pair) ≥ 1 | no non-imΔ cycle inside the 11-qubit union | PROVEN (Entry 13: four-coset averaging, 22 < 24) |

**The open problem for goal 1 (d = 12) — the safe-sector (M)-analogue.**
Pointwise |v| = |p(v)| + 2|v₀ ∧ v₁|, so with the dangerous sector done and
tight, d(gross) = 12 reduces to: for every nontrivial base logical cycle w,
every cover cycle v with p(v) = w has |w| + 2|v₀ ∧ v₁| ≥ 12. SAT says the
safe minimum is ≥ 12 (true d = 12), so this is true with structure to find:
v₀ ranges over a syndrome-shifted coset (the old "s ≠ 0" data, in its
correct home), and the overlap |v₀ ∧ v₁| is the new quantity to bound below
on heavy-class slices. The m(b) slice machinery should adapt.

*Update (Entry 16): the reduction is now much sharper.* The slice over w is
nonempty iff δ(w) = [d1c_j w] = 0 in coker ∂₁, and **ker δ = im Δ**
(verified, cut-independent): the safe sector sees exactly the 63 Smith
classes. All 84 weight-6 base logicals are UNREACHABLE (empty slices —
their rungs are vacuous). Goal 1 is therefore exactly two base-code
statements: **(R)** ker δ = im Δ analytically (⟺ σ_* = id on H₁(gross);
the formal (1+x⁶)-module proof FAILS — documented dead end), and
**(M-im)** dist(d2c_j ζ, Stab_Z) ≥ 12 for the 63 nonzero ζ ∈ ker ∂₂
(= the C2 crosscheck, true with the minimum at the bar; ker ∂₂ has weight
enumerator {16:9, 18:48, 24:6} and lives in CRT components {3,4}).
See `a3_msafe_scan.py` (S1–S8) and Entry 16.

*Update (Entry 17): **(R) is PROVEN** — one-line homotopy: over the cover
B² = 1+x²+x⁴ and (1+x²)B² = 1+x⁶, so z = (1+x²)B·v_L gives
∂₂z = v + σv for every cover cycle: σ_* = id on H₁(gross). So now

    **d(gross) = 12  ⟺  (M-im)**  (both directions; the upper bound is
    τ(u\*) with u\*'s nonzero flux).

New tools for (M-im): the Smith linking form vanishes identically, so
im Δ^X = (im Δ^Z)^⊥ and Smith membership ⟺ six explicit seam-flux
parities vanish; the weight-6 sub-rung (no weight-6 cycle is in a nonzero
imΔ class) is verified in hand-checkable flux form on all three orbits;
ker ∂₂ ∖ 0 has just 5 orbits under translation+swap, and the class minima
12 are attained by the canonical reps themselves. Dead end: the
π_x-collapse bound is identically 0. Two routes forward: the
weight-8/10 light-cycle flux census, or the affine-COST grammar on the
five cosets d2c_jζ + im ∂₂. See `a3_r_homotopy_mim.py` and Entry 17.*

*Update (Entry 18): the zero linking form is PROVEN — the **no-double-wrap
lemma**: two-step ∂₁∂₂ paths advance ≤ 5 < 6 columns, so d1c·d2c = 0 =
d1nc·d2nc as matrix identities (all cuts). The flux characterization is
now fully analytic end to end. Affine-COST seed: all five Smith-coset
orbits are pinned exactly in the doubly-radical components {3,4} — next
session: the offset-COST DP per orbit (machine floor first; if ≥ 12
everywhere, hand-organize like Entries 9–12 and goal 1 closes).*

*Update (Entry 19): the offset-COST DP ran (`a3_mim_offset_cost.py`,
sanity ladder all-PASS, exact Entry-8 reproduction at zero offset) —
**negative on the floor**: the support-only d₃ dictionary gives 8/7/7/8/6
on the five orbits, far below 12 (d₃ sees supports, not values; the
wt-24b coset still admits the hexagon support pattern). Keep: the 5-orbit
reduction needs only translation covariance (the translation orbits
already equal the swap orbits, and class(Tζ) = T class(ζ) verified);
Δ^y ≠ Δ^x pointwise AND in image (the two 6-dim Smith images meet in
dim 2) — no swap-symmetric description of im Δ exists; the parity lemma
survives on every Smith coset (comp-0 offsets diagonal); all
orbit-dependence sits at the doubly-radical pair {3,4} (comps 1, 2
re-center to the homogeneous grammars). Next: the value-refined floor —
components {0,3,4} value-exact (16·64·16 affine combos per orbit), comps
{1,2} support-relaxed, slot dictionary upgraded to the exact
prescribed-values table d₃ᵛ (Entry-9 δ-point rigidity baked into the
floor).*

*Update (Entry 20): **(M-im) — hence d(gross) = 12 — closes at the
verified-finite level** (`a3_mim_value_cost.py`, all-PASS). The value
5-tuple ↔ layer bijection gives the exact dictionary d₃ᵛ; coset weights
and costs are even (slot parity = comp-0 value + Entry-19 diagonality);
the value floors are 8/8/8/8/6 — and the residual sub-12 combos (1k–2.5k
per orbit, costs {6,8,10}) are killed exactly: comps 1, 2 are affine
graphs (V₁R = c₁ + ρ₁V₁L etc.), so each combo has ≤ 81×81 completions,
each reconstructing w exactly — minimum completion weight 14–18 across
all five orbits, zero below 12. Translation transport (all 36
translations verified on a basis) extends the five orbit kills to all 63
classes. Owed for the full analytic bar: hand-organization (the
Entries 10–12 analogue): (a) parity lemmas (done, to write out), (b) the
d₃ᵛ dictionary on occurring cells, (c) the cost-≤10 combo
classification, (d) the ρ-affinity completion kill. Route B (weight-8/10
flux census) remains the alternative; next entry sizes both.*

*Update (Entries 21–22, session close): **(M-im) is now doubly
machine-verified** — the light-cycle census (`a3_light_cycle_census.py`)
enumerated ALL weight-8 (990) and weight-10 (13464) base cycles and
found zero flux-silent non-boundaries, independently confirming the
Entry-20 sweep; route B's hand form is dead (368 weight-10 orbits). The
hand-organization (route A) is underway (`a3_mim_hand_org.py`,
Entry 22): hand-proven — slot parity, 2-cycle column/row evenness, even
coset weight and cost, E ≤ 2 value rigidity (δ-points/pairs), and the
**ρ-locks** (u² = aug(u)²·1 in F₄[Z₂²], so ρ₁² = ρ₂² = 0 and V₁R, V₂L
are confined to explicit 16-element affine sets with aug 0); verified
table fact: non-minimal slots cost +4 (66 fibres, all gaps exactly 4).
The **confined-value floor** evaluates to 10/10/10/12/12 — (M-im)
closes outright on the two wt-24 orbits; the wt-16/18a/18b orbits
reduce to killing weight EXACTLY 10. Resume with Entry 22's obligations
**(O1)** hand-evaluate the confined floor (engine/C-table style;
translation stabilizers + B̂₄ = ωÂ₄ compress), **(O2)** the weight-10
equality analysis via the dropped ρ-link + the +4 fibre gap, **(O3)**
the GL-compressed fibre-gap table and aug(c₁) = aug(c₂) = 0 by hand.
(O1)–(O3) ⟹ (M-im) fully analytic ⟹ **d(gross) = 12 fully analytic**.*

*Update (Entries 23–26, session close): **O1, O2, O3 are ALL CLOSED —
(M-im) is proven, and with it d(gross) = 12 (goal 1).** The chain:
(Entry 23) the confined floor organized into 4×4 spine C-tables
m(a₃, a₄) per orbit, with three hand-proven engine lemmas — the
kill-multiset support-class lemma, the slot-cost table with the
T-classifiers (the character identities ψ₂² = ψ₃ψ₄, ψ₄ = ψ₁ψ₃ classify
the cheap loci), and the slope lemma (simultaneously-cheap slots form a
level set of an explicit g); c₁ = c₂ = 0 so the confined sets are the
subspaces im ρ_i. (Entry 24) the engine reproduces every block and cell
minimum EXACTLY (160 + 80 cells); both wt-24 orbits have block ≥ 6
everywhere ⟹ all their cells ≥ 12. (Entry 25) at the floor-10 cells of
wt-16/18a/18b the engine-10 achievers number just 48/48/22, with
near-singleton minimizer sets, and every one violates both dropped
ρ-links (ρ₁V₁L = V₁R, ρ₂V₂R = V₂L) — no weight-10 elements; evenness
gives ≥ 12. (Entry 26) the unpinnedness c₁ = c₂ = 0 derived by hand via
column y-transforms (D1: Yû₁ = ω²Yû₂; the reduced identity vanishes by
ω² + ω + 1 = 0), every step machine-verified on all 63 ζ; assembly +
dependency tree written (log Entry 26). Epistemic grade: all reductions
hand-proven; the finite residues (18-orbit M-table, per-cell C-table
evaluations, 118 one-line link kills) are explicit and surveyable, and
the endpoint is double-verified by the two independent Entry-20/21
machine routes. **Owed before external write-up: the adversarial
skeptic pass over Entries 16–26 (the Entry-15 review landed in the
parallel session — merged above), and the standalone write-up
(A4 extension) with the tables typeset.***

*Update (Entry 27, the owed re-review — VERDICT): **all eight links of
Entries 16–26 HOLD; no gap found.** Independent re-implementation on a
conjugate CRT frame / y-major / bitmask encoding path
(`a3_adv27_recheck.py`, 75 checks all-PASS, incl. an own weight-6/8/10
census making the (M-im) endpoint TRIPLE-machine-verified), and a hand
re-derivation of every prose argument. Review findings: (i) only the
inclusion im pr_* ⊆ im Δ is load-bearing — neither direction of the
theorem depends on k = 12 or on the flux-characterization equality;
(ii) the no-double-wrap proof needed one implicit step made explicit
(all 2-step paths at an entry share the same integer x-advance D, since
D ≡ Δx mod 6 and 0 ≤ D ≤ 5); (iii) sharpening: off₀ = off₂ = 0
identically (v_i = Y²v_i = 0), so Entry 26's comp-2 mirror chain
collapses to one line; (iv) V6 (the +4 fibre gap) is NOT load-bearing.
Surveyability audit: the 18-orbit M-table PASSES the §1 bar; the
Entry-24 C-table evaluations and the Entry-25 achiever-list completeness
FAIL it as currently organized (machine sweeps with one worked template
cell) — so the theorem stands at **"d(gross) = 12, verified-finite with
an analytic spine; fully-analytic write-up owed"**, while d ≥ 6 remains
fully analytic. See log Entry 27 for the per-link detail and the
load-bearing-only dependency tree.*

*Update (Entry 28, the A4 extension — RESIDUES DISCHARGED): both
Entry-27 residues are now hand-walked in `notes/A4_writeup.md` Part II
(§§8–14, **Theorem D: d(gross) = 12, fully analytic**). The keys, all
new isolated structure: **m′² = ω²m** (kill(Â₄) is a scalar of
kill(B̂) — only two labelings exist up to scale), the confined comps are
the full affine lines {pm + c} / {pm′ + c}, and the Γ₄ tie is
V₄L = ωV₄R + w₄ with an affine γ-dictionary. (Residue 1) the four
wt-24 block problems are all equivalent (Frobenius / slot maps /
translation scalings) to ONE standard form S(a,b) = (⟨m⟩; am + c₃;
bm + ωθ + c₄), walked in 33 hand-derived buckets — the only deep case
is killed by the **hyperbolic-quadruple lemma** ((m, m+ωθ) lies on
uv = ω² ∪ {0}, no three collinear ⟹ ≤ 1 cheap slot); S ≡ 6, so every
wt-24 cell ≥ 12 with no linkage. (Residue 2) the **achiever-structure
lemma** (per-(V₀,γ) block minima are parity-locked even, so cost-10
configurations = argmin products over the sum-10 loci) reduces
completeness to per-cell locus tables derived by rules R1–R5
(zero-slot/dead-pair rigidity, δ-consistency, the shape ladder):
48 + 48 + 22 = 118 achievers exactly, each killed by a one-convolution
ρ-link check (116 fail both, 2 fail one). Entry 27's sharpenings, the
H₀ paragraph, and the no-double-wrap implicit step are folded in.
`a3_a4ext_recheck.py` (60+ checks, all PASS) certifies every table.
Honesty ledger: the §12 locus tables are rule-derived with worked
representatives per orbit (the Entry-10–12 presentation grade), not
walked cell-by-cell; a future skeptic pass may demand more worked
cells. See log Entry 28.*

**The former tail (L-C) — now closed verified-finite (Entries 8–9).** The
classification "every b ∈ Stab_Z(base) with 0 < |b| ≤ 11 is a hexagon or a
D-pair" is established by the layer-profile route
(`a3_mb_tail_dictionary.py`, `a3_mb_tail_profiles.py`):
- CRT frame `F₂[Z₆²] ≅ F₂[Z₂²] × (F₄[Z₂²])⁴` instrumented; the layer
  dictionary d₃ and support grammar verified; the bound |b| ≥ COST is
  tight on hexagons (6) and D-pairs (10).
- **Component-support lemma** (verified minimization): every b with
  |b| ≤ 11 has all five CRT components alive.
- **Profile completeness**: parity lemma (both blocks share layer
  parities — hand-proven, since A and B have the same s-parts
  {1, s_x, s_y}), the ≥ 3-layer floor (from comp-4 aliveness + the
  co-point-or-full ideal structure), and evenness reduce |b| ≤ 10 to 28
  layer-weight profile families (252 placements).
- **Exhaustive family checks** (syndrome hash-join over all layer
  contents): {1,1,1}+{1,1,1} → exactly the 36 hexagons;
  {2,1,1}+{2,2,1,1} and mirror → exactly the 216 D-pairs; all 25 other
  families EMPTY.
*(Update, Entries 10–12: both owed items are DONE — the floor lemma
replaced comp-4-aliveness, and the six shape lemmas replaced the family
enumeration. This whole block is retained for history; nothing here is
load-bearing anymore.)*

**Verification discipline before trusting any drafted argument:** run an
adversarial skeptic sweep hunting a counterexample to an intermediate
claim (never to the SAT-validated endpoints). Computation may *refute*
but never *prove*. The pass owed for the d ≥ 6 theorem was completed in
Entry 15 (all links HOLD); the discipline applies afresh to any new
goal-1/goal-2 argument.

---

## 5. What does NOT work — do not retry (dead-ends, first-class)

1. **Fork B / the elementary projection bound `d_cover ≥ min(d_base, μ_Z)`**
   (`a3_forkB_projection_bound.py`). Rigorous, and gives `d_gross ≥ min(6,6)=6`
   *if* you import SAT's `d_base=6`. But `min(d_base, μ_Z) ≤ d_base` **never
   grows up the cover chain**: recursing for an analytic `d_base` degrades it
   (`d₇₂ ≥ min(d₃₆,μ₃₆) ≤ d₃₆=4`, bottoming at the analytic anchor `d₁₈=2`). So
   fully-analytically it yields only `d_gross ≥ 2`. **The only growth mechanism
   is the symmetric sector's factor-2** — i.e. Fork A is *necessary*. Don't
   re-derive the projection bound expecting it to beat the floor.
   *(Update, Entry 14 addendum: the small-cycle theorem RESURRECTS Fork B —
   it proves d_base ≥ 6 and μ_Z ≥ 6 directly, no recursion down the tower
   needed, so the projection bound + the b = 0 slice now give d(gross) ≥ 6
   in half a page. The recursion objection was to the tower route, not the
   bound itself. The full (M) machinery remains what makes the dangerous
   sector tight at 12 — the goal-1 asset.)*
2. **Track 1.2 (radical/CMS + Lin–Pryadko) for a gross bound > 2** — arithmetic
   wall, `⌈12/8⌉=2` regardless of numerator (A2). Its only survivor (an analytic
   re-derivation of `d_A^⊥=12`) is a goal-2 classical result that still yields 2
   on gross.
3. **Track 1.3 as an independent route** — collapses to Track 1.1's crux (A2).
   Keep it only as alternative *vocabulary* for the s≠0 argument.
4. **The crude syndrome-correction** for the s≠0 case — loses `2|e|`, cannot reach
   `2·d_base` (A3 Entry 3).
5. **Character-theoretic / Fourier bounds on gross** — blocked by non-semisimplicity
   (`HANDOFF.md` §6j, as corrected in A0). The reopened directions are radical-aware
   weight invariants and the homological/cover route (this effort).
6. **Single-sheet decoupling** (Entry 5): relaxing the shared-β coupling
   between the two sheets (i.e. bounding `dist(u + d2c·z, Stab)` alone) is
   provably insufficient — weight-6 cover stabilizers occupy the same affine
   data. Any valid argument must keep the off-supp(b) puncture of m(b).
7. **Multi-cut leverage** (Entry 5): all six cut positions give the SAME
   slice minima (m_j(b) is cut-independent) — the six decompositions are an
   invariance, not independent inequalities. Useful only for choosing a
   convenient cut inside a proof.
8. **Pure counting for the k ≥ 8 tail** (Entry 6): `|b| ≥ 6k − 2e(S)` plus
   Turán-type bounds closes k ≤ 7 and then goes vacuous; don't try to push
   clique-freeness past k = 7 (the needed edge densities become realizable).

---

## 6. Traps and lessons (read before computing)

- **The "fully analytic" constraint (§1)** is the single most important rule.
  A kernel-`decide` base case is *not* analytic. Don't let a tempting finite
  check become load-bearing.
- **Never trust a hand-rolled SAT/CNF without a sanity ladder.** The scout script
  `scripts/a1_smith_sector_sat.py` reports "safe sector min = 6" — *impossible*
  (would mean `d≤6`, contradicting the `d=12` certificate). It's an encoding bug.
  The validated replacements are `a3_s_nonzero_sat.py` / `a3_s0_subcase.py`
  (their encodings reproduce `d=12` first). A cleanup chip was filed to annotate
  the buggy script.
- **Sampling is trap-shaped.** This program's prior conjectures died "held on 400+
  samples, then a hostile counterexample." The Entry-1 sampling lead (s≠0 ⇒ ≥16)
  was only trusted after the validated SAT confirmed it (true value 14). Always
  confirm a sampling pattern with a validated exact method, and hunt adversarially.
- **Citations:** the program was burned by a nonexistent paper ("Pesah–Roffe
  2025") and an over-paraphrased theorem (Jitman–Ling). A1 verified every
  load-bearing citation against the source. The two flagged re-checks are
  **DISCHARGED (2026-06-12, source-verified)**: Chen–Xie–Ding
  `arXiv:2402.02853` Thm 2.1 is verbatim the "generalized van Lint theorem"
  (§2, attributed Chen–Ding 2023 [5] ← van Lint 1991 [28]; Plotkin component
  code-constrained, exactly the hypothesis gross violates; "may be wrong if q
  odd" caveat confirmed); Postema–Kokkelmans `arXiv:2502.17052` authors/title/
  v4-abstract quote confirmed (Otjens appears only in the acknowledgments;
  the "no closed-form formula" line remains apocryphal — 0 grep hits). The
  three "Otjens 2025 / Otjens 2.18" rows in `T2.3_literature_survey.md` were
  relabeled "PK Thm 2.18 (from Arnault et al. 2026)". Bonus: PK Thm 2.18 is
  the generalised Bravyi–Terhal bound imported from Arnault–Gaborit–Rozendaal–
  Saussay–Zémor (IEEE TIT 72(1), 2026), vacuous below n = 8192 — "vacuous at
  gross" inference is valid.
- **A0 errors I fixed (don't reintroduce):** the saturation claim `d_cover=2·d_base`
  is false at `72→36` (6≠2·4); bb_90 and bb_108 *do* have rigorous odd-h bases
  with `k'=8` (an earlier A0 said none did). See `A0_baseline.md` obs. 2–3.

---

## 7. Artifact map

**Notes (read in order for full context):**
- `notes/A0_baseline.md` — scoreboard: per-Bravyi-code `d_A^⊥`, `c`, LP value,
  cover lattice. Key: gross has `d_A^⊥=d_B^⊥=12=d`, LP=2.
- `notes/A1_literature_L{1,2,3,4}.md` — verified literature (repeated-root /
  non-semisimple; cover-transfer & Smith; gross state-of-the-art; small-code
  anchors). L4 found `[[18,8,2]]=HGP(J₃,J₃)`, analytic d=2.
- `notes/A1_synthesis.md` — claims table, per-track impacts, ranked leads (§3 is
  gross-first), honest gaps, supplementary gap round.
- `notes/A2_scouting.md` — the 3-tracks-collapse-to-one result; ranking; first
  work-block; kill criterion; serial-vs-ultracode division of labor.
- `notes/A3_track1p1_log.md` — **the live log.** Entries 0 (framework) → 4
  (Fork B degraded) → 5 (the m(b) collapse) → 6–7 (analytic ladder, k ≤ 7)
  → 8–9 (profile route, verified-finite closure) → 10–12 (hand-organization:
  engine, floor, one-block 16, all six shape lemmas — classification fully
  hand-proven) → 13 (small-cycle theorem: m-rungs + (H0) discharged) →
  14 (**d(gross) ≥ 6 analytic** + dependency tree) → 15 (adversarial
  re-review: all links HOLD; **write-up grade**) → 16–18 (goal 1: the safe
  sector IS the Smith sector; (R) proven by the homotopy; the flux
  characterization via the no-double-wrap lemma; **d(gross) = 12 ⟺
  (M-im)**) → 19–26 (the (M-im) confined-floor program; **d(gross) = 12
  assembled**) → 27 (adversarial re-review of 16–26: every link HOLDS;
  grade = analytic spine + two machine-certified residues) → 28 (the A4
  extension: both residues discharged; **d(gross) = 12 fully
  analytic**). Resume from Entries 27–28 and the §0/§4 update blocks.
- `notes/A4_writeup.md` — **the standalone write-up, Theorems A–D.**
  Part I (review-cleared by Entry 15, Notes 1–2 folded in): Theorems A
  (small cycles; d(base) = 6 with explicit exhibit), B (d(gross) ≥ 6,
  minimal proof), C (dangerous sector ≥ 12 via (M)). Part II (Entry 28,
  review owed): Theorem D (d(gross) = 12, fully analytic) — the slot
  frame, the S(a,b) bucket walk, the locus tables, the ρ-link kills,
  with the compressed tables in Appendix C and the verification map in
  Appendix D.

**Scripts (all under `scripts/`, run via `uv run python scripts/<name>` from
`experiments/bb_lab/`):**
- `analytic_baseline.py` — regenerates `A0`.
- `a3_dangerous_structure.py` — TRUSTWORTHY facts F1–F5 (linear algebra + d=12).
- `a3_cut_decomposition.py` — verifies the `[[∂_nc,∂_c],[∂_c,∂_nc]]` sheet structure.
- `a3_delta_explicit.py` — `Δ=[∂₂c·z]`, verifies `im(Δ)=ker(tr_*)`.
- `a3_s_nonzero_sat.py` — **validated** SAT: s≠0 sector min = 14 (sanity ladder passes).
- `a3_s0_subcase.py` — **validated** SAT: [c]=0 subcase off-minimum (UNSAT ≤14).
- `a3_forkB_projection_bound.py` — μ_Z=μ_X=6; the (degrading) Fork-B bound.
- `a3_syndrome_split_probe.py` — the (sampling) Entry-1 lead; superseded by the SATs.
- `a3_mb_foundations.py` — **Entry 5 foundations, all-PASS**: per-cut blocks,
  Smith exactness per cut, dangerous parametrization, sheet formula, the
  pointwise weight identity, nontriviality bridge, η functionals.
- `a3_mb_scan.py` — light-b enumeration (exactly 36 hexagons + 216 D-pairs),
  m(b) for all light b (4 resp. ≥3; zero violations of (M)), cut-independence
  and translation-invariance checks, witness decodes.
- `a3_mb_structure.py` — T1–T6: difference sets/ov ≤ 1, clique data, local
  cycle-space rung facts (hexagon+2 sweep; pair-union+1 sweep), weight-6
  logical census (84 non-imΔ + 36 stabs, max hexagon overlap 2), ker ∂₂
  (min weight 16), shared-check ≤ 1, octahedron-freeness.
- `a3_mb_crosscheck.py` — C1: b≠0 dangerous min = 14 (direct cover SAT,
  matches the assembled ladder); C2: imΔ-distance = 12.
- `a3_mb_rigidity.py` — **Entry 10**: G1 ideal-rigidity catalog, G2 one-block
  exact minima (16), G3 R1 classification, G4 the master per-shape table.
- `a3_shape_lemmas.py` — **Entries 11–12, all-PASS**: V1 C-table, V2
  direction forcing, V3 R-(2,1,1) = dA-pairs, V4 sharpened one-block ≥ 16
  case analysis, V5 D-pair endgame, V6 R-(3,1,1) κ-table, V7/V8 the
  weight-5 classifications + kills + the comp-1 transfer identity.
- `a3_small_cycles.py` — **Entry 13, all-PASS**: W1 Ann minima, W3–W5 the
  per-split kill intermediates, W6 exhaustive no-cycle-≤5 (both sides),
  W7 weight-6 census = 120, W8 m-rung scaffolding, W9 the inversion
  duality (base AND gross).
- `a3_adv15_recheck.py` — **Entry 15**: the independent adversarial
  re-implementation (49 checks; y-major indexing, bitmask F₂ algebra,
  generator-side SAT hunt, own CRT frame). Confirmation only.
- `a3_adv27_recheck.py` — **Entry 27**: the independent adversarial
  re-implementation of Entries 16–26 (75 checks; conjugate CRT frame,
  own weight-6/8/10 census — the (M-im) endpoint is triple-machine-
  verified). Confirmation only.
- `a3_a4ext_recheck.py` — **Entry 28**: certifies every table of the A4
  Part-II write-up (the slot-frame facts F1–F6; S(a,b) ≡ 6 and the four
  wt-24 reindexings W1–W2; the 33 bucket minima W3; the per-cell linked
  floors and cost-8 kill K1; the C.2–C.4 locus tables K2; the 118
  achievers, the structure-lemma instance, and the 116/2/0 link-kill
  split K3–K4). Confirmation only.
- `a1_smith_*.py` — scout scaffolding. **`a1_smith_sector_sat.py` is BUGGY** (§6).
- `a1_es_four_terms.py`, `a1_es_purity_check.py`, `a1_srb_cover_chain_check.py` —
  substrate (ES exact-sequence (6,6,6,6); purity; SRB cover-chain verification).

**Commits:** `e308e65` (A0) → `b64868d` (A3 entry 4) on branch
`claude/focused-liskov-7fe9f7`; `b87ce85` (entry 5) → `e6bbaff` (entry 10)
on branch `claude/eager-hofstadter-6da593`; entries 11–14 on branch
`claude/competent-proskuriakova-f31540` (rebased continuation, includes the
buggy-scout flag commit). Each `A3` entry is one commit.

---

## 8. Concrete next steps (ranked)

1. ~~Adversarial re-review of the d(gross) ≥ 6 chain~~ **DONE (Entry 15):
   all links HOLD; the theorem is write-up grade.**
2. ~~Goal 1 (d = 12) — the safe-sector (M)-analogue~~ **DONE (Entries
   16–26), review-cleared (Entry 27): d(gross) = 12.** Epistemic grade:
   hand-proven reduction spine + the surveyable 18-orbit M-table + two
   machine-certified finite residues (the Entry-24 C-table evaluations
   and the Entry-25 achiever-list completeness).
3. ~~The A4 write-up extension~~ **DONE (Entry 28): A4 Part II
   (Theorem D) walks the compressed C-tables (the S(a,b) bucket walk)
   and derives the achiever lists (the locus tables + the
   achiever-structure lemma); Entry 15's Notes 1–2 and Entry 27's
   findings folded in. d(gross) = 12 fully analytic.**
4. **The owed skeptic pass over A4 Part II** (Entry-15/27 style): the
   prose vs. the certified tables, with special attention to the §12
   locus-table presentation grade (rule-derived with worked
   representatives; a reviewer may demand more worked cells).
5. **Goal 2 — template runs**: STARTED — see `notes/A5_goal2_log.md`
   (the goal-2 track log). Entry 1: the instance-hypothesis checker
   (`scripts/a5_instance_hypotheses.py`) + corpus sweeps — the
   empirical class {floor-bearing frame ∧ mult-free ∧ dA∩dB=∅} has
   58 members across Z6xZ6/Z15xZ3 (Entry-5 corrigendum; was miscounted
   54) with zero d < 6 exceptions — but see Entries 6–7: that class
   def is INCOMPLETE (needs (iii)).
   Entry 2: **bb_108 template run DONE — d(bb_108) ≥ 6 analytic**
   (Z₂-frame engine, μ(Ann) = 12 via the gross d₃ dictionary pulled
   back through Z₉×Z₃ → Z₃²; confirmation
   `scripts/a5_bb108_smallcycles.py`, W1–W7 PASS), plus the Theorem-B
   transfer to its two n = 216 free-Z₂ covers. Entry 3: gap analysis —
   proposed class-theorem shape with hypotheses (a)–(d); the missing
   deeper-2-part engine and the census-dependence of the (1,3)/(2,2)
   kills are the open gaps. Entry 4: **bb_90 template run DONE —
   d(bb_90) ≥ 6 analytic** (semisimple engine, μ(Ann) = 10 via 5-fold
   pullback to d₃; every kill is projection arithmetic, census-free;
   `scripts/a5_bb90_smallcycles.py` W1–W7 PASS) — the grid is 3-for-3
   across frame shapes, all floors tracing to the single dictionary
   row d₃((3,F)) = 2 (corrected in Entry 7: only the two PULLBACK
   floors; the base uses the layer engine). Entry 5: the (iv)/(v)
   census sweep — 58/58 class members pass, conjectured
   (C-iv)/(C-v). **Entries 6–7 (2026-06-13): (C-iv)/(C-v) as stated
   are FALSE** — a 26-agent workflow's corpus hunt + a human
   verification pass found the **Z3×Z5 family (6 members, d = 4)**
   with full (a)+(b) but a weight-4 (3,1) cycle. The fix is to add
   **(iii) mirrored-projection** as load-bearing: corrected
   conjecture (C-iv′)/(C-v′) = (a)+(b)+(iii) ⟹ d ≥ 6, zero
   counterexamples. The 3 templates survive independent re-derivation.
   Open: the presentation-free multiplicity-profile residue lemma
   (with the Entry-7-corrected even-period weight lemma as ingredient),
   or accept it as a per-instance surveyable check. Next: that lemma;
   (M)-analogue on the bb_108/bb_90 covers (true d = 10).
6. **Maintain `A3_track1p1_log.md`** as the running log for the gross
   arc, and `A5_goal2_log.md` for goal 2; commit per entry.

---

## 9. Lab cheat-sheet

- **Run:** `uv run python scripts/<name>.py` from `experiments/bb_lab/`. Tests:
  `uv run pytest` (~75s). Install dev deps once: `uv sync --extra dev`.
- **Conventions:** `AbelianGroup.index` is row-major (`(x,y) ↦ x·m+y`); sheet =
  `(x ≥ 6)`; base projection `(x,y) ↦ (x mod 6, y)`.
- **Verified numbers (discovery only, never load-bearing):** `d_gross=12`,
  `d_base=6`, `d_A^⊥=d_B^⊥=12`, LP floor `=2` (c=8), `pr_*` rank 6/ker 6,
  dangerous reps `=τ(u)` weight 12, factor-2 cases (s=0,[c]≠0)=12 / (s≠0)=14 /
  ([c]=0)≥16 (Entry-5 sharpening), `μ_Z=μ_X=6`, ES terms `(6,6,6,6)`,
  dangerous = ES non-pure sector. Entry 5/6 layer: light stabilizers = 36
  hexagons (w 6) + 216 D-pairs (w 10) only; m(0)=6, m(hex)=4, m(pair)≥3;
  slice minima 12/14/16; b≠0 dangerous min = 14; imΔ-distance = 12;
  ker ∂₂ min weight 16; weight-6 logicals: 84 non-imΔ + 36 stabs.
- **Don't** run two `lake`/heavy processes concurrently; don't suppress stderr on
  Lean script invocations (a guardrail blocks `2>/dev/null` there); `data/*.duckdb`
  is read-only for this work.
