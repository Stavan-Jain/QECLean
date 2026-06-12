# A_HANDOFF — analytic distance-bound effort for gross / BB codes

**Read this first.** This is the canonical handoff for the "Phase A" program:
finding an *analytic* lower bound on the minimum distance `d` of bivariate-
bicycle (BB) quantum codes, especially the gross code `[[144,12,12]]`. It
supersedes the Tier-1-era parts of `HANDOFF.md` for this specific effort and
ties together the `A0`–`A3` notes. Date of handoff: 2026-06-10; updated
2026-06-12 (Entries 5–6: the m(b) collapse and its analytic ladder).

---

## 0. RESUME HERE (the one-paragraph version)

The attack is the **h=2 cover-transfer theorem** (gross is the free-Z₂ double
cover of `[[72,12,6]]`). As of Entry 5 the previous open "fibre-disjointness /
s≠0" lemma is **dissolved**: the whole dangerous sector is graded by the
projected stabilizer `b = p(v)` via the verified, hand-checkable slice identity

> min{|v| : v nontrivial dangerous, p(v) = b} = |b| + 2·m(b),
> m(b) := min{|(d2c·z_b + u') off supp b| : u' a base 1-cycle, [u'] ∉ imΔ}

(cut-independent — the s=0/s≠0/[c]=0 trichotomy of Entries 1–3 was a
cut-coordinate artifact), so the factor-2 lemma is exactly **(M): |b| + 2·m(b)
≥ 12 for every base Z-stabilizer b**. Entry 6 built the analytic ladder for
(M): `b = 0` and `|b| ≥ 12` proven; the light-b classification proven for
face-supports k ≤ 7 (hexagon-overlap ≤ 1, K₄-freeness, and — Entry 7 —
octahedron-freeness of the overlap Cayley graph, all with full hand proofs;
k = 7 closed via Turán uniqueness); the m-rungs (m(hexagon) ≥ 3,
m(D-pair) ≥ 2) verified exhaustively with hand-proof routes sketched. **The single remaining
unbounded-structure gap is the k ≥ 8 tail**: every base Z-stabilizer whose
minimal face support is ≥ 8 has weight ≥ 12 — a *classical* statement about
one abelian 2-block group code, squarely in the repeated-root/van-Lint lane.
Start at `notes/A3_track1p1_log.md` Entries 5–6 and `scripts/a3_mb_*.py`.

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

### What is and isn't proven

- **Analytically proven** (given `d_base=6` as the transfer input, used only
  at b=0): safe sector ≥ 6; the m(b) reduction itself; (M) on the rungs b=0,
  |b| ≥ 12, and light-b classification through face-support k ≤ 7
  (ov ≤ 1 + K₄-freeness — Entry 6; octahedron-freeness — Entry 7; all full
  hand proofs).
- **Verified finite facts with hand-proofs owed:** the two m-rung locality
  facts (hexagon+2, pair-union+1).
- **Open** (true with margin per SAT): the k ≥ 8 tail — see §4.
- **Therefore: no fully-analytic improvement on `d ≥ 2` exists yet.** Do not
  claim one. (Unchanged — the ladder is not yet closed.)

---

## 4. The precise open problem (where to push)

*(Superseded form: Entries 0–4 posed this as the s≠0 "fibre-disjointness"
case; Entry 5 proved that case split is a cut artifact and replaced it with
the b-graded form below. The Entry-3 "affine syndrome class" diagnosis of why
classical Plotkin fails remains correct — the cure is the puncture in m(b).)*

The factor-2 lemma is exactly **(M): |b| + 2·m(b) ≥ 12 for every base
Z-stabilizer b** (Entry 5; all reductions verified, `a3_mb_foundations.py`).
Status of (M) by rung (Entry 6):

| rung | statement | status |
|---|---|---|
| b = 0 | m(0) ≥ 6 | PROVEN given d_base ≥ 6 (only place d_base is used) |
| \|b\| ≥ 12 | trivial | PROVEN |
| classification | light b = 36 hexagons ∪ 216 D-pairs | PROVEN for face-support k ≤ 7 (Entry 7 closed the octahedron check by hand); **OPEN for k ≥ 8 (the tail)** |
| m(hexagon) ≥ 3 | no non-imΔ cycle in hexagon+2 qubits | verified exhaustively; local hand proof owed |
| m(D-pair) ≥ 1 | cycle space of the 11-qubit pair union = the two columns | verified (rank 9, all 12 types); hand proof owed |

**The open tail (L-C).** Prove: every `b ∈ Stab_Z(base)` whose minimal face
support (mod ker ∂₂, dim 6, min weight 16) is ≥ 8 has `|b| ≥ 12`. Equivalently:
the [72,30] image code of `z ↦ (B·z, A·z)` over `F₂[Z₆×Z₆]` has no weight-≤11
codeword beyond the k ≤ 2 families. True with margin (validated SAT
enumeration: NO light codewords at any k ≥ 3).

State of the attack (Entry 8, `a3_mb_tail_dictionary.py`): the CRT frame
`F₂[Z₆²] ≅ F₂[Z₂²] × (F₄[Z₂²])⁴` is fully instrumented — layer dictionary
d₃ over F₂[Z₃²] (verified; depends only on (#orbits, trivial-flag)),
empirical component transforms, support grammar (radical sides are
co-point-or-full; comp 4 rigid). The bound `|b| ≥ COST(pattern(z))` is tight
on hexagons (6) and D-pairs (10). **Verified lemma: every b with |b| ≤ 11
has all five CRT components alive** (killing any one forces COST ≥ 12).
Remaining for the tail: (i) hand-organize the two finite minimizations;
(ii) equality analysis showing each sub-12-cost pattern class (explicit
list: 4 at cost 6 = hexagon patterns; 24/85/136 near-hexagon at 7–9;
456/904 at 10–11 incl. the D-pair family) is realized at weight ≤ 11 only
by hexagons and D-pairs mod kernel. Forcing tools: weight-1 full-support
layers are δ-points; co-point ideal coefficient rigidity; comp-4 support
equality; S₀ shared between blocks. Counting alone (`6k − 2e(S)`) stays
vacuous for large k — don't go back to it.

**Verification discipline before trusting any drafted argument:** run an
adversarial skeptic sweep hunting a light stabilizer with k ≥ 8 (the kill
criterion for a drafted tail proof is a counterexample to an intermediate
claim, not to (M) itself — (M) is SAT-validated). Computation may *refute*
but never *prove*.

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
- `notes/A3_track1p1_log.md` — **the live log.** Entries 0 (framework) → 4 (Fork B
  killed) → 5 (the m(b) collapse) → 6 (the analytic ladder; k ≤ 7 closed).
  Resume from Entries 5–6.

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
- `a1_smith_*.py` — scout scaffolding. **`a1_smith_sector_sat.py` is BUGGY** (§6).
- `a1_es_four_terms.py`, `a1_es_purity_check.py`, `a1_srb_cover_chain_check.py` —
  substrate (ES exact-sequence (6,6,6,6); purity; SRB cover-chain verification).

**Commits:** `e308e65` (A0) → `b64868d` (A3 entry 4) on branch
`claude/focused-liskov-7fe9f7`; `b87ce85` (entry 5) → `5a05ab0` (entry 6) on
branch `claude/eager-hofstadter-6da593` (fast-forward continuation). Each
`A3` entry is one commit.

---

## 8. Concrete next steps (ranked)

1. **The k ≥ 8 tail (§4; Entries 7–8).** The CRT/layer-dictionary frame is
   instrumented and produced the all-components-alive lemma; continue with
   the equality analysis over the explicit sub-12-cost pattern list (≤ 9
   band first: δ-point forcing should give hexagon-only; then the 10–11
   band where D-pairs live), and hand-organize the two finite
   minimizations. `scripts/a3_mb_tail_dictionary.py` is the working
   instrument. Time-box; failures are first-class outputs (A3 log).
2. **Hand-organize the owed finite checks**: the two rung locality proofs
   (shared-check ≤ 1 is already proven; residue = one-hexagon neighborhood
   analysis). (Octahedron-freeness: DONE by hand, Entry 7.)
3. **Assemble the conditional factor-2 write-up** once 1–2 land, then redo the
   recursion bookkeeping (Entry 4's caution: the safe sector caps the
   full-code bound at d_base — the factor-2 protects, not doubles, the
   inherited bound).
4. **If the tail stalls:** the A2 fallback (structural `d([[36,8,4]]) ≥ 4`
   composing with odd-h SRB Thm 4.7 for `d(bb_108) ≥ 4`) still stands; note
   the m(b) machinery is cover-generic and should transfer to the 36→72 step.
5. **Maintain `A3_track1p1_log.md`** as the running log; commit per entry.

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
