# A_HANDOFF — analytic distance-bound effort for gross / BB codes

**Read this first.** This is the canonical handoff for the "Phase A" program:
finding an *analytic* lower bound on the minimum distance `d` of bivariate-
bicycle (BB) quantum codes, especially the gross code `[[144,12,12]]`. It
supersedes the Tier-1-era parts of `HANDOFF.md` for this specific effort and
ties together the `A0`–`A3` notes. Date of handoff: 2026-06-10.

---

## 0. RESUME HERE (the one-paragraph version)

The effort chose, after a literature sweep and a scouting pass, a single attack:
the **h=2 cover-transfer theorem** (gross is the free-Z₂ double cover of
`[[72,12,6]]`). The framework is fully built and verified; the problem is reduced
to **one open lemma**. The lemma — call it **fibre-disjointness** — is:

> For every nontrivial cover logical `v=(v₀,v₁)` whose two sheets share a
> **nonzero** base syndrome `s = ∂₁c·p(v)` (the "s≠0" case), `|v| ≥ 2·d_base`.

This is **true** (validated SAT: such `v` have weight ≥ 14 > 12) but has **no
analytic proof yet**, and Entry 4 of `A3_track1p1_log.md` proves this lemma is
*necessary* (no elementary shortcut beats the floor). Start at
`notes/A3_track1p1_log.md` Entry 3–4 and `scripts/a3_*.py`. The crux in one
line: in Plotkin coordinates `v=(a, a+b)`, the s≠0 case forces `a` into an
*affine syndrome class* `{a : ∂₁a = ∂₁c·b}` rather than a distance-`d` code, so
the classical Plotkin/van-Lint double-cover bound does not apply; bridging that
is the new mathematics.

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

### The factor-2 lemma and its three cases (located — `a3_s_nonzero_sat.py`, `a3_s0_subcase.py`)

Target: `d_cover ≥ 2·d_base` on the dangerous sector (the only thing that beats
the floor — see §4). Reparametrize `v=(a, a+b)` with `b = p(v)`, `|v|=|a|+|a+b|`
(classical `[u|u+v]` shape); cycle condition ⟺ `∂₁a = ∂₁c·b =: s`.

| case | min weight (validated SAT) | analytic status |
|---|---|---|
| **s=0, [c]≠0** (both sheets nontrivial base logicals) | **12** (achieved) | **PROVEN**: `|v₀|,|v₁| ≥ d_base ⇒ |v| ≥ 2·d_base` |
| s=0, [c]=0 | ≥ 15 (UNSAT ≤14) | off-minimum; analytic ≥12 still owed |
| **s≠0** (seam leakage) | 14 (UNSAT ≤13) | **off-minimum; the open crux** |

The minimum is carried entirely by the one case with a clean proof. The SAT
encodings **pass a sanity ladder** (they reproduce `d=12`) — this is the
validation the buggy scout script lacked (see §5).

### What is and isn't proven

- **Analytically proven** (given `d_base=6` as the transfer input): safe sector
  ≥ 6; clean dangerous case (s=0,[c]≠0) ≥ 12.
- **Open** (true with margin per SAT, no analytic proof): s≠0 ⇒ ≥12; s=0,[c]=0 ⇒ ≥12.
- **Therefore: no fully-analytic improvement on `d ≥ 2` exists yet.** Do not
  claim one. The clean case alone does not bound the whole code.

---

## 4. The precise open problem (where to push)

Prove, analytically: **for `v=(a,a+b)` with `b` a nonzero base stabilizer and
`∂₁a = ∂₁c·b ≠ 0`, `|a|+|a+b| ≥ 2·d_base`.**

Why it's hard (pinned in `A3` Entry 3): the classical Plotkin/van-Lint
double-cover bound `d = min{2·d(C₁), d(C₂)}` needs the first component to range
over a *code with its own distance*. Here `a` ranges over an *affine syndrome
class* `{a : ∂₁a = ∂₁c·b}`, which contains arbitrarily light vectors. (This is
the concrete form of the KP-2013 Thm-8 hypothesis `k^(1+x)=k` that gross
violates.) The crude fix — correct each sheet by a min-weight syndrome rep `e`
(`∂₁e=s`) — gives `|v| ≥ 2·d_base − 2|e|`, losing `2|e|`; it only closes at `s=0`.
The validated truth (≥14) shows the seam structure forces `a, a+b` into *heavy*
classes (not merely nontrivial); capturing that is the new mathematics.

**Candidate angles (untried or partial):**
- A seam-aware weight argument that bounds `|a|` below using that `s = ∂₁c·b` is
  supported only on the 36-entry seam and `b` is a structured base stabilizer.
- KP-2013 Thms 8–9 §IV.E `u = (1+σ)w + γᵀG_Z` decomposition adapted to track the
  γᵀG_Z "degeneracy" terms across the seam (Track 1.3 vocabulary, A1-L2).
- Smith / equivariant arguments: the residual obstruction is the connecting map
  `Δ = ∩ω`; no QEC application of Smith theory exists (A1-L2), so this is genuinely
  new. Degtyarev–Kharlamov App. A.1 / Bredon Ch. 3 are the topology references.
- Exploit gross's extra `x↔y` automorphism for a finite *structural* reduction —
  but only if the reduction is analytic and the residue is a few surveyable cases
  (NOT a `decide` over the whole ball; that fails the constraint, §1).

**Verification discipline before trusting any drafted argument:** run an
adversarial skeptic sweep hunting a cover stabilizer that mixes the two sheets to
drop a dangerous rep below 12 (this is the kill criterion). Computation may
*refute* but never *prove*.

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
  load-bearing citation against the source. Two still need re-checking before any
  write-up: the Chen–Xie–Ding `arXiv:2402.02853` "Thm 2.1 Plotkin" attribution
  (the abstract is a repeated-root cyclic-codes paper), and confirm the
  Postema–Kokkelmans (not "Otjens 2025") `arXiv:2502.17052` quote.
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
  killed). Resume from Entry 3–4.

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
- `a1_smith_*.py` — scout scaffolding. **`a1_smith_sector_sat.py` is BUGGY** (§6).
- `a1_es_four_terms.py`, `a1_es_purity_check.py`, `a1_srb_cover_chain_check.py` —
  substrate (ES exact-sequence (6,6,6,6); purity; SRB cover-chain verification).

**Commits:** `e308e65` (A0) → `b64868d` (A3 entry 4), on branch
`claude/focused-liskov-7fe9f7`. Each `A3` entry is one commit.

---

## 8. Concrete next steps (ranked)

1. **Attack the s≠0 fibre-disjointness lemma (§4).** This is *the* problem and is
   now known to be necessary (not just sufficient). Try the seam-aware weight
   argument and the KP-2013 γᵀG_Z adaptation first; Smith/`Δ=∩ω` if those stall.
   Time-box per approach; failures are first-class outputs (write them in `A3`).
2. **Re-verify the two flagged citations** (§6) before any write-up.
3. **If Track 1.1 stalls:** the fallback per A2 is the goal-2 deliverable
   *structural* `d([[36,8,4]]) ≥ 4` (NOT a `decide`/ILP — must be a structural
   argument on the balanced-product logical space), which composes with the
   already-published *odd-h* SRB Thm 4.7 to give a fully-analytic `d(bb_108) ≥ 4`
   — the first analytic bound on a Bravyi instance. Test whether the technique
   scales to gross's 144-qubit space before investing.
4. **Maintain `A3_track1p1_log.md`** as the running log; commit per entry.

---

## 9. Lab cheat-sheet

- **Run:** `uv run python scripts/<name>.py` from `experiments/bb_lab/`. Tests:
  `uv run pytest` (~75s). Install dev deps once: `uv sync --extra dev`.
- **Conventions:** `AbelianGroup.index` is row-major (`(x,y) ↦ x·m+y`); sheet =
  `(x ≥ 6)`; base projection `(x,y) ↦ (x mod 6, y)`.
- **Verified numbers (discovery only, never load-bearing):** `d_gross=12`,
  `d_base=6`, `d_A^⊥=d_B^⊥=12`, LP floor `=2` (c=8), `pr_*` rank 6/ker 6,
  dangerous reps `=τ(u)` weight 12, factor-2 cases (s=0,[c]≠0)=12 / (s≠0)=14 /
  ([c]=0)≥15, `μ_Z=μ_X=6`, ES terms `(6,6,6,6)`, dangerous = ES non-pure sector.
- **Don't** run two `lake`/heavy processes concurrently; don't suppress stderr on
  Lean script invocations (a guardrail blocks `2>/dev/null` there); `data/*.duckdb`
  is read-only for this work.
